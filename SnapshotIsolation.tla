------------------------- MODULE SnapshotIsolation -------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Set of all transaction ids.
CONSTANT txnIds

\* Set of all data store keys/values.
CONSTANT keys, values

\* An empty value.
CONSTANT Empty


\* The clock, which measures 'time', is just a counter, that increments (ticks) whenever a transaction
\* starts or commits.
VARIABLE clock

\* The set of all currently running transactions.
VARIABLE runningTxns

\* The set of snapshots needed for all running transactions. Each snapshot represents the entire state
\* of the data store as of a given point in time. It is a function from transaction ids to data store snapshots.
VARIABLE txnSnapshots

\* The key-value data store.
VARIABLE dataStore

\* The full history of all transaction operations. It is modeled as a linear sequence of events. 
\* Such a history would most likely never exist in a real implementation, but it is used in the model 
\* to check the properties of snapshot isolation.
VARIABLE txnHistory


\* Model bounds.
BNat == 0..12
BSeq(x) == UNION {[1..n -> x] : n \in BNat}

\* Data type definitions and the type invariant for the entire spec.
DataStoreType == [keys -> (values \cup {Empty})]
BeginOpType   == [type : {"begin"}  , txnId : txnIds , time : BNat]
CommitOpType  == [type : {"commit"} , txnId : txnIds , time : BNat, updatedKeys : SUBSET keys]
WriteOpType   == [type : {"write"}  , txnId : txnIds , key: SUBSET keys , val : SUBSET values]
ReadOpType    == [type : {"read"}   , txnId : txnIds , key: SUBSET keys , val : SUBSET values]
AnyOpType     == UNION {BeginOpType, CommitOpType, WriteOpType, ReadOpType}

TypeInvariant == 
    \* This seems expensive to check with TLC, so disable it for now.
\*  /\ txnHistory   \in BSeq(AnyOpType)
    /\ dataStore    \in DataStoreType
    /\ txnSnapshots \in [txnIds -> (DataStoreType \cup {Empty})]
    /\ runningTxns  \in SUBSET [ id : txnIds, 
                                startTime  : BNat, 
                                commitTime : BNat \cup {Empty}]

\* Generic helper function.
Range(f) == {f[x] : x \in DOMAIN f}

(***************************************************************************)
(* When a transaction starts, it gets a new, unique transaction id and is  *)
(* added to the set of running transactions.  It also "copies" a local     *)
(* snapshot of the data store on which it will perform its reads and       *)
(* writes against.  In a real system, this data would most likely not be   *)
(* literally "copied", but this is the fundamental concept of snapshot     *)
(* isolation i.e. that each transaction appears to operate on its own local*)
(* snapshot of the database.                                               *)
(***************************************************************************)
StartTxn == \E newTxnId \in txnIds : 
                LET newTxn == 
                    [ id |-> newTxnId, 
                      startTime |-> clock+1, 
                      commitTime |-> Empty] IN
                \* Must choose an unused transaction id. There must be no other operation
                \* in the history that already uses this id.
                /\ ~\E op \in Range(txnHistory) : op.txnId = newTxnId
                \* Save a snapshot of current data store for this transaction, and
                \* and append its 'begin' event to the history.
                /\ txnSnapshots' = [txnSnapshots EXCEPT ![newTxnId] = dataStore]
                /\ LET beginOp == [ type  |-> "begin", 
                                    txnId |-> newTxnId, 
                                    time  |-> clock+1 ] IN
                   txnHistory' = Append(txnHistory, beginOp)
                \* Add transaction to the set of active transactions.
                /\ runningTxns' = runningTxns \cup {newTxn}
                \* Tick the clock.
                /\ clock' = clock + 1    
                /\ UNCHANGED <<dataStore>>
                          
                        
(***************************************************************************)
(* When a transaction $T_i$ is ready to commit, it obeys the "First        *)
(* Committer Wins" rule.  $T_i$ will only successfully commit if no        *)
(* concurrent transaction has already committed writes of data objects     *)
(* that $T_i$ intends to write.  Transactions $T_i$,T_k$ are considered    *)
(* concurrent if [start(T_i), commit(T_i)] \cap [start(T_k), commit(T_k)]  *)
(* # {}                                                                    *)
(***************************************************************************)

\* Find transaction ids concurrent with 'txn' that already committed. Assumes 'txn' has not committed yet.
ConcurrentCommittedTxns(txn) == 
    LET historyInds == DOMAIN txnHistory
        txnIndices == 
        {i \in historyInds :
            (\E j \in historyInds :
                LET opBegin  == txnHistory[i]
                    opCommit == txnHistory[j] 
                    tCommit  == opCommit[3] IN
                /\ opBegin[1] = "BEGIN" /\ opCommit[1] = "COMMIT"
                /\ opBegin[2] = opCommit[2] \* txn ids must match.
                /\ tCommit > txn.startTime)} IN
    {txnHistory[k] : k \in txnIndices}

\* Produces the set of all keys updated by a given transaction id.
UpdatedKeys(txnId) == 
    LET writeOps == {op \in Range(txnHistory) : /\ op.type = "write" 
                                                /\ op.txnId = txnId } IN
    { writeOp.key : writeOp \in writeOps}

\* Checks wheter a given transaction is allowed to commit, based on whether it conflicts
\* with other concurrent transactions that have already committed.
TxnCanCommit(txn) ==
    \* There must be no transaction that committed writes during the execution interval of 
    \* this transaction that conflict with this transaction's writes.
    LET updatedKeys == UpdatedKeys(txn.id) IN
        ~\E op \in Range(txnHistory) :
            /\ op.type = "commit" 
            /\ op.time > txn.startTime 
            /\ updatedKeys \cap op.updatedKeys /= {} \* Must be no conflicting keys.
         
CommitTxn(txn) == 
    \* Transaction must be able to commit i.e. have no write conflicts with concurrent.
    \* committed transactions.
    /\ TxnCanCommit(txn)  
    \* Add 'commit' op to the global history.
    /\ LET commitOp == [ type          |-> "commit", 
                         txnId         |-> txn.id, 
                         time          |-> clock+1,
                         updatedKeys   |-> UpdatedKeys(txn.id)] IN
       txnHistory' = Append(txnHistory, commitOp)            
    \* Merge this transaction's updates into the data store. If the 
    \* transaction has updated a key, then we use its version as the new
    \* value for that key. Otherwise the key remains unchanged.
    /\ dataStore' = [k \in keys |-> IF k \in UpdatedKeys(txn.id) 
                                        THEN txnSnapshots[txn.id][k]
                                        ELSE dataStore[k]]
    \* The transaction is over once it commits, so we remove it from the active transaction set. 
    /\ runningTxns' = runningTxns \ {txn}
    /\ clock' = clock + 1
    \* We can leave the snapshot around, since it won't be used again.
    /\ UNCHANGED <<txnSnapshots>>
        
AbortTxn(txn) ==
    \* If a transaction can't commit due to write conflicts, then it
    \* must abort.
    /\ ~ TxnCanCommit(txn)
    /\ LET abortOp == [ type   |-> "abort", 
                        txnId  |-> txn.id, 
                        time   |-> clock+1] IN    
       txnHistory' = Append(txnHistory, abortOp)
    \* The transaction is over once it aborts. 
    /\ runningTxns' = runningTxns \ {txn}
    /\ clock' = clock + 1
    \* No changes are made to the data store. We can leave the snapshot around, 
    \* since it won't be used again.
    /\ UNCHANGED <<dataStore, txnSnapshots>>

\* An action that ends a running transaction by either committing or aborting it.
CompleteTxn == 
    \E txn \in runningTxns :
        \/ CommitTxn(txn)
        \/ AbortTxn(txn)

(***************************************************************************)
(* Read and write actions on the key-value data store.                     *)
(***************************************************************************)

TxnRead(txn, k) == 
    \* Read from this transaction's snapshot and save the event to the history.
    LET valRead == txnSnapshots[txn.id][k]
        readOp == [ type |-> "read", 
                    txnId |-> txn.id, 
                    key |-> k, 
                    val |-> valRead] IN
    /\ txnHistory' = Append(txnHistory, readOp)
    /\ UNCHANGED <<dataStore, clock, runningTxns, txnSnapshots>>
                   
TxnUpdate(txn, k, v) == 
    \* Execute a write and save the event to the history.
    LET writeOp == [ type |-> "write", 
                     txnId |-> txn.id, 
                     key |-> k, 
                     val |-> v] IN    
    /\ txnHistory' = Append(txnHistory, writeOp)
    \* We update the transaction's snapshot, not the actual data store.
    /\ LET updatedSnapshot == [txnSnapshots[txn.id] EXCEPT ![k] = v] IN
           txnSnapshots' = [txnSnapshots EXCEPT ![txn.id] = updatedSnapshot]
    /\ UNCHANGED <<dataStore, runningTxns, clock>>

Init ==  
    /\ runningTxns = {} 
    /\ txnHistory = <<>>
    /\ clock = 0
    /\ txnSnapshots = [id \in txnIds |-> Empty]
    /\ dataStore = [k \in keys |-> Empty]

\* Checks if a running transaction already read or wrote
\* to a given key.
AlreadyTouchedKey(txn, k, opType) == 
   \E op \in Range(txnHistory) :
        /\ op.txnId = txn.id
        /\ op.type = opType
        /\ op.key = k  

\* A read or write action by a running transaction. We limit transactions
\* to only read or write the same key once.
TxnReadWrite(txn) == 
       \E k \in keys : 
       \E v \in values :
            \/ TxnRead(txn, k) /\ ~AlreadyTouchedKey(txn, k, "read")
            \/ TxnUpdate(txn, k, v) /\ ~AlreadyTouchedKey(txn, k, "write")

Next == \/ StartTxn 
        \/ CompleteTxn
        \/ \E txn \in runningTxns :
            TxnReadWrite(txn)

\******************************
\* Correctness Properties
\******************************


\*  In the serialization graph, we put an edge from one committed transaction T1
\*  to another committed transaction T2 in the following situations:
\*  
\*   - T1 produces a version of x, and T2 produces a later version of x (this is a ww-dependency);
\*   - T1 produces a version of x, and T2 reads this (or a later) version of x (this is a wr-dependency);
\*   - T1 reads a version of x, and T2 produces a later version of x (this is a rw-dependency, also
\*          known as an anti-dependency, and is the only case where T1 and T2 can run concurrently).

CommitTime(txnId) == LET commitOp == CHOOSE op \in Range(txnHistory) : op.txnId = txnId IN
                     commitOp.time

WWDependency(history, t1, t2) == 
    \E opT1 \in Range(history) :
    \E opT2 \in Range(history) :  
        /\ opT1.txnId = t1 /\ opT2.txnId = t2
        /\ opT1.type = "write" /\ opT2.type = "write"
        /\ opT1.key = opT2.key
        /\ CommitTime(t2) > CommitTime(t1)

SerializationGraph(history) == 
    LET committedTxnOps == {op \in history : op.type = "commit"} 
        committedTxnIds == {op.id : op \in committedTxnOps} IN
    {<<t1, t2>> \in committedTxnIds :
        \/ WWDependency(history, t1, t2)}


=============================================================================
\* Modification History
\* Last modified Tue Feb 06 00:38:23 EST 2018 by williamschultz
\* Created Sat Jan 13 08:59:10 EST 2018 by williamschultz
