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

vars == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory>>

\* Model bounds.
BNat == 0..8
BSeq(x) == UNION {[1..n -> x] : n \in 1..8}

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

\* Produces the set of all keys updated by a given transaction id.
UpdatedKeys(txnId) == 
    LET writeOps == {op \in Range(txnHistory) : /\ op.type = "write" 
                                                /\ op.txnId = txnId } IN
    { writeOp.key : writeOp \in writeOps}

\* Checks whether a given transaction is allowed to commit, based on whether it conflicts
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

\******************************
\* Correctness Properties
\******************************

\* Returns an set containing all elements that participate in any cycle (i.e. union of all cycles), 
\* or an empty set if no cycle is found.
\*   
\* Taken from https://github.com/pron/amazon-snapshot-spec/blob/master/serializableSnapshotIsolation.tla.
FindAllNodesInAnyCycle(edges) ==

    LET RECURSIVE findCycleNodes(_, _)   (* startNode, visitedSet *)
        (* Returns a set containing all elements of some cycle starting at startNode,
           or an empty set if no cycle is found. 
         *)
        findCycleNodes(node, visitedSet) ==
            IF node \in visitedSet THEN
                {node}  (* found a cycle, which includes node *)
            ELSE
                LET newVisited == visitedSet \union {node}
                    neighbors == {to : <<from, to>> \in 
                                           {<<from, to>> \in edges : from = node}}
                IN  (* Explore neighbors *)
                    UNION {findCycleNodes(neighbor, newVisited) : neighbor \in neighbors}
                    
        startPoints == {from : <<from, to>> \in edges}  (* All nodes with an outgoing edge *)
    IN 
        UNION {findCycleNodes(node, {}) : node \in startPoints}
       
IsCycle(edges) == FindAllNodesInAnyCycle(edges) /= {}


\*  In the serialization graph, we put an edge from one committed transaction T1
\*  to another committed transaction T2 in the following situations:
\*  
\*   - T1 produces a version of x, and T2 produces a later version of x (this is a ww-dependency);
\*   - T1 produces a version of x, and T2 reads this (or a later) version of x (this is a wr-dependency);
\*   - T1 reads a version of x, and T2 produces a later version of x (this is a rw-dependency, also
\*          known as an anti-dependency, and is the only case where T1 and T2 can run concurrently).

CommitTime(h, txnId) == LET commitOp == CHOOSE op \in Range(h) : op.txnId = txnId IN commitOp.time
BeginTime(h, txnId)  == LET beginOp  == CHOOSE op \in Range(h) : op.txnId = txnId IN beginOp.time

CommittedTxns(h) == LET committedTxnOps == {op \in Range(h) : op.type = "commit"} IN
                        {op.txnId : op \in committedTxnOps}
                        
ReadsByTxn(h, txnId)  == {op \in Range(h) : op.txnId = txnId /\ op.type = "read"}
WritesByTxn(h, txnId) == {op \in Range(h) : op.txnId = txnId /\ op.type = "write"}

\* T1 wrote to a key that T2 then also wrote to. The First Committer Wins rule
\* that T1 must have committed before T2 began.
WWDependency(h, t1Id, t2Id) == 
    \E op1 \in WritesByTxn(h, t1Id) :
    \E op2 \in WritesByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ CommitTime(h, t1Id) < CommitTime(h, t2Id)

\* T1 wrote to a key that T2 then later read, after T1 committed.
WRDependency(h, t1Id, t2Id) == 
    \E op1 \in WritesByTxn(h, t1Id) :
    \E op2 \in ReadsByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ CommitTime(h, t1Id) < BeginTime(h, t2Id)    

\* T1 read a key that T2 then later wrote to.
RWDependency(h, t1Id, t2Id) == 
    \E op1 \in ReadsByTxn(h, t1Id) :
    \E op2 \in WritesByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ BeginTime(h, t1Id) < CommitTime(h, t2Id)    

SerializationGraph(history) == 
    LET committedTxnIds == CommittedTxns(history) IN
    {<<t1, t2>> \in (committedTxnIds \X committedTxnIds):
        /\ t1 /= t2
        /\ \/ WWDependency(history, t1, t2)
           \/ WRDependency(history, t1, t2)
           \/ RWDependency(history, t1, t2)}

HistWW == << [type |-> "begin"  , txnId |-> 0 , time |-> 0],
             [type |-> "write"  , txnId |-> 0 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 0 , time |-> 1, updatedKeys |-> {"k1"}],
             [type |-> "begin"  , txnId |-> 1 , time |-> 2],
             [type |-> "write"  , txnId |-> 1 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 1 , time |-> 2, updatedKeys |-> {"k1"}]>>

HistWR == << [type |-> "begin"  , txnId |-> 0 , time |-> 0],
             [type |-> "write"  , txnId |-> 0 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 0 , time |-> 2, updatedKeys |-> {"k1"}],
             [type |-> "begin"  , txnId |-> 1 , time |-> 1],
             [type |-> "read"   , txnId |-> 1 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 1 , time |-> 3, updatedKeys |-> {}]>>

IsSerializable == ~IsCycle(SerializationGraph(txnHistory))

\******************************
\* The spec definition.
\******************************

Init ==  
    /\ runningTxns = {} 
    /\ txnHistory = <<>>
    /\ clock = 0
    /\ txnSnapshots = [id \in txnIds |-> Empty]
    /\ dataStore = [k \in keys |-> Empty]

\* Checks if all transactions finished i.e. committed or aborted.
AllTxnsFinished == LET finishOps == {op \in Range(txnHistory) : op.type \in {"commit", "abort"}} IN
                        {op.txnId : op \in finishOps} = txnIds
    
Next == \/ StartTxn 
        \/ CompleteTxn
        \/ \E txn \in runningTxns :
            TxnReadWrite(txn)
        \* Having all transactions finish is a valid termination, so we have this 
        \* action to prevent it from being interpreted as a deadlock.
        \/ (AllTxnsFinished /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


=============================================================================
\* Modification History
\* Last modified Tue Feb 06 23:39:57 EST 2018 by williamschultz
\* Created Sat Jan 13 08:59:10 EST 2018 by williamschultz
