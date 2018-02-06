------------------------- MODULE SnapshotIsolation -------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Set of all transaction ids.
CONSTANT txnIds
\* Set of all data store keys/values.
CONSTANT keys, values
CONSTANT Empty

\* The clock, which measures 'time', is simply a counter, that increments (ticks) whenever a transaction
\* starts or commits.
VARIABLE clock
\* The set of all currently running transactions.
VARIABLE runningTxns

\* The set of all ids that have already been used by a transaction. Must be a subset of 'txnIds'.
VARIABLE usedTxnIds

\* The set of snapshots needed for all running transactions. Each snapshot represents the entire state
\* of the data store as of a given point in time. It is a function from transaction ids to data store snapshots.
VARIABLE txnSnapshots
VARIABLE dataStore
VARIABLE txnHistory

DataStoreType == [keys -> (values \cup {Empty})]
TypeInvariant == 
    /\ dataStore \in DataStoreType
    /\ txnSnapshots \in [txnIds -> (DataStoreType \cup {Empty})]
    /\ runningTxns \in SUBSET [ id : txnIds, 
                                startTime : Nat, 
                                commitTime : Nat \cup {Empty},
                                updatedKeys : SUBSET keys]

(***************************************************************************)
(* When a transaction starts, it gets a new, unique transaction id and is  *)
(* added to the set of running transactions.  It also "copies" a local     *)
(* snapshot of the data store on which it will perform its reads and       *)
(* writes against.  In a real system, this data would most likely not be   *)
(* literally "copied", but this is the fundamental concept of snapshot     *)
(* isolation i.e. that each transaction appears to operate on its own local*)
(* snapshot of the database.                                               *)
(***************************************************************************)
StartTxn == \E txnId \in txnIds : 
                LET newTxn == 
                    [ id |-> txnId, 
                      startTime |-> clock+1, 
                      commitTime |-> Empty,
                      updatedKeys |-> {}] IN
                \* Must choose a txnId not already in use by a running transaction.
                /\ ~ (txnId \in usedTxnIds)
                /\ usedTxnIds' = usedTxnIds \cup {txnId}
                /\ runningTxns' = runningTxns \cup {newTxn}
                \* Save a snapshot of current data store for this transaction.
                /\ txnSnapshots' = [txnSnapshots EXCEPT ![txnId] = dataStore]
                /\ clock' = clock + 1
                /\ LET beginEvent == <<"BEGIN", txnId, clock+1>> IN
                   txnHistory' = Append(txnHistory, beginEvent)
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

TxnCanCommit(txn) ==
    \* There must be no txn that committed writes during the execution interval of this txn
    \* that conflict with this transaction's writes.
    ~\E i \in DOMAIN txnHistory :
        LET opCommit == txnHistory[i] 
            tCommit  == opCommit[4] 
            updatedKeys == opCommit[3] IN
        /\ opCommit[1] = "COMMIT" 
        /\ tCommit > txn.startTime 
        /\ txn.updatedKeys \cap updatedKeys # {} \* Must be no conflicting keys.
         
CommitTxn(txn) == 
    LET commitEvent == <<"COMMIT", txn.id, txn.updatedKeys, clock+1>> IN
    /\ TxnCanCommit(txn)
    /\ txnHistory' = Append(txnHistory, commitEvent)
    \* The transaction is over once it commits. 
    /\ runningTxns' = runningTxns \ {txn}
    /\ clock' = clock + 1
    \* Merge this transaction's updates into the data store. If the 
    \* transaction has updated a key, then we use its version as the new
    \* value for that key. Otherwise the key is unchanged.
    /\ dataStore' = [k \in keys |-> IF k \in txn.updatedKeys 
                                        THEN txnSnapshots[txn.id][k]
                                        ELSE dataStore[k]]
    /\ UNCHANGED <<txnSnapshots, usedTxnIds>>
        
AbortTxn(txn) ==
    LET abortEvent == <<"ABORT", txn.id, {}, clock+1>> IN
    /\ \neg TxnCanCommit(txn)
    /\ txnHistory' = Append(txnHistory, abortEvent)
    \* The transaction is over once it aborts. 
    /\ runningTxns' = runningTxns \ {txn}
    /\ clock' = clock + 1
    /\ UNCHANGED <<dataStore, txnSnapshots, usedTxnIds>>

CompleteTxn == 
    \E txn \in runningTxns :
        \/ CommitTxn(txn)
        \/ AbortTxn(txn)

(***************************************************************************)
(* Read and write actions on the key-value data store.                     *)
(***************************************************************************)

TxnRead(txn, k) == 
    \* Read from this transaction's snapshot.
    LET valRead == txnSnapshots[txn.id][k] IN
    LET readEvent == <<"READ", txn.id, valRead>> IN
    /\ txnHistory' = Append(txnHistory, readEvent)
    /\ UNCHANGED <<dataStore, clock, runningTxns, txnSnapshots, usedTxnIds>>
                   
TxnUpdate(txn, k, v) == 
    LET writeEvent == <<"WRITE", txn.id, k, v>> IN
    /\ txnHistory' = Append(txnHistory, writeEvent)
    /\ dataStore' = [dataStore EXCEPT ![k] = v]
    \* For simplicity keep track of all keys that this transaction updated.
    /\ runningTxns' = (runningTxns \ {txn}) \cup {[txn EXCEPT !.updatedKeys = txn.updatedKeys \cup {k}]}
    /\ UNCHANGED <<clock, txnSnapshots, usedTxnIds>>

Init ==  
    /\ runningTxns = {} 
    /\ txnHistory = <<>>
    /\ clock = 0
    /\ txnSnapshots = [id \in txnIds |-> Empty]
    /\ dataStore = [k \in keys |-> Empty]
    /\ usedTxnIds = {}

Next == \/ StartTxn 
        \/ CompleteTxn
        \/ \E txn \in runningTxns :
           \E k \in keys : 
           \E v \in values :
                \/ TxnRead(txn, k)
                \/ TxnUpdate(txn, k, v)

=============================================================================
\* Modification History
\* Last modified Mon Feb 05 21:54:34 EST 2018 by williamschultz
\* Created Sat Jan 13 08:59:10 EST 2018 by williamschultz
