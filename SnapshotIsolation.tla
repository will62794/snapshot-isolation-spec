------------------------- MODULE SnapshotIsolation -------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

(**************************************************************************************************)
(* This is a specification of snapshot isolation.  It is based on various sources, integrating    *)
(* ideas and definitions from:                                                                    *)
(*                                                                                                *)
(*     ``Making Snapshot Isolation Serializable", Fekete et al., 2005                             *)
(*     https://www.cse.iitb.ac.in/infolab/Data/Courses/CS632/2009/Papers/p492-fekete.pdf          *)
(*                                                                                                *)
(*     "Serializable Isolation for Snapshot Databases", Cahill, 2009                              *)
(*     https://ses.library.usyd.edu.au/bitstream/2123/5353/1/michael-cahill-2009-thesis.pdf       *)
(*                                                                                                *)
(*     "Debugging Designs", Chris Newcombe, 2011                                                  *)
(*     https://github.com/pron/amazon-snapshot-spec/blob/master/DebuggingDesigns.pdf              *)
(*                                                                                                *)
(* This spec tries to model things at a very high level of abstraction, so as to communicate the  *)
(* important concepts of snapshot isolation, as opposed to how a system might actually implement  *)
(* it.                                                                                            *)
(*                                                                                                *)
(* There is a fixed set of unique transaction ids, and each transaction can execute read/write    *)
(* operations on a key-value store.  We model an actual key-value data store in this spec, but    *)
(* this wouldn't be necessary for verifying the abstract properties of snapshot isolation, since  *)
(* the serializability definitions used below don't depend on the actual data that is being read  *)
(* or written, only the dependency relationships between the reads and writes of concurrent       *)
(* transactions.                                                                                  *)
(**************************************************************************************************)


(**************************************************************************************************)
(* The constant parameters of the spec.                                                           *)
(**************************************************************************************************)

\* Set of all transaction ids.
CONSTANT txnIds

\* Set of all data store keys/values.
CONSTANT keys, values

\* An empty value.
CONSTANT Empty

(**************************************************************************************************)
(* The variables of the spec.                                                                     *)
(**************************************************************************************************)

\* The clock, which measures 'time', is just a counter, that increments (ticks) 
\* whenever a transaction starts or commits.
VARIABLE clock

\* The set of all currently running transactions.
VARIABLE runningTxns

\* The set of snapshots needed for all running transactions. Each snapshot 
\* represents the entire state of the data store as of a given point in time. 
\* It is a function from transaction ids to data store snapshots.
VARIABLE txnSnapshots

\* The key-value data store.
VARIABLE dataStore

\* The full history of all transaction operations. It is modeled as a linear 
\* sequence of events. Such a history would likely never exist in a real implementation, 
\* but it is used in the model to check the properties of snapshot isolation.
VARIABLE txnHistory

vars == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory>>


(**************************************************************************************************)
(* Data type definitions.                                                                         *)
(**************************************************************************************************)

DataStoreType == [keys -> (values \cup {Empty})]
BeginOpType   == [type : {"begin"}  , txnId : txnIds , time : Nat]
CommitOpType  == [type : {"commit"} , txnId : txnIds , time : Nat, updatedKeys : SUBSET keys]
WriteOpType   == [type : {"write"}  , txnId : txnIds , key: SUBSET keys , val : SUBSET values]
ReadOpType    == [type : {"read"}   , txnId : txnIds , key: SUBSET keys , val : SUBSET values]
AnyOpType     == UNION {BeginOpType, CommitOpType, WriteOpType, ReadOpType}

(**************************************************************************************************)
(* The type invariant and initial predicate.                                                      *)
(**************************************************************************************************)

TypeInvariant == 
    \* This seems expensive to check with TLC, so disable it for now.
\*  /\ txnHistory   \in Seq(AnyOpType)
    /\ dataStore    \in DataStoreType
    /\ txnSnapshots \in [txnIds -> (DataStoreType \cup {Empty})]
    /\ runningTxns  \in SUBSET [ id : txnIds, 
                                startTime  : Nat, 
                                commitTime : Nat \cup {Empty}]

Init ==  
    /\ runningTxns = {} 
    /\ txnHistory = <<>>
    /\ clock = 0
    /\ txnSnapshots = [id \in txnIds |-> Empty]
    /\ dataStore = [k \in keys |-> Empty]

(**************************************************************************************************)
(* Helper functions for querying transaction histories.                                           *)
(*                                                                                                *)
(* These are parameterized on a transaction history and a transaction id, if applicable.          *)
(**************************************************************************************************)

\* Generic TLA+ helper.
Range(f) == {f[x] : x \in DOMAIN f}

\* The begin or commit op for a given transaction id.
BeginOp(h, txnId)  == CHOOSE op \in Range(h) : op.txnId = txnId /\ op.type = "begin"
CommitOp(h, txnId) == CHOOSE op \in Range(h) : op.txnId = txnId /\ op.type = "commit"

\* The set of all committed/aborted transaction ids in a given history.
CommittedTxns(h) == {op.txnId : op \in {op \in Range(h) : op.type = "commit"}}
AbortedTxns(h)   == {op.txnId : op \in {op \in Range(h) : op.type = "abort"}}

\* The set of all read or write ops done by a given transaction.                   
ReadsByTxn(h, txnId)  == {op \in Range(h) : op.txnId = txnId /\ op.type = "read"}
WritesByTxn(h, txnId) == {op \in Range(h) : op.txnId = txnId /\ op.type = "write"}

\* The set of all keys read or written to by a given transaction.                   
KeysReadByTxn(h, txnId)    == { op.key : op \in ReadsByTxn(txnHistory, txnId)}
KeysWrittenByTxn(h, txnId) == { op.key : op \in WritesByTxn(txnHistory, txnId)}

\* The index of a given operation in the transaction history sequence.
IndexOfOp(h, op) == CHOOSE i \in DOMAIN h : h[i] = op

(**************************************************************************************************)
(*                                                                                                *)
(* Action Definitions                                                                             *)
(*                                                                                                *)
(**************************************************************************************************)


(**************************************************************************************************)
(* When a transaction starts, it gets a new, unique transaction id and is added to the set of     *)
(* running transactions.  It also "copies" a local snapshot of the data store on which it will    *)
(* perform its reads and writes against.  In a real system, this data would most not be literally *)
(* "copied", but this is the fundamental concept of snapshot isolation i.e.  that each            *)
(* transaction appears to operate on its own local snapshot of the database.                      *)
(**************************************************************************************************)

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
                          
                        
(**************************************************************************************************)
(* When a transaction T0 is ready to commit, it obeys the "First Committer Wins" rule.  T0 will   *)
(* only successfully commit if no concurrent transaction has already committed writes of data     *)
(* objects that T0 intends to write.  Transactions T0, T1 are considered concurrent if the        *)
(* intersection of their timespans is non empty i.e.                                              *)
(*                                                                                                *)
(*     [start(T0), commit(T0)] \cap [start(T1), commit(T1)] != {}                                 *)
(*                                                                                                *)
(**************************************************************************************************)

\* Checks whether a given transaction is allowed to commit, based on whether it conflicts
\* with other concurrent transactions that have already committed.
TxnCanCommit(txn) == 
    ~\E op \in Range(txnHistory) :
        /\ op.type = "commit" 
        /\ op.time > txn.startTime 
        /\ KeysWrittenByTxn(txnHistory, txn.id) \cap op.updatedKeys /= {} \* Must be no conflicting keys.
         
CommitTxn(txn) == 
    \* Transaction must be able to commit i.e. have no write conflicts with concurrent.
    \* committed transactions.
    /\ TxnCanCommit(txn)  
    /\ LET commitOp == [ type          |-> "commit", 
                         txnId         |-> txn.id, 
                         time          |-> clock + 1,
                         updatedKeys   |-> KeysWrittenByTxn(txnHistory, txn.id)] IN
       txnHistory' = Append(txnHistory, commitOp)            
    \* Merge this transaction's updates into the data store. If the 
    \* transaction has updated a key, then we use its version as the new
    \* value for that key. Otherwise the key remains unchanged.
    /\ dataStore' = [k \in keys |-> IF k \in KeysWrittenByTxn(txnHistory, txn.id) 
                                        THEN txnSnapshots[txn.id][k]
                                        ELSE dataStore[k]]
    \* Remove the transaction from the active set. 
    /\ runningTxns' = runningTxns \ {txn}
    /\ clock' = clock + 1
    \* We can leave the snapshot around, since it won't be used again.
    /\ UNCHANGED <<txnSnapshots>>

(**************************************************************************************************)
(* In this spec, a transaction aborts if and only if it cannot commit, due to write conflicts.    *)
(* If an uncommitted transaction ends up in a state where its writes are in conflict with         *)
(* another, committed transaction, it will either continue to do some reads/writes of other keys, *)
(* or abort, but never commit.                                                                    *)
(**************************************************************************************************)

AbortTxn(txn) ==
    \* If a transaction can't commit due to write conflicts, then it
    \* must abort.
    /\ ~TxnCanCommit(txn)
    /\ LET abortOp == [ type   |-> "abort", 
                        txnId  |-> txn.id, 
                        time   |-> clock + 1] IN    
       txnHistory' = Append(txnHistory, abortOp)
    /\ runningTxns' = runningTxns \ {txn} \* transaction is no longer running.
    /\ clock' = clock + 1
    \* No changes are made to the data store.
    /\ UNCHANGED <<dataStore, txnSnapshots>>

\* Ends a given transaction by either committing or aborting it. To exclude uninteresting 
\* histories, we require that a transaction does at least one operation before committing or aborting. 
\* Assumes that the given transaction is currently running.
CompleteTxn(txn) == 
    \* Must not be a no-op transaction.
    /\ (WritesByTxn(txnHistory, txn.id) \cup ReadsByTxn(txnHistory, txn.id)) /= {}
    \* Commit or abort the transaction.
    /\ \/ CommitTxn(txn)
       \/ AbortTxn(txn)

(**************************************************************************************************)
(* Read and write operations executed by transactions.                                            *)
(*                                                                                                *)
(* As a simplification, and to limit the size of potential models, we allow transactions to only  *)
(* read or write to the same key once.  The idea is that it limits the state space without loss   *)
(* of generality.                                                                                 *)
(**************************************************************************************************)

TxnRead(txn, k) == 
    \* Read from this transaction's snapshot.
    LET valRead == txnSnapshots[txn.id][k]
        readOp == [ type  |-> "read", 
                    txnId |-> txn.id, 
                    key   |-> k, 
                    val   |-> valRead] IN
    /\ txnHistory' = Append(txnHistory, readOp)
    /\ UNCHANGED <<dataStore, clock, runningTxns, txnSnapshots>>
                   
TxnUpdate(txn, k, v) == 
    LET writeOp == [ type  |-> "write", 
                     txnId |-> txn.id, 
                     key   |-> k, 
                     val   |-> v] IN    
    \* We update the transaction's snapshot, not the actual data store.
    /\ LET updatedSnapshot == [txnSnapshots[txn.id] EXCEPT ![k] = v] IN
           txnSnapshots' = [txnSnapshots EXCEPT ![txn.id] = updatedSnapshot]
    /\ txnHistory' = Append(txnHistory, writeOp)
    /\ UNCHANGED <<dataStore, runningTxns, clock>>

\* A read or write action by a running transaction. We limit transactions
\* to only read or write the same key once.
TxnReadWrite(txn) == 
       \E k \in keys : 
       \E v \in values :
            \/ TxnRead(txn, k) /\ k \notin KeysReadByTxn(txnHistory, txn.id)
            \/ TxnUpdate(txn, k, v) /\ k \notin KeysWrittenByTxn(txnHistory, txn.id)
            
            
(**************************************************************************************************)
(* The next-state relation and spec definition.                                                   *)
(*                                                                                                *)
(* Since it would be desirable to have TLC check for deadlock, which may indicate bugs in the     *)
(* spec or in the algorithm, we want to explicitly define what a "valid" termination state is.    *)
(* If all transactions have run and either committed or aborted, we consider that valid           *)
(* termination, and is allowed as an infinite suttering step.                                     *)
(*                                                                                                *)
(* Also, once a transaction knows that it cannot commit due to write conflicts, we don't let it   *)
(* do any more reads or writes, so as to eliminate wasted operations.                             *)
(**************************************************************************************************)           

AllTxnsFinished == AbortedTxns(txnHistory) \cup CommittedTxns(txnHistory) = txnIds
    
Next == \/ StartTxn 
        \/ \E txn \in runningTxns : 
                \/ CompleteTxn(txn)
                \/ TxnReadWrite(txn) /\ TxnCanCommit(txn)
        \/ (AllTxnsFinished /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


----------------------------------------------------------------------------------------------------


(**************************************************************************************************)
(*                                                                                                *)
(* Correctness Properties and Tests                                                               *)
(*                                                                                                *)
(**************************************************************************************************)



(**************************************************************************************************)
(* Operator for computing cycles in a given graph, defined by a set of edges.                     *)
(*                                                                                                *)
(* Returns a set containing all elements that participate in any cycle (i.e.  union of all        *)
(* cycles), or an empty set if no cycle is found.                                                 *)
(*                                                                                                *)
(* Source:                                                                                        *)
(* https://github.com/pron/amazon-snapshot-spec/blob/master/serializableSnapshotIsolation.tla.    *)
(**************************************************************************************************)
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



(**************************************************************************************************)
(* In order to check the serializability of transaction histories, we construct a multi-version   *)
(* serialization graph (MVSG).  Details on MVSG can be found in Cahill's thesis, Section 2.5.1.   *)
(* The important rules about how to build this graph are listed below.                            *)
(*                                                                                                *)
(* To construct the MSVG, we put an edge from one committed transaction T1 to another committed   *)
(* transaction T2 in the following situations:                                                    *)
(*                                                                                                *)
(*   (WW-Dependency)                                                                              *)
(*   T1 produces a version of x, and T2 produces a later version of x.                            *)
(*                                                                                                *)
(*   (WR-Dependency)                                                                              *)
(*   T1 produces a version of x, and T2 reads this (or a later) version of x.                     *)
(*                                                                                                *)
(*   (RW-Dependency)                                                                              *)
(*   T1 reads a version of x, and T2 produces a later version of x. This is                       *)
(*   the only case where T1 and T2 can run concurrently.                                          *)
(*                                                                                                *)
(**************************************************************************************************)

\* T1 wrote to a key that T2 then also wrote to. The First Committer Wins rule
\* that T1 must have committed before T2 began.
WWDependency(h, t1Id, t2Id) == 
    \E op1 \in WritesByTxn(h, t1Id) :
    \E op2 \in WritesByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ CommitOp(h, t1Id).time < CommitOp(h, t2Id).time

\* T1 wrote to a key that T2 then later read, after T1 committed.
WRDependency(h, t1Id, t2Id) == 
    \E op1 \in WritesByTxn(h, t1Id) :
    \E op2 \in ReadsByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ CommitOp(h, t1Id).time < BeginOp(h, t2Id).time   

\* T1 read a key that T2 then later wrote to.
RWDependency(h, t1Id, t2Id) == 
    \E op1 \in ReadsByTxn(h, t1Id) :
    \E op2 \in WritesByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ IndexOfOp(h, op2) > IndexOfOp(h, op1)           \* T2's write occurred after T1's read.
        /\ BeginOp(h, t1Id).time < CommitOp(h, t2Id).time  \* T1 starts before T2 commits.

\* Produces the serialization graph as defined above, for a given history.
SerializationGraph(history) == 
    LET committedTxnIds == CommittedTxns(history) IN
    {<<t1, t2>> \in (committedTxnIds \X committedTxnIds):
        /\ t1 /= t2
        /\ \/ WWDependency(history, t1, t2)
           \/ WRDependency(history, t1, t2)
           \/ RWDependency(history, t1, t2)}

\* The key property to verify i.e. serializability of transaction histories.
IsSerializable(h) == ~IsCycle(SerializationGraph(h))

\* Examples of each dependency type.

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

HistRW == << [type |-> "begin"  , txnId |-> 0 , time |-> 0],
             [type |-> "write"  , txnId |-> 0 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 0 , time |-> 2, updatedKeys |-> {"k1"}],
             [type |-> "begin"  , txnId |-> 1 , time |-> 1],
             [type |-> "read"   , txnId |-> 1 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 1 , time |-> 3, updatedKeys |-> {}]>>
     
     
(**************************************************************************************************)
(* Examples of concurrency phenomena under Snapshot Isolation.  These are for demonstration       *)
(* purposes and can be used for checking the above definitions of serializability.                *)
(*                                                                                                *)
(* Write Skew:                                                                                    *)
(*                                                                                                *)
(* Example history from Michael Cahill's Phd thesis:                                              *)
(*                                                                                                *)
(* Section 2.5.1, pg.  16                                                                         *)
(* https://ses.library.usyd.edu.au/bitstream/2123/5353/1/michael-cahill-2009-thesis.pdf           *)
(*                                                                                                *)
(* H: r1(x=50) r1(y=50) r2(x=50) r2(y=50) w1(x=-20) w2(y=-30) c1 c2                               *)
(*                                                                                                *)
(*                                                                                                *)
(* Read-Only Anomaly:                                                                             *)
(*                                                                                                *)
(* "A Read-Only Transaction Anomaly Under Snapshot Isolation", Fekete, O'Neil, O'Neil             *)
(* https://www.cs.umb.edu/~poneil/ROAnom.pdf                                                      *)
(*                                                                                                *)
(*                                                                                                *)
(**************************************************************************************************)

WriteSkewAnomalyTest == <<
    [type |-> "begin",  txnId |-> 1, time |-> 1],                       
    [type |-> "begin",  txnId |-> 2, time |-> 2],
    [type |-> "read",   txnId |-> 1, key |-> "X"],                      
    [type |-> "read",   txnId |-> 1, key |-> "Y"],                      
    [type |-> "read",   txnId |-> 2, key |-> "X"],                      
    [type |-> "read",   txnId |-> 2, key |-> "Y"],                    
    [type |-> "write",  txnId |-> 1, key |-> "X", val |-> 30],           
    [type |-> "write",  txnId |-> 2, key |-> "Y", val |-> 20],        
    [type |-> "commit", txnId |-> 1, time |-> 3, updatedKeys |-> {"X"}],
    [type |-> "commit", txnId |-> 2, time |-> 4, updatedKeys |-> {"Y"}]>>

ReadOnlyAnomalyTest == <<
    [type |-> "begin",  txnId |-> 0, time |-> 0], 
    [type |-> "write",  txnId |-> 0, key |-> "K_X", val |-> 0], 
    [type |-> "write",  txnId |-> 0, key |-> "K_Y", val |-> 0], 
    [type |-> "commit", txnId |-> 0, time |-> 1, updatedKeys |-> {"K_X", "K_Y"}],
    
    (* the history from the paper *) 
                     [type |-> "begin",  txnId |-> 2, time |-> 2], 
    (* R2(X0,0)   *) [type |-> "read",   txnId |-> 2, key |-> "K_X", ver |-> "T_0"], 
    (* R2(Y0,0)   *) [type |-> "read",   txnId |-> 2, key |-> "K_Y", ver |-> "T_0"],
                      
                     [type |-> "begin",  txnId |-> 1, time |-> 3], 
    (* R1(Y0,0)   *) [type |-> "read",   txnId |-> 1, key |-> "K_Y"], 
    (* W1(Y1,20)  *) [type |-> "write",  txnId |-> 1, key |-> "K_Y", val |-> 20],
    (* C1         *) [type |-> "commit", txnId |-> 1, time |-> 4, updatedKeys |-> {"K_Y"}],
     
                     [type |-> "begin",  txnId |-> 3, time |-> 5], 
    (* R3(X0,0)   *) [type |-> "read",   txnId |-> 3, key |-> "K_X", ver |-> "T_0"], 
    (* R3(Y1,20)  *) [type |-> "read",   txnId |-> 3, key |-> "K_Y", ver |-> "T_1"], 
    (* C3         *) [type |-> "commit", txnId |-> 3, time |-> 6, updatedKeys |-> {}],
                      
    (* W2(X2,-11) *) [type |-> "write",  txnId |-> 2, key |-> "K_X", val |-> 11], 
    (* C2         *) [type |-> "commit", txnId |-> 2, time |-> 7, updatedKeys |-> {"K_X"}]
    >>

(**************************************************************************************************)
(* Checks if a given history contains a "read-only" anomaly.  In other words, is this a           *)
(* non-serializable transaction history such that it contains a read-only transaction T, and      *)
(* removing T from the history makes the history serializable.                                    *)
(**************************************************************************************************)

ReadOnlyAnomaly(h) == 
    \* History is non-serializable.
    /\ ~IsSerializable(h)
    /\ \E txnId \in CommittedTxns(h) :
        \* Transaction only did reads.
        /\ WritesByTxn(h, txnId) = {}
        \* Removing the transaction makes the history serializable
        /\ LET txnOpsFilter(t) == (t.txnId # txnId)
           hWithoutTxn == SelectSeq(h, txnOpsFilter) IN
           IsSerializable(hWithoutTxn)

=============================================================================
\* Modification History
\* Last modified Wed Feb 21 23:23:08 EST 2018 by williamschultz
\* Created Sat Jan 13 08:59:10 EST 2018 by williamschultz
