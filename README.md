# Specification of Snapshot Isolation in TLA+

This is a TLA+ specification that can be used for exploring and understanding snapshot isolation. I wrote it partly as a personal exercise and partly as an attempt to share the ideas and semantics of snapshot isolation with other engineers in a precise manner. My goal was to make this spec as simple as possible without removing necessary details. I wanted to focus more on high level concepts than on how a particular system might actually implement snapshot isolation. The comments explain in more detail the structure of the model and the various correctness properties. I drew some inspiration (and a few of the more tricky definitions) from Chris Newcombe's specification of snapshot isolation, which is a bit more complex than mine. He presented a few of his specs in a "Debugging Designs" talk at a [HPTS conference in 2011](http://hpts.ws/papers/2011/agenda.html). His two snapshot isolation specs are very thorough and well documented.

## Checking Properties with TLC

There a few properties already defined in the specification that you can try to verify yourself. Two concurrency anomalies that snapshot isolation allows, Write Skew and a ["read only" transaction anomaly](https://www.cs.umb.edu/~poneil/ROAnom.pdf) are included with examples, and there is a `ReadOnlyAnomaly` property that can be checked using TLC. The main invariant to check is that every history is serializable (which is expected to be violated by anomalous histories). To get started with a TLC model, you can use the following values for spec's `CONSTANT` parameters:

	Empty   <- Model value
	txnIds 	<- {t0, t1, t2}	    (Symmetry set of model values)
	keys 	<- {k1, k2}         (Symmetry set of model values)
	values 	<- {v1, v2}         (Symmetry set of model values)

You can choose `Spec` as the temporal formula and set either of the following two expressions as invariants to check:

*Assert that all histories are serializable:*

```tla
 IsSerializable(txnHistory)
 ```

*Assert that there are no non-serializable histories with a read-only transaction anomaly:*

```tla
 ~ReadOnlyAnomaly(txnHistory)
 ```

Both of these invariants should be violated in specific cases. By running the model checker you can see what kinds of histories violate these invariants.

## Model Checking Statistics

For reference, I was able to produce a trace that violated the `~ReadOnlyAnomaly(txnHistory)` invariant in 1 hour and 4 minutes running TLC on a 12-core (Intel i7-4930K CPU @ 3.40GHz) Ubuntu Linux workstation. It generated a bit over 405 million distinct states and it took a 12 step trace to violate the invariant. While TLC was running it seemed to produce at least ~80GB of auxiliary data on disk, but I did not measure it precisely. You can see the detailed output of this run below:

TLC command line parameters:
```
% java tlc2.TLC -cleanup -gzip -workers 12 -metadir /hdd/tlc_states -config MC.cfg MC.tla

TLC2 Version 2.12 of 29 January 2018
Running breadth-first search Model-Checking with 12 workers on 12 cores with 7143MB heap and 64MB offheap memory (Linux 4.8.0-59-generic amd64, Oracle Corporation 1.8.0_131 x86_6
4).
```

TLC invariant violation output (only last state of trace shown):

```
State 12: <Next line 288, col 12 to line 290, col 36 of module SnapshotIsolation>
/\ txnSnapshots = ( t0 :> (k1 :> Empty @@ k2 :> v1) @@
  t1 :> (k1 :> v1 @@ k2 :> Empty) @@
  t2 :> (k1 :> v1 @@ k2 :> Empty) )
/\ dataStore = (k1 :> v1 @@ k2 :> v1)
/\ txnHistory = << [type |-> "begin", txnId |-> t0, time |-> 1],
                   [type |-> "read", txnId |-> t0, key |-> k1, val |-> Empty],
                   [type |-> "begin", txnId |-> t1, time |-> 2],
                   [type |-> "write", txnId |-> t1, key |-> k1, val |-> v1],
                   [type |-> "commit", txnId |-> t1, time |-> 3, updatedKeys |-> {k1}],
                   [type |-> "begin", txnId |-> t2, time |-> 4],
                   [type |-> "read", txnId |-> t2, key |-> k1, val |-> v1],
                   [type |-> "read", txnId |-> t2, key |-> k2, val |-> Empty],
                   [type |-> "write", txnId |-> t0, key |-> k2, val |-> v1],
                   [type |-> "commit", txnId |-> t0, time |-> 5, updatedKeys |-> {k2}],
                   [type |-> "commit", txnId |-> t2, time |-> 6, updatedKeys |-> {}] >>
/\ clock = 6
/\ runningTxns = {}

529068865 states generated, 405673796 distinct states found, 357574338 states left on queue.
The depth of the complete state graph search is 13.
The average outdegree of the complete state graph is 8 (minimum is 0, the maximum 17 and the 95th percentile is 12).
Finished in 01h 04min at (2018-02-21 23:41:43)
```

Interestingly, running TLC in simulation mode (using the `-simulate` flag) produces a violating trace in just under 3 minutes, on the same hardware. This speedup may be due to the fact that, to produce this particular anomaly, a sufficiently long trace is required. Searching the state space in a breadth first manner (TLC's default) would require the checking of all possible "short" traces before testing out any longer ones. In fact, running TLC simulation in parallel, with 12 cores, often produced a violating trace in under a minute. It seems that simulation mode may be better at finding "interesting" traces more quickly than standard model checking model, at least for this particular model.

```
  % java tlc2.TLC -simulate -cleanup -gzip -workers 12 -metadir /hdd/tlc_states -config MC.cfg MC.tla                                                                      !10179
TLC2 Version 2.12 of 29 January 2018
Running Random Simulation with seed 6802238540282724400 with 12 workers on 12 cores with 7143MB heap and 64MB offheap memory (Linux 4.8.0-59-generic amd64, Oracle Corporation 1.8
.0_131 x86_64).

...


State 13:
/\ txnSnapshots = ( t0 :> (k1 :> Empty @@ k2 :> v2) @@
  t1 :> (k1 :> v2 @@ k2 :> Empty) @@
  t2 :> (k1 :> v2 @@ k2 :> Empty) )
/\ dataStore = (k1 :> v2 @@ k2 :> v2)
/\ txnHistory = << [type |-> "begin", txnId |-> t0, time |-> 1],
   [type |-> "begin", txnId |-> t1, time |-> 2],
   [type |-> "read", txnId |-> t0, key |-> k1, val |-> Empty],
   [type |-> "write", txnId |-> t1, key |-> k1, val |-> v2],
   [type |-> "commit", txnId |-> t1, time |-> 3, updatedKeys |-> {k1}],
   [type |-> "begin", txnId |-> t2, time |-> 4],
   [type |-> "read", txnId |-> t0, key |-> k2, val |-> Empty],
   [type |-> "read", txnId |-> t2, key |-> k1, val |-> v2],
   [type |-> "read", txnId |-> t2, key |-> k2, val |-> Empty],
   [type |-> "write", txnId |-> t0, key |-> k2, val |-> v2],
   [type |-> "commit", txnId |-> t2, time |-> 5, updatedKeys |-> {}],
   [type |-> "commit", txnId |-> t0, time |-> 6, updatedKeys |-> {k2}] >>
/\ clock = 6
/\ runningTxns = {}

The number of states generated: 3489180
Simulation using seed 6802238540282724400 and aril 4642022
Progress: 3489180 states checked.
Finished in 02min 42s at (2018-02-24 11:38:10)
```



