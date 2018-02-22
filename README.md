# Specification of Snapshot Isolation in TLA+

This is a TLA+ specification that can be used for exploring and understanding the details of snapshot isolation. I wrote it partly as a personal exercise and partly as an attempt to share the ideas and semantics of snapshot isolation with other engineers in a precise manner. I tried to abstract things very heavily in this spec; I wanted to make it as simple as possible without removing necessary details. I wanted the spec to focus more on high level concepts than on how a particular system might actually implement snapshot isolation. The comments in the spec explain in more detail the structure of the model and why things are modeled the way they are. I drew some inspiration (and a few of the more tricky definitions) from Chris Newcombe's specification of snapshot isolation, which is a bit more complex than mine. He presented a few of his specs in a "Debugging Designs" talk at a [HPTS conference in 2011](http://hpts.ws/papers/2011/agenda.html). His two snapshot isolation specs are very thorough and well documented.

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