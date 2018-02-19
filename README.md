# Formal Spec of Snapshot Isolation in TLA+

This is a TLA+ specification that can be used for exploring and understanding the details of snapshot isolation. I wrote it partly as a pseronal exercise and partly as a way to way to share the semantics and definitions of snapshot isolation with other engineers. I tried to abstract things very heavily in this spec, so as to make it as simple as possible without removing necessary details. I wanted the spec to focus more on high level concepts than on how a particular system might actually implement snapshot isolation. The comments in the spec explain in more detail the structure of the model and things are modeled the way they are. I drew some inspiration (and a few of the more tricky definitions) from Chris Newcombe's specification of snapshot isolation, which is a bit more complex than mine. As far as I can tell, he presented a few of his specs in a "Debugging Designs" talk at a [conference in 2011](http://hpts.ws/papers/2011/agenda.html). His two snapshot isolation specs are very well structured and documented.

# Verifying Properties with TLC

One of the great parts about a spec written in TLA+ is that you can verify certain properties using the TLC model checker. There a few properties already defined in the specification that you can try to verify yourself. Two concurrency anomalies that snapshot isolation allows, Write Skew and a ["read only" transaction anomaly](https://www.cs.umb.edu/~poneil/ROAnom.pdf) are included with examples, and as a `ReadOnlyAnomaly` property that can be checked using TLC. The main invariant to check is that every history is serializable. This can be expressed with the following invariant:

	`IsSerializable(txnHistory)

TODO: Finish this section...