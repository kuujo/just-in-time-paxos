# JITPaxos

This project provides a [TLA+] specification for the Just-In-Time Paxos consensus protocol.

JITPaxos is a variant of the Paxos consensus protocol designed for environments where
process clocks are synchronized with high precision.  The protocol
relies on synchronized clocks to establish a global total ordering of
events, avoiding coordination between replicas when requests arrive in
the expected order, and reconciling requests only when they arrive out
of order.  This allows JITPaxos to reach consensus within a single
round trip in the normal case, falling back to traditional replication
strategies only when required.

## Summary
* Protocol moves through a sequence of views
* Each view deterministically assigns a primary plus a set of replicas that form a quorum
* Client requests are timestamped using the client's local system clock and sent by the
client in parallel to all replicas in the view's quorum
* Replicas maintain a commit log, appending requests to the log in chronological order
* The primary dictates the final order of the log and executes client requests
* If a request is received out of chronological order it is rejected
* Replicas reply to clients with a checksum of the local log
* If the primary rejects a request, it must be retried with a new timestamp
* If the primary accepts a request, the client compares checksums for each replica to the
primary's checksum; if checksums do not match, the client initiates a reconciliation protocol
* The reconciliation protocol reconciles inconsistencies in the log by replicating the
primary's log to the quorum
* Once the client receives matching acknowledgements from all the replicas in the quorum a request 
is committed
* During view changes, the new primary selects the most recent log from a majority of replicas
and replicates the log to the view quorum, ensuring the view is initialized with all commits
from prior views
* Clocks satisfy sequential consistency, and quorums satisfy linearizability across views

## Protocol
JITPaxos uses a view-based approach to elect a primary and reconcile
logs across views.  Views are identified by a monotonically increasing,
globally unique view ID.  Each view deterministically assigns a quorum,
and within the quorum a primary replica responsible for executing
client requests and reconciling inconsistencies in the logs of the
remaining replicas.  JITPaxos replicas to not coordinate with each
other in the normal case.  Clients send timestamped requests in
parallel to every replica in the view's quorum.  When a replica
receives a client request, if the request is received in chronological
order, it's appended to the replica's log.  If a request is received
out of order (i.e.  the request timestamp is less than the last
timestamp in the replica's log), the request is rejected by the
replica.  Clients are responsible for identifying inconsistencies in
the quorum's logs and initiating the reconciliation protocol.  To help
clients identify inconsistencies, replicas return a checksum
representing the contents of the log up to the request point with each
client reply.  If a client's request is received out of chronological
order, or if the checksums provided by the quorum do not match, the
client must initiate the reconcilitation protocol to reconcile the
inconsistencies in the quorum's logs.

When requests are received out-of-order, the reconciliation protocol
works to re-order requests using the view's primary as a reference.
When a client initiates the reconciliation protocol for an inconsistent
replica, the replica stops accepting client requests and sends a repair
request to the primary.  The primary responds with the subset of the
log not yet reconciled on the replica, and the replica replaces the
out-of-order entries in its log.  Once the replica's log has been
reconciled with the primary, it can acknowledge the reconciled request
and begin accepting requests again.  Once a client has reconciled all
the divergent replicas and has received acknowledgement from each of
the replicas in the quorum, the request can be committed.

View primaries and quorums are evenly distributed amongst view IDs.
View changes can be initiated to change the primary or the set of
replicas in the quorum.  When a view change is initiated, each replica
sends its log to the primary for the initiated view.  Once the primary
has received logs from a majority of replicas, it initializes the view
with the log from the most recent in-sync replica, broadcasting the log
to its peers.  The use of quorums to determine both the commitment of a
request and the initialization of new views ensures that each view log
contains all prior committed requests.

[NOPaxos]: https://www.usenix.org/system/files/conference/osdi16/osdi16-li.pdf
[TLA+]: https://lamport.azurewebsites.net/tla/tla.html