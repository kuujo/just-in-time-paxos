# JITPaxos

This project provides a [TLA+] specification for the JITPaxos consensus protocol.

Just-In-Time Paxos is a consensus protocol that relies on synchronized system clocks
to reach consensus without coordination. Using a novel approach that builds on prior 
work (like [NOPaxos]), JITPaxos can reach consensus in just a single round-trip in the
normal case. Messages are ordered using synchronized clocks, and replicas do not need
to coordinate with one another unless a message is lost. When messages are lost or
arrive out of order, replicas coordinate with each other to recover lost messages
and ensure their logs are consistent.

[NOPaxos]: https://www.usenix.org/system/files/conference/osdi16/osdi16-li.pdf
[TLA+]: https://lamport.azurewebsites.net/tla/tla.html