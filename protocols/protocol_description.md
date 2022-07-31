Here we briefly describe the 27 distributed protocols evaluated by DuoAI. Their sources are referenced in the paper.

- `chord_ring_maintenance`: Implements a distributed hashtable. Nodes are organized in a dynamic ring, where each node can join or leave freely, leading to the restructuring of the ring. The protocol guarantees that the ring always satisfies some connectivity property.

- `consensus_forall`: Variant of `consensus_epr`. Ghost variables are introduced such that the protocol can be verified with only universally quantified invariants.

- `consensus_wo_decide`: Simplified version of `consensus_forall`. Participants select a leader by a quorum, without deciding on a value.

- `database_chain_replication`: Implements a database sharded across multiple nodes. Each transaction is split into sequential subtransactions. If a subtransaction satisfies a set of constraints (e.g., no reads until previous writes to the same location are committed), it can progress, otherwise it may abort. The protocol ensures linearizability and atomicity.

- `decentralized_lock`: Simplified version of `distributed_lock`. Nodes do not specify an epoch when transferring the lock and do not check the epoch when accepting the lock.

- `distributed_lock`: Nodes transfer ownership of a lock through messages via an unreliable network. Each node has its local clock (epochs). When transferring the lock, the sender includes a future epoch number in the message. When receiving a message with epoch *E*, a node only accept the lock (at epoch *E*) if *E* is greater than its own epoch.

- `ring_leader_election`: Nodes with distinct IDs are organized in a ring. Each node passes its ID to the next node (clockwise). When a node receives an ID larger than itself, it passes the received ID to the next node. A node becomes the leader when it receives its own ID. 

- `learning_switch_ternary`: Each switch in the network manages a routing table. When receiving a packet, the switch inserts a table entry if the source is not seen before. If the destination is in the table, the switch routes the packet accordingly, otherwise the switch flood the packet to all neighbors except the incoming one.

- `learning_switch_quad`: Variant of `learning_switch_ternary`. The pending packet is represented in a quad instead of ternary relation.

- `lock_server_async`: Extends `lock_server_sync`. Connection is established by asynchronous messages rather than atomically.

- `lock_server_sync`: Multiple clients try to connect to a server. The server maintains a semaphore, which is occupied when a client connects and freed when the client disconnect.

- `sharded_key_value_store`: A distributed key-value store. Each shard stores a portion of key-value pairs. One shard can transfer a key-value pair to another through an asynchronous message.

- `ticket_lock`: A first in first out synchronization protocol. The system maintains two ever-increasing global integers --- the current serving ticket and the next allocatable ticket. When a thread wants to enter the critical section, it gets the next allocatable ticket. The thread enters the critical section when the current serving ticket matches its own ticket, and increments the current serving ticket when it leaves.

- `toy_consensus_forall`: Variant of `toy_consensus_epr`. Ghost variables are introduced such that the protocol can be verified with only universally quantified invariants.

- `two_phase_commit`: An atomic commitment protocol. Participants are asked whether they are ready to commit. If the coordinator receives "Yes" from every participant, a commit message is sent to each participant, otherwise an abort message is sent.

- `client_server_ae`: Simplified version of `client_server_db_ae`. The server directly respond to each request without querying a database.

- `client_server_db_ae`: Multiple clients can send requests to a server. The server queries the database for each request and returns a response to the respective client. Both the server and the database may process the requests/queries out-of-order.

- `consensus_epr`: Reach consensus among reliable participants in an unreliable network. Participants can request votes from others. Upon receiving a request, a participant can send a vote to the requester. If a participant receives a quorum of votes, it can become the leader and decide on a value.

- `hybrid_reliable_broadcast`: Broadcast message in an asynchronous network. There are unreliable nodes that may fail to send messages when they are supposed to, and adversarial nodes that can send wrong messages. The protocol ensures that under certain constraints, honest nodes will only accept messages from other honest nodes.   

- `sharded_kv_no_lost_keys`: Variant of `sharded_key_value_store` with a different safety property.

- `toy_consensus_epr`: Simplified version of `consensus_epr`. Runs on a reliable network where all votes are globally visible.

- `paxos`: A textbook protocol to reach consensus among unreliable nodes. [The Wikipedia page](https://en.wikipedia.org/wiki/Paxos_(computer_science)) gives a nice description. One can read the [*Paxos made EPR*](https://dl.acm.org/doi/10.1145/3140568) paper to better understand this and other Paxos-family protocols and how they were encoded in Ivy.

- `flexible_paxos`: Extends `paxos`. `paxos` requires that all pairs of quorums intersect, while `flexible_paxos` only requires that quorums in Phase 1 intersect with quorums in Phase 2. The consensus guarantee is provably preserved.

- `multi_paxos`: Extends `paxos`. Nodes run a set of instances of `paxos` and reach consensus on each instance. Instances share the same round structure.

- `stoppable_paxos`: Extends `multi_paxos`. The instance set is totally ordered. A node can propose a special value called *stop*. If *stop* is decided in an instance, then no value will be decided on all greater instances. 

- `fast_paxos`: Variant of `paxos`. Apart from classic rounds, there are *fast* rounds in which any node can propose a value without going through the proposer. Additional mechanism is introduced to ensure consistency.

- `vertical_paxos`: Variant of `paxos`. An external reconfiguration master can dynamically assign configurations to rounds. Each configuration specifies a set of usable quorums. Nodes notify the master when a round is complete.
