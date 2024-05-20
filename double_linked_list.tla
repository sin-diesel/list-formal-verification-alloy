------------------------------ MODULE double_linked_list -----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT 
    NodeId,
    Data 

VARIABLES 
    list,             
    mutexes,          
    next,             
    prev,             
    data              

NodeType == [id: NodeId, next: NodeId, prev: NodeId, data: Data]
MutexType == [locked: BOOLEAN]

Init ==
    /\ list = <<>>
    /\ mutexes = [n \in NodeId |-> [locked |-> FALSE]]
    /\ next = [n \in NodeId |-> n]
    /\ prev = [n \in NodeId |-> n]
    /\ data = [n \in NodeId |-> CHOOSE d: d \in Data]

NodeInList(node) == node \in list
ProperlyLinked(node) ==
    /\ next[node] \in NodeId
    /\ prev[next[node]] = node
    /\ prev[node] \in NodeId
    /\ next[prev[node]] = node

Invariant == \A node \in list: ProperlyLinked(node)
AcquireMutex(node) ==
    /\ mutexes[node].locked = FALSE
    /\ mutexes' = [mutexes EXCEPT ![node].locked = TRUE]

ReleaseMutex(node) ==
    /\ mutexes[node].locked = TRUE
    /\ mutexes' = [mutexes EXCEPT ![node].locked = FALSE]

InsertAfter(predNode, newNode) ==
    /\ newNode \notin list
    /\ AcquireMutex(predNode)
    /\ AcquireMutex(next[predNode])
    /\ next' = [next EXCEPT ![predNode] = newNode, ![newNode] = next[predNode]]
    /\ prev' = [prev EXCEPT ![newNode] = predNode, ![next[predNode]] = newNode]
    /\ list' = Append(list, newNode)
    /\ ReleaseMutex(predNode)
    /\ ReleaseMutex(next[predNode])

Remove(node) ==
    /\ node \in list
    /\ AcquireMutex(prev[node])
    /\ AcquireMutex(node)
    /\ AcquireMutex(next[node])
    /\ next' = [next EXCEPT ![prev[node]] = next[node]]
    /\ prev' = [prev EXCEPT ![next[node]] = prev[node]]
    /\ list' = list \ {node}
    /\ ReleaseMutex(prev[node])
    /\ ReleaseMutex(node)
    /\ ReleaseMutex(next[node])

Next ==
    \/ \E predNode \in NodeId, newNode \in NodeId: InsertAfter(predNode, newNode)
    \/ \E node \in NodeId: Remove(node)
    \/ \E node \in NodeId: AcquireMutex(node) \/ ReleaseMutex(node)

Spec == Init /\ [][Next]_<<list, mutexes, next, prev, data>>

InvariantList == 
    /\ Invariant
    /\ \A node \in NodeId: NodeInList(node) => ProperlyLinked(node)

=============================================================================
\* For model checking
CheckSpec == Spec /\ InvariantList
=============================================================================