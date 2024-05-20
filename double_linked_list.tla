----------------------------- MODULE double_linked_list -----------------------------
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
    /\ data = [n \in NodeId |-> CHOOSE d \in Data : TRUE]

NodeInList(node) == \E i \in 1..Len(list): list[i] = node
ProperlyLinked(node) ==
    /\ next[node] \in NodeId
    /\ prev[next[node]] = node
    /\ prev[node] \in NodeId
    /\ next[prev[node]] = node

Invariant == \A node \in NodeId: NodeInList(node) => ProperlyLinked(node)
AcquireMutex(node) ==
    /\ ~mutexes[node].locked
    /\ mutexes' = [mutexes EXCEPT ![node].locked = TRUE]
    /\ UNCHANGED <<list, next, prev, data>>

ReleaseMutex(node) ==
    /\ mutexes[node].locked
    /\ mutexes' = [mutexes EXCEPT ![node].locked = FALSE]
    /\ UNCHANGED <<list, next, prev, data>>

InsertAfter(predNode, newNode) ==
    /\ ~NodeInList(newNode)
    /\ AcquireMutex(predNode)
    /\ AcquireMutex(next[predNode])
    /\ next' = [next EXCEPT ![predNode] = newNode, ![newNode] = next[predNode]]
    /\ prev' = [prev EXCEPT ![newNode] = predNode, ![next[predNode]] = newNode]
    /\ list' = Append(list, newNode)
    /\ ReleaseMutex(predNode)
    /\ ReleaseMutex(next[predNode])
    /\ UNCHANGED data

Remove(node) ==
    /\ NodeInList(node)
    /\ AcquireMutex(prev[node])
    /\ AcquireMutex(node)
    /\ AcquireMutex(next[node])
    /\ next' = [next EXCEPT ![prev[node]] = next[node]]
    /\ prev' = [prev EXCEPT ![next[node]] = prev[node]]
    /\ list' = SubSeq(list, 1, Len(list) - 1)
    /\ ReleaseMutex(prev[node])
    /\ ReleaseMutex(node)
    /\ ReleaseMutex(next[node])
    /\ UNCHANGED data

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
NodeId == {1, 2, 3, 4, 5}
Data == {"A", "B", "C", "D", "E"}
CheckSpec == Spec /\ InvariantList
=============================================================================