sig Node {
    next : lone Node
}

one sig Head in Node {}
lone sig Tail in Node {}

fact {
    no Tail.next
    Node in Head.*next

    all n : Node | no n.next => n in Tail
}

run {} for 4