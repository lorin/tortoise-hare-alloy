sig Node {
    next : lone Node
}

one sig Head in Node {}
lone sig Tail in Node {}

abstract sig CycleStatus {}
one sig Cycle, NoCycle, Running extends CycleStatus {}
var one sig Result in CycleStatus {}

fact {
    Node in Head.*next

    all n : Node | no n.next <=> n = Tail
}

abstract sig Token {
    var at : Node
}

one sig Tortoise, Hare extends Token {}


pred spec {
    always (
        move or
        done
    )
}

fact init {
    Token.at in Head
    Result = Running
}

pred done {
    Result in Cycle + NoCycle
    Tortoise.at' = Tortoise.at
    Hare.at' = Hare.at
    Result' = Result
}


fun advance[n : Node] : Node {
    (n = Tail) implies n else n.next
}

pred move {
    // enabling condition
    Result = Running

    // advance the pointers
    Tortoise.at' = advance[Tortoise.at]
    Hare.at' = advance[advance[Hare.at]]

    // update Result if the hare has reached the tail or tortoise and hare collided
    Hare.at' = Tail implies Result' = NoCycle
                    else    Hare.at' = Tortoise.at' implies Result' = Cycle
                                                    else    Result' = Result
}

// This is so the visualizer can show the tokens as attributes on the nodes
fun tokens[] : Node -> Token {
    ~at
}

assert terminates {
    spec => eventually done
}

pred has_cycle {
    some n : Node | n in n.^next
}

assert correctness {
     spec => (has_cycle <=> eventually Result=Cycle)
}

check terminates for exactly 5 Node

check correctness for exactly 5 Node

example: run { spec } for exactly 5 Node