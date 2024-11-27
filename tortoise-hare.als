sig Node {
    next : lone Node
}

one sig Head in Node {}
lone sig Tail in Node {}

abstract sig CycleStatus {}
one sig Cycle, NoCycle, Running extends CycleStatus {}
var one sig Result in CycleStatus {}

fact {
    no Tail.next
    Node in Head.*next

    all n : Node | no n.next => n = Tail
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
    n = Tail implies n
             else n.next
}

pred move {
    Result = Running
    Tortoise.at' = advance[Tortoise.at]
    Hare.at' = advance[advance[Hare.at]]

    Hare.at' = Tail implies Result' = NoCycle
                    else    Hare.at' = Tortoise.at' implies Result' = Cycle
                                                    else    Result' = Result
}

// This is so the visualizer can show the tokens as attributes on the nodes
fun tokens[] : Node -> Token {
    ~at
}

run { spec } for 3 but exactly 5 Node