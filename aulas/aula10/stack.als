open util/ordering[StackState]

sig Element {}

sig StackState {
    elements: seq Element
}{
    //
}

abstract sig Event {
    pre, post: StackState
}{
    // constraints that should hold for each Event
}

fact firstState {
    // constraints for the first StackState
}

fact trace {
     
    // relate all `StackState`s and `Event`s 
}

sig Push extends Event {
    value: Element
}{
    // -- model pushing by relating `pre`, `post`, and `value`
}

sig Pop extends Event {
    //
}{
    // -- model popping
}

assert popThenPush {
    // ...
}
check popThenPush


assert sameNumberPushesPops {
    // ...
}
check sameNumberPushesPops


assert noPopFromEmpty {
    // ...
}
check noPopFromEmpty
