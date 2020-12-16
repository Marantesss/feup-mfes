open util/ordering[StackState]

sig Element {}

sig StackState {
    elements: seq Element
}{
    //
}

abstract sig Event {
    pre: disj one StackState,
    post: disj one StackState
}{
    // constraints that should hold for each Event
    // this in Push => #pre.elements + 1 = #post.elements
    // this in Pop => (#pre.elements = 0 and #post.elements = 0) or 
    //						(#pre.elements = #post.elements - 1)
}

// fact firstState {
//    // constraints for the first StackState
//    first.elements.isEmpty	   
// }

pred Init[s: StackState] {
	s.elements.isEmpty
}

fact trace {
     // initial state
     Init[first]

    // other but the intial states
    // relate all `StackState`s and `Event`s 
    all s: StackState - last | let s1 = s.next |
      	some e: Event { 
        	e.pre = s
		e.post = s1
      	}
}

sig Push extends Event {
    value: Element
}{
    // -- model pushing by relating `pre`, `post`, and `value`
    value = post.elements.first
    post.elements = pre.elements.add[value]
}

sig Pop extends Event {
    value: lone Element
}{
    // -- model popping
    pre.elements.isEmpty => no value
    value = pre.elements.first
    post.elements.add[value] = pre.elements
}

run {} for 3

//fact PopAfterPushes {
//	all s: StackState - last | let s' = s.next |
//		some pre.s' <: Pop => one pre.s <: Push
//}

assert popThenPush {
	all s: StackState - last | let s1 = s.next |
		some pre.s <: Push and some pre.s1 <: Pop 
}
check popThenPush


//fact InitEqualsFinal {
//	first.elements.isEmpty 
//	last.elements.isEmpty
//}

assert sameNumberPushesPops {
    #Pop = #Push
}
check sameNumberPushesPops


//fact ForbidPopEmpty {
//	all popEvent: Pop | !popEvent.pre.elements.isEmpty
//}

assert noPopFromEmpty {
    no popEvent: Pop | popEvent.pre.elements.isEmpty
}
check noPopFromEmpty