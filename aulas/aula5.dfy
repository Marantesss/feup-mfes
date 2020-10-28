type T = int // for demo purposes, but could be another type
 
class {:autocontracts} Deque {
    // (Private) concrete state variables 
    const list: array<T>; // circular array, from list[start] (front) to 
                             list[(start+size-1) % list.Length] (back) 
    var start : nat; 
    var size : nat;
 
    constructor (capacity: nat) {
        list := new T[capacity];
        start := 0;
        size := 0;
    }
 
    predicate method isEmpty() {
        size == 0
    }
    
    predicate method isFull() {
        size == list.Length
    }
 
    function method front() : T {
        list[start]
    }
 
    function method back() : T {
        list[(start + size - 1) % list.Length] 
    }
    
    method push_back(x : T) {
        list[(start + size) % list.Length] := x;
        size := size + 1;
    }
 
    method pop_back() {
        size := size - 1;
    }
 
    method push_front(x : T) {
        if start > 0 {
            start := start - 1;
        }
        else {
            start := list.Length - 1;
        }
        list[start] := x;
        size := size + 1;
    }    
 
    method pop_front() {
        if start + 1 < list.Length {
            start := start + 1;
        }
        else {
            start := 0;
        }
        size := size - 1;
    } 
}
 
// A simple test scenario.
method testDeque()
{
    var q := new Deque(3);
    assert q.isEmpty();
    q.push_front(1);
    assert q.front() == 1;
    assert q.back() == 1;
    q.push_front(2);
    assert q.front() == 2;
    assert q.back() == 1;
    q.push_back(3);
    assert q.front() == 2;
    assert q.back() == 3;
    assert q.isFull();
    q.pop_back();
    assert q.front() == 2;
    assert q.back() == 1;
    q.pop_front();
    assert q.front() == 1;
    assert q.back() == 1;
    q.pop_front();
    assert q.isEmpty();
}
