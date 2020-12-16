// Exercise 4
function R(n: nat): nat {
    if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}


method calcR(n: nat) returns (r: nat)
    ensures r == R(n)
{
    r := 0;
    var i := 0;
    while i < n 
        decreases n - i
        invariant r == R(i)
        invariant i <= n
    {
        i := i + 1;
        if r > i {
            r := r - i;
        } 
        else {
            r := r + i;
        }
    }
}

// exercise 5
type T = int // example

// Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.
method partition(a: array<T>) returns(pivotPos: int)
    modifies a
    requires a.Length > 0
    ensures 0 <= pivotPos < a.Length
    ensures forall x :: 0 <= x < pivotPos ==> a[x] < a[pivotPos]
    ensures forall x :: pivotPos < x < a.Length ==> a[x] >= a[pivotPos]
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    pivotPos := a.Length - 1;   // chooses pivot at end of array 
    var i := 0;                 // index that separates values smaller than pivot (0 to i-1), 
                                // and values greater or equal than pivot (i to j-1) 
    var j := 0;                 // index to scan the array
 
    // Scan the array and move elements as needed
    while  j < a.Length - 1
        decreases a.Length - j
        invariant 0 <= i <= j < a.Length
        invariant forall k :: 0 <= k < i ==> a[k] < a[pivotPos]
        invariant forall k :: i <= k < j ==> a[k] >= a[pivotPos]
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if a[j] < a[pivotPos] {
        a[i], a[j] := a[j], a[i];
        i := i + 1;
      }
      j := j + 1;
    }
 
    // Swap pivot to the 'mid' of the array
    a[a.Length-1], a[i] := a[i], a[a.Length-1];
    pivotPos := i;  
}

// Exercise 6
// File system node
trait Node {

    const name: string; // unique within each folder
    ghost const depth: nat; // starts in 0 at file system root
}

    class {:autocontracts} File extends Node {

    }

    class {:autocontracts} Folder extends Node {
    var child: set<Node>; 

    predicate Valid() {
        (forall x, y :: x in child && y in child && x != y ==>
            x.name != y.name // no child can have the same name as sibling
            &&
            x.depth == this.depth + 1 // depth of child nodes is parent depth + 1
        ) 
    }

    constructor (name: string, parent: Folder?) 
        modifies parent

        requires parent != null ==> (forall x :: x in parent.child ==> x.name != name)      // if parent not null then parent's children cannot have the same name as this
        requires parent != null ==> parent.Valid()

        ensures this.name == name
        ensures this.child == {}
        ensures this.depth == if parent == null then 0 else parent.depth + 1

        ensures parent != null ==> parent.child == old(parent.child) + {this} // parent just got a new child :) (congrats)
        ensures parent != null ==> parent.Valid()
    {
        // this object initialization
        this.name := name;
        this.depth := if parent == null then 0 else parent.depth + 1;
        this.child := {};
        // other objets' updates (after special "new" keyword)
        new;
        if parent != null {
            parent.child := parent.child + {this};
        }
    }
}
