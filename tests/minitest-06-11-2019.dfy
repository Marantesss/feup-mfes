// Exercise 5
function P(n: nat): nat { if n <= 2 then 1 else P(n-2) + P(n-3) }

method calcP(n: nat) returns (res: nat)  
    ensures res == P(n)
{
    if n <= 2 {
        return 1;
    }
    var a, b, c := 1, 1, 1; // P(0), P(1), P(2)
    var i := 2;
    while i < n 
        decreases n - i
        invariant i <= n // while condition
        invariant a == P(i - 2) && b == P(i - 1) && c == P(i) // Padovan Sequence
    {
        a, b, c := b, c, a + b;
        i := i + 1;
    }
    res := c;
}

// Exercise 6
type T = int // example 

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
method merge(a: array<T>, b: array<T>) returns (c: array<T>)
    requires sorted(a, a.Length) && sorted(b, b.Length)
    ensures sorted(c, c.Length)
    ensures elems(c, c.Length) == elems(a, a.Length) + elems(b, b.Length)
{
    c := new T[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b'

    // Repeatedly pick the smallest element from 'a' and 'b' and copy it into 'c':
    while i < a.Length || j < b.Length
        decreases a.Length - i + (b.Length - j)
        invariant 0 <= i <= a.Length && 0 <= j <= b.Length
        invariant sorted(c, i + j)
        invariant elems(c, i + j) == elems(a, i) + elems(b, j)
        invariant i < a.Length && i + j > 0 ==> c[i + j - 1] <= a[i]
        invariant j < b.Length && i + j > 0 ==> c[i + j - 1] <= b[j]
        //invariant forall k, l :: i <= k < a.Length && 0 < l < i + j ==> c[l] <= a[k]
        //invariant forall k, l :: j <= k < b.Length && 0 < l < i + j ==> c[l] <= b[k]
    {
        if i < a.Length && (j == b.Length  || a[i] <= b[j]) {
            c[i + j] := a[i];
            i := i+1;
        } 
        else {
            c[i + j] := b[j];
            j:= j+1;
        }
    }
}

// Checks if the first 'n' elements in array 'a' are sorted.
predicate sorted(a: array<T>, n : nat)
  requires n <= a.Length
  reads a
{ forall i, j :: 0 <= i < j < n ==> a[i] <= a[j] }

// Obtain the multiset corresponding to the first 'n' elements in array 'a'.
function elems(a: array<T>, n: nat): multiset<T>
  requires n <= a.Length
  reads a
{ multiset(a[..n]) }
 
method testMerge() {
    var a: array<T> := new T[3] [1, 3, 5];
    var b: array<T> := new T[2] [2, 4]; 
    var c := merge(a, b);
    assert a[..a.Length]  == [1, 3, 5];
    assert b[..b.Length]  == [2, 4];
    assert elems(c, c.Length) == multiset{1, 2, 3, 4, 5};
    assert c[..] == [1, 2, 3, 4, 5];
}

// Exercise 7
class {:autocontracts} BSTNode {
    // Concrete implementation variables.
    var value: T 
    var left: BSTNode?  // elements smaller than 'value' (? - may be null)
    var right: BSTNode? // elements greater than 'value' (? - may be null)

    // Ghost variable used for specification & verification purposes.
    // Holds the set of values in the subtree starting in this node (inclusive). 
    ghost var elems: set<T> 

    // Class invariant with the integrity constraints for the above variables
    predicate Valid() { 
      (elems == {value} + (if left == null then {} else left.elems) + (if right == null then {} else right.elems))
      &&
      (left != null ==> forall x :: x in left.elems ==> value > x)
      &&
      (right != null ==> forall x :: x in right.elems ==> value < x)
    }

    // Check if the subtree starting in this node contains a value 'x'.
    method contains(x: T) returns (res: bool)
      ensures res <==> x in elems
      decreases elems
    {
        if x == value { res := true; } 
        else if x < value && left != null  { res := left.contains(x); } 
        else if x > value && right != null { res := right.contains(x); } 
        else { res := false; }
    }
}
