// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>)
  reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate isSortedInterval(a: array<int>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j] 
}

// Checks if 'x' is NOT in array 'a'
predicate notIn(a: array<int>, x: int)
    reads a
{
    forall i :: 0 <= i < a.Length ==> a[i] != x
}


// Finds a value 'x' in a sorted array 'a', and returns its index,
// or -1 if not found. 
method binarySearch(a: array<int>, x: int) returns (index: int)
    requires isSorted(a)
    ensures (0 <= index < a.Length && a[index] == x) ||
        (notIn(a, x) && index == -1) // notIn(a, x) -> x !in a[..]
{   
    var low, high := 0, a.Length;
    while low < high
        decreases high - low
        invariant 0 <= low <= high <= a.Length
        invariant forall i :: 0 <= i < a.Length && !(low <= i < high) ==> a[i] != x
        // OR
        //invariant x !in [..low] && x !in [high..]
    {
        var mid := low + (high - low) / 2;
        if 
        {
            case a[mid]  < x => low := mid + 1;
            case a[mid]  > x => high := mid;
            case a[mid] == x => return mid;
        }
    }
    return -1;
}

// Simple test cases to check the post-condition.
method testBinarySearch() {
    var a := new int[5] [1, 4, 4, 6, 8];
    assert a[..]  == [1, 4, 4, 6, 8];
    var id1 := binarySearch(a, 6);
    assert id1 == 3;
    var id2 := binarySearch(a, 3);
    assert id2 == -1;
    var id3 := binarySearch(a, 4);
    assert id3 in {1, 2};
}



// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>)
    modifies a
    ensures isSorted(a)
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var i := 0;
    while i < a.Length
        decreases a.Length - i // not needed -> dafny figures it out
        invariant 0 <= i <= a.Length
        invariant isSortedInterval(a, 0, i)
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var j := i;
        while j > 0 && a[j-1] > a[j]
            decreases j
            invariant 0 <= j <= i
            invariant multiset(a[..]) == multiset(old(a[..]))
            // sorted from 0 to i ignoring j
            invariant forall lhs, rhs :: 0 <= lhs < rhs < i  && rhs != j ==> a[lhs] <= a[rhs]

        {
            a[j-1], a[j] := a[j], a[j-1];
            j := j - 1;
        }
        i := i + 1;
    }
}

// Simple test case to check the postcondition
method testInsertionSort() {
  var a := new int[5][9, 4, 3, 6, 8];
  assert a[..] == [9, 4, 3, 6, 8];
  insertionSort(a);
  assert a[..] == [3, 4, 6, 8, 9];
}

