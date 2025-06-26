/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another type

// Auxiliary predicate that checks if a sequence 'a' is sorted. 
ghost predicate IsSorted(s: seq<int>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] 
}

// Sorts array 'a' using the insertion sort algorithm.
method InsertionSort(a: array<int>) 
    modifies a    
    ensures IsSorted(a[..])
    ensures multiset(a[..]) == multiset(old(a[..]))
{    
    // In each iteration, it picks the next element from the unsorted part of the array
    // and inserts it into the correct position in the sorted part of the array.  
    for i := 0 to a.Length
      invariant IsSorted(a[..i]) 
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      var j := i; 
      // move the element at index 'i' to the left as needed (position 'j'),
      // to keep the array sorted. 
      while j > 0 && a[j-1] > a[j]
        invariant 0 <= j <= i
        invariant forall l, r :: 0 <= l < r <= i && r != j ==> a[l] <= a[r] 
        invariant multiset(a[..]) == multiset(old(a[..]))
      {
        a[j-1], a[j] := a[j], a[j-1]; // swap (parallel assignment)
        j := j - 1;
      }
    }
}


method TestSortSimple() {
    var a := new T[] [9, 4, 6, 3, 8]; 
    assert a[..] == [9, 4, 6, 3, 8]; // helper
    InsertionSort(a);
    assert a[..] == [3, 4, 6, 8, 9];
}  

