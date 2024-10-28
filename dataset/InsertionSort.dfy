/* 
 * Formal verification of the insertion sort algorithm with Dafny. 
 */

type T = int // for demo purposes, but could be another type


// Auxiliary predicate that checks if a sequence 'a' is sorted. 
predicate IsSorted(s: seq<int>) {
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

method TestSortWithDups() {
    var a := new T[] [9, 3, 6, 9];
    assert a[..] == [9, 3, 6, 9]; // helper
    InsertionSort(a);
    SortingUniquenessProp(a[..],  [3, 6, 9, 9]);
    assert a[..] ==  [3, 6, 9, 9];
}

// State and prove by induction the property that, if two sequences are sorted and have 
// the same multiset of elements, then they must be identical (so sorting has a unique solution). 
lemma SortingUniquenessProp(a: seq<T>, b: seq<T>)
    requires IsSorted(a) && IsSorted(b) && multiset(a) == multiset(b) 
    ensures a == b
{
    // recalls useful properties about sequences and their multisets  
    seqProps(a);
    seqProps(b);

    // key steps of proof by induction on 'a' and 'b' (the rest is filled in by Dafny) 
    if |a| > 0 {
      SortingUniquenessProp(a[1..], b[1..]);
    }
}

// States two properties about sequences (proved by Dafny alone): 
// - sequence concatenation reverts splitting in head and tail;
// - elements of a sequence belong to its multiset.
lemma seqProps(a: seq<T>) 
    ensures |a| > 0 ==> a == [a[0]] + a[1..] 
    ensures forall i :: 0 <= i < |a| ==> a[i] in multiset(a)
{}

