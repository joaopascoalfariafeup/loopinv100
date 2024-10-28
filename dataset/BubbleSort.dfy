/* 
* Formal verification of the bubble sort algorithm with Dafny.
* The algorithm was taken from https://en.wikipedia.org/wiki/Bubble_sort .
*/

// Checks if a sequence 'a' is sorted.
ghost predicate IsSorted(a: seq<int>) {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// Sorts array 'a' inplace using the bubble sort algorithm.
method BubbleSort(a: array<int>)
  modifies a
  ensures IsSorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
    var n := a.Length; // sorted elements are a[n..] (and greater than a[..n])

    // Does multiple passes over the array, each time bubbling the largest element to the end.
    while n  > 1
      invariant 0 <= n <= a.Length
      invariant forall x, y :: 0 <= x < y < a.Length && n <= y ==> a[x] <= a[y] // a[n..] is sorted and >= a[..n]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      // Scans the array a[..n] from left to right, swapping adjacent elements if they
      // are in the wrong order. At the same time, keeps the index of the last swap (newn). 
      var newn : nat := 0;
      for i := 1 to n
        invariant 0 <= newn < i 
        invariant forall x, y :: 0 <= x < y < a.Length && n <= y ==> a[x] <= a[y]  // a[n..] is sorted and >= a[..n]      
        invariant forall x, y :: 0 <= x < y < i && newn <= y ==> a[x] <= a[y] // a[newn..i] is sorted and >= a[..newn]
        invariant multiset(a[..]) == multiset(old(a[..])) // same elements
      {
          if (a[i-1] > a[i]) { 
              a[i-1], a[i] := a[i], a[i-1]; 
              newn := i;
          }
      }
      n := newn;
    }
}

// A simple test case checked statically.
method TestBubbleSort() {
    var a := new int[] [7, 3, 4, 6];
    assert a[..] == [7, 3, 4, 6]; // proof helper
    BubbleSort(a);
    assert a[..] == [3, 4, 6, 7];
}

