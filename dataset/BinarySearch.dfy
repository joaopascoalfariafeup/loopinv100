/*  
* Formal verification of the binary search algorithm in Dafny. 
*/

type T = int // for demo purposes, but could be another type 

// Checks if a sequence 's' is sorted.
predicate isSorted(a: seq<T>) {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}
  
// Finds a value 'x' in a sorted array 'a', and returns its index, or -1 if not found. 
method BinarySearch(a: array<T>, x: T) returns (index: int)
  requires isSorted(a[..])
  ensures (0 <= index < a.Length && a[index] == x) || (index == -1 && x !in a[..])
{   
  var low, high := 0, a.Length;
  while low < high 
    invariant 0 <= low <= high <= a.Length
    invariant x !in a[..low] && x !in a[high..]
  {
    var mid := low + (high - low) / 2;
    if {
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
  var id1 := BinarySearch(a, 1); assert a[0] == 1; assert id1 == 0; // found
  var id2 := BinarySearch(a, 3); assert id2 == -1; // not found
//  var id3 := BinarySearch(a, 4); assert id3 in {1, 2}; // duplicate
} 