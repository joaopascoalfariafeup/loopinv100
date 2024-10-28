// Move all zeroes to the end of the array, preserving the order of non-zero elements.
method MoveZeroesToEnd(a: array<int>)
    modifies a
    ensures a[..] == fill(filter(old(a[..]), x => x !=0 ), 0, a.Length)
{
    var nz := 0; // number of non-zero elems to the left of index i
    for i := 0 to a.Length // iterate over the array and swap non-zero elements to the left
        invariant 0 <= nz <= i
        invariant a[..nz] == filter(old(a[..i]), x => x != 0) // first nz elements are non-zero, by the same order
        invariant forall k :: nz <= k < i ==> a[k] == 0 // then zero up to index i (exclusive)
        invariant a[i..] == old(a[i..])  // then old values up to the end
        
    {
        if a[i] != 0 {
            if nz < i {
                a[nz], a[i] := a[i], a[nz]; // swap non-zero element to the left
            }
            nz := nz + 1; // increment number of non-zero elements
        }
        assert old(a[..i+1] == a[..i] + [a[i]]); // helper
    }    
    assert old(a[..] == a[..a.Length]); // helper
}

// Sequence utilities

// Filters a sequence using a predicate.
// Returns a new sequence with the elements of s that satisfy the predicate p.
function filter<T>(s: seq<T>, p: T -> bool): (r : seq<T>)
    ensures |r| <= |s| // useful sometimes    
{
    if |s| == 0 then s
    else if p(last(s)) then filter(butlast(s), p) + [last(s)]
    else filter(butlast(s), p)
}

// Appens a value (x) to a sequence (s), to fullfil a given length (len).
// Returns a new sequence with the elements of s, followed by x repeated until the length is reached. 
function fill<T>(s: seq<T>, x: T, len: nat): (r: seq<T>) 
  requires len >= |s|
  decreases len - |s|
  ensures |r| == len
  ensures r[..|s|] == s
  ensures forall i :: |s| <= i < len ==> r[i] == x
{
    if |s| == len then s else fill(s + [x], x, len)
}

// Retrieves the same sequence with the last element removed 
function butlast<T>(s: seq<T>): seq<T>
    requires |s| > 0
    ensures s == butlast(s) + [last(s)]
{ s[..|s|-1] }

// Retrieves the last element of a non-empty sequence
function last<T>(s: seq<T>): T
    requires |s| > 0
{ s[|s|-1] }

// End of sequence utilities

// Test cases checked statically by Dafny (with helper assertions)
method MoveZeroesToEndTest(){
    var a1 := new int[] [1, 0, 2, 0, 3];
    assert a1[..] == [1, 0, 2, 0, 3]; // proof helper
    assert butlast([1, 0, 2, 0, 3]) == [1, 0, 2, 0]; // proof helper
    assert butlast([1, 0, 2, 0]) == [1, 0, 2]; // proof helper
    MoveZeroesToEnd(a1);
    assert a1[..] == [1, 2, 3, 0, 0];
 
    var a2 := new int[] [0, 1, 0, 1, 1];
    assert a2[..] == [0, 1, 0, 1, 1]; // proof helper
    assert butlast([0, 1, 0, 1, 1]) == [0, 1, 0, 1]; // proof helper
    MoveZeroesToEnd(a2);
    assert a2[..] == [1, 1, 1, 0, 0];
}