// Returns an array of the cubes of the elements of the input array.
method CubeElements(a: array<int>) returns (cubed: array<int>)
    ensures fresh(cubed)
    ensures cubed[..] == MapSeq(a[..], cube)
{
    cubed := new int[a.Length];
    for i := 0 to a.Length
        invariant cubed[..i] == MapSeq(a[..i], cube)
    {
        cubed[i] := cube(a[i]);
    }
}

function cube(x: int) : int {
     x * x * x
}

// Auxiliary function that applies a function to every element of a sequence
// using sequence comprehension.
ghost function {:opaque} MapSeq<T, E>(s: seq<T>, f: T -> E) : (res: seq<E>) 
  ensures |res| == |s| && (forall i :: 0 <= i < |s| ==> res[i] == f(s[i]))
{
    seq(|s|, i requires 0 <= i < |s| => f(s[i])) 
}

// Test cases checked statically.
method CubeElementsTest(){
  var a1 := new int[] [1, 2, 3, 4, 5];
  var res1 := CubeElements(a1);
  assert res1[..] == [1, 8, 27, 64, 125];

  var a2 := new int[] [2, 1, 0, -1, -2];
  var res2 := CubeElements(a2);
  assert res2[..] == [8, 1, 0, -1, -8];
}