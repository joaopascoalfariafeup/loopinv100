// Resturns a sequence with the negative numbers in the input array, by the same order.
method FindNegativeNumbers(arr: array<int>) returns (negativeList: seq<int>)
  ensures negativeList == Filter(arr[..], x => x < 0)
{
  negativeList := [];
  for i := 0 to arr.Length
    invariant negativeList == Filter(arr[..i], x => x < 0)
  {
    assert arr[..i+1] == arr[..i] + [arr[i]]; // helper
    if arr[i] < 0 {
      negativeList := negativeList + [arr[i]];
    }
  }
  assert arr[..] == arr[..arr.Length]; // helper
}


// Select from a sequence 'a' the elements that satisfy a predicate 'p'.
function {:fuel 5} Filter<T(==)>(a: seq<T>, p: (T) -> bool): seq<T> {
  if |a| == 0 then []
  else if p(Last(a)) then Filter(DropLast(a), p) + [Last(a)]
  else Filter(DropLast(a), p)
}

// Auxiliary function that gives the last element of a non-empty sequence
function Last<T>(a: seq<T>): T
  requires |a| > 0
{
  a[|a| - 1]
}

// Auxiliary function that gives a sequence without the last element.
function DropLast<T>(a: seq<T>): seq<T>
  requires |a| > 0
{
  a[0..|a| - 1]
}

// Test cases checked statically.
method FindNegativeNumbersTest(){
  var a1 := new int[] [-1, 4, 5, -6];
  var res1 := FindNegativeNumbers(a1);
  assert a1[..] == [-1, 4, 5, -6] == [-1, 4, 5] + [-6]; // helper
  assert res1 == [-1, -6];

  var a2:= new int[] [-1, -2, -3];
  var res2 := FindNegativeNumbers(a2);
  assert res2 == [-1, -2, -3];

  var a3:= new int[] [0, 1];
  var res3 := FindNegativeNumbers(a3);
  assert res3 == [];
}