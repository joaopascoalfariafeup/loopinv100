// Returns a sequence with the odd numbers in the input array, by the same order.
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
  ensures oddList == Filter(arr[..], IsOdd)
{
  oddList := [];
  for i := 0 to arr.Length
    invariant oddList == Filter(arr[..i], IsOdd)
  {
    assert arr[..i+1] == arr[..i] + [arr[i]]; // proof helper
    if IsOdd(arr[i]) {
      oddList := oddList + [arr[i]];
    }
  }
  assert arr[..] == arr[..arr.Length]; // proof helper
}

// Auxiliary predicate to checks if a number is odd
predicate IsOdd(n: int) {
  n % 2 != 0
}

// Select from a sequence 'a' the elements that satisfy a predicate 'p'.
function {:fuel 4} Filter<T(==)>(a: seq<T>, p: (T) -> bool): seq<T> {
  if |a| == 0 then []
  else if p(Last(a)) then Filter(DropLast(a), p) + [Last(a)]
  else Filter(DropLast(a), p)
}

// Auxiliary function that gives the last element of a non-empty sequence
function {:fuel 2} Last<T>(a: seq<T>): T
  requires |a| > 0
{
  a[|a| - 1]
}

// Auxiliary function that gives a sequence without the last element.
function {:fuel 2} DropLast<T>(a: seq<T>): seq<T>
  requires |a| > 0
{
  a[0..|a| - 1]
}

// Test cases checked statically.
method FilterOddNumbersTest(){
  var a1:= new int[] [1, 2, 3, 4];
  var res1 := FilterOddNumbers(a1);
  assert IsOdd(a1[0]); // helper
  assert IsOdd(a1[2]);
  assert res1 == [1, 3];

  var a2:= new int[] [1, 3, 5];
  var res2 := FilterOddNumbers(a2);
  assert res2 == [1, 3, 5];

  var a3 := new int[] [2, 4, 6, 8];
  var res3:=FilterOddNumbers(a3);
  assert res3 == [];
}
