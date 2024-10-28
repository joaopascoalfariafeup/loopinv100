// Returns the difference between the sum of the cubes and the
// sum of the first n positive natural numbers.
method DifferenceSumCubesAndSumNumbers(n: nat) returns (diff: int)
  ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
  var sumCubes := SumCubes(n);
  var sumNumbers := SumNumbers(n);
  return sumCubes - sumNumbers;
}


// Computes  the sum of the cubes of the first n positive natural numbers.
method SumCubes(n: nat) returns (sumCubes: nat)
  ensures sumCubes == (n * n * (n + 1) * (n + 1)) / 4
{
  sumCubes := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sumCubes == i * i * (i + 1) * (i + 1) / 4
  {
    i := i + 1;
    sumCubes := sumCubes + i * i * i;
  }
}

// Computes the sum of the first n positive natural numbers.
method SumNumbers(n: nat) returns (sumNumbers: nat)
  ensures sumNumbers == (n * (n + 1)) / 2
{
  sumNumbers := 0;
  var i : nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sumNumbers == i * (i + 1) / 2
  {
    i := i + 1;
    sumNumbers := sumNumbers + i;
  }
}

// Test cases checked statically.
method DifferenceSumCubesAndSumNumbersTest(){
  var res4 := DifferenceSumCubesAndSumNumbers(0);
  assert res4 == 0;

  var res5 := DifferenceSumCubesAndSumNumbers(1);
  assert res5 == 0;

  var res6 := DifferenceSumCubesAndSumNumbers(2);
  assert res6 == 6; // (1+8) - (1+2)

  var res1:= DifferenceSumCubesAndSumNumbers(3);
  assert res1==30;
}