// Returns the sum of the decimal digits of a natural number.
function SumOfDigits(n: nat) : (sum: nat) { // recursive definition
    if n < 10 then n else SumOfDigits(n / 10) + n % 10
}
by method // iterative implementation
{
    sum := 0; // partial sum
    var num : nat := n; // remaining number
    while num > 0           
        invariant SumOfDigits(n) == sum + SumOfDigits(num)  
    {
        sum := sum + num % 10;
        num := num / 10;
    }
}

// Test cases checked statically by Dafny.
method SumOfDigitsTest() {
    assert SumOfDigits(0) == 0;
    assert SumOfDigits(9) == 9;
    assert SumOfDigits(10) == 1;
    assert SumOfDigits(99) == 18;
    assert SumOfDigits(111111111) == 9;
}