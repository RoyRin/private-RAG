module Math {
    // Power of 2
    function Pow2(n: nat): nat
        ensures n >= 1 ==> Pow2(n) >= 2
    {
        if n == 0 then 1
        else 2 * Pow2(n-1)
    }

    // Ceiling of logarithm base 2
    function CeilLog2(n: nat): nat
        requires n > 0
    {
        if n == 1 then 0
        else if n == 2 then 1
        else 1 + CeilLog2((n + 1) / 2)
    }

    // Floor of logarithm base 2
    function FloorLog2(n: nat): nat
        requires n > 0
    {
        if n == 1 then 0
        else if n == 2 then 1
        else 1 + FloorLog2(n  / 2)
    }
}
