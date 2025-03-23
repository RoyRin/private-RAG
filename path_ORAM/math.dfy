module Math {
    // Minimum size requirement for ORAM to be secure
    const MIN_BLOCKS: nat := 2;

    // Power of 2
    function method Pow2(n: nat): nat
        ensures n == 0 ==> Pow2(n) == 1
        ensures n > 0 ==> Pow2(n) == 2 * Pow2(n-1)
        ensures Pow2(n) > 0
    {
        if n == 0 then 1
        else 2 * Pow2(n-1)
    }
    
    // Helper lemma to prove (n+1)/2 < n for n > 2
    lemma CeilLog2Decreases(n: nat)
        requires n > MIN_BLOCKS
        ensures (n + 1) / 2 < n
    {
        assert n > 2;
        assert (n + 1) / 2 < n;
    }

    // Ceiling of logarithm base 2
    function method CeilLog2(n: nat): nat
        requires n >= MIN_BLOCKS  // Require at least 2 blocks for ORAM
        ensures CeilLog2(n) >= 2  // Ensures result is at least 2
        ensures n <= Pow2(CeilLog2(n))
        ensures n > Pow2(CeilLog2(n) - 1)
        decreases n
    {
        if n <= MIN_BLOCKS then 
            2
        else 
            var m := (n + 1) / 2;
            CeilLog2Decreases(n);
            assert m < n;
            var result := 1 + CeilLog2(m);
            CeilLog2Bounds(n);
            result
    }

    // Helper lemmas for verification
    lemma Pow2Positive(n: nat)
        ensures Pow2(n) > 0
    {
        if n == 0 {
            assert Pow2(n) == 1;
        } else {
            Pow2Positive(n-1);
            assert Pow2(n) == 2 * Pow2(n-1);
        }
    }

    lemma {:fuel Pow2,2} Pow2Monotonic(n: nat)
        ensures n > 0 ==> Pow2(n) > Pow2(n-1)
    {
        if n > 0 {
            assert Pow2(n) == 2 * Pow2(n-1);
            Pow2Positive(n-1);
        }
    }

    lemma {:fuel Pow2,4} Pow2Increases(n: nat, m: nat)
        requires n > m
        ensures Pow2(n) > Pow2(m)
        decreases n - m
    {
        if n == m + 1 {
            Pow2Monotonic(n);
        } else {
            assert n - m > 1;
            Pow2Increases(n-1, m);
            Pow2Monotonic(n);
        }
    }
    
    lemma {:induction n} CeilLog2Bounds(n: nat)
        requires n >= MIN_BLOCKS
        ensures n <= Pow2(CeilLog2(n))
        ensures n > Pow2(CeilLog2(n) - 1)
        decreases if n > MIN_BLOCKS then n else 0
    {
        if n <= MIN_BLOCKS {
            assert CeilLog2(n) == 2;
            assert Pow2(2) == 4;
            assert Pow2(1) == 2;
            assert n <= 4;
            assert n > 2;
        } else {
            var m := (n + 1) / 2;
            CeilLog2Decreases(n);
            assert m < n;
            CeilLog2Bounds(m);
            
            // Calculate CeilLog2 values
            var r := CeilLog2(m);
            var log_n := CeilLog2(n);
            assert log_n == 1 + r;
            
            // Prove upper bound: n <= Pow2(log_n)
            assert Pow2(log_n) == Pow2(1 + r) == 2 * Pow2(r);
            assert m <= Pow2(r);
            assert n <= 2*m;
            assert n <= 2*Pow2(r);
            assert n <= Pow2(log_n);
            
            // Prove lower bound: n > Pow2(log_n - 1)
            assert log_n - 1 == r;
            assert Pow2(log_n - 1) == Pow2(r);
            assert m > Pow2(r-1);
            assert n > m;
            assert n > Pow2(r);
            assert n > Pow2(log_n - 1);
        }
    }






}
