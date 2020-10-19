/********************
    EXERCICIO 1
 ********************/

function fib(n : nat ) : nat
    decreases n
{
    if n < 2 then n else fib(n - 2) + fib(n - 1)
}

method computeFib (n : nat) returns (x : nat)
    // pre-conditions
    requires true // not necessary
    // post-conditions
    ensures x == fib(n)
{
    var i := 0;
    x := 0; // fib(i)
    var y := 1; // fib(i + 1)

    // Invariant needs to be valid initially (not necessary to write this down)
    assert 0 <= i <= n && x == fib(i) && y == fib(i + 1);

    while  i < n
        // Variant -> distance to the final value
        // while i < n ---> i := i + 1;
        decreases n - i
        // we need to add a loop invariant in order for the post-condition "ensures x == fib(n)" to hold
        invariant 0 <= i <= n && x == fib(i) && y == fib(i + 1)
    {
        x, y := y, x + y; // multiple assignment
        i := i + 1;
    }
    // in the end of the loop, dafny is trying to prove that:
    // i >= n && x == fib(i) && y == fib(i + 1) ==> x == fib(n)
    // which means:
    // - i >= n (from the while condition)
    // - x == fib(i) && y == fib(i + 1) (from the invariant)
    // - x == fib(n) (from the post-condition)
    // we need something else: 0 <= i <= n

    // we can also use 'assert' keyword (not necessary to write this down, dafny does this automatically)
    assert i >= n && 0 <= i <= n && x == fib(i) && y == fib(i + 1) ==> x == fib(n);
}

/********************
    EXERCICIO 2
 ********************/

function method fact(n: nat) : nat
    decreases n
{
    if n == 0 then 1 else n * fact(n-1)
}

method factIter(n: nat) returns (f : nat)
    requires true
    ensures f == fact(n)
{
    f := 1;
    var i := 0;
    while i < n
        decreases n - i
        invariant 0 <= i <= n && f == fact(i)
    {
        i := i + 1;
        f := f * i;
    }
}

/********************
    EXERCICIO 3
 ********************/

/**
    ambas seguem um paradigma imperativo
    function não vai para o executavel
    function method está presente em runtime
 */
function method abs(x: int): nat
{
    if x >= 0 then x else -x
}

// Computes the quotient 'q' and remainder 'r' of 
// the integer division of a (non-negative) dividend
// 'n' by a (positive) divisor 'd'.
method div(n: int, d: int) returns (q: int, r: nat)
    requires d != 0
    ensures 0 <= r < abs(d) && q * d + r == n
{
    q := 0;
    // distinguish these 2 cases
    if n > 0 {
        r := n;
    } else {
        r:= -n;
    }
    while abs(r) >= d
        decreases abs(r)
        invariant abs(d) <= abs(r) < abs(n)
        invariant q * d + r == n 
    {
        q := q + 1;
        // distinguish these 2 cases
        if n > 0 {
            r := r - abs(d);
        } else {
            r := r + abs(d);
        }
    }
}

// testing cenas
// if the asserts are wrong then DafnyServer automatically marks them as "Assertion Error"
method Main()
{
    assert 1 == fact(0);
    assert 1 == fact(1);
    assert 2 == fact(2);
    assert 6 == fact(3);

    // a method cannot be used directly on an assert statement
    var ret := factIter(0);
    assert ret == 1;

    var q, r := div(15, 6);
    assert q == 2;
    assert r == 3;
    q, r := div(15, -6);
    assert q == -2;
    assert r == 3;
    q, r := div(-15, 6);
    assert q == -3;
    assert r == 3;
    q, r := div(-15, -6);
    assert q == 3;
    assert r == 3;
    print "q = ", q, " r=", "\n";
}

