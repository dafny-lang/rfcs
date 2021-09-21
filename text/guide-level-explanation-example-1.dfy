
class FibonacciMemoizer {
  var cache: map<nat, nat>
  constructor() reads {} {
    cache := map[];
  }
  method Get(n: nat) returns (r: nat) 
    reads this
    modifies this
  {
    if n <= 2 {
      return 1;
    }
    if n in cache {
      r := cache[n];
    } else {
      var oneBefore := Get(n - 1);
      var twoBefore := Get(n - 2);
      r := oneBefore + twoBefore;
      cache := cache[n := r];
    }
  }
}

// Sharing a memoizer instance between threads is not allowed.
method {:extern} UnsafeFibonacci(n: nat, memoizer: FibonacciMemoizer) returns (r: nat)
  reads {}
{
  r := memoizer.Get(n);   // Error: insufficient reads clause to invoke method
                          // Error: call may violate context's modifies clause
}

// It IS allowed, though, to manipulate mutable state that is freshly
// allocated by a single thread. This does not violate the reads or modifies clauses.
method {:extern} SafeFirstNFibonaccis(n: nat) returns (rs: seq<nat>)
  reads {}
{
  var memoizer := new FibonacciMemoizer();
  rs := [];
  for i := 1 to n + 1 {
    var r := memoizer.Get(i);
    rs := rs + [r];
  }
}
