method {:extern} Fibonacci(n: nat) returns (r: nat)
  reads {}
  // modifies {} -- This is the default so it can be omitted
{
  var x, y := 0, 1;
  for i := 0 to n {
    x, y := y, x + y;
  }
  return x;
}

// Attempting to memoize the fibonacci function with a shared cache.

class Box<T> {
  var value: T
  constructor(value: T)
    reads {}
  {
    this.value := value;
  }
}

method {:extern} UnsafeMemoizedFibonacci(n: nat, cacheBox: Box<map<nat, nat>>) returns (r: nat)
  reads {}
{
  var cache := cacheBox.value; // Error: insufficient reads clause to read field
  if n in cache.Keys { 
    r := cache[n];
  } else {
    r := Fibonacci(n);
    cacheBox.value := cache[n := r]; // Error: assignment may update an object not in the enclosing context's modifies clause
  }
}

// TODO: example of permitted thread-local mutable state - creating new objects and modifying them IS allowed.
