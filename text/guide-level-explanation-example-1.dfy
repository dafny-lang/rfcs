method {:extern} Fibonacci(n: nat) returns (r: nat)
  reads {}
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
  constructor(value: T) {
    this.value := value;
  }
}

method {:extern} UnsafeMemoizedFibonacci(n: int, cacheBox: Box<map<nat, nat>>) returns (r: nat)
  reads {}
{
  var cache := cacheBox.value; // Error: insufficient reads clause to read field
  if n in cache.Keys { 
    r := cache[n];
  } else {
    r := Fibonacci(n);
    cacheBox.value := cache[n := r];
  }
}
