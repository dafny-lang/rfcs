datatype Option<T> = Some(value: T) | None

//
// Wrapper around a concurrent data structure, such as
// ConcurrentHashMap<K, V> in Java.
//
// Note the lack of a ghost variable to track the state of the map,
// which intentionally puts the mutable state outside of the Dafny-verified model.
// These methods instead appear to have non-deterministic behavior to Dafny, which accurately
// represents the fact that it cannot assume anything about state that might be changed by
// other threads.
//
class {:extern} ExternalMutableMap<K, V> {
  constructor {:extern} () reads {}
  method {:extern} Put(k: K, v: V) reads {}
  method {:extern} Get(k: V) returns (v: Option<V>) reads {}
}

class FibonacciMemoizer {
  const cache: ExternalMutableMap<nat, nat>
  constructor() reads {} {
    cache := new ExternalMutableMap();
  }
  method Get(n: nat) returns (r: nat)
    reads {}
  {
    if n <= 2 {
      return 1;
    }
    var cached := cache.Get(n);
    if cached.Some? {
      r := cached.value;
    } else {
      var oneBefore := Get(n - 1);
      var twoBefore := Get(n - 2);
      r := oneBefore + twoBefore;
      cache.Put(n, r);
    }
  }
}

method {:extern} SafeFibonacci(n: nat, memoizer: FibonacciMemoizer) returns (r: nat)
  reads {}
{
  r := memoizer.Get(n);
}
