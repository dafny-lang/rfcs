datatype Option<T> = Some(value: T) | None

class {:extern} ExternalMutableMap<K, V> {
  method {:extern} Put(k: K, v: V)
  method {:extern} Get(k: V) returns (v: Option<V>)
}

method {:extern} SafeMemoizedFibonacci(n: int, cache: ExternalMutableMap<nat, nat>) returns (r: nat)
  reads {}
{
  var cached := cache.Get(n);
  if cached.Some? {
    r := cached.value;
  } else {
    r := Fibonacci(n);
    cache.Put(n, r);
  }
}
