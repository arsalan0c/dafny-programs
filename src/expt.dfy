function expt(b: int, n: int): int
  requires n >= 0
{
  if n == 0 then 1 else b * expt(b, n - 1)
}