import Qsort

def main : IO Unit := do
  let mut l := #[]
  for i in [0:500000000] do
    l := l.push i
  l := l.reverse
  l := Monadic.qsort l (Nat.blt) 
