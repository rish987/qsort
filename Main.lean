import Qsort

def main : IO Unit := do
  let mut l := #[]
  for i in [0:10] do
    l := l.push i
  l := l.reverse
  dbg_trace s!"DBG[23]: Main.lean:7: l={l}"
  l := Pure.qsort l (Nat.blt) 
  dbg_trace s!"DBG[23]: Main.lean:7: l={l}"
