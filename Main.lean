import Qsort

def main : IO Unit := do
  let mut l := #[]
  for i in [0:10] do
    l := l.push i
  dbg_trace s!"DBG[34]: Main.lean:6"
  l := l.reverse
  dbg_trace s!"DBG[33]: Main.lean:8 (after dbg_trace s!DBG[23]: Main.lean:7: l=)"
  let max := 1
  -- let max := 1000000000
  for i in [0:max + 1] do
    let ret : Array Nat ← pure $ Monadic.qsort l (Nat.blt) 
    if i == max then
      dbg_trace s!"DBG[35]: Main.lean:12 {ret}"
  dbg_trace s!"DBG[32]: Main.lean:9 (after l := Monadic.qsort l (Nat.blt))"
