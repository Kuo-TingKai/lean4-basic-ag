def fibonacci : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacci n + fibonacci (n + 1)

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def main (args : List String) : IO UInt32 := do
  IO.println "=== Lean4 純 IO 範例 ==="
  IO.println ""
  IO.println s!"3 + 0 = {3 + 0}"
  IO.println s!"2 * (3 + 4) = {2 * (3 + 4)}"
  IO.println s!"fibonacci 5 = {fibonacci 5}"
  IO.println s!"factorial 5 = {factorial 5}"
  IO.println ""
  IO.println "執行結束！"
  return 0 