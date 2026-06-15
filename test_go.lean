import Mathlib.Data.List.Basic
#check List.take_append
#check List.take_append'
#check List.take_eq_take
#print List.take_append

def delim : List Bool := [false, false, true]

example (p s t : List Bool) (heq : p ++ (delim ++ s) = delim ++ t) (hp : 3 ≤ p.length) :
    p.take 3 = delim := by
  rw [delim] at heq
  have := congrArg (List.take 3) heq
  sorry
