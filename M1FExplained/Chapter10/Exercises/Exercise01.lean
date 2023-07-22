import Mathlib.Tactic

namespace Chapter10.Exercise01

/- 
Lean can find the answers to this exercise 
by itself easily with the following: 
-/

#eval Nat.gcd 17 29 -- 1
#eval Nat.gcdA 17 29 -- 12
#eval Nat.gcdB 17 29 -- -7

/- 
The intended solution however, is to apply the Euclidian Algorithm. 
We can show the process with `have`'s, but note this is purley for illustration:
`norm_num` would instantly prove all parts of this question. 
-/


lemma part_i_a : Nat.gcd 17 29 = 1 := by
  have : 29 = 17 * 1 + 12 := by norm_num
  have : 17 = 12 * 1 + 5  := by norm_num
  have : 12 = 5 * 2 + 2   := by norm_num
  have : 5  = 2 * 2 + 1   := by norm_num
  have : 2  = 2 * 1 + 0   := by norm_num
  norm_num


-- Finding two integers s,t such that 1 = s * 17 + t * 29.
lemma part_i_b : 1 = 12 * 17 - 7 * 29  := by
  calc
    1 = 5 - 2 * 2                  := by norm_num
    _ = 5 - 2 * (12 - 5 * 2)       := by norm_num
    _ = 5 * 5 - 2 * 12             := by norm_num
    _ = 5 * (17 - 12 * 1) - 2 * 12 := by norm_num
    _ = 5 * 17 - 7 * 12            := by norm_num
    _ = 5 * 17 - 7 * (29 - 17 *1 ) := by norm_num
    _ = 12 * 17 - 7 * 29           := by norm_num


-- Parts ii, iii follow in exactly the same way.
#eval Nat.gcd 713 552 -- 23
#eval Nat.gcdA 713 552 -- 7
#eval Nat.gcdB 713 552 -- -9


lemma part_ii_a : Nat.gcd 713 552 = 23 := by
  have : 713 = 552 * 1 + 161 := by norm_num
  have : 552 = 161 * 3 + 69  := by norm_num
  have : 161 = 69 * 2 + 23   := by norm_num
  have : 69 = 23 * 3 + 0     := by norm_num
  norm_num


lemma part_ii_b : 23 = 7 * 713 - 9 * 552 := by
  calc
    23 = 161 - 2 * 69                  := by norm_num
    _  = 161 - 2 * (552 - 3 * 161)     := by norm_num
    _  = 7 * 161  - 2 * 552            := by norm_num
    _  = 7 * (713 - 1 * 552) - 2 * 552 := by norm_num
    _  = 7 * 713 - 9 * 552             := by norm_num


#eval Nat.gcd 299 345  -- 23
#eval Nat.gcdA 299 345 -- -6
#eval Nat.gcdB 299 345 -- 7


lemma part_iii_a : Nat.gcd 299 345 = 23 := by
  have : 345 = 299 * 1 + 46 := by norm_num
  have : 299 = 46 * 6 + 23  := by norm_num
  have : 46 = 23 * 2 + 0    := by norm_num
  norm_num


lemma part_iii_b : 23 = 7 * 299 - 6 * 345 := by
  calc
    23 = 299 - 6 * 46              := by norm_num
    _  = 299 - 6 * (345 - 1 * 299) := by norm_num
    _  = 7 * 299 - 6 * 345         := by norm_num


end Chapter10.Exercise01
