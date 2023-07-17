import Mathlib.Tactic

namespace Chapter08.Exercise06

-- l for Lucas. For convenience set l₀ = 2.
def l : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => l n + l (n + 1)

end Chapter08.Exercise06

