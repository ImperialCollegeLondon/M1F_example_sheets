import algebra.group_power
import xenalib.modified_induction

theorem S0502'' (n : ℕ) : n ≥ 2 → 4 ^ n > 3 ^ n + 2 ^ n :=
begin
  apply modified_induction,
    -- case n = 2
  { exact dec_trivial},
  { intros d Hd Hind, -- inductive step
    exact calc
    4 ^ nat.succ d > (3 ^ d + 2 ^ d) * 4 : mul_lt_mul_of_pos_right Hind dec_trivial
    ...            = 3 ^ d * 4 + 2 ^ d * 4 : by rw add_mul
    ...            ≥ 3 ^ d * 3 + 2 ^ d * 4 : add_le_add_right (nat.mul_le_mul_left _ (dec_trivial)) _
    ...            ≥ 3 ^ d * 3 + 2 ^ d * 2 : add_le_add_left (nat.mul_le_mul_left _ (dec_trivial)) _
  }
end
