namespace Proofs.Mod61Math

def M61 : Nat := 2^61-1

-- The multiplication identity behind `mul61`, with every quantity named.
theorem expand (au ad bu bd : Nat) :
    (au * 2^31 + ad) * (bu * 2^31 + bd) = au * bu * 2^62 + (ad * bu + au * bd) * 2^31 + ad * bd := by
  simp only [Nat.add_mul, Nat.mul_add]
  have e : (2:Nat)^62 = 2^31 * 2^31 := by decide
  rw [e]
  ac_rfl

theorem mul61_math (a b au ad bu bd mid midu midd : Nat) (ha : a < 2^61) (hb : b < 2^61)
    (hau : au = a / 2^31) (had : ad = a % 2^31) (hbu : bu = b / 2^31) (hbd : bd = b % 2^31)
    (hmid : mid = ad * bu + au * bd) (hmu : midu = mid / 2^30) (hmd : midd = mid % 2^30) :
    au * bu * 2 + midu + midd * 2^31 + ad * bd < 2^64 ∧
      (au * bu * 2 + midu + midd * 2^31 + ad * bd) % M61 = (a * b) % M61 := by
  have hab : a = au * 2^31 + ad := by
    have := Nat.div_add_mod a (2^31); rw [← hau,← had] at this; omega
  have hbb : b = bu * 2^31 + bd := by
    have := Nat.div_add_mod b (2^31); rw [← hbu,← hbd] at this; omega
  have hmm : mid = midu * 2^30 + midd := by
    have := Nat.div_add_mod mid (2^30); rw [← hmu,← hmd] at this; omega
  have au_lt : au < 2^30 := by omega
  have bu_lt : bu < 2^30 := by omega
  have ad_lt : ad < 2^31 := by omega
  have bd_lt : bd < 2^31 := by omega
  have p1 : au * bu ≤ (2^30-1) * (2^30-1) := Nat.mul_le_mul (by omega) (by omega)
  have p2 : ad * bu ≤ (2^31-1) * (2^30-1) := Nat.mul_le_mul (by omega) (by omega)
  have p3 : au * bd ≤ (2^30-1) * (2^31-1) := Nat.mul_le_mul (by omega) (by omega)
  have p4 : ad * bd ≤ (2^31-1) * (2^31-1) := Nat.mul_le_mul (by omega) (by omega)
  have ex := expand au ad bu bd
  rw [← hab,← hbb] at ex
  have midd_lt : midd < 2^30 := by omega
  have midu_lt : midu < 2^32 := by omega
  constructor
  · omega
  · unfold M61
    omega

end Proofs.Mod61Math
