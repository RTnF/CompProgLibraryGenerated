import Proofs.Cpp.Lib.Basic

/-! Logical payload space of the Euclidean loop, not Lean evaluation or C++ heap
usage. A loop frame keeps the current two magnitudes and one remainder; it does
not retain the sequence of earlier states. Integers are counted in bits here. -/
namespace Proofs.Cpp.RatioSpace

def step (s : Nat × Nat) : Nat × Nat :=
  if s.2 = 0 then s else (s.2, s.1 % s.2)

def stateAt : Nat → (Nat × Nat) → Nat × Nat
  | 0, s => s
  | k + 1, s => step (stateAt k s)

def bounded (B : Nat) (s : Nat × Nat) : Prop := s.1 ≤ B ∧ s.2 ≤ B

/-- Live payloads include the temporary remainder, but no history. -/
def frame (s : Nat × Nat) : List Nat := [s.1, s.2, s.1 % s.2]

def payloadBits (values : List Nat) : Nat :=
  (values.map (fun value => Nat.log2 (value + 1))).sum

theorem step_bounded (B : Nat) (s : Nat × Nat) (h : bounded B s) :
    bounded B (step s) := by
  unfold step
  split
  · exact h
  · exact ⟨h.2, le_trans (Nat.mod_le _ _) h.1⟩

theorem stateAt_bounded (B k : Nat) (s : Nat × Nat) (h : bounded B s) :
    bounded B (stateAt k s) := by
  induction k with
  | zero => exact h
  | succ k ih => exact step_bounded B _ ih

theorem frame_length (s : Nat × Nat) : (frame s).length = 3 := by rfl

theorem magnitude_bits (value bits : Nat) (h : value ≤ 2 ^ bits) :
    Nat.log2 (value + 1) ≤ bits + 1 := by
  have hp : (1 : Nat) ≤ 2 ^ bits := Nat.succ_le_of_lt (Nat.two_pow_pos bits)
  have hv : value + 1 ≤ 2 ^ (bits + 1) := by
    rw [Nat.pow_succ]
    omega
  have hl := Proofs.Cpp.log2_mono2 (value + 1) (2 ^ (bits + 1)) hv
  simpa only [Nat.log2_two_pow] using hl

theorem frame_bits (s : Nat × Nat) (bits : Nat) (h : bounded (2 ^ bits) s) :
    payloadBits (frame s) ≤ 3 * (bits + 1) := by
  have ha := magnitude_bits s.1 bits h.1
  have hb := magnitude_bits s.2 bits h.2
  have hr := magnitude_bits (s.1 % s.2) bits (le_trans (Nat.mod_le _ _) h.1)
  simp only [payloadBits, frame, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- Independent of iteration count: three payloads, O(bits + 1) payload bits. -/
theorem all_frames (a b bits k : Nat) (ha : a ≤ 2 ^ bits) (hb : b ≤ 2 ^ bits) :
    (frame (stateAt k (a, b))).length = 3 ∧
    payloadBits (frame (stateAt k (a, b))) ≤ 3 * (bits + 1) := by
  exact ⟨frame_length _, frame_bits _ bits (stateAt_bounded _ k _ ⟨ha, hb⟩)⟩

/-- The translated loop's nonnegative integer update has exactly this state
transition; C++ truncating remainder agrees with emod on these values. -/
theorem integer_step (a b : Int) (ha : 0 ≤ a) (hb : 0 < b) :
    (b.toNat, (a % b).toNat) = step (a.toNat, b.toNat) := by
  have hn : b.toNat ≠ 0 := by omega
  simp only [step, hn, ↓reduceIte, Int.toNat_emod ha (Int.le_of_lt hb)]

theorem integer_truncating_step (a b : Int) (ha : 0 ≤ a) (hb : 0 < b) :
    (b.toNat, (a.tmod b).toNat) = step (a.toNat, b.toNat) := by
  rw [Int.tmod_eq_emod_of_nonneg ha]
  exact integer_step a b ha hb

/-- A caller retains a fixed collection of payloads while a callee runs. -/
theorem payloadBits_append (xs ys : List Nat) :
    payloadBits (xs ++ ys) = payloadBits xs + payloadBits ys := by
  simp [payloadBits, List.map_append, List.sum_append]

theorem context_bits (context : List Nat) (bits : Nat)
    (h : ∀ value ∈ context, value ≤ 2 ^ bits) :
    payloadBits context ≤ context.length * (bits + 1) := by
  induction context with
  | nil => simp [payloadBits]
  | cons value rest ih =>
    have hv := magnitude_bits value bits (h value (by simp))
    have hr : ∀ x ∈ rest, x ≤ 2 ^ bits := by
      intro x hx
      exact h x (by simp [hx])
    have hi := ih hr
    simp only [payloadBits, List.map_cons, List.sum_cons, List.length_cons]
    change Nat.log2 (value + 1) + payloadBits rest ≤ _
    calc
      _ ≤ (bits + 1) + rest.length * (bits + 1) := Nat.add_le_add hv hi
      _ = _ := by rw [Nat.add_mul]; omega

/-- Arbitrarily many loop iterations do not accumulate caller or callee frames. -/
theorem with_context (context : List Nat) (a b bits k : Nat)
    (hc : ∀ value ∈ context, value ≤ 2 ^ bits)
    (ha : a ≤ 2 ^ bits) (hb : b ≤ 2 ^ bits) :
    (context ++ frame (stateAt k (a, b))).length = context.length + 3 ∧
    payloadBits (context ++ frame (stateAt k (a, b))) ≤
      (context.length + 3) * (bits + 1) := by
  have hframe := all_frames a b bits k ha hb
  have hcontext := context_bits context bits hc
  constructor
  · simp only [List.length_append, hframe.1]
  · rw [payloadBits_append, Nat.add_mul]
    exact Nat.add_le_add hcontext hframe.2

/-- The LCM algorithm retains its two scaling operands while Euclid computes
its divisor. These values belong to the pure algorithm, not runtime copies. -/
def lcmContext (a b : Nat) : List Nat := [a, b]

theorem lcm_frames (a b bits k : Nat) (ha : a ≤ 2 ^ bits) (hb : b ≤ 2 ^ bits) :
    (lcmContext a b ++ frame (stateAt k (a, b))).length = 5 ∧
    payloadBits (lcmContext a b ++ frame (stateAt k (a, b))) ≤ 5 * (bits + 1) := by
  have hc : ∀ value ∈ lcmContext a b, value ≤ 2 ^ bits := by
    intro value hv
    simp [lcmContext] at hv
    rcases hv with rfl | rfl
    · exact ha
    · exact hb
  exact with_context (lcmContext a b) a b bits k hc ha hb

/-- Payloads of the final LCM scaling stage, after Euclid has returned. -/
def lcmScale (a b : Nat) : List Nat :=
  [a, b, Nat.gcd a b, a / Nat.gcd a b, a / Nat.gcd a b * b]

theorem lcm_scale_bits (a b bits : Nat) (ha0 : 0 < a)
    (ha : a ≤ 2 ^ bits) (hb : b ≤ 2 ^ bits) :
    (lcmScale a b).length = 5 ∧ payloadBits (lcmScale a b) ≤ 10 * (bits + 1) := by
  have hp : 2 ^ (2 * bits) = 2 ^ bits * 2 ^ bits := by
    rw [show 2 * bits = bits + bits by omega, Nat.pow_add]
  have hB : (1 : Nat) ≤ 2 ^ bits := Nat.succ_le_of_lt (Nat.two_pow_pos bits)
  have ha' : a ≤ 2 ^ (2 * bits) := by rw [hp]; nlinarith
  have hb' : b ≤ 2 ^ (2 * bits) := by rw [hp]; nlinarith
  have hg := le_trans (Nat.le_of_dvd ha0 (Nat.gcd_dvd_left a b)) ha'
  have hq := le_trans (Nat.div_le_self a (Nat.gcd a b)) ha'
  have hr : a / Nat.gcd a b * b ≤ 2 ^ (2 * bits) := by
    rw [hp]
    exact Nat.mul_le_mul (le_trans (Nat.div_le_self _ _) ha) hb
  have hs : ∀ value ∈ lcmScale a b, value ≤ 2 ^ (2 * bits) := by
    intro value hv
    simp [lcmScale] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact ha'
    · exact hb'
    · exact hg
    · exact hq
    · exact hr
  have hsize := context_bits (lcmScale a b) (2 * bits) hs
  change payloadBits (lcmScale a b) ≤ 5 * (2 * bits + 1) at hsize
  exact ⟨rfl, by omega⟩

/-- Either phase of the pure LCM algorithm uses O(bits + 1) payload bits. -/
theorem lcm_peak_bits (a b bits k : Nat) (ha0 : 0 < a)
    (ha : a ≤ 2 ^ bits) (hb : b ≤ 2 ^ bits) :
    max (payloadBits (lcmContext a b ++ frame (stateAt k (a, b))))
      (payloadBits (lcmScale a b)) ≤ 10 * (bits + 1) := by
  have hl := (lcm_frames a b bits k ha hb).2
  have hs := (lcm_scale_bits a b bits ha0 ha hb).2
  exact max_le (by omega) hs

/-- A signed payload includes a sign bit in addition to its magnitude. -/
def signedPayloadBits (values : List Int) : Nat :=
  values.length + payloadBits (values.map Int.natAbs)

theorem signed_context_bits (values : List Int) (bits : Nat)
    (h : ∀ value ∈ values, value.natAbs ≤ 2 ^ bits) :
    signedPayloadBits values ≤ 2 * values.length * (bits + 1) := by
  have hm : ∀ value ∈ values.map Int.natAbs, value ≤ 2 ^ bits := by
    intro value hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact h x hx
  have hs := context_bits (values.map Int.natAbs) bits hm
  simp only [List.length_map] at hs
  unfold signedPayloadBits
  nlinarith

/-- Retained normalization fields and the signed GCD wrapper's arguments. -/
def normalizeContext (n d : Int) : List Int := [n, d, n, d]

def normalizeScale (n d : Int) : List Int :=
  if n = 0 then [0, 1] else
    let g : Int := Int.gcd n d
    [n, d, g, n / g, d / g]

theorem normalize_loop_bits (n d : Int) (bits k : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) :
    signedPayloadBits (normalizeContext n d) +
      payloadBits (frame (stateAt k (n.natAbs, d.natAbs))) ≤ 11 * (bits + 1) := by
  have hc : ∀ value ∈ normalizeContext n d, value.natAbs ≤ 2 ^ bits := by
    intro value hv
    simp [normalizeContext] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hn
    · exact hd
    · exact hn
    · exact hd
  have hs := signed_context_bits (normalizeContext n d) bits hc
  change signedPayloadBits (normalizeContext n d) ≤ 8 * (bits + 1) at hs
  have hf := (all_frames n.natAbs d.natAbs bits k hn hd).2
  omega

theorem normalize_scale_bits (n d : Int) (bits : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) :
    signedPayloadBits (normalizeScale n d) ≤ 10 * (bits + 1) := by
  have hg : (Int.gcd n d : Int).natAbs ≤ 2 ^ bits := by
    simp only [Int.natAbs_natCast, Int.gcd]
    by_cases hz : n.natAbs = 0
    · simpa only [hz, Nat.gcd_zero_left] using hd
    · exact le_trans (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hn
  have hq₁ := le_trans (Int.natAbs_ediv_le_natAbs n (Int.gcd n d)) hn
  have hq₂ := le_trans (Int.natAbs_ediv_le_natAbs d (Int.gcd n d)) hd
  have hs : ∀ value ∈ normalizeScale n d, value.natAbs ≤ 2 ^ bits := by
    intro value hv
    by_cases hz : n = 0
    · simp [normalizeScale, hz] at hv
      rcases hv with rfl | rfl
      · simp
      · exact Nat.succ_le_of_lt (Nat.two_pow_pos bits)
    · simp [normalizeScale, hz] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact hn
      · exact hd
      · exact hg
      · exact hq₁
      · exact hq₂
  have hb := signed_context_bits (normalizeScale n d) bits hs
  have hlen : (normalizeScale n d).length ≤ 5 := by
    unfold normalizeScale
    split <;> simp
  calc
    _ ≤ 2 * (normalizeScale n d).length * (bits + 1) := hb
    _ ≤ 10 * (bits + 1) := Nat.mul_le_mul_right _ (by omega)

theorem normalize_peak_bits (n d : Int) (bits k : Nat)
    (hn : n.natAbs ≤ 2 ^ bits) (hd : d.natAbs ≤ 2 ^ bits) :
    max (signedPayloadBits (normalizeContext n d) +
      payloadBits (frame (stateAt k (n.natAbs, d.natAbs))))
      (signedPayloadBits (normalizeScale n d)) ≤ 11 * (bits + 1) := by
  exact max_le (normalize_loop_bits n d bits k hn hd)
    (le_trans (normalize_scale_bits n d bits hn hd) (by omega))

end Proofs.Cpp.RatioSpace
