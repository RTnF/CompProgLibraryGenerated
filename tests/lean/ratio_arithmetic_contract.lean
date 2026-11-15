-- Appended to the complete generated candidate after importing RatioMath.
open Proofs.Cpp Proofs.Cpp.Gen

theorem ratio_normalize_int_run [NumericCost] (n d : Int) (t : Nat) :
    (cp.Ratio.normalize (⟨n, d⟩ : cp.Ratio Int)).run t =
      some ((⟨(RatioMath.normalize n d).1, (RatioMath.normalize n d).2⟩ : cp.Ratio Int),
        t + 1 + if n = 0 then 0 else numericGcdCost n d) := by
  by_cases hn : n = 0
  · subst n
    simp [cp.Ratio.normalize, RatioMath.normalize, tick, StateT.run, modify]
    rfl
  · by_cases hd : d < 0
    · simp [cp.Ratio.normalize, RatioMath.normalize, hn, hd, numericGcd, numericGcdCost,
        tick, tickN, StateT.run, modify, NumericGcd.magnitude, NumericGcd.ofNat, Nat.add_assoc]
      change some (_, t + 1 + _) = some (_, t + (1 + _))
      simp only [Nat.add_assoc]
    · simp [cp.Ratio.normalize, RatioMath.normalize, hn, hd, numericGcd, numericGcdCost,
        tick, tickN, StateT.run, modify, NumericGcd.magnitude, NumericGcd.ofNat, Nat.add_assoc]
      change some (_, t + 1 + _) = some (_, t + (1 + _))
      simp only [Nat.add_assoc]

theorem ratio_normalize_int_canonical [NumericCost] (n d : Int) (hd : d ≠ 0) (t : Nat) :
    (cp.Ratio.normalize (⟨n, d⟩ : cp.Ratio Int)).run t =
      some ((⟨(Rat.divInt n d).num, ((Rat.divInt n d).den : Int)⟩ : cp.Ratio Int),
        t + 1 + if n = 0 then 0 else numericGcdCost n d) := by
  rw [ratio_normalize_int_run, RatioMath.normalize_eq_canonical n d hd]

theorem ratio_init_int_run [NumericCost] (n d : Int) (t : Nat) :
    (cp.Ratio.init_T_T n d).run t =
      some ((⟨(RatioMath.normalize n d).1, (RatioMath.normalize n d).2⟩ : cp.Ratio Int),
        t + 2 + if n = 0 then 0 else numericGcdCost n d) := by
  change Option.bind ((cp.Ratio.normalize (⟨n, d⟩ : cp.Ratio Int)).run (t + 1))
    (fun result => some ((⟨result.1.n, result.1.d⟩ : cp.Ratio Int), result.2)) = _
  rw [ratio_normalize_int_run]
  simp only [Option.bind_some]

theorem ratio_init_scalar_run {T : Type} [One T] (n : T) (t : Nat) :
    (cp.Ratio.init_T n).run t = some ((⟨n, 1⟩ : cp.Ratio T), t + 1) := by
  rfl

theorem ratio_prefix_increment_run {T : Type} [Add T] (n d : T) (t : Nat) :
    (cp.Ratio.op_inc_0 (⟨n, d⟩ : cp.Ratio T)).run t =
      some (((⟨n + d, d⟩ : cp.Ratio T), (⟨n + d, d⟩ : cp.Ratio T)), t + 1) := by
  rfl

theorem ratio_postfix_increment_run {T : Type} [Add T] (n d : T) (tag : Int) (t : Nat) :
    (cp.Ratio.op_inc_int (⟨n, d⟩ : cp.Ratio T) tag).run t =
      some (((⟨n, d⟩ : cp.Ratio T), (⟨n + d, d⟩ : cp.Ratio T)), t + 2) := by
  rfl

theorem ratio_prefix_decrement_run {T : Type} [Sub T] (n d : T) (t : Nat) :
    (cp.Ratio.op_dec_0 (⟨n, d⟩ : cp.Ratio T)).run t =
      some (((⟨n - d, d⟩ : cp.Ratio T), (⟨n - d, d⟩ : cp.Ratio T)), t + 1) := by
  rfl

theorem ratio_postfix_decrement_run {T : Type} [Sub T] (n d : T) (tag : Int) (t : Nat) :
    (cp.Ratio.op_dec_int (⟨n, d⟩ : cp.Ratio T) tag).run t =
      some (((⟨n, d⟩ : cp.Ratio T), (⟨n - d, d⟩ : cp.Ratio T)), t + 2) := by
  rfl

theorem ratio_unary_plus_run {T : Type} (n d : T) (t : Nat) :
    (cp.Ratio.op_add (⟨n, d⟩ : cp.Ratio T)).run t =
      some ((⟨n, d⟩ : cp.Ratio T), t + 1) := by
  rfl

theorem ratio_unary_minus_int_run [NumericCost] (n d : Int) (t : Nat) :
    (cp.Ratio.op_sub (⟨n, d⟩ : cp.Ratio Int)).run t =
      some ((⟨(RatioMath.normalize (-n) d).1, (RatioMath.normalize (-n) d).2⟩ : cp.Ratio Int),
        t + 3 + if -n = 0 then 0 else numericGcdCost (-n) d) := by
  change (cp.Ratio.init_T_T (-n) d).run (t + 1) = _
  rw [ratio_init_int_run]

theorem ratio_add_assign_int_run [NumericCost] (n d m e : Int) (t : Nat) :
    let l : Int := Int.lcm d e
    let z := l / d * n + l / e * m
    let p := RatioMath.add n d m e
    let q : cp.Ratio Int := ⟨p.1, p.2⟩
    (cp.Ratio.op_add_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t =
      some ((q, q), t + 2 + numericLcmCost d e + if z = 0 then 0 else numericGcdCost z l) := by
  dsimp only
  let l : Int := Int.lcm d e
  let z := l / d * n + l / e * m
  change Option.bind ((cp.Ratio.normalize (⟨z, l⟩ : cp.Ratio Int)).run
    (t + 1 + numericLcmCost d e))
    (fun result => some ((result.1, result.1), result.2)) = _
  rw [ratio_normalize_int_run]
  simp only [Option.bind_some]
  congr 2
  dsimp only [z, l]
  omega

theorem ratio_sub_assign_int_run [NumericCost] (n d m e : Int) (t : Nat) :
    let l : Int := Int.lcm d e
    let z := l / d * n - l / e * m
    let p := RatioMath.sub n d m e
    let q : cp.Ratio Int := ⟨p.1, p.2⟩
    (cp.Ratio.op_sub_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t =
      some ((q, q), t + 2 + numericLcmCost d e + if z = 0 then 0 else numericGcdCost z l) := by
  dsimp only
  let l : Int := Int.lcm d e
  let z := l / d * n - l / e * m
  change Option.bind ((cp.Ratio.normalize (⟨z, l⟩ : cp.Ratio Int)).run
    (t + 1 + numericLcmCost d e))
    (fun result => some ((result.1, result.1), result.2)) = _
  rw [ratio_normalize_int_run]
  simp only [Option.bind_some]
  congr 2
  dsimp only [z, l]
  omega

theorem ratio_add_assign_int_value [NumericCost] (n d m e : Int)
    (hd : d ≠ 0) (he : e ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.Ratio.op_add_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t = some ((q, q), c) ∧
      Rat.divInt q.n q.d = Rat.divInt n d + Rat.divInt m e := by
  let p := RatioMath.add n d m e
  refine ⟨⟨p.1, p.2⟩, _, ratio_add_assign_int_run n d m e t, ?_⟩
  exact RatioMath.add_value n d m e hd he

theorem ratio_sub_assign_int_value [NumericCost] (n d m e : Int)
    (hd : d ≠ 0) (he : e ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.Ratio.op_sub_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t = some ((q, q), c) ∧
      Rat.divInt q.n q.d = Rat.divInt n d - Rat.divInt m e := by
  let p := RatioMath.sub n d m e
  refine ⟨⟨p.1, p.2⟩, _, ratio_sub_assign_int_run n d m e t, ?_⟩
  exact RatioMath.sub_value n d m e hd he

theorem ratio_mul_assign_int_run [NumericCost] (n d m e : Int) (t : Nat) :
    let p := RatioMath.mul n d m e
    let q : cp.Ratio Int := ⟨p.1, p.2⟩
    (cp.Ratio.op_mul_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t =
      some ((q, q), t + 1 + numericGcdCost n e + numericGcdCost m d) := by
  rfl

theorem ratio_mul_assign_int_value [NumericCost] (n d m e : Int)
    (hd : d ≠ 0) (he : e ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.Ratio.op_mul_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t = some ((q, q), c) ∧
      Rat.divInt q.n q.d = Rat.divInt n d * Rat.divInt m e := by
  let p := RatioMath.mul n d m e
  refine ⟨⟨p.1, p.2⟩, _, ratio_mul_assign_int_run n d m e t, ?_⟩
  exact RatioMath.mul_value n d m e hd he

theorem ratio_div_assign_int_run [NumericCost] (n d m e : Int) (hm : m ≠ 0) (t : Nat) :
    let g : Int := Int.gcd n m
    let h : Int := Int.gcd d e
    let z := n / g * (e / h)
    let w := d / h * (m / g)
    let p := RatioMath.div n d m e
    let q : cp.Ratio Int := ⟨p.1, p.2⟩
    (cp.Ratio.op_div_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t =
      some ((q, q), t + 2 + numericGcdCost n m + numericGcdCost d e +
        if z = 0 then 0 else numericGcdCost z w) := by
  dsimp only
  have hc : decide (m ≠ 0) = true := decide_eq_true hm
  simp only [cp.Ratio.op_div_assign, check, hc, ite_true,
    tick, tickN, StateT.run, modify, modifyGet, pure, bind, StateT.bind,
    StateT.pure, Option.bind_some]
  change Option.bind ((cp.Ratio.normalize
    (⟨n / (Int.gcd n m : Int) * (e / (Int.gcd d e : Int)),
      d / (Int.gcd d e : Int) * (m / (Int.gcd n m : Int))⟩ : cp.Ratio Int)).run
      (t + 1 + numericGcdCost n m + numericGcdCost d e))
    (fun result => some ((result.1, result.1), result.2)) = _
  rw [ratio_normalize_int_run]
  simp only [Option.bind_some]
  congr 2
  omega

theorem ratio_div_assign_int_value [NumericCost] (n d m e : Int)
    (hd : d ≠ 0) (hm : m ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.Ratio.op_div_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t = some ((q, q), c) ∧
      Rat.divInt q.n q.d = Rat.divInt n d / Rat.divInt m e := by
  let p := RatioMath.div n d m e
  refine ⟨⟨p.1, p.2⟩, _, ratio_div_assign_int_run n d m e hm t, ?_⟩
  exact RatioMath.div_value n d m e hd hm

theorem ratio_compare_int_run [NumericCost] (n d m e : Int) (t : Nat) :
    (cp.Ratio.op_cmp (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t =
      some ((if e / (Int.gcd d e : Int) * n < d / (Int.gcd d e : Int) * m then Ordering.lt
        else if d / (Int.gcd d e : Int) * m < e / (Int.gcd d e : Int) * n then Ordering.gt
        else Ordering.eq), t + 1 + numericGcdCost d e) := by
  rfl

theorem ratio_compare_int_value [NumericCost] (n d m e : Int)
    (hd : 0 < d) (he : 0 < e) (t : Nat) :
    (cp.Ratio.op_cmp (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t =
      some ((if Rat.divInt n d < Rat.divInt m e then Ordering.lt
        else if Rat.divInt m e < Rat.divInt n d then Ordering.gt else Ordering.eq),
        t + 1 + numericGcdCost d e) := by
  rw [ratio_compare_int_run]
  have h := RatioMath.compare_lt m e n d he hd
  rw [Int.gcd_comm e d] at h
  simp only [RatioMath.compare_lt n d m e hd he, h]

theorem ratio_equal_run {T : Type} [DecidableEq T] (n d m e : T) (t : Nat) :
    (cp.Ratio.op_eq (⟨n, d⟩ : cp.Ratio T) (⟨m, e⟩ : cp.Ratio T)).run t =
      some (decide (n = m ∧ d = e), t + 1) := by
  rfl

theorem ratio_equal_normalized_value (n d m e : Int)
    (hd : d ≠ 0) (he : e ≠ 0) (t : Nat) :
    let p := RatioMath.normalize n d
    let q := RatioMath.normalize m e
    (cp.Ratio.op_eq (⟨p.1, p.2⟩ : cp.Ratio Int) (⟨q.1, q.2⟩ : cp.Ratio Int)).run t =
      some (decide (Rat.divInt n d = Rat.divInt m e), t + 1) := by
  dsimp only
  rw [ratio_equal_run]
  have h := RatioMath.normalize_eq_iff n d m e hd he
  rw [Prod.ext_iff] at h
  simp only [h]

/-- Wrapping preserves the compound operation's effects and nonreturn. -/
theorem ratio_add_Ratio_Ratio_run {T : Type} [Zero T] [One T] [Add T] [Mul T] [Neg T] [Div T] [LT T] [DecidableLT T] [DecidableEq T] [NumericCost] [NumericGcd T] (a : (cp.Ratio T)) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_add_Ratio_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_add_assign a b).run (t + 1))
        (fun result => some (result.1.1, result.2)) := by
  rfl

/-- Wrapping preserves the compound operation's effects and nonreturn. -/
theorem ratio_add_Ratio_T_run {T : Type} [Zero T] [One T] [Add T] [Mul T] [Neg T] [Div T] [LT T] [DecidableLT T] [DecidableEq T] [NumericCost] [NumericGcd T] (a : (cp.Ratio T)) (b : T) (t : Nat) :
    (cp.op_add_Ratio_T a b).run t =
      Option.bind ((cp.Ratio.op_add_assign a (⟨b, 1⟩ : cp.Ratio T)).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

/-- Wrapping preserves the compound operation's effects and nonreturn. -/
theorem ratio_add_T_Ratio_run {T : Type} [Zero T] [One T] [Add T] [Mul T] [Neg T] [Div T] [LT T] [DecidableLT T] [DecidableEq T] [NumericCost] [NumericGcd T] (a : T) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_add_T_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_add_assign (⟨a, 1⟩ : cp.Ratio T) b).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

/-- Wrapping preserves the compound operation's effects and nonreturn. -/
theorem ratio_sub_Ratio_Ratio_run {T : Type} [Zero T] [One T] [Sub T] [Mul T] [Neg T] [Div T] [LT T] [DecidableLT T] [DecidableEq T] [NumericCost] [NumericGcd T] (a : (cp.Ratio T)) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_sub_Ratio_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_sub_assign a b).run (t + 1))
        (fun result => some (result.1.1, result.2)) := by
  rfl

/-- Wrapping preserves the compound operation's effects and nonreturn. -/
theorem ratio_sub_Ratio_T_run {T : Type} [Zero T] [One T] [Sub T] [Mul T] [Neg T] [Div T] [LT T] [DecidableLT T] [DecidableEq T] [NumericCost] [NumericGcd T] (a : (cp.Ratio T)) (b : T) (t : Nat) :
    (cp.op_sub_Ratio_T a b).run t =
      Option.bind ((cp.Ratio.op_sub_assign a (⟨b, 1⟩ : cp.Ratio T)).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

/-- Wrapping preserves the compound operation's effects and nonreturn. -/
theorem ratio_sub_T_Ratio_run {T : Type} [Zero T] [One T] [Sub T] [Mul T] [Neg T] [Div T] [LT T] [DecidableLT T] [DecidableEq T] [NumericCost] [NumericGcd T] (a : T) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_sub_T_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_sub_assign (⟨a, 1⟩ : cp.Ratio T) b).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

/-- Wrapping preserves the compound operation's effects and nonreturn. -/
theorem ratio_mul_Ratio_Ratio_run {T : Type} [Mul T] [Div T] [NumericCost] [NumericGcd T] (a : (cp.Ratio T)) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_mul_Ratio_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_mul_assign a b).run (t + 1))
        (fun result => some (result.1.1, result.2)) := by
  rfl

/-- Wrapping preserves the compound operation's effects and nonreturn. -/
theorem ratio_mul_Ratio_T_run {T : Type} [One T] [Mul T] [Div T] [NumericCost] [NumericGcd T] (a : (cp.Ratio T)) (b : T) (t : Nat) :
    (cp.op_mul_Ratio_T a b).run t =
      Option.bind ((cp.Ratio.op_mul_assign a (⟨b, 1⟩ : cp.Ratio T)).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

/-- Wrapping preserves the compound operation's effects and nonreturn. -/
theorem ratio_mul_T_Ratio_run {T : Type} [One T] [Mul T] [Div T] [NumericCost] [NumericGcd T] (a : T) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_mul_T_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_mul_assign (⟨a, 1⟩ : cp.Ratio T) b).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

/-- Wrapping preserves the compound operation's effects and nonreturn. -/
theorem ratio_div_Ratio_Ratio_run {T : Type} [Zero T] [One T] [Mul T] [Neg T] [Div T] [LT T] [DecidableLT T] [DecidableEq T] [NumericCost] [NumericGcd T] (a : (cp.Ratio T)) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_div_Ratio_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_div_assign a b).run (t + 1))
        (fun result => some (result.1.1, result.2)) := by
  rfl

/-- Wrapping preserves the compound operation's effects and nonreturn. -/
theorem ratio_div_Ratio_T_run {T : Type} [Zero T] [One T] [Mul T] [Neg T] [Div T] [LT T] [DecidableLT T] [DecidableEq T] [NumericCost] [NumericGcd T] (a : (cp.Ratio T)) (b : T) (t : Nat) :
    (cp.op_div_Ratio_T a b).run t =
      Option.bind ((cp.Ratio.op_div_assign a (⟨b, 1⟩ : cp.Ratio T)).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

/-- Wrapping preserves the compound operation's effects and nonreturn. -/
theorem ratio_div_T_Ratio_run {T : Type} [Zero T] [One T] [Mul T] [Neg T] [Div T] [LT T] [DecidableLT T] [DecidableEq T] [NumericCost] [NumericGcd T] (a : T) (b : (cp.Ratio T)) (t : Nat) :
    (cp.op_div_T_Ratio a b).run t =
      Option.bind ((cp.Ratio.op_div_assign (⟨a, 1⟩ : cp.Ratio T) b).run (t + 2))
        (fun result => some (result.1.1, result.2)) := by
  rfl

theorem ratio_add_Ratio_Ratio_value [NumericCost] (n d m e : Int)
    (hd : d ≠ 0) (he : e ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.op_add_Ratio_Ratio (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t = some (q, c) ∧
        Rat.divInt q.n q.d = Rat.divInt n d + Rat.divInt m e := by
  obtain ⟨q, c, hr, hv⟩ := ratio_add_assign_int_value n d m e hd he (t + 1)
  refine ⟨q, c, ?_, ?_⟩
  · rw [ratio_add_Ratio_Ratio_run, hr]
    rfl
  · simpa only [Rat.divInt_one] using hv

theorem ratio_add_Ratio_T_value [NumericCost] (n d b : Int)
    (hd : d ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.op_add_Ratio_T (⟨n, d⟩ : cp.Ratio Int) b).run t = some (q, c) ∧
        Rat.divInt q.n q.d = Rat.divInt n d + (b : Rat) := by
  obtain ⟨q, c, hr, hv⟩ := ratio_add_assign_int_value n d b 1 hd (by decide) (t + 2)
  refine ⟨q, c, ?_, ?_⟩
  · rw [ratio_add_Ratio_T_run, hr]
    rfl
  · simpa only [Rat.divInt_one] using hv

theorem ratio_add_T_Ratio_value [NumericCost] (a m e : Int)
    (he : e ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.op_add_T_Ratio a (⟨m, e⟩ : cp.Ratio Int)).run t = some (q, c) ∧
        Rat.divInt q.n q.d = (a : Rat) + Rat.divInt m e := by
  obtain ⟨q, c, hr, hv⟩ := ratio_add_assign_int_value a 1 m e (by decide) he (t + 2)
  refine ⟨q, c, ?_, ?_⟩
  · rw [ratio_add_T_Ratio_run, hr]
    rfl
  · simpa only [Rat.divInt_one] using hv

theorem ratio_sub_Ratio_Ratio_value [NumericCost] (n d m e : Int)
    (hd : d ≠ 0) (he : e ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.op_sub_Ratio_Ratio (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t = some (q, c) ∧
        Rat.divInt q.n q.d = Rat.divInt n d - Rat.divInt m e := by
  obtain ⟨q, c, hr, hv⟩ := ratio_sub_assign_int_value n d m e hd he (t + 1)
  refine ⟨q, c, ?_, ?_⟩
  · rw [ratio_sub_Ratio_Ratio_run, hr]
    rfl
  · simpa only [Rat.divInt_one] using hv

theorem ratio_sub_Ratio_T_value [NumericCost] (n d b : Int)
    (hd : d ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.op_sub_Ratio_T (⟨n, d⟩ : cp.Ratio Int) b).run t = some (q, c) ∧
        Rat.divInt q.n q.d = Rat.divInt n d - (b : Rat) := by
  obtain ⟨q, c, hr, hv⟩ := ratio_sub_assign_int_value n d b 1 hd (by decide) (t + 2)
  refine ⟨q, c, ?_, ?_⟩
  · rw [ratio_sub_Ratio_T_run, hr]
    rfl
  · simpa only [Rat.divInt_one] using hv

theorem ratio_sub_T_Ratio_value [NumericCost] (a m e : Int)
    (he : e ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.op_sub_T_Ratio a (⟨m, e⟩ : cp.Ratio Int)).run t = some (q, c) ∧
        Rat.divInt q.n q.d = (a : Rat) - Rat.divInt m e := by
  obtain ⟨q, c, hr, hv⟩ := ratio_sub_assign_int_value a 1 m e (by decide) he (t + 2)
  refine ⟨q, c, ?_, ?_⟩
  · rw [ratio_sub_T_Ratio_run, hr]
    rfl
  · simpa only [Rat.divInt_one] using hv

theorem ratio_mul_Ratio_Ratio_value [NumericCost] (n d m e : Int)
    (hd : d ≠ 0) (he : e ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.op_mul_Ratio_Ratio (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t = some (q, c) ∧
        Rat.divInt q.n q.d = Rat.divInt n d * Rat.divInt m e := by
  obtain ⟨q, c, hr, hv⟩ := ratio_mul_assign_int_value n d m e hd he (t + 1)
  refine ⟨q, c, ?_, ?_⟩
  · rw [ratio_mul_Ratio_Ratio_run, hr]
    rfl
  · simpa only [Rat.divInt_one] using hv

theorem ratio_mul_Ratio_T_value [NumericCost] (n d b : Int)
    (hd : d ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.op_mul_Ratio_T (⟨n, d⟩ : cp.Ratio Int) b).run t = some (q, c) ∧
        Rat.divInt q.n q.d = Rat.divInt n d * (b : Rat) := by
  obtain ⟨q, c, hr, hv⟩ := ratio_mul_assign_int_value n d b 1 hd (by decide) (t + 2)
  refine ⟨q, c, ?_, ?_⟩
  · rw [ratio_mul_Ratio_T_run, hr]
    rfl
  · simpa only [Rat.divInt_one] using hv

theorem ratio_mul_T_Ratio_value [NumericCost] (a m e : Int)
    (he : e ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.op_mul_T_Ratio a (⟨m, e⟩ : cp.Ratio Int)).run t = some (q, c) ∧
        Rat.divInt q.n q.d = (a : Rat) * Rat.divInt m e := by
  obtain ⟨q, c, hr, hv⟩ := ratio_mul_assign_int_value a 1 m e (by decide) he (t + 2)
  refine ⟨q, c, ?_, ?_⟩
  · rw [ratio_mul_T_Ratio_run, hr]
    rfl
  · simpa only [Rat.divInt_one] using hv

theorem ratio_div_Ratio_Ratio_value [NumericCost] (n d m e : Int)
    (hd : d ≠ 0) (hm : m ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.op_div_Ratio_Ratio (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t = some (q, c) ∧
        Rat.divInt q.n q.d = Rat.divInt n d / Rat.divInt m e := by
  obtain ⟨q, c, hr, hv⟩ := ratio_div_assign_int_value n d m e hd hm (t + 1)
  refine ⟨q, c, ?_, ?_⟩
  · rw [ratio_div_Ratio_Ratio_run, hr]
    rfl
  · simpa only [Rat.divInt_one] using hv

theorem ratio_div_Ratio_T_value [NumericCost] (n d b : Int)
    (hd : d ≠ 0) (hm : b ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.op_div_Ratio_T (⟨n, d⟩ : cp.Ratio Int) b).run t = some (q, c) ∧
        Rat.divInt q.n q.d = Rat.divInt n d / (b : Rat) := by
  obtain ⟨q, c, hr, hv⟩ := ratio_div_assign_int_value n d b 1 hd hm (t + 2)
  refine ⟨q, c, ?_, ?_⟩
  · rw [ratio_div_Ratio_T_run, hr]
    rfl
  · simpa only [Rat.divInt_one] using hv

theorem ratio_div_T_Ratio_value [NumericCost] (a m e : Int)
    (hm : m ≠ 0) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.op_div_T_Ratio a (⟨m, e⟩ : cp.Ratio Int)).run t = some (q, c) ∧
        Rat.divInt q.n q.d = (a : Rat) / Rat.divInt m e := by
  obtain ⟨q, c, hr, hv⟩ := ratio_div_assign_int_value a 1 m e (by decide) hm (t + 2)
  refine ⟨q, c, ?_, ?_⟩
  · rw [ratio_div_T_Ratio_run, hr]
    rfl
  · simpa only [Rat.divInt_one] using hv

/-- Failed divisor assertions do not become successful normalized zero values. -/
theorem ratio_div_zero_run [NumericCost] (n d e : Int) (t : Nat) :
    (cp.Ratio.op_div_assign (⟨n, d⟩ : cp.Ratio Int) (⟨0, e⟩ : cp.Ratio Int)).run t = none := by
  rfl

theorem ratio_div_Ratio_Ratio_zero [NumericCost] (n d e : Int) (t : Nat) :
    (cp.op_div_Ratio_Ratio (⟨n, d⟩ : cp.Ratio Int) (⟨0, e⟩ : cp.Ratio Int)).run t = none := by
  rw [ratio_div_Ratio_Ratio_run, ratio_div_zero_run]
  rfl

theorem ratio_div_Ratio_T_zero [NumericCost] (n d : Int) (t : Nat) :
    (cp.op_div_Ratio_T (⟨n, d⟩ : cp.Ratio Int) 0).run t = none := by
  rw [ratio_div_Ratio_T_run, ratio_div_zero_run]
  rfl

theorem ratio_div_T_Ratio_zero [NumericCost] (a e : Int) (t : Nat) :
    (cp.op_div_T_Ratio a (⟨0, e⟩ : cp.Ratio Int)).run t = none := by
  rw [ratio_div_T_Ratio_run, ratio_div_zero_run]
  rfl

theorem ratio_prefix_increment_canonical_value (n d : Int)
    (h : RatioMath.Canonical n d) (t : Nat) :
    ∃ (q r : cp.Ratio Int) (c : Nat),
      (cp.Ratio.op_inc_0 (⟨n, d⟩ : cp.Ratio Int)).run t = some ((q, r), c) ∧
      Rat.divInt q.n q.d = Rat.divInt n d + 1 ∧
      RatioMath.Canonical q.n q.d ∧ RatioMath.Canonical r.n r.d := by
  refine ⟨⟨n + d, d⟩, ⟨n + d, d⟩, t + 1,
    ratio_prefix_increment_run n d t, ?_, ?_, ?_⟩
  · exact RatioMath.increment_value n d (Int.ne_of_gt h.1)
  · exact RatioMath.increment_canonical n d h
  · exact RatioMath.increment_canonical n d h

theorem ratio_postfix_increment_canonical_value (n d : Int)
    (h : RatioMath.Canonical n d) (tag : Int) (t : Nat) :
    ∃ (q r : cp.Ratio Int) (c : Nat),
      (cp.Ratio.op_inc_int (⟨n, d⟩ : cp.Ratio Int) tag).run t = some ((q, r), c) ∧
      Rat.divInt q.n q.d = Rat.divInt n d ∧
      RatioMath.Canonical q.n q.d ∧ RatioMath.Canonical r.n r.d := by
  refine ⟨⟨n, d⟩, ⟨n + d, d⟩, t + 2,
    ratio_postfix_increment_run n d tag t, ?_, ?_, ?_⟩
  · rfl
  · exact h
  · exact RatioMath.increment_canonical n d h

theorem ratio_prefix_decrement_canonical_value (n d : Int)
    (h : RatioMath.Canonical n d) (t : Nat) :
    ∃ (q r : cp.Ratio Int) (c : Nat),
      (cp.Ratio.op_dec_0 (⟨n, d⟩ : cp.Ratio Int)).run t = some ((q, r), c) ∧
      Rat.divInt q.n q.d = Rat.divInt n d - 1 ∧
      RatioMath.Canonical q.n q.d ∧ RatioMath.Canonical r.n r.d := by
  refine ⟨⟨n - d, d⟩, ⟨n - d, d⟩, t + 1,
    ratio_prefix_decrement_run n d t, ?_, ?_, ?_⟩
  · exact RatioMath.decrement_value n d (Int.ne_of_gt h.1)
  · exact RatioMath.decrement_canonical n d h
  · exact RatioMath.decrement_canonical n d h

theorem ratio_postfix_decrement_canonical_value (n d : Int)
    (h : RatioMath.Canonical n d) (tag : Int) (t : Nat) :
    ∃ (q r : cp.Ratio Int) (c : Nat),
      (cp.Ratio.op_dec_int (⟨n, d⟩ : cp.Ratio Int) tag).run t = some ((q, r), c) ∧
      Rat.divInt q.n q.d = Rat.divInt n d ∧
      RatioMath.Canonical q.n q.d ∧ RatioMath.Canonical r.n r.d := by
  refine ⟨⟨n, d⟩, ⟨n - d, d⟩, t + 2,
    ratio_postfix_decrement_run n d tag t, ?_, ?_, ?_⟩
  · rfl
  · exact h
  · exact RatioMath.decrement_canonical n d h

theorem ratio_mul_assign_canonical_value [NumericCost] (n d m e : Int)
    (ha : RatioMath.Canonical n d) (hb : RatioMath.Canonical m e) (t : Nat) :
    ∃ (q : cp.Ratio Int) (c : Nat),
      (cp.Ratio.op_mul_assign (⟨n, d⟩ : cp.Ratio Int) (⟨m, e⟩ : cp.Ratio Int)).run t = some ((q, q), c) ∧
      Rat.divInt q.n q.d = Rat.divInt n d * Rat.divInt m e ∧
      RatioMath.Canonical q.n q.d := by
  let p := RatioMath.mul n d m e
  refine ⟨⟨p.1, p.2⟩, _, ratio_mul_assign_int_run n d m e t, ?_, ?_⟩
  · exact RatioMath.mul_value n d m e (Int.ne_of_gt ha.1) (Int.ne_of_gt hb.1)
  · exact RatioMath.mul_canonical n d m e ha hb
