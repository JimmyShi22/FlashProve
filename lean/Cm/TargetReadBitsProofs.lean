-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetReadBitsProofs.lean: proofs for Cm/TargetReadBits.lean (separable atoms, their readings,
the calculus), and a guard.

That file's head has the definitions. Each of its statements is proved here under the same name.

Main names (statements and hypotheses: Cm/TargetReadBits.lean):
  `sep_read`: from at most n pieces to a reading with at most n items.
  `spiece_ext` (stated here): its main lemma, from `ofBits_ok`, `ofBits_vtx` (Cm/SegIdxProofs.lean).
  `sep_cell`: the base rule: one cell under gT, gU, 0 elsewhere.
  `sep_low`: d more variables in front: F read at b % 2^v.
  `sep_bits`: atoms given by bits (`BitAtom`, Cm/TargetRead.lean), a piece for a piece.
  `sep_guard` (stated here): a guard (lean/GLOSSARY.md): an atom on 3 variables (`sepGuardF`) that
    reads the row before (row t - 1 at t = 1; nothing at t = 0) at a column that is no bit pattern
    (5 - 2 u), with a constant, is separable with at most one piece in shapes of 2 rows and 6
    columns, by the base and the calculus; so it has a reading with at most one item.

Limits: what the head of Cm/TargetReadBits.lean lists as not said is not said here either. A place
whose row and column read the same variable is not taken in.
-/
import Cm.TargetReadBits
import Cm.TargetReadProofs
import Cm.SegIdxUnitProofs

set_option autoImplicit false

namespace Cm.TR

open Cb Blocks Finset Cm.Seg

variable {E : Type} [Field E]

/-- Under `hOK` (no variable is named twice in cs and rs together, and all are below v), the
multilinear extension of a separable piece at a point is its item's value. -/
theorem spiece_ext (P : SPiece E) (R C : ℕ → ℕ) (v : ℕ) (hOK : Src.OK (P.cs ++ P.rs) v)
    (A : ℕ → ℕ → ℕ → E) (γ : ℕ → E) :
    ext v (fun b => P.at R C v b A) γ = (sepItem P).val R C γ A := by
  have h1 := ofBits_ok E E (fmtT E (C P.seg) P.cs.length) v P.cs P.rs P.β rfl hOK
    (fun y c => ∑ r ∈ range (R P.seg), P.α c r * A P.seg r y) γ
  have h2 : ∀ b,
      (ofBits P.cs P.rs P.β).at (fmtT E (C P.seg) P.cs.length)
          (fun y c => ∑ r ∈ range (R P.seg), P.α c r * A P.seg r y) (vtx v b) =
        P.at R C v b A := fun b => by
    rw [ofBits_vtx E E (fmtT E (C P.seg) P.cs.length) v P.cs P.rs P.β rfl
        (fun y c => ∑ r ∈ range (R P.seg), P.α c r * A P.seg r y) b]
    show ∑ y ∈ range (C P.seg),
        P.β (Src.num P.rs v b) y * ∑ r ∈ range (R P.seg), P.α (Src.num P.cs v b) r * A P.seg r y =
      ∑ r ∈ range (R P.seg),
        ∑ y ∈ range (C P.seg), P.α (Src.num P.cs v b) r * P.β (Src.num P.rs v b) y * A P.seg r y
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun r _ => by ring
  rw [show (fun b => P.at R C v b A) =
        fun b =>
          (ofBits P.cs P.rs P.β).at (fmtT E (C P.seg) P.cs.length)
            (fun y c => ∑ r ∈ range (R P.seg), P.α c r * A P.seg r y) (vtx v b)
            from funext fun b => (h2 b).symm, h1]
  show ∑ y ∈ range (C P.seg), ∑ c ∈ range (2 ^ (P.cs.length + 0)),
      (∑ u ∈ range (2 ^ P.rs.length), eqN P.rs.length 0 (Src.pt P.rs γ) u * P.β u y) *
        eqN (P.cs.length + 0) 0 (Src.pt P.cs γ) c * (∑ r ∈ range (R P.seg), P.α c r * A P.seg r y) =
    ∑ r ∈ range (R P.seg), ∑ y ∈ range (C P.seg),
      (∑ t ∈ range (2 ^ P.cs.length), eqN P.cs.length 0 (Src.pt P.cs γ) t * P.α t r) *
        (∑ u ∈ range (2 ^ P.rs.length), eqN P.rs.length 0 (Src.pt P.rs γ) u * P.β u y) * A P.seg r y
  rw [Nat.add_zero, sum_comm (s := range (R P.seg))]
  refine sum_congr rfl fun y _ => ?_
  generalize (∑ u ∈ range (2 ^ P.rs.length), eqN P.rs.length 0 (Src.pt P.rs γ) u * P.β u y) = col
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun r _ => sum_congr rfl fun c _ => by ring

theorem sepAtom_read (B : SepAtom E) (R C : ℕ → ℕ) (v : ℕ) (f : ℕ → CForm E)
    (hIs : ∀ b < 2 ^ v, ∀ A, (f b).val A = B.at R C v b A) (hOK : B.OK v) :
    (B.reading v).Of R C v f := by
  intro A γ
  rw [ext_congr v (fun b hb => hIs b hb A)]
  unfold SepAtom.at
  rw [ext_add, ext_list_sum]
  show _ = ext v B.k γ + ((B.pieces.map sepItem).map fun t => t.val R C γ A).sum
  rw [List.map_map]
  congr 2
  exact List.map_congr_left fun P hP => spiece_ext P R C v (hOK P hP) A γ

theorem sep_read : Spec.sep_read := fun _ _ R C v _ f ⟨B, h1, h2, h3⟩ => ⟨B.reading v, sepAtom_read B R C v f h1 h2, by rw [show (B.reading v).items.length = (B.pieces.map sepItem).length from rfl, List.length_map]; exact h3⟩

/-! ## The calculus -/

theorem sep_congr : Spec.sep_congr := fun _ _ _ _ _ _ _ _ h ⟨B, h1, h2, h3⟩ =>
  ⟨B, fun b hb A => (h b hb A).trans (h1 b hb A), h2, h3⟩

theorem sep_mono : Spec.sep_mono := fun _ _ _ _ _ _ _ _ h ⟨B, h1, h2, h3⟩ =>
  ⟨B, h1, h2, le_trans h3 h⟩

theorem sep_const : Spec.sep_const := fun _ _ _ _ _ k =>
  ⟨⟨k, []⟩, fun _ _ _ => (add_zero _).symm, fun _ h => absurd h List.not_mem_nil, le_refl 0⟩

theorem sep_add : Spec.sep_add := by
  rintro E _ R C v n m F G ⟨B, h1, h2, h3⟩ ⟨B', g1, g2, g3⟩
  refine ⟨⟨fun b => B.k b + B'.k b, B.pieces ++ B'.pieces⟩, fun b hb A => ?_, fun P hP => ?_, ?_⟩
  · show F b A + G b A = _
    rw [h1 b hb A, g1 b hb A]
    unfold SepAtom.at
    rw [List.map_append, List.sum_append]
    ring
  · rcases List.mem_append.1 hP with h | h
    · exact h2 P h
    · exact g2 P h
  · rw [show (B.pieces ++ B'.pieces).length = B.pieces.length + B'.pieces.length
        from List.length_append]
    exact Nat.add_le_add h3 g3

theorem sep_smul : Spec.sep_smul := by
  rintro E _ R C v n c F ⟨B, h1, h2, h3⟩
  refine ⟨⟨fun b => c * B.k b, B.pieces.map fun P => { P with α := fun t r => c * P.α t r }⟩,
    fun b hb A => ?_, fun P hP => ?_, ?_⟩
  · show c * F b A = _
    rw [h1 b hb A]
    unfold SepAtom.at
    rw [mul_add, List.map_map, ← List.sum_map_mul_left]
    congr 2
    refine List.map_congr_left fun P _ => ?_
    show c * P.at R C v b A =
      ∑ r ∈ range (R P.seg),
        ∑ y ∈ range (C P.seg), c * P.α (Src.num P.cs v b) r * P.β (Src.num P.rs v b) y * A P.seg r y
    unfold SPiece.at
    rw [mul_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun y _ => by ring
  · obtain ⟨P0, h0, rfl⟩ := List.mem_map.1 hP
    exact h2 P0 h0
  · rw [show (B.pieces.map fun P => ({ P with α := fun t r => c * P.α t r } : SPiece E)).length =
          B.pieces.length from List.length_map _]
    exact h3

theorem sep_sub : Spec.sep_sub := fun E _ R C v n m F G hF hG =>
  sep_congr E R C v (n + m) _ (fun b A => F b A + (-1) * G b A) (fun _ _ _ => by ring)
    (sep_add E R C v n m F _ hF (sep_smul E R C v m (-1) G hG))

theorem sep_sum : Spec.sep_sum := by
  intro E _ R C v n m F
  induction m with
  | zero =>
    intro _
    exact sep_congr E R C v _ _ (fun _ _ => 0) (fun _ _ _ => rfl)
      (sep_mono E R C v 0 _ _ (Nat.zero_le _) (sep_const E R C v fun _ => 0))
  | succ m ih =>
    intro h
    refine sep_congr E R C v _ _ (fun b A => (∑ k ∈ range m, F k b A) + F m b A)
      (fun _ _ _ => sum_range_succ _ _) ?_
    rw [Nat.succ_mul]
    exact sep_add E R C v (m * n) n _ _
      (ih fun k hk => h k (Nat.lt_succ_of_lt hk)) (h m (Nat.lt_succ_self m))

theorem list_range_sum (Q : ℕ) (f : ℕ → E) : ((List.range Q).map f).sum = ∑ j ∈ range Q, f j := by
  induction Q with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ,
      List.map_singleton, List.sum_singleton]

/-- The base (`Spec.sep_cell`), with premises at all numbers t, u, not only at those that the
sources can form. -/
theorem sep_cell0 (E : Type) [Field E] (R C : ℕ → ℕ) (v seg Q : ℕ) (cs rs : List Src)
    (gT gU : ℕ → Prop) [DecidablePred gT] [DecidablePred gU] (c : ℕ → E) (q : ℕ → ℕ) (ρ : ℕ → ℕ → ℕ)
    (κ : ℕ → ℕ) (hOK : Src.OK (cs ++ rs) v) (hq : ∀ u, gU u → q u < Q)
    (hs : ∀ t u, gT t → gU u → ρ t (q u) < R seg ∧ κ u < C seg) :
    SepV R C v Q fun b A =>
      if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
        c (Src.num rs v b) * A seg (ρ (Src.num cs v b) (q (Src.num rs v b))) (κ (Src.num rs v b))
      else 0 := by
  refine ⟨⟨fun _ => 0,
      (List.range Q).map fun j =>
        ⟨seg, cs, rs, fun t r => if gT t ∧ r = ρ t j then 1 else 0,
          fun u y => if gU u ∧ q u = j ∧ y = κ u then c u else 0⟩⟩,
    fun b _ A => ?_, fun P hP => ?_, ?_⟩
  · unfold SepAtom.at
    rw [zero_add, List.map_map, list_range_sum]
    show (if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
          c (Src.num rs v b) * A seg (ρ (Src.num cs v b) (q (Src.num rs v b))) (κ (Src.num rs v b))
        else 0) =
      ∑ j ∈ range Q, ∑ r ∈ range (R seg), ∑ y ∈ range (C seg),
        (if gT (Src.num cs v b) ∧ r = ρ (Src.num cs v b) j then (1 : E) else 0) *
          (if gU (Src.num rs v b) ∧ q (Src.num rs v b) = j ∧ y = κ (Src.num rs v b) then
              c (Src.num rs v b)
            else 0) * A seg r y
    generalize Src.num cs v b = t
    generalize Src.num rs v b = u
    by_cases hg : gT t ∧ gU u
    · rw [if_pos hg, sum_eq_single (q u), sum_eq_single (ρ t (q u)), sum_eq_single (κ u)]
      · rw [if_pos ⟨hg.1, rfl⟩, if_pos ⟨hg.2, rfl, rfl⟩, one_mul]
      · intro y _ hy
        rw [if_neg (fun h : gU u ∧ q u = q u ∧ y = κ u => hy h.2.2), mul_zero, zero_mul]
      · intro h
        exact absurd (mem_range.2 (hs t u hg.1 hg.2).2) h
      · intro r _ hr
        exact sum_eq_zero fun y _ => by rw [if_neg (fun h => hr h.2), zero_mul, zero_mul]
      · intro h
        exact absurd (mem_range.2 (hs t u hg.1 hg.2).1) h
      · intro j _ hj
        exact sum_eq_zero fun r _ =>
          sum_eq_zero fun y _ => by
            rw [if_neg (fun h : gU u ∧ q u = j ∧ y = κ u => hj h.2.1.symm), mul_zero, zero_mul]
      · intro h
        exact absurd (mem_range.2 (hq u hg.2)) h
    · rw [if_neg hg]
      refine (sum_eq_zero fun j _ => sum_eq_zero fun r _ => sum_eq_zero fun y _ => ?_).symm
      by_cases h1 : gT t
      · rw [if_neg (fun h : gU u ∧ q u = j ∧ y = κ u => hg ⟨h1, h.1⟩), mul_zero, zero_mul]
      · rw [if_neg (fun h : gT t ∧ r = ρ t j => h1 h.1), zero_mul, zero_mul]
  · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hP
    exact hOK
  · rw [show ((List.range Q).map fun j =>
          (⟨seg, cs, rs, fun t r => if gT t ∧ r = ρ t j then 1 else 0,
            fun u y => if gU u ∧ q u = j ∧ y = κ u then c u else 0⟩ : SPiece E)).length =
        Q by rw [List.length_map, List.length_range]]

theorem sep_cell : Spec.sep_cell := by
  intro E _ R C v seg Q cs rs gT gU _ _ c q ρ κ hOK hq hs
  refine sep_congr E R C v Q _ _ (fun b _ A => ?_)
    (sep_cell0 E R C v seg Q cs rs (fun t => t < 2 ^ cs.length ∧ gT t)
      (fun u => u < 2 ^ rs.length ∧ gU u) c q ρ κ hOK (fun u hu => hq u hu.1 hu.2)
      fun t u ht hu => hs t ht.1 u hu.1 ht.2 hu.2)
  have h1 := num_lt cs v b
  have h2 := num_lt rs v b
  show (if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then _ else 0) =
    if (Src.num cs v b < 2 ^ cs.length ∧ gT (Src.num cs v b)) ∧
        (Src.num rs v b < 2 ^ rs.length ∧ gU (Src.num rs v b)) then _
    else 0
  by_cases hg : gT (Src.num cs v b) ∧ gU (Src.num rs v b)
  · rw [if_pos hg, if_pos ⟨⟨h1, hg.1⟩, h2, hg.2⟩]
  · rw [if_neg hg, if_neg fun h => hg ⟨h.1.2, h.2.2⟩]

/-! ## More variables in front -/

theorem up_bitAt (d v b : ℕ) (s : Src) : (s.up d).bitAt (d + v) b = s.bitAt v (b % 2 ^ v) := by
  have key : ∀ u, (decide (d + u < d + v) && b.testBit (d + v - 1 - (d + u))) =
      (decide (u < v) && (b % 2 ^ v).testBit (v - 1 - u)) := fun u => by
    by_cases hu : u < v
    · rw [decide_eq_true (show d + u < d + v by omega), decide_eq_true hu, Bool.true_and,
        Bool.true_and, Nat.testBit_mod_two_pow, decide_eq_true (show v - 1 - u < v by omega),
        Bool.true_and, show d + v - 1 - (d + u) = v - 1 - u by omega]
    · rw [decide_eq_false (show ¬ d + u < d + v by omega), decide_eq_false hu,
        Bool.false_and, Bool.false_and]
  cases s with
  | var u => exact key u
  | nvar u => exact congrArg (!·) (key u)
  | bit _ => rfl

theorem up_num (d v b : ℕ) (l : List Src) :
    Src.num (l.map (Src.up d)) (d + v) b = Src.num l v (b % 2 ^ v) := by
  unfold Src.num
  rw [List.map_map]
  exact congrArg numL (List.map_congr_left fun s _ => up_bitAt d v b s)

theorem up_vars (d : ℕ) : ∀ l : List Src, Src.vars (l.map (Src.up d)) = (Src.vars l).map (d + ·)
  | [] => rfl
  | .var _ :: l => congrArg (List.cons _) (up_vars d l)
  | .nvar _ :: l => congrArg (List.cons _) (up_vars d l)
  | .bit _ :: l => up_vars d l

theorem up_ok (d v : ℕ) (l : List Src) (h : Src.OK l v) : Src.OK (l.map (Src.up d)) (d + v) := by
  unfold Src.OK
  rw [up_vars]
  refine ⟨h.1.map fun _ _ e => Nat.add_left_cancel e, fun u hu => ?_⟩
  obtain ⟨u0, h0, rfl⟩ := List.mem_map.1 hu
  exact Nat.add_lt_add_left (h.2 u0 h0) d

theorem sep_low : Spec.sep_low := by
  rintro E _ R C v d n F ⟨B, h1, h2, h3⟩
  refine ⟨⟨fun b => B.k (b % 2 ^ v),
      B.pieces.map fun P => { P with cs := P.cs.map (Src.up d), rs := P.rs.map (Src.up d) }⟩,
    fun b _ A => ?_, fun P hP => ?_, ?_⟩
  · show F (b % 2 ^ v) A = _
    rw [h1 (b % 2 ^ v) (Nat.mod_lt _ (Nat.two_pow_pos v)) A]
    unfold SepAtom.at
    rw [List.map_map]
    congr 2
    refine List.map_congr_left fun P _ => ?_
    show P.at R C v (b % 2 ^ v) A =
      ∑ r ∈ range (R P.seg), ∑ y ∈ range (C P.seg),
        P.α (Src.num (P.cs.map (Src.up d)) (d + v) b) r *
          P.β (Src.num (P.rs.map (Src.up d)) (d + v) b) y * A P.seg r y
    rw [up_num, up_num]
    rfl
  · obtain ⟨P0, h0, rfl⟩ := List.mem_map.1 hP
    show Src.OK (P0.cs.map (Src.up d) ++ P0.rs.map (Src.up d)) (d + v)
    rw [← List.map_append]
    exact up_ok d v _ (h2 P0 h0)
  · rw [show (B.pieces.map fun P =>
            ({ P with cs := P.cs.map (Src.up d), rs := P.rs.map (Src.up d) } : SPiece E)).length =
          B.pieces.length from List.length_map _]
    exact h3

/-! ## Atoms given by bits -/

theorem sep_bits : Spec.sep_bits := by
  intro E _ R C v f B hIs hOK
  refine ⟨⟨B.k,
      B.pieces.map fun P => ⟨P.seg, P.cs, P.rs, fun t r => if r = P.R0 + t then 1 else 0, P.T⟩⟩,
    fun b hb A => ?_, fun P hP => ?_, ?_⟩
  · show (f b).val A = _
    rw [hIs b hb A]
    unfold SepAtom.at
    rw [List.map_map]
    congr 2
    refine List.map_congr_left fun P hP => ?_
    show P.at C v b A =
      ∑ r ∈ range (R P.seg), ∑ y ∈ range (C P.seg),
        (if r = P.R0 + Src.num P.cs v b then (1 : E) else 0) *
          P.T (Src.num P.rs v b) y * A P.seg r y
    have hr : P.R0 + Src.num P.cs v b < R P.seg :=
      lt_of_lt_of_le (Nat.add_lt_add_left (num_lt P.cs v b) _) (hOK P hP).2
    rw [sum_eq_single (P.R0 + Src.num P.cs v b)]
    · exact sum_congr rfl fun y _ => by rw [if_pos rfl, one_mul]
    · intro r _ hne
      exact sum_eq_zero fun y _ => by rw [if_neg hne, zero_mul, zero_mul]
    · intro h
      exact absurd (mem_range.2 hr) h
  · obtain ⟨P0, h0, rfl⟩ := List.mem_map.1 hP
    exact (hOK P0 h0).1
  · rw [show (B.pieces.map fun P =>
            (⟨P.seg, P.cs, P.rs, fun t r => if r = P.R0 + t then 1 else 0,
              P.T⟩ : SPiece E)).length = B.pieces.length from List.length_map _]

/-! ## A guard -/

/-- An atom on 3 variables: variable 2 is the row bit t, variable 1 the column bit u, variable 0 is
read by nobody. Its form is the constant 7, and at t = 1 also 3 times the cell of segment 0 in the
row before (t - 1) at the column 5 - 2 u. -/
def sepGuardF (E : Type) [Field E] (b : ℕ) : CForm E :=
  if Src.num [.var 2] 3 b = 1 then
    ⟨7, [(3, (0, Src.num [.var 2] 3 b - 1, 5 - 2 * Src.num [.var 1] 3 b))]⟩
  else ⟨7, []⟩

theorem sep_guard (E : Type) [Field E] :
    Sep (fun _ => 2) (fun _ => 6) 3 1 (sepGuardF E) ∧
    ∃ ρ : LdPartRg E, ρ.Of (fun _ => 2) (fun _ => 6) 3 (sepGuardF E) ∧ ρ.items.length ≤ 1 := by
  have h : Sep (fun _ => 2) (fun _ => 6) 3 1 (sepGuardF E) := by
    refine sep_congr E _ _ 3 1 _
      (fun b A =>
        7 + (if Src.num [.var 2] 3 b = 1 ∧ True then
              (3 : E) * A 0 (Src.num [.var 2] 3 b - 1) (5 - 2 * Src.num [.var 1] 3 b)
            else 0))
      (fun b _ A => ?_)
      (sep_add E _ _ 3 0 1 _ _ (sep_const E _ _ 3 fun _ => 7)
        (sep_cell E (fun _ => 2) (fun _ => 6) 3 0 1 [.var 2] [.var 1] (fun t => t = 1)
          (fun _ => True) (fun _ => 3) (fun _ => 0) (fun t _ => t - 1) (fun u => 5 - 2 * u)
          ⟨by simp [Src.vars], by simp [Src.vars]⟩ (fun _ _ _ => Nat.one_pos)
          (fun t _ u _ ht _ =>
            ⟨(by show t - 1 < 2; have : t = 1 := ht; omega), (by show 5 - 2 * u < 6; omega)⟩)))
    show (sepGuardF E b).val A =
      7 + (if Src.num [.var 2] 3 b = 1 ∧ True then
            (3 : E) * A 0 (Src.num [.var 2] 3 b - 1) (5 - 2 * Src.num [.var 1] 3 b)
          else 0)
    unfold sepGuardF
    by_cases ht : Src.num [.var 2] 3 b = 1
    · rw [if_pos ht, if_pos ⟨ht, trivial⟩]
      simp [CForm.val]
    · rw [if_neg ht, if_neg (fun h => ht h.1)]
      simp [CForm.val]
  exact ⟨h, sep_read E _ _ 3 1 _ h⟩

end Cm.TR
