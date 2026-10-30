-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetReadProofs.lean: the statements of Cm/TargetRead.lean, proved; and a guard.

That file's head has the definitions (readings, items, pieces and atoms given by bits). Its two
statements are proved here under the same names.

Main names:
  `guard_two_parts`: a guard of `read_bits`: an atom on 3 variables, of which one is named by no
    source, with two parts (first rows 0 and 2), a first column that is not 0, coefficients 1 and
    256 and a constant: it is a `BitAtom` with OK, so it has a reading with two items, in shapes of
    4 rows and 7 columns.

Limits: what the head of Cm/TargetRead.lean lists as not said is not said here either. That is: that
the model's atoms are BitAtoms; that reads are shared; whose matrices are read; anything on
protocols, errors or cost.

Terms: lean/GLOSSARY.md.
-/
import Cm.TargetRead
import Cm.SegIdxProofs
import Cm.SegFFCellKit

set_option autoImplicit false

namespace Cm.TR

open Cb Blocks Finset Cm.Seg

variable {E : Type} [Field E]

theorem ext_add (v : ℕ) (f g : ℕ → E) (γ : ℕ → E) :
    ext v (fun b => f b + g b) γ = ext v f γ + ext v g γ := by
  unfold Blocks.ext
  rw [← sum_add_distrib]
  exact sum_congr rfl fun b _ => mul_add _ _ _

theorem ext_congr (v : ℕ) {f g : ℕ → E} (h : ∀ b < 2 ^ v, f b = g b) (γ : ℕ → E) :
    ext v f γ = ext v g γ :=
  sum_congr rfl fun b hb => by rw [h b (mem_range.1 hb)]

theorem ext_list_sum {α : Type} (v : ℕ) (l : List α) (f : α → ℕ → E) (γ : ℕ → E) :
    ext v (fun b => (l.map fun a => f a b).sum) γ = (l.map fun a => ext v (f a) γ).sum := by
  induction l with
  | nil => simp [Blocks.ext]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ext_add, ih]

/-- One term in the shapes. -/
theorem sum_single (n : ℕ) (R C : ℕ → ℕ) (A : ℕ → ℕ → ℕ → E) (w : E) (q : Cb.Place)
    (h : q.1 < n ∧ q.2.1 < R q.1 ∧ q.2.2 < C q.1) :
    ∑ s ∈ range n,
        ∑ c ∈ range (C s), ∑ r ∈ range (R s), (if q = (s, r, c) then w else 0) * A s r c =
      w * A q.1 q.2.1 q.2.2 := by
  obtain ⟨q1, q2, q3⟩ := q
  obtain ⟨h1, h2, h3⟩ := h
  rw [sum_eq_single q1, sum_eq_single q3, sum_eq_single q2]
  · rw [if_pos rfl]
  · intro r _ hr
    rw [if_neg (fun e => hr (by simpa using (congrArg (fun z : Cb.Place => z.2.1) e).symm)),
      zero_mul]
  · intro hr
    exact absurd (mem_range.2 h2) hr
  · intro c _ hc
    refine sum_eq_zero fun r _ => ?_
    rw [if_neg (fun e => hc (by simpa using (congrArg (fun z : Cb.Place => z.2.2) e).symm)),
      zero_mul]
  · intro hc
    exact absurd (mem_range.2 h3) hc
  · intro s _ hs
    refine sum_eq_zero fun c _ => sum_eq_zero fun r _ => ?_
    rw [if_neg (fun e => hs (by simpa using (congrArg (fun z : Cb.Place => z.1) e).symm)), zero_mul]
  · intro hs
    exact absurd (mem_range.2 h1) hs

theorem sum_coefAt (n : ℕ) (R C : ℕ → ℕ) (A : ℕ → ℕ → ℕ → E) :
    ∀ (l : List (E × Cb.Place)), (∀ t ∈ l, t.2.1 < n ∧ t.2.2.1 < R t.2.1 ∧ t.2.2.2 < C t.2.1) →
      ∑ s ∈ range n, ∑ c ∈ range (C s),
          ∑ r ∈ range (R s), (l.map fun t => if t.2 = (s, r, c) then t.1 else 0).sum * A s r c =
        (l.map fun t => t.1 * A t.2.1 t.2.2.1 t.2.2.2).sum
  | [], _ => by simp
  | t :: l, h => by
    simp only [List.map_cons, List.sum_cons, add_mul, sum_add_distrib]
    rw [sum_single n R C A t.1 t.2 (h t (List.mem_cons_self ..)),
      sum_coefAt n R C A l fun t' ht' => h t' (List.mem_cons_of_mem _ ht')]

theorem sum_map_flatMap {α β : Type} (l : List α) (g : α → List β) (h : β → E) :
    ((l.flatMap g).map h).sum = (l.map fun a => ((g a).map h).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

/-- A sum over the rows of a block. -/
theorem sum_block (Rn R0 N : ℕ) (h : R0 + N ≤ Rn) (G : ℕ → E) :
    ∑ r ∈ range Rn, (if R0 ≤ r ∧ r < R0 + N then G r else 0) = ∑ c ∈ range N, G (R0 + c) := by
  rw [← sum_filter]
  have hf : (range Rn).filter (fun r => R0 ≤ r ∧ r < R0 + N) = Ico R0 (R0 + N) := by
    ext r
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hf, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

theorem read_byCol : Spec.read_byCol := by
  intro E _ n R C v f hf A γ
  have hval : ∀ b < 2 ^ v, (f b).val A =
      (f b).c0 +
        ∑ s ∈ range n,
          ∑ c ∈ range (C s), ∑ r ∈ range (R s), coefAt (f b) (s, r, c) * A s r c := fun b hb => by
    unfold CForm.val coefAt
    rw [sum_coefAt n R C A (f b).terms (hf b hb)]
  rw [ext_congr v hval, ext_add]
  congr 1
  show _ = (((List.range n).flatMap fun s =>
        (List.range (C s)).map fun c =>
          (⟨s, fun γ r => ext v (fun b => coefAt (f b) (s, r, c)) γ,
            fun _ c' => if c' = c then 1 else 0⟩ : Item E)).map
      fun t => t.val R C γ A).sum
  rw [sum_map_flatMap, sum_map_range]
  unfold Blocks.ext
  rw [show (∑ X ∈ range (2 ^ v), eqN v 0 γ X *
      ∑ s ∈ range n, ∑ c ∈ range (C s), ∑ r ∈ range (R s), coefAt (f X) (s, r, c) * A s r c)
      = ∑ s ∈ range n, ∑ X ∈ range (2 ^ v),
        eqN v 0 γ X * ∑ c ∈ range (C s), ∑ r ∈ range (R s), coefAt (f X) (s, r, c) * A s r c by
    rw [sum_comm]
    exact sum_congr rfl fun X _ => mul_sum _ _ _]
  refine sum_congr rfl fun s _ => ?_
  rw [List.map_map, sum_map_range]
  rw [show (∑ X ∈ range (2 ^ v),
      eqN v 0 γ X * ∑ c ∈ range (C s), ∑ r ∈ range (R s), coefAt (f X) (s, r, c) * A s r c)
      = ∑ c ∈ range (C s),
        ∑ X ∈ range (2 ^ v), eqN v 0 γ X * ∑ r ∈ range (R s), coefAt (f X) (s, r, c) * A s r c by
    rw [sum_comm]
    exact sum_congr rfl fun X _ => mul_sum _ _ _]
  refine sum_congr rfl fun c hc => ?_
  show _ = ∑ r ∈ range (R s), ∑ c' ∈ range (C s),
      (∑ X ∈ range (2 ^ v), eqN v 0 γ X * coefAt (f X) (s, r, c)) *
        (if c' = c then 1 else 0) * A s r c'
  rw [show (∑ X ∈ range (2 ^ v), eqN v 0 γ X * ∑ r ∈ range (R s), coefAt (f X) (s, r, c) * A s r c)
      = ∑ r ∈ range (R s), ∑ X ∈ range (2 ^ v), eqN v 0 γ X * (coefAt (f X) (s, r, c) * A s r c) by
    rw [sum_comm]
    exact sum_congr rfl fun X _ => mul_sum _ _ _]
  refine sum_congr rfl fun r _ => ?_
  have hr : ∑ c' ∈ range (C s), (∑ X ∈ range (2 ^ v), eqN v 0 γ X * coefAt (f X) (s, r, c)) *
        (if c' = c then 1 else 0) * A s r c' =
      (∑ X ∈ range (2 ^ v), eqN v 0 γ X * coefAt (f X) (s, r, c)) * A s r c := by
    rw [sum_eq_single c]
    · rw [if_pos rfl, mul_one]
    · intro c' _ hc'
      rw [if_neg hc', mul_zero, zero_mul]
    · intro h
      exact absurd hc h
  rw [hr, sum_mul]
  exact sum_congr rfl fun X _ => (mul_assoc _ _ _).symm

/-- A format for the transposed block: as many "rows" as the segment has columns, as many "column
bits" as the block has row bits; its code is not read. -/
def fmtT (E : Type) [Field E] (h τ : ℕ) : IdxFmt E := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩, h, τ, 0⟩

/-- Under `hOK` (no variable is named twice in cs and rs together, and all are below v) and `hR`
(the block of rows lies in the segment's matrix), the multilinear extension of a piece at a point is
its item's value. -/
theorem piece_ext (P : Piece E) (R C : ℕ → ℕ) (v : ℕ) (hOK : Src.OK (P.cs ++ P.rs) v)
    (hR : P.R0 + 2 ^ P.cs.length ≤ R P.seg) (A : ℕ → ℕ → ℕ → E) (γ : ℕ → E) :
    ext v (fun b => P.at C v b A) γ = (bitItem P).val R C γ A := by
  have h1 := ofBits_ok E E (fmtT E (C P.seg) P.cs.length) v P.cs P.rs P.T rfl hOK
    (fun y c => A P.seg (P.R0 + c) y) γ
  have h2 : ∀ b,
      (ofBits P.cs P.rs P.T).at (fmtT E (C P.seg) P.cs.length)
          (fun y c => A P.seg (P.R0 + c) y) (vtx v b) =
        P.at C v b A := fun b =>
    ofBits_vtx E E (fmtT E (C P.seg) P.cs.length) v P.cs P.rs P.T rfl
      (fun y c => A P.seg (P.R0 + c) y) b
  rw [show (fun b => P.at C v b A) =
        fun b =>
          (ofBits P.cs P.rs P.T).at (fmtT E (C P.seg) P.cs.length)
            (fun y c => A P.seg (P.R0 + c) y) (vtx v b) from funext fun b => (h2 b).symm, h1]
  show ∑ y ∈ range (C P.seg), ∑ c ∈ range (2 ^ (P.cs.length + 0)),
      (∑ u ∈ range (2 ^ P.rs.length), eqN P.rs.length 0 (Src.pt P.rs γ) u * P.T u y) *
        eqN (P.cs.length + 0) 0 (Src.pt P.cs γ) c * A P.seg (P.R0 + c) y =
    ∑ r ∈ range (R P.seg), ∑ y ∈ range (C P.seg),
      (if P.R0 ≤ r ∧ r < P.R0 + 2 ^ P.cs.length then eqN P.cs.length 0 (Src.pt P.cs γ) (r - P.R0)
          else 0) *
        (∑ u ∈ range (2 ^ P.rs.length), eqN P.rs.length 0 (Src.pt P.rs γ) u * P.T u y) * A P.seg r y
  rw [sum_comm, Nat.add_zero]
  have e : ∀ r,
      (∑ y ∈ range (C P.seg),
          (if P.R0 ≤ r ∧ r < P.R0 + 2 ^ P.cs.length then
                eqN P.cs.length 0 (Src.pt P.cs γ) (r - P.R0)
              else 0) *
            (∑ u ∈ range (2 ^ P.rs.length), eqN P.rs.length 0 (Src.pt P.rs γ) u * P.T u y) *
            A P.seg r y) =
        if P.R0 ≤ r ∧ r < P.R0 + 2 ^ P.cs.length then
          ∑ y ∈ range (C P.seg), eqN P.cs.length 0 (Src.pt P.cs γ) (r - P.R0) *
            (∑ u ∈ range (2 ^ P.rs.length), eqN P.rs.length 0 (Src.pt P.rs γ) u * P.T u y) *
            A P.seg r y
        else 0 := fun r => by
    split_ifs
    · rfl
    · exact sum_eq_zero fun y _ => by rw [zero_mul, zero_mul]
  rw [sum_congr rfl fun r _ => e r, sum_block _ _ _ hR]
  refine sum_congr rfl fun c _ => sum_congr rfl fun y _ => ?_
  rw [Nat.add_sub_cancel_left]
  ring

theorem read_bits : Spec.read_bits := by
  intro E _ R C v f B hIs hOK A γ
  rw [ext_congr v (fun b hb => hIs b hb A), ext_add, ext_list_sum]
  show _ = ext v B.k γ + ((B.pieces.map bitItem).map fun t => t.val R C γ A).sum
  rw [List.map_map]
  congr 2
  exact List.map_congr_left fun P hP => piece_ext P R C v (hOK P hP).1 (hOK P hP).2 A γ

/-! ## A guard -/

/-- An atom on 3 variables; variable 0 is read by nobody; variable 2 is the row bit, variable 1 the
column bit; two parts (first rows 0 and 2), first column 5. -/
def guardF (E : Type) [Field E] (b : ℕ) : CForm E :=
  ⟨7, [(1, (0, 0 + Src.num [.var 2] 3 b, 5 + Src.num [.var 1] 3 b)),
      (256, (0, 2 + Src.num [.var 2] 3 b, 5 + Src.num [.var 1] 3 b))]⟩

def guardB (E : Type) [Field E] : BitAtom E :=
  ⟨fun _ => 7,
    [⟨0, 0, [.var 2], [.var 1], fun u y => if y = 5 + u then 1 else 0⟩,
      ⟨0, 2, [.var 2], [.var 1], fun u y => if y = 5 + u then 256 else 0⟩]⟩

theorem guard_num_lt (s : Src) (v b : ℕ) : Src.num [s] v b < 2 := by
  unfold Src.num numL
  simp only [List.map_cons, List.map_nil, numL, List.length_nil, pow_zero, add_zero]
  split_ifs <;> norm_num

theorem guard_two_parts (E : Type) [Field E] :
    (guardB E).Is (fun _ => 7) 3 (guardF E) ∧
    (guardB E).OK (fun _ => 4) 3 ∧
    ((guardB E).reading 3).Of (fun _ => 4) (fun _ => 7) 3 (guardF E) ∧
    ((guardB E).reading 3).items.length = 2 := by
  have h1 : (guardB E).Is (fun _ => 7) 3 (guardF E) := by
    intro b _ A
    have hu := guard_num_lt (.var 1) 3 b
    have hs : ∀ (c : E) (r : ℕ), ∑ y ∈ range 7,
          (if y = 5 + Src.num [.var 1] 3 b then c else 0) * A 0 r y =
        c * A 0 r (5 + Src.num [.var 1] 3 b) := fun c r => by
      rw [sum_eq_single (5 + Src.num [.var 1] 3 b)]
      · rw [if_pos rfl]
      · intro y _ hy
        rw [if_neg hy, zero_mul]
      · intro h
        exact absurd (mem_range.2 (by omega)) h
    simp only [guardF, guardB, CForm.val, Piece.at, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hs]
  have h2 : (guardB E).OK (fun _ => 4) 3 := by
    intro P hP
    simp only [guardB, List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl <;> exact ⟨⟨by simp [Src.vars], by simp [Src.vars]⟩, by norm_num⟩
  exact ⟨h1, h2, read_bits E _ _ 3 _ _ h1 h2, rfl⟩

end Cm.TR
