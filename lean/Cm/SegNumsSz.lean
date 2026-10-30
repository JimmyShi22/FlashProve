-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegNumsSz.lean: tools for the model's sizes: how many atoms a family holds, how many sums, and
over how many further variables (`FamSz`).

Statements on data only, with their proofs.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean).

Why: If the terms of a family f name atoms below f.na, the number of masks of a sumcheck on the
family is bounded by the family's number of variables, degree and size
(Cm/ReqRefNeed.lean: sz f = its atoms + the atoms in all its terms); the sizes bound its numbers of
factor and product rows too (Cm/ReqRefNeed.lean: `opn_le`, `rel_le`). Where one vector under a code
holds masks, their number is a length of that code, and a code with all properties exists for
lengths in a range only. The tools here bound the sizes of one family at a time
(gluing puts atoms and terms side by side: Cm/ReqRefNeed.lean, Cm/ReqRefGlueS.lean).

Main names:
  `FamSz f a b c W`: sz f ≤ a; the sizes of the sums among its atoms together, sS f ≤ b; their
    number lS f ≤ c; none has more than W further variables (`WLe`).

The rules that compute sizes of compiled expressions are Cm/ReqRefEx.lean's.

Limits: no statement here is on a segment: this file states no bound on the sizes of the model's
segments. It says nothing on lookups' and the range check's own vectors. No number here is a
security level.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegNums
import Cm.ReqRefEx

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.All Finset Cm.Seg.Ex Cm.Ref

/-! ## 1. Tools -/

section Tools
variable {X E : Type} [Field E]

/-- the sizes of a family -/
structure FamSz (f : Fam X E) (a b c W : ℕ) : Prop where
  sz : Ref.sz f ≤ a
  sS : Ref.sS f ≤ b
  lS : Ref.lS f ≤ c
  w : WLe f W

theorem FamSz.of {f : Fam X E} {a b c W a' b' c' W' : ℕ} (h : FamSz f a b c W) (h1 : a ≤ a')
    (h2 : b ≤ b') (h3 : c ≤ c') (h4 : W ≤ W') : FamSz f a' b' c' W' :=
  ⟨le_trans h.sz h1, le_trans h.sS h2, le_trans h.lS h3, fun x hx => le_trans (h.w x hx) h4⟩

/-- no sum atom of the expression has more than W further variables -/
abbrev WL (W : ℕ) (p : Ex1 X E) : Prop := Ex.All (fun a => ∀ b, asSum a = some b → b.1 ≤ W) p

theorem WL.aff (W : ℕ) (f : ℕ → CForm E) : WL (X := X) W (aff f) := All.one fun _ e => by cases e
theorem WL.idx (W : ℕ) (a : IdxAtom E) : WL (X := X) W (Seg.idx a) := All.one fun _ e => by cases e
theorem WL.sumA {W w : ℕ} (v : ℕ) (q : Ex0 X E) (h : w ≤ W) :
    WL W (sumA v w q) := All.one fun _ e => by
  cases e
  exact h

/-- the sizes of a compiled family, from four numbers of its expression -/
theorem famSz_ex {v a b c W : ℕ} {p : Ex1 X E} (h1 : 2 * fl p ≤ a) (h2 : wt ωS p ≤ b)
    (h3 : wt ωL p ≤ c) (h4 : WL W p) : FamSz (Ex1.fam v p) a b c W :=
  ⟨by rw [sz_fam]; exact h1, by rw [sS_fam]; exact h2, by rw [lS_fam]; exact h3, wLe_fam h4⟩

theorem famSz_aff (v : ℕ) (f : ℕ → CForm E) : FamSz (affFam (X := X) v f) 2 0 0 0 :=
  ⟨le_of_eq (sz_affFam v f), le_of_eq (sS_affFam v f), le_of_eq (lS_affFam v f), wLe_affFam v f 0⟩

theorem sum_le_len {α : Type} (l : List α) (u : α → ℕ) (B : ℕ) (h : ∀ a ∈ l, u a ≤ B) :
    (l.map u).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact Nat.add_le_add (ih fun x hx => h x (List.mem_cons_of_mem _ hx)) (h a List.mem_cons_self)

end Tools

/-! ## 2. The head -/

section Led
variable {X E : Type} [Field E]

theorem ws_inner_le (B : ℕ → ℕ → CForm E) (s : ℕ) :
    fl (Ex.pSum 5 fun l =>
          Ex.pSum 5 fun l' =>
            if l + l' = s then aff0 (B l) * aff0 (B l') else (Ex.zero : Ex0 X E)) ≤ 50 := by
  simp only [wt_pSum, wt_ite, wt_mul, fl_aff0, nm_aff0, wt_zero]
  calc ∑ l ∈ range 5, ∑ l' ∈ range 5, (if l + l' = s then 1 * 1 + 1 * 1 else 0) ≤ ∑ _l ∈ range 5, ∑ _l' ∈ range 5, 2 :=
        sum_le_sum fun _ _ => sum_le_sum fun _ _ => by split_ifs <;> norm_num
    _ = 50 := by simp

@[simp] theorem fl_rowEx (D : ℕ → ℕ → CForm E) (g : (ℕ → CForm E) → CForm E) :
    wt (fun _ => 1) (rowEx D g : Ex1 X E) = 1 := fl_aff _
@[simp] theorem nm_rowEx (D : ℕ → ℕ → CForm E) (g : (ℕ → CForm E) → CForm E) :
    nm (rowEx D g : Ex1 X E) = 1 := rfl
@[simp] theorem ωS_rowEx (D : ℕ → ℕ → CForm E) (g : (ℕ → CForm E) → CForm E) :
    wt ωS (rowEx D g : Ex1 X E) = 0 := ωS_aff _
@[simp] theorem ωL_rowEx (D : ℕ → ℕ → CForm E) (g : (ℕ → CForm E) → CForm E) :
    wt ωL (rowEx D g : Ex1 X E) = 0 := ωL_aff _
theorem WL.rowEx (W : ℕ) (D : ℕ → ℕ → CForm E) (g : (ℕ → CForm E) → CForm E) :
    WL (X := X) W (Seg.rowEx D g) := WL.aff W _

/-- the 17 identities of a ledger, with W_s as the sum atom of Cm/SegHeadLedger.lean -/
theorem famSz_led (np : NormPar) (v w : ℕ) (B : ℕ → ℕ → CForm E) (D : ℕ → ℕ → CForm E) (k : ℕ) :
    FamSz (Ex1.fam v (ledEx (X := X) np (wsEx v w B) D k)) 10 100 1 w := by
  have hw : ∀ s, wt ωS (wsEx (X := X) v w B s) ≤ 100 := fun s => by
    unfold wsEx
    rw [ωS_sumA]
    have := ws_inner_le (X := X) B s
    omega
  have r := fun g => WL.rowEx (X := X) w D g
  unfold ledEx
  split_ifs with hk
  · refine famSz_ex ?_ ?_ ?_ (All.add (WL.sumA _ _ (le_refl w)) (r _))
    · simp [wsEx]
    · rw [wt_add, ωS_rowEx, Nat.add_zero]
      exact hw k
    · simp [wsEx]
  · match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact absurd (by norm_num) hk
    | 9 => exact famSz_ex (by simp) (by simp) (by simp) (All.sub (All.mul (r _) (r _)) (r _))
    | 10 => exact famSz_ex (by simp) (by simp) (by simp) (All.sub (r _) (All.mul (r _) (r _)))
    | 11 => exact famSz_ex (by simp) (by simp) (by simp) (All.sub (r _) (All.mul (r _) (r _)))
    | 12 => exact famSz_ex (by simp) (by simp) (by simp) (r _)
    | 13 =>
      exact famSz_ex (by simp) (by simp) (by simp)
        (All.sub (All.add (All.mul (r _) (r _)) (All.mul (r _) (r _))) (r _))
    | 14 => exact famSz_ex (by simp) (by simp) (by simp) (All.mul (r _) (r _))
    | 15 =>
      exact famSz_ex (by simp) (by simp) (by simp)
        (All.sub (r _) (All.smul _ (All.mul (r _) (r _))))
    | 16 => exact famSz_ex (by simp) (by simp) (by simp) (r _)
    | _ + 17 => exact famSz_ex (by simp) (by simp) (by simp) All.zero

end Led

/-! ## 3. Feed-forward -/

section FF
variable [scl : Scl] {X : Type}

theorem sum_two (n : ℕ) : ((List.range n).map fun _ => 2).sum = 2 * n := by simp [Nat.mul_comm]

/-- a family in the quadratic normal form of Cm/SegFFCellKit.lean -/
theorem famSz_q {E : Type} [Field E] (S : QSpec X E) :
    FamSz S.fam (4 + 4 * S.nQ) (4 * S.nS) 1 S.w := by
  have hs : sumsN S.fam = [(S.w, S.inner)] := by
    show (List.range (2 + 2 * S.nQ)).filterMap (fun j => asSum (S.fam.atom j)) = _
    have h0 : asSum (S.fam.atom 0) = some (S.w, S.inner) := rfl
    rw [show 2 + 2 * S.nQ = (1 + 2 * S.nQ) + 1 by ring, List.range_succ_eq_map,
      List.filterMap_cons_some (f := fun j => asSum (S.fam.atom j)) h0]
    congr 1
    rw [List.filterMap_eq_nil_iff]
    intro j hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hj
    show asSum (if i + 1 = 0 then Atom.sum S.w S.inner
          else if i + 1 = 1 then .base (.cell S.a)
          else
            .base
              (.cell (if (i + 1) % 2 = 0 then S.f ((i + 1 - 2) / 2) else S.g ((i + 1 - 2) / 2)))) =
      none
    rw [if_neg (Nat.succ_ne_zero i)]
    split_ifs <;> rfl
  have hin : Ref.sz S.inner.toFam = 4 * S.nS := by
    show 2 * S.nS +
        tl (((List.range S.nS).map fun n => (⟨S.κ n, [2 * n, 2 * n + 1]⟩ : Term X E)).map
            Term.atoms) = _
    unfold tl
    rw [List.map_map, List.map_map,
      show ((List.length ∘ Term.atoms) ∘ fun n => (⟨S.κ n, [2 * n, 2 * n + 1]⟩ : Term X E)) =
        fun _ => 2 from rfl, sum_two]
    ring
  refine ⟨le_of_eq ?_, le_of_eq ?_, le_of_eq ?_, fun a ha => ?_⟩
  · show (2 + 2 * S.nQ) +
        tl (((⟨fun _ _ => 1, [0]⟩ : Term X E) :: ⟨fun _ _ => 1, [1]⟩ ::
              (List.range S.nQ).map fun n =>
                (⟨fun _ _ => 1, [2 * n + 2, 2 * n + 3]⟩ : Term X E)).map Term.atoms) = _
    unfold tl
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
      List.map_map, List.map_map,
      show ((List.length ∘ Term.atoms) ∘
          fun n => (⟨fun _ _ => 1, [2 * n + 2, 2 * n + 3]⟩ : Term X E)) =
        fun _ => 2 from rfl, sum_two]
    show 2 + 2 * S.nQ + (1 + (1 + 2 * S.nQ)) = _
    ring
  · unfold Ref.sS
    rw [hs]
    simp [hin]
  · unfold Ref.lS
    rw [hs]
    rfl
  · rw [hs, List.mem_singleton] at ha
    rw [ha]

theorem nm_cellsE {E : Type} [Field E] (vx w : ℕ) :
    ∀ fs : List (ℕ → ℕ → ℕ → ℕ → CForm E), nm (cellsE (X := X) vx w fs) = 1
  | [] => rfl
  | _ :: l => by rw [cellsE, nm_mul, nm_aff0, nm_cellsE vx w l]

theorem fl_cellsE {E : Type} [Field E] (vx w : ℕ) :
    ∀ fs : List (ℕ → ℕ → ℕ → ℕ → CForm E), fl (cellsE (X := X) vx w fs) = fs.length
  | [] => rfl
  | f :: l => by
    show wt (fun _ => 1) (aff0 (at4 vx w f) * cellsE vx w l) = _
    rw [wt_mul, fl_aff0, nm_aff0, nm_cellsE vx w l,
      show wt (fun _ => 1) (cellsE (X := X) vx w l) = l.length from fl_cellsE vx w l,
      List.length_cons]
    ring

section Blk
variable {E : Type} [Field E] (vx w n : ℕ) (c : ℕ → ℕ → ℕ → ℕ → ℕ → E)
  (fs : List (ℕ → ℕ → ℕ → ℕ → CForm E)) (ia : ℕ → IdxAtom E)

@[simp] theorem fl_blk : wt (fun _ => 1) (blk (X := X) vx w n c fs ia) = 1 := fl_sumA _ _ _
@[simp] theorem nm_blk : nm (blk (X := X) vx w n c fs ia) = 1 := rfl
@[simp] theorem ωL_blk : wt ωL (blk (X := X) vx w n c fs ia) = 1 := ωL_sumA _ _ _
@[simp] theorem ωS_blk : wt ωS (blk (X := X) vx w n c fs ia) = 2 * (n * (fs.length + 1)) := by
  unfold blk
  rw [ωS_sumA]
  simp only [wt_pSum, wt_sc, wt_mul, nm_cellsE, fl_idx0, nm_idx0,
    show ∀ l, wt (fun _ => 1) (cellsE (X := X) vx w l) = l.length from fl_cellsE vx w]
  simp
theorem WL.blk {W : ℕ} (h : w ≤ W) : WL W (Seg.blk (X := X) vx w n c fs ia) := WL.sumA _ _ h

end Blk

end FF

end Cm.Seg
