-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegNums.lean: tools for the model's numbers: degrees of expressions and of the families of the
model's conditions, on which the errors of the preamble of a request depend.

Statements on data only (no game, no protocol), with their proofs.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean).

What is counted (Cb/Req/ReqNumsGlue.lean). `Fam.DegLe f d`: no term of the family f, and no term
under a sum atom of f, has more than d atoms (a round of a sumcheck costs d + 1 of |E|). f.v ≤ V:
the number of variables (a zerocheck costs v of |E|). `SegSpec.NumsLe S d V`: both, for all
families of the segment S.

The figures, by kind of segment: Cm/TargetPartNumSeg.lean.

Main names:
  `d1_rowEx`, `d1_wsEx`, `d1_ledEx`, `qspec_degLe`, `dg_cellsE`, `d1_blk`: degrees of the
    expressions of the head and of the feed-forward segment. `vx_le`: a family's index has at most
    14 bits.
  `NumsLe.of`: `SegSpec.NumsLe` from bounds on its two numbers.

Notation: `Ex X E α` (Cm/SegHeadExp.lean): a type: an expression: a sum of monomials; `Ex1 X E`
(Cm/SegHeadExp.lean): := `Ex X E (Atom X E)`: expressions in atoms of all three kinds; `Dg n p`
(Cm/SegNumsExp.lean; n: a natural number, p: `Ex X E α`): a proposition: no monomial has more than
n atoms; `D1 n p` (Cm/SegNumsExp.lean; p: `Ex1 X E`): a proposition: no term has more than n atoms,
in the expression and under its sum atoms.

Limits: no number here is a security level. This file says nothing on the lookups' own errors, the
range check, fold, switch or codes. The numbers of further variables of the sum atoms (up to 31, in
the head) enter no error, only the number of rounds; they are not stated here.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegNumsExp
import Cm.ReqModel
import Cm.SegAttOK
import Cb.Gen.ParLists

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.All Finset Cm.Seg.Ex
open scoped ENNReal

/-! ## 1. The head -/

section Led
variable {X E : Type} [Field E]

theorem d1_rowEx (D : ℕ → ℕ → CForm E) (g : (ℕ → CForm E) → CForm E) : D1 (X := X) 1 (rowEx D g) :=
  D1.aff _

theorem d1_wsEx (v w : ℕ) (B : ℕ → ℕ → CForm E) (s : ℕ) : D1 (X := X) 2 (wsEx v w B s) := by
  unfold wsEx
  exact (D1.sumA _ _
      (Dg.pSum fun _ _ =>
        Dg.pSum fun _ _ => Dg.ite (fun _ => (Dg.aff0 _).mul (Dg.aff0 _)) fun _ => Dg.zero)).of
    (by decide)

theorem d1_ledEx (np : NormPar) {Ws : ℕ → Ex1 X E} (D : ℕ → ℕ → CForm E)
    (k : ℕ) (hW : ∀ s, D1 2 (Ws s)) : D1 2 (ledEx np Ws D k) := by
  have r := fun g => d1_rowEx (X := X) D g
  unfold ledEx
  split_ifs with hk
  · exact ((hW k).add (r _)).of (by decide)
  · match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact absurd (by norm_num) hk
    | 9 => exact (((r _).mul (r _)).sub (r _)).of (by decide)
    | 10 => exact ((r _).sub ((r _).mul (r _))).of (by decide)
    | 11 => exact ((r _).sub ((r _).mul (r _))).of (by decide)
    | 12 => exact (r _).of (by decide)
    | 13 => exact ((((r _).mul (r _)).add ((r _).mul (r _))).sub (r _)).of (by decide)
    | 14 => exact ((r _).mul (r _)).of (by decide)
    | 15 => exact ((r _).sub (((r _).mul (r _)).smul _)).of (by decide)
    | 16 => exact (r _).of (by decide)
    | _ + 17 => exact D1.zero.of (by decide)

end Led

/-! ## 2. Feed-forward -/

section FF
variable [scl : Scl] {X : Type}

theorem qspec_degLe {E : Type} [Field E] (S : QSpec X E) : S.fam.DegLe 2 := by
  refine ⟨(Req.deg_le_iff X E _ 2).2 fun t ht => ?_, fun j w P e => ?_⟩
  · have ht' : t ∈
        (⟨fun _ _ => 1, [0]⟩ : Term X E) :: ⟨fun _ _ => 1, [1]⟩ ::
          (List.range S.nQ).map fun n => (⟨fun _ _ => 1, [2 * n + 2, 2 * n + 3]⟩ : Term X E) := ht
    rcases List.mem_cons.1 ht' with rfl | ht'
    · exact Nat.le_succ 1
    · rcases List.mem_cons.1 ht' with rfl | ht'
      · exact Nat.le_succ 1
      · obtain ⟨n, _, rfl⟩ := List.mem_map.1 ht'
        exact le_refl _
  · have e' : (if j = 0 then Atom.sum S.w S.inner
          else if j = 1 then .base (.cell S.a)
          else .base (.cell (if j % 2 = 0 then S.f ((j - 2) / 2) else S.g ((j - 2) / 2)))) =
        Atom.sum w P := e
    split_ifs at e'
    cases e'
    refine (Req.deg_le_iff X E _ 2).2 fun t ht => ?_
    obtain ⟨n, _, rfl⟩ := List.mem_map.1
      (show t ∈ (List.range S.nS).map fun n => (⟨S.κ n, [2 * n, 2 * n + 1]⟩ : Term X E) from ht)
    exact le_refl _

theorem dg_cellsE {E : Type} [Field E] (vx w : ℕ) :
    ∀ fs : List (ℕ → ℕ → ℕ → ℕ → CForm E), Dg (X := X) fs.length (cellsE vx w fs)
  | [] => Dg.con _
  | _ :: l => ((Dg.aff0 _).mul (dg_cellsE vx w l)).of (by rw [List.length_cons, Nat.add_comm])

theorem d1_blk {E : Type} [Field E] (vx w n : ℕ) (c : ℕ → ℕ → ℕ → ℕ → ℕ → E)
    (fs : List (ℕ → ℕ → ℕ → ℕ → CForm E)) (ia : ℕ → IdxAtom E) :
    D1 (X := X) (max 1 (fs.length + 1)) (blk vx w n c fs ia) :=
  D1.sumA _ _ (Dg.pSum fun _ _ => ((dg_cellsE vx w fs).mul (Dg.idx0 _)).sc _)

theorem vx_le (s : FFSeg.Fam) : vxOf s ≤ 14 := Nat.clog_le_of_le_pow (by cases s <;> decide)

end FF

/-! ## 3. Numbers -/

theorem NumsLe.of {X F E : Type} [Field E] {S : SegSpec X F E} {a b d V : ℕ} (h : S.NumsLe a b)
    (h1 : a ≤ d) (h2 : b ≤ V) : S.NumsLe d V :=
  ⟨fun f hf => ⟨DegLe.of (h.1 f hf).1 h1, le_trans (h.1 f hf).2 h2⟩,
    fun k hk => ⟨DegLe.of (h.2 k hk).1 h1, le_trans (h.2 k hk).2 h2⟩⟩

end Cm.Seg
