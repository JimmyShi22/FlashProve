-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Inst/Model/Att/KeyFormsExt/All.lean: the key forms of an attention segment, at the rule values, are
the multilinear extensions of the calls' vectors of looked-up values.

Statements with their proofs; the parts are in the other files of this folder. No protocol and no
probability: an identity of polynomials in the cells and the challenges. The calls 1 to 4 of the
comments are 0 to 3 in `Fin 4`, as in Inst/Model/Att/KeyForms.lean.
Main names:
  `lin5`, `piece2`: the linear algebra of a family of call 2; the extension of a piece of call 2.
  `kf1`: call 2 of the comments.
  `kfExt`: for each call c: `KF D C p (rv D C p t) c = Blocks.ext (C.a c) (keyVec D tb t c) (C.zC c
    p.z)` (`KF`, `rv`: Inst/Model/Att/KeyForms.lean; `keyVec`: Inst/Model/Att/Trace.lean; `zC`:
    Inst/Model/Att/Points.lean), for every field, every content t of the cells, all challenges p and
    all tables tb.
  `kfExt_ref`: at the reference sizes, for lawful scales, no hypothesis on sizes is left (by
    `ref_calls_ok`, Inst/Model/Att/Trace.lean, and `ref_deep`, Inst/Model/Att/Points.lean).
Limits: `kfExt` stands under `C.OK D`, under "no piece is longer than a tree" (u.l D ≤ C.Dk for
every family u), and under "calls 1 and 2 have the same size" (C.a 0 = C.a 1). The last is used for
call 2 alone: the sums SS2M, SS2D are formed with the weights of call 1. That the statement fails
without it is not shown here. This folder says nothing on the values of sent scalars, on `joinRhs`,
on step 18 of Inst/Model/Att/Sums.lean, or on any protocol. Coordinate 0 of a point belongs to the
most significant bit, as in Blocks/Ext.lean. The library has sizes (`Dim`, `Calls`) for the
reference sizes alone: at any other sizes the three hypotheses are shown of nothing, and at small
sizes "no piece is longer than a tree" and the clause `ten` of `C.OK D` may fail. It is not shown,
at any sizes, that the programs, or the verifier in OnBytes/, lay their looked-up values as `keyVec`
does: the calls in this order, the pieces family by family, these paddings, the top bit first.
-/
import Inst.Model.Att.KeyFormsExt.OffLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Inst.Model.AttSeg.KeyFormsExt
open Inst.Model Inst.Model.AttSeg Finset

variable {E : Type} [Field E]

/-- the linear algebra of a family of call 2 -/
theorem lin5 (n : ℕ) (W G e0 e1 e2 e3 e4 : ℕ → E) :
    ∑ b ∈ range n, W b * G b - (∑ b ∈ range n, W b * e0 b + 128 * ∑ b ∈ range n, W b) -
        256 * (∑ b ∈ range n, W b * e1 b + 128 * ∑ b ∈ range n, W b) + 2 ^ 32 * ∑ b ∈ range n, W b *
            e2 b +
        2 ^ 33 * (∑ b ∈ range n, W b * e3 b + 128 * ∑ b ∈ range n, W b + 256 * ∑ b ∈ range n, W b *
            e4 b) =
      ∑ b ∈ range n, W b * (G b - ((e0 b + 128) + 256 * (e1 b + 128)) + 2 ^ 32 * e2 b + 2 ^ 33 *
          ((e3 b + 128) + 256 * e4 b)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    linear_combination ih

variable (D : AttSeg.Dim) (C : AttSeg.Calls) [scl : Scl] (tb : Tables) (p : AttSeg.Pub E)
    (t : AttSeg.Raw → E)

omit scl in
/-- a piece of call 2 -/
theorem piece2 [Scl] (ρ : AttSeg.Reg) (l : ℕ) (q : ℕ → E) (b : ℕ) :
    Blocks.ext l (AttSeg.key2 D t ρ b) q =
      Blocks.ext l (AttSeg.gp D t ρ b) q -
        ((Blocks.ext l (fun x => t (.c ρ 0 b x)) q + 128) + 256 *
            (Blocks.ext l (fun x => t (.c ρ 1 b x)) q + 128)) +
        2 ^ 32 * Blocks.ext l (fun x => t (.c ρ 2 b x)) q +
        2 ^ 33 * ((Blocks.ext l (fun x => t (.c ρ 3 b x)) q + 128) + 256 *
            Blocks.ext l (fun x => t (.c ρ 4 b x)) q) := by
  show Blocks.ext l (fun x => AttSeg.key2 D t ρ b x) q = _
  unfold AttSeg.key2 AttSeg.rm AttSeg.wtV AttSeg.r0 AttSeg.r1 AttSeg.flV AttSeg.w0 AttSeg.w1
  rw [Blocks.ext_add, Blocks.ext_add, Blocks.ext_sub, Blocks.ext_add, Blocks.ext_add,
      Blocks.ext_smul, Blocks.ext_add,
    Blocks.ext_smul, Blocks.ext_smul, Blocks.ext_add, Blocks.ext_add, Blocks.ext_smul,
        Blocks.ext_const]

/-- Call 2 of the comments (1 in `Fin 4`). -/
theorem kf1 (hC : C.OK D) (hM : D.lM ≤ C.Dk) (hs : C.a 0 = C.a 1) :
    AttSeg.KF D C p (AttSeg.rv D C p t) 1 =
        Blocks.ext (C.a 1) (AttSeg.keyVec D tb t 1) (C.zC 1 p.z) := by
  have hl : D.lD ≤ D.lM := by unfold AttSeg.Dim.lD AttSeg.Dim.lM; omega
  have ha : C.Dk ≤ C.a 0 := hC.le 0
  have hz : C.zC 1 p.z = C.zC 0 p.z := by
    funext s
    unfold AttSeg.Calls.zC AttSeg.Calls.e
    rw [hs]
  have hwm : ∀ b, AttSeg.wp D C p.z .m2 b = AttSeg.wp D C p.z .m1 b := by
    intro b
    show Blocks.eqN (C.a 1 - D.lM) 0 (C.zC 1 p.z) (0 + b) =
        Blocks.eqN (C.a 0 - D.lM) 0 (C.zC 0 p.z) (0 + b)
    rw [hz, hs]
  have hwd : ∀ b, AttSeg.wp D C p.z .d2 b = AttSeg.wp D C p.z .d1 b := by
    intro b
    show Blocks.eqN (C.a 1 - D.lD) 0 (C.zC 1 p.z) (D.nb * 2 ^ (D.lM - D.lD) + b) =
      Blocks.eqN (C.a 0 - D.lD) 0 (C.zC 0 p.z) (D.nb * 2 ^ (D.lM - D.lD) + b)
    rw [hz, hs]
  have him : AttSeg.inn D C p.z .m2 = AttSeg.uM D C p.z := by
    show AttSeg.sh (C.zC 1 p.z) (C.a 1 - D.lM) = AttSeg.sh (C.zC 0 p.z) (C.a 0 - D.lM)
    rw [hz, hs]
  have hid : AttSeg.inn D C p.z .d2 = AttSeg.uD D C p.z := by
    show AttSeg.sh (C.zC 1 p.z) (C.a 1 - D.lD) = AttSeg.sh (C.zC 0 p.z) (C.a 0 - D.lD)
    rw [hz, hs]
  have hLm : AttSeg.LL D C p.z .m2 = AttSeg.LL D C p.z .m1 := by
    unfold AttSeg.LL
    exact Finset.sum_congr rfl fun b _ => hwm b
  have hLd : AttSeg.LL D C p.z .d2 = AttSeg.LL D C p.z .d1 := by
    unfold AttSeg.LL
    exact Finset.sum_congr rfl fun b _ => hwd b
  -- DP at the rule values is the gap's sum
  have dpM : AttSeg.DP D C p (AttSeg.rv D C p t) .M =
      ∑ b ∈ range D.nb, AttSeg.wp D C p.z .m1 b *
          Blocks.ext D.lM (AttSeg.gp D t .M b) (AttSeg.uM D C p.z) := by
    rw [gapM]
    show (∑ b ∈ range D.nb, AttSeg.wp D C p.z .m2 b * _) - AttSeg.sumPhi D C p t .s6b +
      ((D.cutC : ℤ) : E) * AttSeg.LL D C p.z .m2 * AttSeg.ones (D.lP + 1) (AttSeg.zs D C p.z) = _
    rw [hLm]
    simp only [hwm]
  have dpD : AttSeg.DP D C p (AttSeg.rv D C p t) .D =
      ∑ b ∈ range D.nb, AttSeg.wp D C p.z .d1 b *
          Blocks.ext D.lD (AttSeg.gp D t .D b) (AttSeg.uD D C p.z) := by
    rw [gapD D C p t hM ha]
    show (∑ b ∈ range D.nb, AttSeg.wp D C p.z .d2 b * _) - AttSeg.sumPhi D C p t .s6d +
      ((AttSeg.Om D : ℤ) : E) * AttSeg.LL D C p.z .d2 *
          (1 - AttSeg.LE D.lB (AttSeg.zj' D C p.z) (AttSeg.zi' D C p.z)) = _
    rw [hLd]
    simp only [hwd]
  -- the vector
  have hv : AttSeg.keyVec D tb t 1 =
      AttSeg.twoFam D.nb D.lM D.lD (AttSeg.key2 D t .M) (AttSeg.key2 D t .D)
      (((D.cutC - 2 ^ D.sh + 2 ^ 32 : ℤ)) : E) := rfl
  rw [hv, twoFam_ext (C.a 1) D.nb D.lM D.lD hl (by omega) (hC.fits 1)]
  have eM : AttSeg.sh (C.zC 1 p.z) (C.a 1 - D.lM) = AttSeg.uM D C p.z := him
  have eD : AttSeg.sh (C.zC 1 p.z) (C.a 1 - D.lD) = AttSeg.uD D C p.z := hid
  have hw1 : ∀ b, Blocks.eqN (C.a 1 - D.lM) 0 (C.zC 1 p.z) (0 + b) = AttSeg.wp D C p.z .m1 b := hwm
  have hw2 : ∀ b, Blocks.eqN (C.a 1 - D.lD) 0 (C.zC 1 p.z) (D.nb * 2 ^ (D.lM - D.lD) + b) =
      AttSeg.wp D C p.z .d1 b := hwd
  rw [eM, eD]
  simp only [hw1, hw2, piece2]
  rw [← lin5, ← lin5, ← dpM, ← dpD]
  show (1 - AttSeg.LL D C p.z .m2 - AttSeg.LL D C p.z .d2) *
      (((D.cutC - 2 ^ D.sh + 2 ^ 32 : ℤ)) : E) +
      ∑ u ∈ ({.m2, .d2} : Finset AttSeg.Fam), (AttSeg.DP D C p (AttSeg.rv D C p t) u.reg -
        (AttSeg.rv D C p t (.cell u 0) + 128 * AttSeg.LL D C p.z u) - 256 *
            (AttSeg.rv D C p t (.cell u 1) + 128 * AttSeg.LL D C p.z u) +
        2 ^ 32 * AttSeg.rv D C p t (.cell u 2) +
        2 ^ 33 * (AttSeg.rv D C p t (.cell u 3) + 128 * AttSeg.LL D C p.z u + 256 *
            AttSeg.rv D C p t (.cell u 4))) = _
  rw [Finset.sum_pair (by decide), hLm, hLd]
  have rM : ∀ jj : ℕ, AttSeg.rv D C p t (.cell .m2 jj) =
      ∑ b ∈ range D.nb, AttSeg.wp D C p.z .m2 b *
          Blocks.ext D.lM (fun x => t (.c .M jj b x)) (AttSeg.inn D C p.z .m2) :=
    fun _ => rfl
  have rD : ∀ jj : ℕ, AttSeg.rv D C p t (.cell .d2 jj) =
      ∑ b ∈ range D.nb, AttSeg.wp D C p.z .d2 b *
          Blocks.ext D.lD (fun x => t (.c .D jj b x)) (AttSeg.inn D C p.z .d2) :=
    fun _ => rfl
  simp only [rM, rD, hwm, hwd, him, hid]
  unfold AttSeg.LL
  show _ + ((AttSeg.DP D C p (AttSeg.rv D C p t) .M - _ - _ + _ + _) +
      (AttSeg.DP D C p (AttSeg.rv D C p t) .D - _ - _ + _ + _)) = _
  ring

/-- All four calls: the key form at the rule values is the multilinear extension of the call's
vector of looked-up values at its key point. -/
theorem kfExt (hC : C.OK D) (hdeep : ∀ u : AttSeg.Fam, u.l D ≤ C.Dk) (hs : C.a 0 = C.a 1)
    (c : Fin 4) :
    AttSeg.KF D C p (AttSeg.rv D C p t) c =
        Blocks.ext (C.a c) (AttSeg.keyVec D tb t c) (C.zC c p.z) := by
  have hM : D.lM ≤ C.Dk := hdeep .m1
  have hW : D.lW ≤ C.Dk := hdeep .w3
  fin_cases c
  · exact kf0 D C tb p t hC (le_trans hM (hC.le 0))
  · exact kf1 D C tb p t hC hM hs
  · exact kf2 D C tb p t hC (le_trans hW (hC.le 2))
  · exact kf3 D C tb p t hC hW

/-- At the reference sizes, for lawful scales, no hypothesis on sizes is left. -/
theorem kfExt_ref [law : Lawful] (c : Fin 4) :
    AttSeg.KF AttSeg.Dim.ref AttSeg.Calls.ref p (AttSeg.rv AttSeg.Dim.ref AttSeg.Calls.ref p t) c =
      Blocks.ext (AttSeg.Calls.ref.a c) (AttSeg.keyVec AttSeg.Dim.ref tb t c)
          (AttSeg.Calls.ref.zC c p.z) :=
  kfExt AttSeg.Dim.ref AttSeg.Calls.ref tb p t AttSeg.ref_calls_ok AttSeg.ref_deep.1
      AttSeg.ref_deep.2.1 c

end Inst.Model.AttSeg.KeyFormsExt
