-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/Join.lean: the four key forms of an attention segment as affine forms on entries, and
the claim that joins them to the lookup.

Definitions, statements and proofs. The library writes the four key forms as functions KF of the
values v of the named scalars (Inst/Model/Att/KeyForms.lean). In a sub-proof these values are
hidden: each is what was sent less a mask entry, an affine form on the entries. This file writes
the key forms on such forms, and the verifier's claim on the calls' key vectors: the sum over the
calls c of e_c (alpha - c theta - KF_c), plus a public term for the trees that hold only padding,
less the hidden value at the end of the lookup's key side, is 0.

Main names:
  dpA, remA, kfA D C p vF: the forms DP, REM and KF on forms vF k in the place of values.
  val_kfA: the value of kfA is KF at the values of the forms vF k.
  JoinPub E: the public letters of the join: alpha, theta, the calls' weights e, the padding trees'
    term.
  joinVal: the left side of the join, on values. joinA: the same as a form; val_joinA.

Limits: the letters of JoinPub and the form of the hidden value at the end of the key side are the
lookup's; nothing is said of them here. Nothing on an honest prover or on hiding.


-/
import Cb.Pv.Att.End.Forms
import Inst.Model.Att.KeyForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open TWhole Cb Finset Blocks
open Inst.Model Inst.Model.AttSeg

variable {E J : Type} [Field E] [scl : Scl] (D : Dim) (C : Calls) (p : Pub E)
  (vF : KSc → Aff E J)

/-- DP on forms. -/
def dpA : Reg → Aff E J
  | .M => aAdd (aSub (vF (.ms .M)) (vF (.ss .M)))
      (aConst (((D.cutC : ℤ) : E) * LL D C p.z .m2 * ones (D.lP + 1) (zs D C p.z)))
  | .D => aAdd (aSub (vF (.ms .D)) (vF (.ss .D)))
      (aConst (((Om D : ℤ) : E) * LL D C p.z .d2 * (1 - LE D.lB (zj' D C p.z) (zi' D C p.z))))

/-- REM on forms. -/
def remA : Aff E J := aSub (aAdd (aSmul 2 (vF .acc)) (vF .zc)) (aSmul 2 (vF .zo))

/-- A form plus 128 times the sum of a family's weights. -/
def plus128 (u : Fam) (a : Aff E J) : Aff E J := aAdd a (aConst (128 * LL D C p.z u))

/-- The four key forms on forms. -/
def kfA : Fin 4 → Aff E J
  | 0 => aSum ({.m1, .d1} : Finset Fam) fun u =>
      aAdd (aAdd (plus128 D C p u (vF (.cell u 0)))
        (aSmul (2 ^ 20) (plus128 D C p u (vF (.cell u 1))))) (aSmul (2 ^ 40) (vF (.cell u 2)))
  | 1 => aAdd
      (aConst ((1 - LL D C p.z .m2 - LL D C p.z .d2) * ((D.cutC - 2 ^ D.sh + 2 ^ 32 : ℤ) : E)))
      (aSum ({.m2, .d2} : Finset Fam) fun u =>
        aAdd (aAdd (aSub (aSub (dpA D C p vF u.reg) (plus128 D C p u (vF (.cell u 0))))
          (aSmul 256 (plus128 D C p u (vF (.cell u 1))))) (aSmul (2 ^ 32) (vF (.cell u 2))))
          (aSmul (2 ^ 33) (aAdd (plus128 D C p u (vF (.cell u 3))) (aSmul 256 (vF (.cell u 4))))))
  | 2 => aAdd (aAdd
      (aSmul (1 - zChi D C p.z)
        (aSub (remA vF) (aSmul (2 ^ 16) (plus128 D C p .w3 (vF .rh)))))
      (aSmul (zChi D C p.z)
        (aSub (aSub (aSub (aSmul 2 (vF .zc)) (aConst (LL D C p.z .w3))) (remA vF))
          (aSmul (2 ^ 16) (plus128 D C p .w3 (vF .rh'))))))
      (aSmul (2 ^ (16 - D.lT))
        (aSub (aConst (LL D C p.z .x3 * idP D.lT (xi D C p.z)))
          (aSum (range D.lT) fun k => aSmul (2 ^ k) (vF (.ib k)))))
  | 3 => aAdd (plus128 D C p .f4 (vF .rg)) (aSmul (2 ^ 20) (plus128 D C p .f4 (vF .rg')))

variable [Fintype J] (x : J → E)

omit scl in
theorem val_plus128 (u : Fam) (a : Aff E J) :
    (plus128 D C p u a).val x = a.val x + 128 * LL D C p.z u := by
  unfold plus128
  rw [val_aAdd, val_aConst]

theorem val_dpA (r : Reg) : (dpA D C p vF r).val x = DP D C p (fun k => (vF k).val x) r := by
  cases r <;> simp only [dpA, DP, val_aAdd, val_aSub, val_aConst]

omit scl in
theorem val_remA : (remA vF).val x = REM fun k => (vF k).val x := by
  simp only [remA, REM, val_aAdd, val_aSub, val_aSmul]

/-- The value of a key form on forms is the key form at the forms' values. -/
theorem val_kfA (c : Fin 4) : (kfA D C p vF c).val x = KF D C p (fun k => (vF k).val x) c := by
  match c with
  | 0 => simp only [kfA, KF, val_aSum, val_aAdd, val_aSmul, val_plus128]
  | 1 => simp only [kfA, KF, val_aSum, val_aAdd, val_aSub, val_aSmul, val_aConst, val_plus128,
      val_dpA]
  | 2 => simp only [kfA, KF, val_aSum, val_aAdd, val_aSub, val_aSmul, val_aConst, val_plus128,
      val_remA]
  | 3 => simp only [kfA, KF, val_aAdd, val_aSmul, val_plus128]

/-! ### The join -/

/-- The public letters of the join. -/
structure JoinPub (E : Type) where
  /-- the element from which the keys are taken away -/
  alpha : E
  /-- the shift between the calls' tables -/
  theta : E
  /-- the calls' weights -/
  e : Fin 4 → E
  /-- the term of the trees that hold only padding -/
  pad : E

/-- The left side of the join: kf: the four key forms' values; ce: the hidden value at the end of
the lookup's key side. -/
def joinVal (q : JoinPub E) (kf : Fin 4 → E) (ce : E) : E :=
  ∑ c : Fin 4, q.e c * (q.alpha - (c.val : E) * q.theta - kf c) + q.pad - ce

/-- The left side of the join as a form. -/
def joinA (q : JoinPub E) (kf : Fin 4 → Aff E J) (ce : Aff E J) : Aff E J :=
  aSub (aAdd (aSum univ fun c : Fin 4 =>
    aSmul (q.e c) (aSub (aConst (q.alpha - (c.val : E) * q.theta)) (kf c))) (aConst q.pad)) ce

omit scl in
theorem val_joinA (q : JoinPub E) (kf : Fin 4 → Aff E J) (ce : Aff E J) :
    (joinA q kf ce).val x = joinVal q (fun c => (kf c).val x) (ce.val x) := by
  simp only [joinA, joinVal, val_aSub, val_aAdd, val_aSum, val_aSmul, val_aConst]

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.val_kfA
#print axioms Cb.Pv.Att.End.val_joinA
