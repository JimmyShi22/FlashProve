-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsPullIff.lean: what the pull-back of the ledger of the claims on the norms says,
as an equivalence.

Cb/Pv/Lay/End/NormsA.lean concludes five clauses from the pull-back of the ledger to the early
entries. This file says what that premise is worth. Under the premises on sizes, names and forms,
the pull-back holds if and only if three things hold: the record NormsLast at the letters read off
the parts of a last statement, with each late entry at the value of its form; and the first output
claim of either sumcheck. So the premise can be met wherever these three can.

Main theorem: norms_pull_iff.

Limits: as Cb/Pv/Lay/End/NormsA.lean.


-/
import Cb.Pv.Lay.End.NormsA
import Cb.Pv.Lay.End.NormsIff

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Cell lDd)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] (P : NormPar0 E) {Nm J₂ : Type}
  [Fintype J₂] [DecidableEq P.J] [DecidableEq J₂]

omit [DecidableEq P.J] [DecidableEq J₂] in
/-- The claim that the product layer of the squares leaves is worth 0 if and only if the layer's
first output claim holds. -/
theorem u1At_iff (o1 : P.sq.R.L.toSum.T.par.Out) (m : P.J → E) (u : J₂ → E) :
    Blocks.Form.val (Sum.elim m u) (u1At P o1) = 0 ↔ P.sq.R.L.toSum.T.par.UHolds o1 m := by
  unfold u1At
  rw [val_upForm]
  exact Cb.Sub.formU_holds _ _ (fun _ _ b _ => Empty.elim b) o1 m

omit [DecidableEq P.J] [DecidableEq J₂] in
/-- The same for the token sumcheck of the row products. -/
theorem u2At_iff (o2 : P.rows.tok.toSum.T.par.Out) (m : P.J → E) (u : J₂ → E) :
    Blocks.Form.val (Sum.elim m u) (u2At P o2) = 0 ↔ P.rows.tok.toSum.T.par.UHolds o2 m := by
  unfold u2At
  rw [val_upForm]
  exact Cb.Sub.formU_holds _ _ (fun _ _ b _ => Empty.elim b) o2 m

/-- What the pull-back of the ledger of the claims on the norms says. -/
theorem norms_pull_iff
    (hrd : ∀ (a b : E) (m m' : P.J → E) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (Y : LateLay Nm J₂) (ι : NormsNm → Nm) (fm : Nm → TWhole.Aff E P.J) (p : Fin P.D.lT → E)
    (sW : Fin (P.D.nNu * 9) → E) (c : E) (o1 : P.sq.R.L.toSum.T.par.Out)
    (sP : Fin (P.D.nNu * 7) → E) (σ z : E) (o2 : P.rows.tok.toSum.T.par.Out) (zt : ℕ → E)
    (m : P.J → E) (b s B : ℕ) (hl : lDd P.D = b + s) (hd : P.D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b)
    (hfm : ∀ x, InRange P.D.nNu B P.D.ne P.D.nx x → fm (ι x) =
      toAff (normsFm P.rd P.D (normsEAt P p sW c o1 sP σ z o2 zt) (P.D.lL + 1) b s x))
    (gXi : ∀ ν l kh, ν < P.D.nNu → l < 5 → kh < B → Y.good (ι (.xi ν l kh)))
    (gP : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atP ν n)))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atR ν n)))
    (gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (ι (.sel l x))) :
    TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm)
      (normsLed (namesAt P (readsAt Y ι)) (normsEAt P p sW c o1 sP σ z o2 zt) (u1At P o1)
        (u2At P o2) P.D (P.D.lL + 1) b B)) m ↔
      NormsLast (namesAt P (readsAt Y ι)) (normsEAt P p sW c o1 sP σ z o2 zt) P.D (P.rd m)
        (P.D.lL + 1) b s (Sum.elim m fun j => (lateA Y fm j).val m) ∧
      P.sq.R.L.toSum.T.par.UHolds o1 m ∧ P.rows.tok.toSum.T.par.UHolds o2 m := by
  have hn : P.D.nNu = 2 ^ (P.D.lL + 1) := by
    show 2 * 2 ^ P.D.lL = _
    rw [pow_succ, Nat.mul_comm]
  rw [Cb.Sub.pullL_holds]
  unfold normsLed
  rw [ledOf_holds, norms_cl_iff _ _ _ _ P.D (P.rd m) (P.D.lL + 1) b s B _ hn hl hd hB
    (tables_true P hrd Y ι fm _ (P.D.lL + 1) b s B hfm gXi gP gR gS m), u1At_iff, u2At_iff]

end Cb.Pv.Lay.End
