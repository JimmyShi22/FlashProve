-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsParts.lean: the norms' six clauses of what the chain of a layers' sub-proof's own
rounds owes at its end, at a last statement that is made from parts, with the ledger shown to hold.

Cb/Pv/Lay/End/Parts.lean makes a last statement of the chain from a record of its parts.
Cb/Pv/Lay/End/NormsMeetAt.lean names scalars and outputs at which the ledger of the claims on the
norms holds. This file takes a record whose parts up to the second sumcheck are these, shows all
premises of norms_bill (Cb/Pv/Lay/End/NormsBillAt.lean) at the statement made from it, and applies
that theorem. The conclusion is in the record's parts, as Parts.bill_e has them.

Main theorems: eAt_parts (the letters of the claims, off the record), led_at_parts (the pull-back of
the ledger holds), norms_at_parts.

Limits. The premises left: equations on the record's own fields; the forms of the late entries at
the norms' names (hfm) and that the names in range are good; three conditions on sizes; and of the
cells: lines 12 and 16 at the extensions of each norm's bytes at the token point, and that the
extension of each defect d10 vanishes at zt. The statement made from the record need be no run's.


-/
import Cb.Pv.Lay.End.NormsBillAt
import Cb.Pv.Lay.End.NormsMeetAt
import Cb.Pv.Lay.End.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (d10 lDd)
open Inst.Model.Ledger (l1 h1 sig rr rq)
open Blocks (ext)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : OwnPar E M X)
  (W : P.WPart) {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Y : LateLay Nm J₂)
  (ι : NormsNm → Nm) (fm : Nm → TWhole.Aff E P.J) (q : (tailAt P W).Parts) (m : M)
  (p : Fin P.D.lT → E) (c σ dl e1 e2 : E) (ρj : Fin (P.D.lL + 1) → E)
  (pt1 : PPt P.nr.sq.R.L.toSum.T.par.fmt) (pt2 : PPt P.nr.rows.tok.toSum.T.par.fmt)
  (zt : ℕ → E)
  (hx : q.x.2 = p) (hsL : q.sL = sWAt P.nr (P.msg m) p) (hcN : q.cN = c)
  (ho1 : q.o1 = o1At P.nr (P.msg m) p c ρj e1 pt1) (hsP : q.sP = sPAt P.nr (P.msg m) p dl)
  (hcP : q.cP = σ) (hr2 : q.r2 = fun _ => zAt P.nr (P.msg m) p dl σ)
  (ho2 : q.o2 = o2At P.nr (P.msg m) p dl σ e2 pt2)

include hx hsL hcN ho1 hsP hcP hr2 ho2 in
omit [Fintype J₂] [DecidableEq J₂] in
/-- The letters of the claims on the norms, off the record. -/
theorem eAt_parts :
    eAt P W q.e zt = normsEAt P.nr p (sWAt P.nr (P.msg m) p) c (o1At P.nr (P.msg m) p c ρj e1 pt1)
      (sPAt P.nr (P.msg m) p dl) σ (zAt P.nr (P.msg m) p dl σ)
      (o2At P.nr (P.msg m) p dl σ e2 pt2) zt := by
  show normsEAt P.nr q.x.2 q.sL q.cN q.o1 q.sP q.cP (@id (Fin 1 → E) q.r2 0) q.o2 zt = _
  rw [hx, hsL, hcN, ho1, hsP, hcP, hr2, ho2]
  rfl

variable (b s B : ℕ) (hl : lDd P.D = b + s) (hd : P.D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b)
  (hfm : ∀ x, InRange P.D.nNu B P.D.ne P.D.nx x →
    fm (ι x) = toAff (normsFm P.rd P.D (eAt P W q.e zt) (P.D.lL + 1) b s x))
  (gXi : ∀ ν l kh, ν < P.D.nNu → l < 5 → kh < B → Y.good (ι (.xi ν l kh)))
  (gP : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atP ν n)))
  (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atR ν n)))
  (gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (ι (.sel l x)))
  (h12 : ∀ ν, ν < P.D.nNu → l1 (Dgs P.nr (P.msg m) p ν) + h1 (Dgs P.nr (P.msg m) p ν) -
    2 * sig (Dgs P.nr (P.msg m) p ν) = 0)
  (h16 : ∀ ν, ν < P.D.nNu → rr (Dgs P.nr (P.msg m) p ν) + rq (Dgs P.nr (P.msg m) p ν) -
    sig (Dgs P.nr (P.msg m) p ν) + 1 = 0)
  (hHot : ∀ l, l < P.D.ne → ext P.D.lT (d10 P.D (P.rd (P.msg m)) l) zt = 0)

include hx hsL hcN ho1 hsP hcP hr2 ho2 hl hd hB hfm gXi gP gR gS h12 h16 hHot in
/-- The pull-back of the ledger of the claims on the norms holds. -/
theorem led_at_parts :
    TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (ledAt P W Y ι q.e zt b B)) (P.msg m) := by
  have hE := eAt_parts P W q m p c σ dl e1 e2 ρj pt1 pt2 zt hx hsL hcN ho1 hsP hcP hr2 ho2
  rw [hE] at hfm
  show TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm)
    (normsLed (namesAt P.nr (readsAt Y ι)) (eAt P W q.e zt) (u1At P.nr q.o1) (u2At P.nr q.o2) P.D
      (P.D.lL + 1) b B)) (P.msg m)
  rw [hE, ho1, ho2]
  exact (norms_pull_iff P.nr P.hrd Y ι fm p _ c _ _ σ _ _ zt (P.msg m) b s B hl hd hB hfm gXi gP gR
    gS).2 ⟨last_meets P.nr _ (P.msg m) _ p c σ dl e1 e2 ρj pt1 pt2 zt b s hl h12 h16 hHot,
      outU_holds _ _ _ _ _ _, outU_holds _ _ _ _ _ _⟩

include hx hsL hcN ho1 hsP hcP hr2 ho2 hl hd hB hfm gXi gP gR gS h12 h16 hHot in
/-- The norms' six clauses, in the record's parts: norms_bill applied, with every premise shown. One
of them (c1) is True at this chain. -/
theorem norms_at_parts :
    (tailAt P W).lL q.x q.sL m ∧ (tailAt P W).s1.Lc (((q.x, q.sL), q.cN), q.pN) q.r1 m ∧
      (tailAt P W).ow1 q.b1 m ∧ (tailAt P W).lP (q.b1, q.d1) q.sP m ∧
      (tailAt P W).s2.Lc (((q.b1, q.d1), q.sP), q.cP) q.r2 m ∧ (tailAt P W).ow2 q.b2 m := by
  have hst : ((tailAt P W).b1 q.e).2.st.1.2 = ((tailAt P W).b1 q.e).1.1.1.2 := by
    show q.o1.st.1.2 = q.cN
    rw [ho1, hcN]
    rfl
  exact norms_bill P W Y ι fm q.e zt m b s B hl hd hB hst hfm gXi gP gR gS
    (led_at_parts P W Y ι fm q m p c σ dl e1 e2 ρj pt1 pt2 zt hx hsL hcN ho1 hsP hcP hr2 ho2 b s B
      hl hd hB hfm gXi gP gR gS h12 h16 hHot)

end Cb.Pv.Lay.End
