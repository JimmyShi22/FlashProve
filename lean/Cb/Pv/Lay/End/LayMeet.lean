-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/LayMeet.lean: the premises of the four shares of what the chain of a layers'
sub-proof's own rounds owes at its end can be met together, at any value of the chain's letters.

What the chain owes at its end (LayTail.Bill, Cb/Pv/Lay/End/Last.lean) is paid share by share from
parts of the ledger of the verifier's claims: the norms' share, that of the terms and the batched
sumcheck, the gated products' and the weights'. Each share has been applied at a last statement made
from a record of parts (Cb/Pv/Lay/End/Parts.lean), with its own part of the ledger shown to hold:
Cb/Pv/Lay/End/NormsParts.lean, Cb/Pv/Lay/End/TermsMeet.lean, Cb/Pv/Lay/End/GatedParts.lean. This
file lays the four side by side: one value of the letters, one lay of the late entries, one family
of forms, one record, one tuple of messages.

Main names:
  `LateLay.sum`: two lays of late entries side by side.
  `bill_at_parts`: the whole bill at the statement made from the record, with "true" for what is
  claimed of the first statement.
Limits. The statement made from the record need be no run's: no transcript is given that leads to
it. So this is no value for lay_owed and lay_hEnd_at (Cb/Pv/Lay/End/LayHEndAt.lean), which speak of
runs alone. The share that pays what is claimed of the first statement is not
treated. The premises left are equations on the record's own fields, the forms of the late entries
at the three families of names, that the names in range are good, conditions on sizes, and three
conditions on the cells of the ledgers and the selectors.


-/
import Cb.Pv.Lay.End.NormsParts
import Cb.Pv.Lay.End.TermsMeet
import Cb.Pv.Lay.End.GatedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)
open Inst.Model.FFSeg (d10 lDd lF lFe)
open Inst.Model.Ledger (l1 h1 sig rr rq)
open Blocks (ext)

/-- Two lays of late entries side by side. -/
def LateLay.sum {N₁ N₂ K₁ K₂ : Type} (Y₁ : LateLay N₁ K₁) (Y₂ : LateLay N₂ K₂) :
    LateLay (N₁ ⊕ N₂) (K₁ ⊕ K₂) where
  nm := Sum.map Y₁.nm Y₂.nm
  at' := Sum.map Y₁.at' Y₂.at'
  good := Sum.elim Y₁.good Y₂.good
  ok := fun x hx => by
    cases x with
    | inl a => exact congrArg Sum.inl (Y₁.ok a hx)
    | inr b => exact congrArg Sum.inr (Y₂.ok b hx)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂]

/-- The whole bill at the statement made from a record of parts: the four shares applied, each with
its part of the ledger shown to hold, under one lay, one family of forms and one tuple of
messages. -/
theorem bill_at_parts (Y : LateLay Nm J₂) (ιN : NormsNm → Nm) (ιT : TermsNm → Nm)
    (ιG : GatedNm → Nm) (fm : Nm → TWhole.Aff E P.J) (q : (tailAt P.toOwnPar P.wPart).Parts)
    (m : M) (p : Fin P.D.lT → E) (c σ dl e1 e2 : E) (ρj : Fin (P.D.lL + 1) → E)
    (pt1 : PPt P.nr.sq.R.L.toSum.T.par.fmt) (pt2 : PPt P.nr.rows.tok.toSum.T.par.fmt)
    (zt : ℕ → E)
    (hx : q.x.2 = p) (hsL : q.sL = sWAt P.nr (P.msg m) p) (hcN : q.cN = c)
    (ho1 : q.o1 = o1At P.nr (P.msg m) p c ρj e1 pt1) (hsP : q.sP = sPAt P.nr (P.msg m) p dl)
    (hcP : q.cP = σ) (hr2 : q.r2 = fun _ => zAt P.nr (P.msg m) p dl σ)
    (ho2 : q.o2 = o2At P.nr (P.msg m) p dl σ e2 pt2)
    (b s B : ℕ) (hl : lDd P.D = b + s) (hd : P.D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b)
    (hfmN : ∀ x, InRange P.D.nNu B P.D.ne P.D.nx x →
      fm (ιN x) = toAff (normsFm P.rd P.D (eAt P.toOwnPar P.wPart q.e zt) (P.D.lL + 1) b s x))
    (gXi : ∀ ν l kh, ν < P.D.nNu → l < 5 → kh < B → Y.good (ιN (.xi ν l kh)))
    (gP : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ιN (.atP ν n)))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ιN (.atR ν n)))
    (gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (ιN (.sel l x)))
    (h12 : ∀ ν, ν < P.D.nNu → l1 (Dgs P.nr (P.msg m) p ν) + h1 (Dgs P.nr (P.msg m) p ν) -
      2 * sig (Dgs P.nr (P.msg m) p ν) = 0)
    (h16 : ∀ ν, ν < P.D.nNu → rr (Dgs P.nr (P.msg m) p ν) + rq (Dgs P.nr (P.msg m) p ν) -
      sig (Dgs P.nr (P.msg m) p ν) + 1 = 0)
    (hHot : ∀ l, l < P.D.ne → ext P.D.lT (d10 P.D (P.rd (P.msg m)) l) zt = 0)
    (a3 : P.tp.tm.toSum.T.par.Out) (a4 : P.ip.inn.toSum.T.par.Out) (heps : a3.eps ≠ 0)
    (h3 : q.o3 = trueOut P.tp a3 (P.msg m))
    (h4 : q.o4 = honOut P.ip.inn.toSum.T.par a4 (P.msg m))
    (hfmT : ∀ x : TermsNm, x.InR P.D → fm (ιT x) =
      toAff (termsFm P.rd P.D (termsEAt P.tp (trueOut P.tp a3 (P.msg m))).rt x))
    (tR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ιT (.row ν n)))
    (tC : ∀ l k, l < P.D.ne → k < 3 → Y.good (ιT (.sc l k)))
    (tS : ∀ l x k, l < P.D.ne → x < P.D.nx → k < 1 → Y.good (ιT (.sel l x k)))
    (sG : ℕ) (k1 : 1 ≤ P.D.lL) (ks1 : sG ≤ lF P.D) (ks2 : sG ≤ lFe P.D)
    (kfe : P.D.fe = 2 ^ lFe P.D) (a5 : P.fp.gp.toSum.T.par.Out)
    (a6 : P.fp.rt.L.toSum.T.par.Out) (h5 : q.o5 = honOut P.fp.gp.toSum.T.par a5 (P.msg m))
    (h6 : q.o6 = honOut P.fp.rt.L.toSum.T.par a6 (P.msg m))
    (hfmG : ∀ x : GatedNm, x.InR P.D sG →
      fm (ιG x) = toAff (gatedFm P.rd P.D (gatedEAt P.fp q.o5 q.o6) sG x))
    (hY : GoodNm Y ιG P.D sG) (a7 : P.wp0.wt.L.toSum.T.par.Out)
    (h7 : q.o7 = honOut P.wp0.wt.L.toSum.T.par a7 (P.msg m)) :
    (tailAt P.toOwnPar P.wPart).Bill (fun _ _ => True) q.e m := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := norms_at_parts P.toOwnPar P.wPart Y ιN fm q m p c σ dl e1 e2
    ρj pt1 pt2 zt hx hsL hcN ho1 hsP hcP hr2 ho2 b s B hl hd hB hfmN gXi gP gR gS h12 h16 hHot
  obtain ⟨t1, t2, t3, t4⟩ := terms_at_parts P.toOwnPar P.wPart Y ιT fm q m a3 a4 heps h3 h4 hfmT
    tR tC tS
  obtain ⟨g1, g2, g3, g4⟩ := gated_at_parts P Y ιG fm q m sG k1 ks1 ks2 kfe a5 a6 h5 h6 hfmG hY
  obtain ⟨w1, w2, w3⟩ := weights_at_parts P (lateA Y fm) q m a7 h7
  exact (q.bill_e _ m).2 ⟨trivial, n1, n2, n3, n4, n5, n6, t1, t2, t3, t4, g1, g2, g3, g4, w1, w2,
    w3⟩

end Cb.Pv.Lay.End

#print axioms Cb.Pv.Lay.End.bill_at_parts
