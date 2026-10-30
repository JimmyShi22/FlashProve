-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/TermsFirst.lean: the four clauses of the sumcheck of the terms and of the batched
sumcheck in what the chain of the first layers' sub-proof's own rounds owes at its end.

The first sub-proof has a chain of its own (Cb/Pv/Lay/At/OwnFirst.lean): three points stand before
its stages, and its last stretch differs. The sumcheck of the terms and the batched sumcheck are
those of the later sub-proofs. So the statements of Cb/Pv/Lay/End/TermsBillAt.lean and
Cb/Pv/Lay/End/TermsMeet.lean carry over, with the same two parts of the ledger.

Main names:
  `terms_bill_first`: the fields c3, o3, c4, o4 of the chain's bill, off a last statement.
  `terms_at_parts_first`: the same at a statement made from a record of parts whose two outputs are
  trueOut and honOut: no ledger is a premise any more.
Limits: as Cb/Pv/Lay/End/TermsBillAt.lean and Cb/Pv/Lay/End/TermsMeet.lean.


-/
import Cb.Pv.Lay.At.OwnFirst
import Cb.Pv.Lay.End.TermsMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : OwnFPar E M X)
  (W : P.WFPart) {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂]

/-- The four fields of the first chain's bill that belong to the sumcheck of the terms and to the
batched sumcheck. -/
theorem terms_bill_first (Y : LateLay Nm J₂) (ι : TermsNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (e : (P.layVF W).toTail.s7.Nx) (m : M) (heps : ((P.layVF W).toTail.b3 e).2.eps ≠ 0)
    (hfm : ∀ x : TermsNm, x.InR P.D → fm (ι x) =
      toAff (termsFm P.rd P.D (termsEAt P.tp ((P.layVF W).toTail.b3 e).2).rt x))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.row ν n)))
    (gC : ∀ l k, l < P.D.ne → k < 3 → Y.good (ι (.sc l k)))
    (gS : ∀ l x k, l < P.D.ne → x < P.D.nx → k < 1 → Y.good (ι (.sel l x k)))
    (h3 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm)
      (termsLed P.tp (readsT Y ι) ((P.layVF W).toTail.b3 e).2)) (P.msg m))
    (h4 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm)
      (stackLed P.ip ((P.layVF W).toTail.b4 e).2)) (P.msg m)) :
    (P.layVF W).toTail.s3.Lc ((P.layVF W).toTail.b3 e).1.1 ((P.layVF W).toTail.b3 e).1.2 m ∧
      (P.layVF W).toTail.ow3 ((P.layVF W).toTail.b3 e) m ∧
      (P.layVF W).toTail.s4.Lc ((P.layVF W).toTail.b4 e).1.1 ((P.layVF W).toTail.b4 e).1.2 m ∧
      (P.layVF W).toTail.ow4 ((P.layVF W).toTail.b4 e) m :=
  ⟨trivial,
    ⟨heps, terms_pull P.tp P.hrd Y ι fm ((P.layVF W).toTail.b3 e).2 hfm gR gC gS (P.msg m) h3⟩,
    trivial, stack_pull P.ip P.hrd (lateA Y fm) ((P.layVF W).toTail.b4 e).2 (P.msg m) h4⟩

/-- The four clauses at a record whose two outputs are trueOut and honOut: terms_bill_first is
applied, and both its ledgers are shown to hold. -/
theorem terms_at_parts_first (Y : LateLay Nm J₂) (ι : TermsNm → Nm)
    (fm : Nm → TWhole.Aff E P.J) (p : (P.layVF W).toTail.Parts) (m : M)
    (a3 : P.tp.tm.toSum.T.par.Out) (a4 : P.ip.inn.toSum.T.par.Out) (heps : a3.eps ≠ 0)
    (h3 : p.o3 = trueOut P.tp a3 (P.msg m))
    (h4 : p.o4 = honOut P.ip.inn.toSum.T.par a4 (P.msg m))
    (hfm : ∀ x : TermsNm, x.InR P.D → fm (ι x) =
      toAff (termsFm P.rd P.D (termsEAt P.tp (trueOut P.tp a3 (P.msg m))).rt x))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.row ν n)))
    (gC : ∀ l k, l < P.D.ne → k < 3 → Y.good (ι (.sc l k)))
    (gS : ∀ l x k, l < P.D.ne → x < P.D.nx → k < 1 → Y.good (ι (.sel l x k))) :
    (P.layVF W).toTail.s3.Lc p.b2 p.r3 m ∧ (P.layVF W).toTail.ow3 p.b3 m ∧
      (P.layVF W).toTail.s4.Lc (p.b3, p.c4) p.r4 m ∧ (P.layVF W).toTail.ow4 p.b4 m :=
  terms_bill_first P W Y ι fm p.e m (by show p.o3.eps ≠ 0; rw [h3]; exact heps)
    (by
      show ∀ x : TermsNm, x.InR P.D → fm (ι x) = toAff (termsFm P.rd P.D (termsEAt P.tp p.o3).rt x)
      rw [h3]
      exact hfm)
    gR gC gS
    (by
      show TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (termsLed P.tp (readsT Y ι) p.o3)) _
      rw [h3]
      exact terms_meets P.toOwnPar Y ι fm a3 m hfm gR gC gS)
    (by
      show TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (stackLed P.ip p.o4)) _
      rw [h4]
      exact stack_meets P.toOwnPar (lateA Y fm) a4 m)

end Cb.Pv.Lay.End

#print axioms Cb.Pv.Lay.End.terms_bill_first
#print axioms Cb.Pv.Lay.End.terms_at_parts_first
