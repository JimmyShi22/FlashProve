-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/TermsMeet.lean: at any value of the letters of the chain of a layers' sub-proof's own
rounds, and any entries, there are outputs of the sumcheck of the terms and of the batched sumcheck
at which the two parts of the ledger hold; and the four clauses of the chain's bill in the parts of
a last statement.

Cb/Pv/Lay/End/TermsBillAt.lean pays four clauses of the chain's bill from the pull-backs of two
parts of the ledger. This file shows that these two premises can be met, whatever the cells are: at
the output trueOut (Cb/Pv/Lay/End/TermsIff.lean) and at the output honOut
(Cb/Pv/Lay/End/HonOut.lean). It also says terms_bill on a record of parts
(Cb/Pv/Lay/End/Parts.lean), so that no nest of pairs has to be unfolded at a value.

Main names:
  `terms_meets`: the pull-back of the claims on the end values holds at trueOut.
  `stack_meets`: the pull-back of the three claims on the batched sumcheck's output holds at honOut.
  `terms_parts`: the clauses c3, o3, c4, o4 in the parts of a last statement.
  `terms_at_parts`: the same at a record whose two outputs are trueOut and honOut: no ledger is a
  premise any more.
Limits: rd is asked to be linear in the entries; the drawn coefficient of the first output is asked
not to be 0; the late entries' names and forms are as in Cb/Pv/Lay/End/TermsA.lean.


-/
import Cb.Pv.Lay.End.Parts
import Cb.Pv.Lay.End.TermsIff
import Cb.Pv.Lay.End.StackIff
import Cb.Pv.Lay.End.TermsBillAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : OwnPar E M X)
  (W : P.WPart) {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂]

/-- The pull-back of the claims on the end values of the sumcheck of the terms holds at the output
with the true masked values. -/
theorem terms_meets (Y : LateLay Nm J₂) (ι : TermsNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (o : P.tp.tm.toSum.T.par.Out) (m : M)
    (hfm : ∀ x : TermsNm, x.InR P.D → fm (ι x) =
      toAff (termsFm P.rd P.D (termsEAt P.tp (trueOut P.tp o (P.msg m))).rt x))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.row ν n)))
    (gC : ∀ l k, l < P.D.ne → k < 3 → Y.good (ι (.sc l k)))
    (gS : ∀ l x k, l < P.D.ne → x < P.D.nx → k < 1 → Y.good (ι (.sel l x k))) :
    TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm)
      (termsLed P.tp (readsT Y ι) (trueOut P.tp o (P.msg m)))) (P.msg m) :=
  (terms_pull_iff P.tp P.hrd Y ι fm _ hfm gR gC gS (P.msg m)).2 (trueOut_ev P.tp o (P.msg m))

/-- The pull-back of the three claims on the batched sumcheck's output holds at the output at which
all output claims hold. -/
theorem stack_meets (a : J₂ → TWhole.Aff E P.J) (o : P.ip.inn.toSum.T.par.Out) (m : M) :
    TWhole.Ledger.Holds
      (Cb.Sub.pullL a (stackLed P.ip (honOut P.ip.inn.toSum.T.par o (P.msg m)))) (P.msg m) :=
  (stack_pull_iff P.ip P.hrd a _ (P.msg m)).2
    ⟨(honOut_holds _ o (P.msg m)).1, (honOut_holds _ o (P.msg m)).2 _,
      (honOut_holds _ o (P.msg m)).2 _⟩

/-- The four clauses in the parts of a last statement. -/
theorem terms_parts (Y : LateLay Nm J₂) (ι : TermsNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (p : (tailT P W).Parts) (m : M) (heps : p.o3.eps ≠ 0)
    (hfm : ∀ x : TermsNm, x.InR P.D → fm (ι x) = toAff (termsFm P.rd P.D (termsEAt P.tp p.o3).rt x))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.row ν n)))
    (gC : ∀ l k, l < P.D.ne → k < 3 → Y.good (ι (.sc l k)))
    (gS : ∀ l x k, l < P.D.ne → x < P.D.nx → k < 1 → Y.good (ι (.sel l x k)))
    (h3 : TWhole.Ledger.Holds
      (Cb.Sub.pullL (lateA Y fm) (termsLed P.tp (readsT Y ι) p.o3)) (P.msg m))
    (h4 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (stackLed P.ip p.o4)) (P.msg m)) :
    (tailT P W).s3.Lc p.b2 p.r3 m ∧ (tailT P W).ow3 p.b3 m ∧
      (tailT P W).s4.Lc (p.b3, p.c4) p.r4 m ∧ (tailT P W).ow4 p.b4 m :=
  terms_bill P W Y ι fm p.e m heps hfm gR gC gS h3 h4

/-- The four clauses at a record whose two outputs are trueOut and honOut: no ledger is a premise
any more: terms_bill is applied, and both its ledgers are shown to hold. -/
theorem terms_at_parts (Y : LateLay Nm J₂) (ι : TermsNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (p : (tailT P W).Parts) (m : M) (a3 : P.tp.tm.toSum.T.par.Out)
    (a4 : P.ip.inn.toSum.T.par.Out) (heps : a3.eps ≠ 0)
    (h3 : p.o3 = trueOut P.tp a3 (P.msg m))
    (h4 : p.o4 = honOut P.ip.inn.toSum.T.par a4 (P.msg m))
    (hfm : ∀ x : TermsNm, x.InR P.D → fm (ι x) =
      toAff (termsFm P.rd P.D (termsEAt P.tp (trueOut P.tp a3 (P.msg m))).rt x))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.row ν n)))
    (gC : ∀ l k, l < P.D.ne → k < 3 → Y.good (ι (.sc l k)))
    (gS : ∀ l x k, l < P.D.ne → x < P.D.nx → k < 1 → Y.good (ι (.sel l x k))) :
    (tailT P W).s3.Lc p.b2 p.r3 m ∧ (tailT P W).ow3 p.b3 m ∧
      (tailT P W).s4.Lc (p.b3, p.c4) p.r4 m ∧ (tailT P W).ow4 p.b4 m :=
  terms_parts P W Y ι fm p m (by rw [h3]; exact heps) (by rw [h3]; exact hfm) gR gC gS
    (by rw [h3]; exact terms_meets P Y ι fm a3 m hfm gR gC gS)
    (by rw [h4]; exact stack_meets P (lateA Y fm) a4 m)

end Cb.Pv.Lay.End

#print axioms Cb.Pv.Lay.End.terms_at_parts
#print axioms Cb.Pv.Lay.End.terms_meets
#print axioms Cb.Pv.Lay.End.stack_meets
#print axioms Cb.Pv.Lay.End.terms_parts
