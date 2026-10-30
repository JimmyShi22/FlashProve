-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/TermsBillAt.lean: the four clauses of the sumcheck of the terms and of the batched
sumcheck in what the chain of a layers' sub-proof's own rounds owes at its end, at the chain's
value, from the pull-backs of two parts of the ledger.

Cb/Pv/Lay/At/Own.lean has the chain of the own rounds of a layers' sub-proof that is not the first,
at the library's description. Cb/Pv/Lay/End/Last.lean writes what a chain owes at its end as a
record, LayTail.Bill. This file reads the two sumchecks' outputs off a last statement e of that
chain and pays the record's fields o3 and o4 (c3 and c4 are True at this chain).

Main names:
  `tailT`: the chain's letters. `termsLedAt`, `stackLedAt`: the two parts of the ledger, off e.
  `terms_bill`: the four fields.
Limits. The ledgers say no more than the rows (terms_pull_iff in Cb/Pv/Lay/End/TermsIff.lean,
stack_pull_iff in Cb/Pv/Lay/End/StackIff.lean): a change of words. What bears on soundness lies in
what is left open here: that the link's late forms are these, and that the lists are the programs'.
heps: the coefficient drawn in the sumcheck of the terms, inside e, is not 0; it is the first half
of o3. No ledger pays it. It comes from a test of the last statement that is laid behind the chain
(LayVO.epsOK in Cb/Pv/Lay/OwnTest.lean). hfm and the three conditions on good names: the late
entries' names and forms, as in Cb/Pv/Lay/End/TermsA.lean. The three claims of stackLedAt are
written on the early entries (Cb/Pv/Lay/End/StackA.lean). That either part of the ledger is a
program's is not said here. The other fourteen fields of the record are not paid here.


-/
import Cb.Pv.Lay.At.Own
import Cb.Pv.Lay.End.Last
import Cb.Pv.Lay.End.TermsA
import Cb.Pv.Lay.End.StackA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : OwnPar E M X)
  (W : P.WPart) {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂]

/-- The letters of the chain behind the token point. -/
noncomputable abbrev tailT : LayTail E M P.XT := (P.layV W).toTail

/-- The claims on the end values of the sumcheck of the terms, off a last statement of the chain. -/
noncomputable def termsLedAt (Y : LateLay Nm J₂) (ι : TermsNm → Nm) (e : (tailT P W).s7.Nx) :
    TWhole.Ledger E (P.J ⊕ J₂) :=
  termsLed P.tp (readsT Y ι) ((tailT P W).b3 e).2

/-- The three claims on the batched sumcheck's output, off a last statement of the chain. -/
noncomputable def stackLedAt (e : (tailT P W).s7.Nx) : TWhole.Ledger E (P.J ⊕ J₂) :=
  stackLed P.ip ((tailT P W).b4 e).2

/-- The four fields of the chain's bill that belong to the sumcheck of the terms and to the batched
sumcheck. -/
theorem terms_bill (Y : LateLay Nm J₂) (ι : TermsNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (e : (tailT P W).s7.Nx) (m : M) (heps : ((tailT P W).b3 e).2.eps ≠ 0)
    (hfm : ∀ x : TermsNm, x.InR P.D → fm (ι x) =
      toAff (termsFm P.rd P.D (termsEAt P.tp ((tailT P W).b3 e).2).rt x))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.row ν n)))
    (gC : ∀ l k, l < P.D.ne → k < 3 → Y.good (ι (.sc l k)))
    (gS : ∀ l x k, l < P.D.ne → x < P.D.nx → k < 1 → Y.good (ι (.sel l x k)))
    (h3 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (termsLedAt P W Y ι e)) (P.msg m))
    (h4 : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (stackLedAt P W e)) (P.msg m)) :
    (tailT P W).s3.Lc ((tailT P W).b3 e).1.1 ((tailT P W).b3 e).1.2 m ∧
      (tailT P W).ow3 ((tailT P W).b3 e) m ∧
      (tailT P W).s4.Lc ((tailT P W).b4 e).1.1 ((tailT P W).b4 e).1.2 m ∧
      (tailT P W).ow4 ((tailT P W).b4 e) m :=
  ⟨trivial,
    ⟨heps, terms_pull P.tp P.hrd Y ι fm ((tailT P W).b3 e).2 hfm gR gC gS (P.msg m) h3⟩,
    trivial, stack_pull P.ip P.hrd (lateA Y fm) ((tailT P W).b4 e).2 (P.msg m) h4⟩

end Cb.Pv.Lay.End

#print axioms Cb.Pv.Lay.End.terms_bill
