-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsBillAt.lean: the six clauses of the norms' two stretches in what the chain of a
layers' sub-proof's own rounds owes at its end, at the chain's value, from the pull-back of the
ledger of the verifier's claims on the norms.

Cb/Pv/Lay/At/Own.lean has the chain of the own rounds of a layers' sub-proof that is not the first,
at the library's description (P.layV W, P.layVO W). Cb/Pv/Lay/End/Last.lean writes what a chain owes
at its end as a record, LayTail.Bill. This file reads the letters of the claims on the norms off a
last statement e of that chain and pays the record's fields lL, o1, lP, c2, o2 (c1 is True at this
chain).

Main definitions: tailAt (the chain's letters), eAt (the letters of the claims, off e), ledAt (the
ledger of the claims on the norms, off e). Main theorems: norms_bill; hst_run (its premise hst holds
in the last statement of a run).

Limits. hst: the state that the first sumcheck's output inside e carries holds the element drawn
inside e; of a last statement that is no run's it need not hold. zt, the tail of the lookup's
point, is a letter. hfm, the g's: the late entries' names and forms, as in
Cb/Pv/Lay/End/NormsA.lean. That the ledger is a program's is not said here. The other twelve fields
of the record are not paid here.


-/
import Cb.Pv.Lay.At.Own
import Cb.Pv.Lay.End.Last
import Cb.Pv.Lay.End.NormsA
import Cb.Pv.Lay.End.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : OwnPar E M X)
  (W : P.WPart) {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂]

/-- The letters of the chain behind the token point. -/
noncomputable abbrev tailAt : LayTail E M P.XT := (P.layV W).toTail

/-- The letters of the claims on the norms, off a last statement of the chain. -/
noncomputable def eAt (e : (tailAt P W).s7.Nx) (zt : ℕ → E) : NormsE E :=
  normsEAt P.nr ((tailAt P W).xL e).2 ((tailAt P W).b1 e).1.1.1.1.2 ((tailAt P W).b1 e).1.1.1.2
    ((tailAt P W).b1 e).2 ((tailAt P W).b2 e).1.1.1.2 ((tailAt P W).b2 e).1.1.2
    (@id (Fin 1 → E) ((tailAt P W).b2 e).1.2 0) ((tailAt P W).b2 e).2 zt

/-- The ledger of the claims on the norms, off a last statement of the chain. -/
noncomputable def ledAt (Y : LateLay Nm J₂) (ι : NormsNm → Nm) (e : (tailAt P W).s7.Nx)
    (zt : ℕ → E) (b B : ℕ) : TWhole.Ledger E (P.J ⊕ J₂) :=
  normsLed (namesAt P.nr (readsAt Y ι)) (eAt P W e zt) (u1At P.nr ((tailAt P W).b1 e).2)
    (u2At P.nr ((tailAt P W).b2 e).2) P.D (P.D.lL + 1) b B

/-- The six fields of the chain's bill that belong to the norms; c1 is True at this chain. -/
theorem norms_bill (Y : LateLay Nm J₂) (ι : NormsNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (e : (tailAt P W).s7.Nx) (zt : ℕ → E) (m : M) (b s B : ℕ) (hl : lDd P.D = b + s)
    (hd : P.D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b)
    (hst : ((tailAt P W).b1 e).2.st.1.2 = ((tailAt P W).b1 e).1.1.1.2)
    (hfm : ∀ x, InRange P.D.nNu B P.D.ne P.D.nx x →
      fm (ι x) = toAff (normsFm P.rd P.D (eAt P W e zt) (P.D.lL + 1) b s x))
    (gXi : ∀ ν l kh, ν < P.D.nNu → l < 5 → kh < B → Y.good (ι (.xi ν l kh)))
    (gP : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atP ν n)))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atR ν n)))
    (gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (ι (.sel l x)))
    (h : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (ledAt P W Y ι e zt b B)) (P.msg m)) :
    (tailAt P W).lL ((tailAt P W).xL e) ((tailAt P W).b1 e).1.1.1.1.2 m ∧
      (tailAt P W).s1.Lc ((tailAt P W).b1 e).1.1 ((tailAt P W).b1 e).1.2 m ∧
      (tailAt P W).ow1 ((tailAt P W).b1 e) m ∧
      (tailAt P W).lP ((tailAt P W).xP e) ((tailAt P W).b2 e).1.1.1.2 m ∧
      (tailAt P W).s2.Lc ((tailAt P W).b2 e).1.1 ((tailAt P W).b2 e).1.2 m ∧
      (tailAt P W).ow2 ((tailAt P W).b2 e) m := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := norms_pull P.nr P.hrd Y ι fm ((tailAt P W).xL e).2
    ((tailAt P W).b1 e).1.1.1.1.2 ((tailAt P W).b1 e).1.1.1.2 ((tailAt P W).b1 e).2
    ((tailAt P W).b2 e).1.1.1.2 ((tailAt P W).b2 e).1.1.2
    (@id (Fin 1 → E) ((tailAt P W).b2 e).1.2 0)
    ((tailAt P W).b2 e).2 zt (P.msg m) b s B hl hd hB hst hfm gXi gP gR gS h
  exact ⟨a1, trivial, a2, a3, a4, a5⟩

/-- In the last statement of a run the premise hst of norms_bill holds. -/
theorem hst_run (x : P.XT) (ts : (tailAt P W).ch.Trs) :
    ((tailAt P W).b1 ((tailAt P W).ch.run x ts)).2.st.1.2 =
      ((tailAt P W).b1 ((tailAt P W).ch.run x ts)).1.1.1.2 := by
  rw [st1_run]
  rfl

end Cb.Pv.Lay.End
