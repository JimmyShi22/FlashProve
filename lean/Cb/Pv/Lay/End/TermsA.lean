-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/TermsA.lean: the late entries that the claims on the end values of the sumcheck of the
terms read, as forms on the early entries; the tables are true of them; and what the pull-back of
the ledger then pays.

The link of a sub-proof takes the late entries through forms on the early entries
(Cb/Sub/Late.lean: pullL). This file writes these forms for the three kinds of late entries that
termsCl (Cb/Pv/Lay/End/TermsCl.lean) reads: each is the extension, at the end point of the sumcheck
of the terms, of one cell over the positions. With each late entry at the value of its form the
tables are true (TermsTrue). So that premise of Cb/Pv/Lay/End/TermsPay.lean falls away, and the
ledger enters by its pull-back.

Main names:
  `TermsNm`, `TermsNm.InR`, `termsFm`: the names of the late entries, which of them are in range,
  and what each is meant to be.
  `readsT`: the late entries of these names. `termsLed`: the claims as a ledger.
  `terms_true`: TermsTrue, with each late entry at the value of its form.
  `terms_pull`: if the pull-back of termsLed holds of the early entries, the output rows on all end
  values of the sumcheck of the terms hold.
Limits: rd is asked to be linear in the entries. That the programs' late message has these entries
at these places is not said here, nor that the smallness test gives agreement with these forms. The
names of all parts of a sub-proof are a letter Nm, into which TermsNm is laid by a map. The forms
are asked at the names in range alone (TermsNm.InR): so the map may send a name out of range
wherever it likes, also onto another name's entry.


-/
import Cb.Pv.Lay.End.NormsA
import Cb.Pv.Lay.End.TermsPay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell)
open Blocks (Form)

/-- The names of the late entries that termsCl reads: cell n of the ledger of norm ν; cell k of the
score of routed layer l; cell k of entry x of its selector; all at the end point. -/
inductive TermsNm
  | row (ν n : ℕ)
  | sc (l k : ℕ)
  | sel (l x k : ℕ)

/-- The names in range: those that termsCl reads at the sizes D. -/
def TermsNm.InR (D : Dim) : TermsNm → Prop
  | .row ν n => ν < D.nNu ∧ n < 99
  | .sc l k => l < D.ne ∧ k < 3
  | .sel l x k => l < D.ne ∧ x < D.nx ∧ k < 1

/-- What the late entry of a name is meant to be. -/
def termsFm {E J : Type} [Field E] [DecidableEq J] (rd : (J → E) → Cell → E) (D : Dim)
    (rt : ℕ → E) : TermsNm → Form J E
  | .row ν n => extF rd D.lT (fun p => ⟨.D, 0, ν, n, p⟩) rt
  | .sc l k => extF rd D.lT (fun p => ⟨.sc, k, l, 0, p⟩) rt
  | .sel l x k => extF rd D.lT (fun p => ⟨.sel, k, l, x, p⟩) rt

/-- The late entries that termsCl reads. -/
def readsT {Nm J₂ : Type} (Y : LateLay Nm J₂) (ι : TermsNm → Nm) : TermsReads J₂ where
  uRow ν n := Y.at' (ι (.row ν n))
  uSc l k := Y.at' (ι (.sc l k))
  uSel l x k := Y.at' (ι (.sel l x k))

variable {E : Type} [Field E] [Fintype E] [scl : Scl] (P : TermPar0 E) {Nm J₂ : Type}
  [Fintype J₂] [DecidableEq P.J] [DecidableEq J₂]

/-- The claims on the end values as a ledger. -/
noncomputable def termsLed (U : TermsReads J₂) (o : P.tm.toSum.T.par.Out) :
    TWhole.Ledger E (P.J ⊕ J₂) :=
  ledOf (termsCl (namesT P U) (termsEAt P o) P.D)

omit [Fintype J₂] [DecidableEq J₂] in
/-- With each late entry at the value of its form, the tables are true. -/
theorem terms_true
    (hrd : ∀ (a b : E) (m m' : P.J → E) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (Y : LateLay Nm J₂) (ι : TermsNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (o : P.tm.toSum.T.par.Out)
    (hfm : ∀ x : TermsNm, x.InR P.D → fm (ι x) = toAff (termsFm P.rd P.D (termsEAt P o).rt x))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.row ν n)))
    (gC : ∀ l k, l < P.D.ne → k < 3 → Y.good (ι (.sc l k)))
    (gS : ∀ l x k, l < P.D.ne → x < P.D.nx → k < 1 → Y.good (ι (.sel l x k))) (m : P.J → E) :
    TermsTrue (namesT P (readsT Y ι)) (termsEAt P o) P.D (P.rd m)
      (Sum.elim m fun j => (lateA Y fm j).val m) := by
  have key : ∀ x : TermsNm, x.InR P.D → Y.good (ι x) → (lateA Y fm (Y.at' (ι x))).val m =
      Form.val m (termsFm P.rd P.D (termsEAt P o).rt x) := fun x hr hx => by
    unfold lateA
    rw [Y.ok _ hx, hfm _ hr, toAff_val]
  refine ⟨fun ν n h1 h2 => ?_, fun l k h1 h2 => ?_, fun l x k h1 h2 h3 => ?_⟩
  · show (lateA Y fm (Y.at' (ι (.row ν n)))).val m = _
    rw [key (.row ν n) ⟨h1, h2⟩ (gR ν n h1 h2)]
    exact val_extF P.rd hrd m _ _ _
  · show (lateA Y fm (Y.at' (ι (.sc l k)))).val m = _
    rw [key (.sc l k) ⟨h1, h2⟩ (gC l k h1 h2)]
    exact val_extF P.rd hrd m _ _ _
  · show (lateA Y fm (Y.at' (ι (.sel l x k)))).val m = _
    rw [key (.sel l x k) ⟨h1, h2, h3⟩ (gS l x k h1 h2 h3)]
    exact val_extF P.rd hrd m _ _ _

/-- The output rows on all end values of the sumcheck of the terms, from the pull-back of the ledger
of the claims on them to the early entries. -/
theorem terms_pull
    (hrd : ∀ (a b : E) (m m' : P.J → E) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (Y : LateLay Nm J₂) (ι : TermsNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (o : P.tm.toSum.T.par.Out)
    (hfm : ∀ x : TermsNm, x.InR P.D → fm (ι x) = toAff (termsFm P.rd P.D (termsEAt P o).rt x))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.row ν n)))
    (gC : ∀ l k, l < P.D.ne → k < 3 → Y.good (ι (.sc l k)))
    (gS : ∀ l x k, l < P.D.ne → x < P.D.nx → k < 1 → Y.good (ι (.sel l x k))) (m : P.J → E)
    (h : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (termsLed P (readsT Y ι) o)) m) :
    ∀ a, P.tm.toSum.T.par.EHolds o m a :=
  terms_pay P (readsT Y ι) o m _ (terms_true P hrd Y ι fm o hfm gR gC gS m)
    ((ledOf_holds _ _).1 ((Cb.Sub.pullL_holds _ _ _).1 h))

end Cb.Pv.Lay.End

#print axioms Cb.Pv.Lay.End.terms_pull
