-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/CarriageParts.lean: THE FIELD `ledger` OF Johnson/Road/K4/CarriageLedger.lean, CUT
INTO THE LIBRARY's EIGHT PARTS, EACH SAID WITHOUT THE PULL-BACK. Two definitions and one theorem.
Bookkeeping.

The library's ledger of a layers' sub-proof has eleven parts (`LayCl`, Cb/Pv/Lay/End/LayEnd.lean).
Three are letters there (look, planes, emb): here they are empty, so that nothing is asked here of
the lookup's own claims, of the planes' and of the embedding's. The pull-back
of a ledger along the late entries' forms holds of the early entries exactly if the ledger holds of
the early entries with each late entry at its form's value (`pullL_holds`, Cb/Sub/Late.lean).

  `noRest3`: the three letters, empty.
  `lateAt P Y fm e m`: the late entries at their forms' values: i ↦ (lateA Y (fm e) i).val (msg m).
  `ledger_of_parts`: if each of the eight parts sq, bat, led, terms, gated, hot, stack, merge of
    `clAt … e` holds of `Sum.elim (P.msg m) (lateAt P Y fm e m)`, the pull-back of the whole ledger
    holds of `P.msg m`.

By definition (Cb/Pv/Lay/End/LayHEnd.lean's `clAt`, LayAll.lean's `restAt`) the eight parts are:
sqAt, batAt, rowsAt (the norms' three), termsLedAt, gatedLedOf, hotAt, stackLedAt, mergeLed.

Limits. An implication between statements on lists of forms. That a program's claims give any part
is not said here.
-/
import Cb.Pv.Lay.End.LayAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Y : LateLay Nm J₂)

/-- The three parts of the ledger that are letters in the library's theorem, empty. -/
def noRest3 (_ : (tailF P).s7.Nx) : Rest3 E (P.J ⊕ J₂) := ⟨[], [], []⟩

/-- The late entries, each at its form's value. -/
noncomputable def lateAt (fm : (tailF P).s7.Nx → Nm → TWhole.Aff E P.J) (e : (tailF P).s7.Nx)
    (m : M) : J₂ → E := fun i => (lateA Y (fm e) i).val (P.msg m)

variable {Y} {ιN : NormsNm → Nm} {ιT : TermsNm → Nm} {ιG : GatedNm → Nm}

/-- **The whole ledger's pull-back, from its eight parts.** -/
theorem ledger_of_parts (fm : (tailF P).s7.Nx → Nm → TWhole.Aff E P.J)
    (zt : (tailF P).s7.Nx → ℕ → E) (b B sG : ℕ) (e : (tailF P).s7.Nx) (m : M)
    (hsq : Ledger.Holds (clAt P.toOwnPar P.wPart Y ιN
      (restAt P Y ιT ιG (noRest3 P) sG) zt b B e).sq (Sum.elim (P.msg m) (lateAt P Y fm e m)))
    (hbat : Ledger.Holds (clAt P.toOwnPar P.wPart Y ιN
      (restAt P Y ιT ιG (noRest3 P) sG) zt b B e).bat (Sum.elim (P.msg m) (lateAt P Y fm e m)))
    (hled : Ledger.Holds (clAt P.toOwnPar P.wPart Y ιN
      (restAt P Y ιT ιG (noRest3 P) sG) zt b B e).led (Sum.elim (P.msg m) (lateAt P Y fm e m)))
    (hterms : Ledger.Holds (clAt P.toOwnPar P.wPart Y ιN
      (restAt P Y ιT ιG (noRest3 P) sG) zt b B e).terms (Sum.elim (P.msg m) (lateAt P Y fm e m)))
    (hgated : Ledger.Holds (clAt P.toOwnPar P.wPart Y ιN
      (restAt P Y ιT ιG (noRest3 P) sG) zt b B e).gated (Sum.elim (P.msg m) (lateAt P Y fm e m)))
    (hhot : Ledger.Holds (clAt P.toOwnPar P.wPart Y ιN
      (restAt P Y ιT ιG (noRest3 P) sG) zt b B e).hot (Sum.elim (P.msg m) (lateAt P Y fm e m)))
    (hstack : Ledger.Holds (clAt P.toOwnPar P.wPart Y ιN
      (restAt P Y ιT ιG (noRest3 P) sG) zt b B e).stack (Sum.elim (P.msg m) (lateAt P Y fm e m)))
    (hmerge : Ledger.Holds (clAt P.toOwnPar P.wPart Y ιN
      (restAt P Y ιT ιG (noRest3 P) sG) zt b B e).merge
      (Sum.elim (P.msg m) (lateAt P Y fm e m))) :
    Ledger.Holds (pullL (lateA Y (fm e))
      (clAt P.toOwnPar P.wPart Y ιN (restAt P Y ιT ιG (noRest3 P) sG) zt b B e).all)
      (P.msg m) := by
  have h0 : Ledger.Holds (pullL (lateA Y (fm e)) ([] : Ledger E (P.J ⊕ J₂))) (P.msg m) :=
    fun _ hf => absurd hf (List.not_mem_nil)
  exact (holds_all _ _ _).2 ⟨h0, (pullL_holds _ _ _).2 hsq, (pullL_holds _ _ _).2 hbat,
    (pullL_holds _ _ _).2 hled, (pullL_holds _ _ _).2 hterms, (pullL_holds _ _ _).2 hgated,
    (pullL_holds _ _ _).2 hhot, h0, h0, (pullL_holds _ _ _).2 hstack,
    (pullL_holds _ _ _).2 hmerge⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ledger_of_parts
