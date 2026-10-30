-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/CarriagePartsFirst.lean: THE FIELD `ledger` OF `Plan4F.HeardL`
(Johnson/Road/K4/CarriageFirst.lean), CUT INTO THE LIBRARY's NINE PARTS, EACH SAID WITHOUT THE
PULL-BACK: Johnson/Road/K4/CarriageParts.lean for the first layers' sub-proof. Two definitions and
one theorem. Bookkeeping.

The first chain's ledger `clFirst` (Cb/Pv/Lay/End/LayFirst.lean) has eleven parts. Two are letters
there (look, planes): here they are empty. The part emb holds the claim on the stream that comes in.

  `noRest2`: the two letters, empty.
  `lateAtF P Y fm e m`: the late entries at their forms' values.
  `ledgerF_of_parts`: if each of the nine parts sq, bat, led, terms, gated, hot, emb, stack, merge
    of `clFirst … e` holds of `Sum.elim (P.msg m) (lateAtF P Y fm e m)`, the pull-back of the whole
    ledger holds of `P.msg m`.

Limits. An implication between statements on lists of forms. That a program's claims give any part
is not said here.
-/
import Cb.Pv.Lay.End.LayFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullFPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Y : LateLay Nm J₂)

/-- The two parts of the ledger that are letters in the library's theorem, empty. -/
def noRest2 (_ : (tailW P).s7.Nx) : Rest2 E (P.J ⊕ J₂) := ⟨[], []⟩

/-- The late entries, each at its form's value. -/
noncomputable def lateAtF (fm : (tailW P).s7.Nx → Nm → TWhole.Aff E P.J) (e : (tailW P).s7.Nx)
    (m : M) : J₂ → E := fun i => (lateA Y (fm e) i).val (P.msg m)

variable {Y} {ιN : NormsNm → Nm} {ιT : TermsNm → Nm} {ιG : GatedNm → Nm} {ιE : EmbNm → Nm}

/-- **The whole ledger's pull-back, from its nine parts.** -/
theorem ledgerF_of_parts (fm : (tailW P).s7.Nx → Nm → TWhole.Aff E P.J)
    (zt : (tailW P).s7.Nx → ℕ → E) (b B sG : ℕ) (e : (tailW P).s7.Nx) (m : M)
    (hsq : Ledger.Holds (clFirst P Y ιN ιT ιG ιE (noRest2 P) zt b B sG e).sq
      (Sum.elim (P.msg m) (lateAtF P Y fm e m)))
    (hbat : Ledger.Holds (clFirst P Y ιN ιT ιG ιE (noRest2 P) zt b B sG e).bat
      (Sum.elim (P.msg m) (lateAtF P Y fm e m)))
    (hled : Ledger.Holds (clFirst P Y ιN ιT ιG ιE (noRest2 P) zt b B sG e).led
      (Sum.elim (P.msg m) (lateAtF P Y fm e m)))
    (hterms : Ledger.Holds (clFirst P Y ιN ιT ιG ιE (noRest2 P) zt b B sG e).terms
      (Sum.elim (P.msg m) (lateAtF P Y fm e m)))
    (hgated : Ledger.Holds (clFirst P Y ιN ιT ιG ιE (noRest2 P) zt b B sG e).gated
      (Sum.elim (P.msg m) (lateAtF P Y fm e m)))
    (hhot : Ledger.Holds (clFirst P Y ιN ιT ιG ιE (noRest2 P) zt b B sG e).hot
      (Sum.elim (P.msg m) (lateAtF P Y fm e m)))
    (hemb : Ledger.Holds (clFirst P Y ιN ιT ιG ιE (noRest2 P) zt b B sG e).emb
      (Sum.elim (P.msg m) (lateAtF P Y fm e m)))
    (hstack : Ledger.Holds (clFirst P Y ιN ιT ιG ιE (noRest2 P) zt b B sG e).stack
      (Sum.elim (P.msg m) (lateAtF P Y fm e m)))
    (hmerge : Ledger.Holds (clFirst P Y ιN ιT ιG ιE (noRest2 P) zt b B sG e).merge
      (Sum.elim (P.msg m) (lateAtF P Y fm e m))) :
    Ledger.Holds (pullL (lateA Y (fm e))
      (clFirst P Y ιN ιT ιG ιE (noRest2 P) zt b B sG e).all) (P.msg m) := by
  have h0 : Ledger.Holds (pullL (lateA Y (fm e)) ([] : Ledger E (P.J ⊕ J₂))) (P.msg m) :=
    fun _ hf => absurd hf (List.not_mem_nil)
  exact (holds_all _ _ _).2 ⟨h0, (pullL_holds _ _ _).2 hsq, (pullL_holds _ _ _).2 hbat,
    (pullL_holds _ _ _).2 hled, (pullL_holds _ _ _).2 hterms, (pullL_holds _ _ _).2 hgated,
    (pullL_holds _ _ _).2 hhot, h0, (pullL_holds _ _ _).2 hemb, (pullL_holds _ _ _).2 hstack,
    (pullL_holds _ _ _).2 hmerge⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ledgerF_of_parts
