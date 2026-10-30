-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Earlier.lean: the kind "lookup" (K3): the library's sentences
on a form, a row and what a lookup heard, each said at a ledger (`Fo.FormIs`, `Fo.RowIs`,
OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean; `Fo.HeardIs`, OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean),
pass back from a later ledger to an earlier one at which the forms' slots are filled. So the
lookup's two sentences "row out" on the planes and on the keys pass on from an earlier ledger to a
later one. Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md ("ledger", "form", "slot"). In this file: G is later than F:
`Fo.Later F G` (FoForm.lean). A form's slots are filled at F: `Fo.FilledA F a`
(OnBytes/Tie/Pv/Lookup/Forest/FoEv.lean). `Fo.Tp.PadNames g F` (Johnson/Top/H/Keep/PadNamed.lean)
says of the four families of forms in what a lookup heard (the rows, the key side's end form, the
form on the bits' end slot, the leaves' start form) that each names no entry, and slots alone that
are there and filled at F. The binders `inc`, `r`, `En`, `h`, `lm`, `first`, `ν` and `Kv` are
written without a type: Lean takes each from the library's definition in which it stands.

What is shown.
  `getD_mem`: an array's entry below its size is a member of its list. (The library has this
    sentence, general in the type: `OnBytes.Params.getD_mem`, OnBytes/Params/Fit/TreesSites.lean;
    and the like at arrays of numbers: `Fo.Ret.getD_mem`, Johnson/Top/H/Ret/RetMessages.lean
    [not in this library]. Neither file stands among this file's import lines.)
  `formIs_earlier`, `rowIs_earlier`: from `Fo.Later F G`, `Fo.FilledA F` of the form, and the
    sentence at G: the sentence at F.
  `heardIs_earlier`: from `Fo.Later F G`, `PadNames g F` and `HeardIs ρ g G En`: `HeardIs ρ g F En`.
    It is the converse of the library's `heardIsLater` (Johnson/Top/H/K3LeftLater.lean), under
    `PadNames`.
  `k3OutPlanes_later`, `k3OutKeys_later`: from `Fo.Later F G` and `PadNames g F`: `K3OutPlanes` and
    `K3OutKeys` (Johnson/Top/H/K3RowOut.lean) at F give the same at G.
In the other direction, from a later ledger to an earlier one and without `PadNames`, the library
has `k3OutPlanes_back` and `k3OutKeys_back` (Johnson/Desc/First/Look/K3WorthStep.lean) and
`k3OutBack` (K3LeftLater.lean). The third item of the row out, `K3OutRows` (K3RowOut.lean), is not
carried on here.

Hypotheses that remain. `hL`: G is later than F. `hC` (in `formIs_earlier` and `rowIs_earlier`): the
form's slots are filled at F. `N` (in the last three): `PadNames g F`. `h` (in the three "earlier"):
the sentence at G. `H` (in the last two): the sentence at F. `hi` (in `getD_mem`): i is below the
size. By a reading of the definitions, not by Lean: without "filled at F" `formIs_earlier` and
`rowIs_earlier` fail in general, since a slot that is free at F can be filled otherwise on another
ledger later than F. No instance of that is exhibited.

How the proof goes. The sentence at G is taken at G itself (`Fo.Later.refl`); the library's
`value_later` and `publicPart_later` say that value and public part at G are those at F; `formIs_of`
and `rowIs_of` make the sentence at F of these (all in FoForm.lean). `HeardIs` names the ledger in
four fields alone. The conclusions of `K3OutPlanes` and `K3OutKeys` do not name the ledger.

Users. Honest/K3/Law/WorthOn.lean calls `k3OutPlanes_later` and `k3OutKeys_later`.

Limits. That `PadNames g F` holds at any ledger is not said here: Honest/K3/Law/NamedDigits.lean
shows it behind the seated lookup on the digits, under the hypotheses that its head lists. No
instance of the hypotheses together is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Top.H.K3RowOut
import Johnson.Top.H.Keep.K3Named

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes.Model (Fork Aff)

/-- An array's entry below its size is a member of its list. -/
theorem getD_mem {α : Type} (a : Array α) (d : α) {i : Nat} (hi : i < a.size) :
    a.getD i d ∈ a.toList := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  exact Array.getElem_mem_toList hi

variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

/-- **The sentence on a form passes back to an earlier ledger at which its slots are filled.** -/
theorem formIs_earlier {F G : Fork} {C : Aff} {tg : K} {inc} (hL : _root_.Fo.Later F G)
    (hC : _root_.Fo.FilledA F C) (h : _root_.Fo.FormIs ρ G C tg inc) :
    _root_.Fo.FormIs ρ F C tg inc :=
  _root_.Fo.formIs_of ρ hC
    (fun x hx => (h G (_root_.Fo.Later.refl G)).1 x ((_root_.Fo.publicPart_later hL C hC).trans hx))
    (fun mask entry => (_root_.Fo.value_later ρ hL C hC mask entry).symm.trans
      ((h G (_root_.Fo.Later.refl G)).2 mask entry))

/-- **The like of the sentence on a row.** -/
theorem rowIs_earlier {F G : Fork} {row : Aff} {r} (hL : _root_.Fo.Later F G)
    (hC : _root_.Fo.FilledA F row) (h : _root_.Fo.RowIs ρ G row r) : _root_.Fo.RowIs ρ F row r :=
  _root_.Fo.rowIs_of ρ hC fun mask entry =>
    (_root_.Fo.value_later ρ hL row hC mask entry).symm.trans
      (h G (_root_.Fo.Later.refl G) mask entry)

/-- **The sentence on what a lookup heard passes back to an earlier ledger at which its four
families of forms are filled.** -/
theorem heardIs_earlier {g : OnBytes.Model.Forest.Heard} {F G : Fork} {En}
    (hL : _root_.Fo.Later F G) (N : _root_.Fo.Tp.PadNames g F) (h : _root_.Fo.HeardIs ρ g G En) :
    _root_.Fo.HeardIs ρ g F En :=
  { h with
    rows := fun i hi => rowIs_earlier ρ hL (N.rows _ (getD_mem g.rows {} hi)).filledA (h.rows i hi)
    lvStart := formIs_earlier ρ hL N.start.filledA h.lvStart
    sBitAt := formIs_earlier ρ hL N.sBit.filledA h.sBitAt
    cEnd := formIs_earlier ρ hL N.cEnd.filledA h.cEnd }

/-- **"Row out" on the planes passes on to a later ledger, where the four families of forms in what
was heard are filled at the earlier one** (`N`). -/
theorem k3OutPlanes_later {h lm first ν} {g : OnBytes.Model.Forest.Heard} {F G : Fork}
    (hL : _root_.Fo.Later F G) (N : _root_.Fo.Tp.PadNames g F)
    (H : VerifiableInference.OnPublicFiles.K3OutPlanes h lm first ν ρ g F) :
    VerifiableInference.OnPublicFiles.K3OutPlanes h lm first ν ρ g G :=
  fun rs hI => H rs (heardIs_earlier ρ hL N hI)

/-- **"Row out" on the keys passes on to a later ledger, where the four families of forms in what
was heard are filled at the earlier one** (`N`). -/
theorem k3OutKeys_later {h lm first ν Kv} {g : OnBytes.Model.Forest.Heard} {F G : Fork}
    (hL : _root_.Fo.Later F G) (N : _root_.Fo.Tp.PadNames g F)
    (H : VerifiableInference.OnPublicFiles.K3OutKeys h lm first ν Kv ρ g F) :
    VerifiableInference.OnPublicFiles.K3OutKeys h lm first ν Kv ρ g G :=
  fun rs hI => H rs (heardIs_earlier ρ hL N hI)

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.getD_mem
#print axioms ProofFile.Honest.K3.Law.formIs_earlier
#print axioms ProofFile.Honest.K3.Law.rowIs_earlier
#print axioms ProofFile.Honest.K3.Law.heardIs_earlier
#print axioms ProofFile.Honest.K3.Law.k3OutPlanes_later
#print axioms ProofFile.Honest.K3.Law.k3OutKeys_later
