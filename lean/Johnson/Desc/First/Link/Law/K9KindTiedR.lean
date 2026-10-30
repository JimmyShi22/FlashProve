-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K9KindTiedR.lean: THE BATCHING KIND's SHARE OF THE CHAIN OF PROMISES, IN
THE SECOND FORM, IN THE VERY TERMS IN WHICH THE KINDS' SHARES ARE JOINED (`KindTiedR … .K9`,
Johnson/Desc/Sound/TiedR.lean): «every piece that stands at a place of the kind K9, with the table's
extractor at that number, is tied there». From one list of debts a link (`LinkAsksR`,
LinkTiedEachR.lean: it pays the batching's place and the one equation's), one a shutting
(`ShutAsksR`), and a Bool on the written list («a place of the kind K9 is a link's batching, its one
equation or its shutting»). Definitions, a theorem, evaluations.

What is said.
  `batchAt links pl m`: the number, in the list, of link m's batching. `k9At`, `k9Fit links pl`: the
    Bool. `k9_at`: the fact at a place. `k9Fit_full`: the kernel's yes at the full list.
    `k9Count_full`: 75 places of the full list are of the kind K9. `k9Fit_bent`: a negative test:
    the first segment's one equation and the sub-protocol behind it changed over: no. `ShutAsksR`:
    all that `shut_tied_pubR` takes, the letters under «there are». `k9_kindTiedR`: **`KindTiedR Nm
    Mg links pl Rch E pcs .K9`.**

Limits. BOOK-KEEPING: AN IMPLICATION. `LinkAsksR` and `ShutAsksR` at every link ARE THE DEBTS:
nothing is paid here. The place of the frame's sub-protocol behind the batching is of another kind:
`behind_tied_eachR` serves it from the same list. Rch, the table's letters and the list of pieces
are free. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTiedEachR
import Johnson.Desc.First.Link.Law.LinkPlacesFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Where atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers flatPlacesOf)
open _root_.Run (ckP)

/-- The number, in the list, of link m's batching. -/
def batchAt (links : List ModelPart) (pl : List Place) (m : ℕ) : ℕ :=
  pl.findIdx fun p => p.link == some m && p.piece == hearN links m + 1

/-- **The test at number i of the list**: a place of the kind K9 is a link's batching, its one
equation or its shutting. -/
def k9At (links : List ModelPart) (pl : List Place) (i : ℕ) : Bool :=
  match pl[i]? with
  | some p =>
    if p.kind == .K9 then
      match p.link with
      | some m => decide (m < links.length) && decide (batchAt links pl m + 4 < pl.length) &&
          (i == batchAt links pl m || i == batchAt links pl m + 2 || i == batchAt links pl m + 4)
      | none => false
    else true
  | none => true

/-- **The test along the list.** -/
def k9Fit (links : List ModelPart) (pl : List Place) : Bool := (List.range pl.length).all (k9At links pl)

/-- **THE FACT AT A PLACE.** -/
theorem k9_at (links : List ModelPart) (pl : List Place) (h : k9Fit links pl = true) (i : ℕ) (p : Place)
    (hp : pl[i]? = some p) (hk : p.kind = .K9) :
    ∃ m, m < links.length ∧ batchAt links pl m + 4 < pl.length ∧
      (i = batchAt links pl m ∨ i = batchAt links pl m + 2 ∨ i = batchAt links pl m + 4) := by
  unfold k9Fit at h
  rw [List.all_eq_true] at h
  have h0 := h i (List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1)
  unfold k9At at h0
  rw [hp] at h0
  simp only [hk, beq_self_eq_true, if_true] at h0
  cases hl : p.link with
  | none => simp [hl] at h0
  | some m =>
    simp only [hl, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h0
    exact ⟨m, h0.1.1, h0.1.2, by
      rcases h0.2 with (e | e) | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr e)⟩

set_option maxRecDepth 1000000 in
/-- **THE YES AT THE FULL LIST.** -/
theorem k9Fit_full : k9Fit fullList (flatPlacesOf fullList true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **75 PLACES OF THE FULL LIST ARE OF THE KIND K9.** -/
theorem k9Count_full :
    ((flatPlacesOf fullList true).filter fun p => p.kind == .K9).length = 75 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A NEGATIVE TEST: THE FIRST SEGMENT's ONE EQUATION AND THE SUB-PROTOCOL BEHIND IT CHANGED
OVER** (numbers 11 and 12 of the list). -/
theorem k9Fit_bent : k9Fit fullList (swapAt (flatPlacesOf fullList true) 11) = false := by
  decide +kernel

variable {P W : Type} {F : Frame}

/-- **ALL THAT THE SHUTTING's TIE TAKES, THE LETTERS UNDER «THERE ARE».** -/
def ShutAsksR (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (Rch : ℕ → (P × S) × F.E.Str → Prop) (k : ℕ) (qs : Piece (ckP .two) F (P × S) Claim W)
    (Es : (P × S) × F.E.Str → (P × S) × F.E.Str → W → W) : Prop :=
  ∃ (pw : Where) (piece : ℕ) (b₅ : Block S Claim),
    qs.b = (below b₅).lift Prod.snd (fun t s => (t.1, s)) ∧ (∀ a b w, Es a b w = w) ∧
    ∀ z, ShutOwesR Nm Mg links pl (RchAt Rch z) z k pw piece b₅ (atRec qs (below b₅))

/-- **THE BATCHING KIND's SHARE OF THE CHAIN OF PROMISES, SECOND FORM.** -/
theorem k9_kindTiedR (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (Rch : ℕ → (P × S) × F.E.Str → Prop)
    (E : ℕ → (P × S) × F.E.Str → (P × S) × F.E.Str → W → W)
    (pcs : List (Piece (ckP .two) F (P × S) Claim W)) (hfit : k9Fit links pl = true)
    (hlen : pl.length ≤ pcs.length)
    (HL : ∀ m < links.length, ∀ qb qq qe, pcs[batchAt links pl m]? = some qb →
      pcs[batchAt links pl m + 1]? = some qq → pcs[batchAt links pl m + 1 + 1]? = some qe →
      LinkAsksR Nm Mg links pl Rch (batchAt links pl m) qb qq qe (E (batchAt links pl m))
        (E (batchAt links pl m + 1)) (E (batchAt links pl m + 1 + 1)))
    (HS : ∀ m < links.length, ∀ qs, pcs[batchAt links pl m + 4]? = some qs →
      ShutAsksR Nm Mg links pl Rch (batchAt links pl m + 4) qs (E (batchAt links pl m + 4))) :
    KindTiedR Nm Mg links pl Rch E pcs .K9 := by
  intro i q a hq ha hk
  obtain ⟨m, hm, hb, hi⟩ := k9_at links pl hfit i a ha hk
  rcases hi with rfl | rfl | rfl
  · have g := tiedR_of_asks (HL m hm pcs[batchAt links pl m] pcs[batchAt links pl m + 1]
      pcs[batchAt links pl m + 1 + 1] (List.getElem?_eq_getElem (by omega))
      (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem (by omega)))
    obtain rfl : pcs[batchAt links pl m] = q :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hq)
    exact g.1
  · have g := tiedR_of_asks (HL m hm pcs[batchAt links pl m] pcs[batchAt links pl m + 1]
      pcs[batchAt links pl m + 1 + 1] (List.getElem?_eq_getElem (by omega))
      (List.getElem?_eq_getElem (by omega)) (List.getElem?_eq_getElem (by omega)))
    obtain rfl : pcs[batchAt links pl m + 1 + 1] = q :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hq)
    exact g.2.2
  · obtain ⟨pw, piece, b₅, hqs, hEs, H⟩ := HS m hm q hq
    exact shut_tied_pubR Nm Mg links pl Rch _ pw piece b₅ q hqs _ hEs H

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k9_at
#print axioms VerifiableInference.Desc.LinkJoin.k9Fit_full
#print axioms VerifiableInference.Desc.LinkJoin.k9Count_full
#print axioms VerifiableInference.Desc.LinkJoin.k9Fit_bent
#print axioms VerifiableInference.Desc.LinkJoin.k9_kindTiedR
