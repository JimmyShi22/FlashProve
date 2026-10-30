-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsFitLaw.lean: FROM EACH LAYER's OWN LEMMA "my sentence reads the witness
through
the list that I name" AND THE TEST `readsFit` (Johnson/Desc/First/ReadsFit.lean) TO THE PREMISE ON
READING THAT THE CHAIN OF PROMISES SPENDS (`ReadsOkAtQ`, Johnson/Desc/Sound/BordersSidesOn.lean).
Definitions and theorems.
  `ReadsAt ok R N Mg i`: THE FORM OF A LAYER's LEMMA: at a record and strings inside the fence ok,
  two
    witnesses that share the components R i give the item i one truth.
  `readsAt_mono`: a longer list, or a narrower fence, does no harm.
  `readsAt_of_holds`: THE LEMMA IS OF THE SENTENCE, NOT OF THE TERM: two meanings at which the item
  says
    one thing share it: so a layer proves it at its own fill, and the composed filling has it.
  `readsOkAt_of_fit`: **THE ONE THEOREM**: every item that rides at border k stands in the list;
  each
    item of the list has its lemma, inside the fence "the record bears no mark; the item rides at k
    (it is open there and block k does not close it); the promise in front of block k holds";
    `readsFit` says yes: THEN `ReadsOkAtQ k`.
  `readsAt_forms`: THE EXAMPLE: the runs' forms' layer (Johnson/Desc/Sound/BordersForms.lean): at
  its
    four sorts of item R := the table's own list, at EVERY record (no fence is spent): the four arms
    of `readsOkForms`, without its premise on the meaning beneath; under two premises on wt.
Limits: a frame. Which R a layer names, and its lemma, are that layer's. That every rider stands in
the list (hI) is a premise: the table's open sets are lists: a test. Nothing on soundness.

-/
import Johnson.Desc.First.ReadsFit
import Johnson.Desc.Sound.BordersSidesOn
import Johnson.Desc.Sound.BordersForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp start)
open VerifiableInference.Desc.K9 (Readers)

section
variable {P Cells Tok : Type}

/-- **The form of a layer's lemma.** -/
def ReadsAt (ok : P × First.S → Strs → Prop) (R : Item → List Comp) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (i : Item) : Prop :=
  ∀ (a : P × First.S) (y : Strs) (w w' : Wit Cells Tok MsgT), ok a y →
    (∀ c ∈ R i, sameQ c w w') → i.holds N Mg a y w → i.holds N Mg a y w'

/-- A longer list, or a narrower fence, does no harm. -/
theorem readsAt_mono (ok ok' : P × First.S → Strs → Prop) (R R' : Item → List Comp) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (i : Item) (hk : ∀ a y, ok' a y → ok a y)
    (hR : ∀ c ∈ R i, c ∈ R' i) (h : ReadsAt ok R N Mg i) : ReadsAt ok' R' N Mg i :=
  fun a y w w' ho hc hw => h a y w w' (hk a y ho) (fun c hcc => hc c (hR c hcc)) hw

/-- The lemma is of the sentence, not of the term. -/
theorem readsAt_of_holds (ok : P × First.S → Strs → Prop) (R : Item → List Comp) (N : Numbers)
    (Mg Mg' : Meaning P (Wit Cells Tok MsgT)) (i : Item) (e : i.holds N Mg' = i.holds N Mg)
    (h : ReadsAt ok R N Mg i) : ReadsAt ok R N Mg' i := by
  intro a y w w' ho hc hw
  rw [e] at hw ⊢
  exact h a y w w' ho hc hw

/-- **THE ONE THEOREM.** -/
theorem readsOkAt_of_fit {A : Type} {Fr : Frame} (arr : ℕ → ℕ → ℕ) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (k : ℕ) (R : Item → List Comp) (items : List Item)
    (hI : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → i ∈ items)
    (hL : ∀ i ∈ items, ReadsAt
      (fun b y => b.2.failed = none ∧
        openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i ∧ ¬ insQ links ps k i ∧
        ∃ a : A × Fr.E.Str, get a.1 = b ∧ strsOf Fr a.2 = y ∧ onQ N Mg links ps get k a) R N Mg i)
    (hF : First.readsFit arr N links R items = true) :
    ReadsOkAtQ (Fr := Fr) arr N Mg links ps get k := by
  intro i a w w' ha hm ho hn hc hw
  have hi := hI i ho hn
  exact hL i hi (get a.1) (strsOf Fr a.2) w w' ⟨hm, ho, hn, a, rfl, rfl, ha⟩
    (fun c hcc => hc c (First.readsFit_mem arr N links R items hF i hi c hcc)) hw

end

/-! ## The example: the runs' forms' layer -/

section
variable (cs : OnBytes.Codes) {P Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (Rd : ℕ → Readers) (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
  (after : ℕ → First.S → Except String First.S) (N : Numbers)
  (wt : ℕ → P × First.S → Strs → Wit Cells Tok MsgT → Prop) (rw : ℕ → First.S → Bool)
  (ah : ℕ → String → Bool)

/-- Is the item one of the four sorts that this layer lays? -/
def formsSort : Item → Bool
  | .forms _ _ _ => true
  | .formsT _ _ _ => true
  | .totalB _ => true
  | .total _ => true
  | _ => false

/-- **At its four sorts of item the layer reads what the table books, at every record.** Mg: any
meaning beneath. -/
theorem readsAt_forms (links : List ModelPart) (Mg : Meaning P (Wit Cells Tok MsgT))
    (hF : ∀ m k a y w w', (∀ c ∈ (Item.forms m k "weights").reads arr N links, sameQ c w w') →
      wt m a y w → wt m a y w')
    (hT : ∀ m k a y w w', (∀ c ∈ (Item.formsT m k "weights").reads arr N links, sameQ c w w') →
      wt m a y w → wt m a y w')
    (i : Item) (hi : formsSort i = true) :
    ReadsAt (fun _ _ => True) (fun j => j.reads arr N links) N
      (meaningForms cs arr ms Rd runs St after N wt rw ah Mg) i := by
  intro a y w w' _ hc hw
  cases i with
  | forms m k r =>
    refine ⟨fun p hp => ?_, fun e => ?_⟩
    · have h1 := hw.1 p hp
      by_cases e : ah p.1 p.2 = true
      · rw [if_pos e] at h1 ⊢
        exact formsQA_congr (N.sent m) _ (Rd m) p.1 p.2 a.2 _ _
          (sameSeats cs arr ms N links _ w w' hc) h1
      · rw [if_neg e] at h1 ⊢
        exact formsQ_congr (Rd m) _ p.1 p.2 a.2 _ _ (sameSeats cs arr ms N links _ w w' hc) h1
    · subst e
      exact hF m k a y w w' hc (hw.2 rfl)
  | formsT m k r =>
    refine ⟨fun p hp => formsTQ_congr (Rd m) St _ p.1 p.2 a.2 _ _
      (sameSeats cs arr ms N links _ w w' hc) (hw.1 p hp), fun e => ?_⟩
    subst e
    exact hT m k a y w w' hc (hw.2 rfl)
  | totalB m =>
    exact ⟨totalBQ_congr (after _) _ a.2 _ _ (sameSeats cs arr ms N links _ w w' hc) hw.1, hw.2⟩
  | total m =>
    exact ⟨totalQ_congr _ a.2 _ _ (sameSeats cs arr ms N links _ w w' hc) hw.1, hw.2⟩
  | _ => exact nomatch hi

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.readsAt_mono
#print axioms VerifiableInference.Desc.Sound.readsAt_of_holds
#print axioms VerifiableInference.Desc.Sound.readsOkAt_of_fit
#print axioms VerifiableInference.Desc.Sound.readsAt_forms
