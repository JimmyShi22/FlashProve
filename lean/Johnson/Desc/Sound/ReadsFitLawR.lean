-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsFitLawR.lean: the one theorem of Johnson/Desc/Sound/ReadsFitLaw.lean
("each part's lemma on what its sentence reads of the witness, and one test on the table, give
what the chain asks at a border") WITH THE REACHED STATES IN THE FENCE. One theorem.
Why. A part's lemma `ReadsAt ok R N Mg i` may assume a fence `ok` on the verifier's state.
That fence may hold what the table asks at the border (`onQ`).
Thirteen public tests stand off the table (Johnson/Desc/First/SmallDoor.lean); their facts
hold at reached states. A part whose lemma needs one (the pending claims' part reads the shapes of
the oracle messages) cannot have it from `onQ` alone.
  `readsOkAtR_of_fit`: as `readsOkAt_of_fit`, with `Rch k a` as one clause more in the fence of
    the parts' lemmas; it ends in `ReadsOkAtQR` (Johnson/Desc/Sound/BordersSidesOnR.lean).
Limits: a frame. No part's lemma is shown here. No soundness is claimed.

-/
import Johnson.Desc.Sound.ReadsFitLaw
import Johnson.Desc.Sound.BordersSidesOnR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp start)

/-- **The one theorem, with the reached states in the fence.** -/
theorem readsOkAtR_of_fit {A P Cells Tok : Type} {Fr : Frame} (arr : ℕ → ℕ → ℕ) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ) (R : Item → List Comp)
    (items : List Item)
    (hI : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → i ∈ items)
    (hL : ∀ i ∈ items, ReadsAt
      (fun b y => b.2.failed = none ∧
        openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i ∧ ¬ insQ links ps k i ∧
        ∃ a : A × Fr.E.Str, get a.1 = b ∧ strsOf Fr a.2 = y ∧ onQ N Mg links ps get k a ∧
          Rch k a) R N Mg i)
    (hF : First.readsFit arr N links R items = true) :
    ReadsOkAtQR (Fr := Fr) arr N Mg links ps get Rch k := by
  intro i a w w' ha hr hm ho hn hc hw
  have hi := hI i ho hn
  exact hL i hi (get a.1) (strsOf Fr a.2) w w' ⟨hm, ho, hn, a, rfl, rfl, ha, hr⟩
    (fun c hcc => hc c (First.readsFit_mem arr N links R items hF i hi c hcc)) hw

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.readsOkAtR_of_fit
