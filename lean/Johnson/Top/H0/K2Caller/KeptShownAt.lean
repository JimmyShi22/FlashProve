-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeptShownAt.lean: THE PREMISE hsn OF THE CODE SWITCH's FIRST TIE
(K2Caller/TieOneR.lean) AND THE PREMISE hsh OF ITS FOURTH (TieFourR.lean) FROM THE TABLE OF JOINTS'
PROMISE, AT THE COMPOSED MEANING `mgAll 𝔇 Mg` (Johnson/Desc/Sound/MgAll.lean), general in 𝔇: at a
state without a mark under the promise at border k, at every kept tenant of segment m: its word is
shown, and there is no collision at its OOD sample.

  hsn_mgAll          from "pinKept m is open at border k": by `on_parts` and
                     `kept_sampled` (K2Caller/TiesFront.lean) and the composed meaning's two fields
                     (`mgAll_shown`, `mgAll_noColl`: by unfolding)
  hsn_of_sampled     the same from "every kept tenant of m is among the sampled tenants of what is
                     open at border k": the form in which a closed fact on the written list gives it

  hsh_mgAll          hsh is the first half of hsn: "its word is shown" alone

The ends are hsn | hsh to the letter at r.cs := 𝔇.cs, G := 𝔇.G, ms := 𝔇.ms, smpNamed r.cs seats :=
𝔇.smp.

Limits. "pinKept m is open at border k" is a premise: a closed fact on the written list, place by
place. Under a promise that no state meets the sentence says nothing: that the promise is met
anywhere is not shown here. No soundness statement.

-/
import Johnson.Desc.Sound.MgAll
import Johnson.Top.H0.K2Caller.TiesFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers sampledIn openSets start)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {F : Frame} (N : Numbers) (links : List ModelPart) (ps : List Place) (k m : ℕ) (z : P)

/-- **From "every kept tenant of m is sampled at border k".** -/
theorem hsn_of_sampled
    (hS : ∀ q ∈ N.keptOf m, q ∈ sampledIn N ((openSets links ps (start links))[k]?.getD [])) :
    ∀ a : First.S × F.E.Str, onQ N (mgAll 𝔇 Mg) links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none →
      ∀ q ∈ N.keptOf m, shownJT 𝔇.cs 𝔇.G 𝔇.ms q.1 q.2 (strsOf F a.2) ∧
        noCollJT 𝔇.cs 𝔇.G 𝔇.smp 𝔇.ms q.1 q.2 (z, a.1) (strsOf F a.2) :=
  fun a ha hm q hq => (on_parts N (mgAll 𝔇 Mg) links ps k z a ha hm).2.1 q (hS q hq)

/-- **From "pinKept m is open at border k".** -/
theorem hsn_mgAll (hO : Item.pinKept m ∈ (openSets links ps (start links))[k]?.getD []) :
    ∀ a : First.S × F.E.Str, onQ N (mgAll 𝔇 Mg) links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none →
      ∀ q ∈ N.keptOf m, shownJT 𝔇.cs 𝔇.G 𝔇.ms q.1 q.2 (strsOf F a.2) ∧
        noCollJT 𝔇.cs 𝔇.G 𝔇.smp 𝔇.ms q.1 q.2 (z, a.1) (strsOf F a.2) :=
  hsn_of_sampled 𝔇 Mg N links ps k m z fun q hq => kept_sampled N m _ hO q hq

/-- **The fourth tie's premise**: the first half. -/
theorem hsh_mgAll (hO : Item.pinKept m ∈ (openSets links ps (start links))[k]?.getD []) :
    ∀ a : First.S × F.E.Str, onQ N (mgAll 𝔇 Mg) links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none →
      ∀ q ∈ N.keptOf m, shownJT 𝔇.cs 𝔇.G 𝔇.ms q.1 q.2 (strsOf F a.2) :=
  fun a ha hm q hq => (hsn_mgAll 𝔇 Mg N links ps k m z hO a ha hm q hq).1

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.hsn_of_sampled
#print axioms VerifiableInference.Desc.First.K2Caller.hsn_mgAll
#print axioms VerifiableInference.Desc.First.K2Caller.hsh_mgAll
