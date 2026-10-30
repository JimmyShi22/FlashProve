-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GoodLay.lean: "GOOD" AS K9's COUNT IN THE COVER's FORM TAKES IT (`goodW`,
Honest/K9/GateArms.lean) AT A FEED-FORWARD SEGMENT, FROM "GOOD" ON DATA IN FRONT OF THE DRAW (`GoodLayers`,
Honest/K9/LayersFree.lean). One statement; its proof is three calls. No file of ours turns by it. No goal is stated.
  **`goodW_layers`**   `Walk L p4 nU s a₀` and `GoodLayers p4 s a₀ n` ⊢ `goodW p ‹the link's gatherer› s n`: by
      `goodS_layers`, `runsLaw_layers` (Honest/K9/LayersFree.lean) and `goodW_of_goodS` (Honest/K9/GateArms.lean). Where
      draw and gatherer return at no challenge it holds idly
WHY: `k9_fallDebt` (Honest/K9/FallDebtK9.lean) asks `goodW`; at attention and at the head's segment forms of it lie
(`goodW_att`, `goodW_head`); at the feed-forward segments the three lemmas lay apart.
WHAT IS NOT CLAIMED. `GoodLayers` at any state of a run: no member is shown. `Walk`: Honest/K9/AtSeat.lean has it in
scope at every state that stands in the segment. That n is the tests' number. No member; called by no line. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.LayersFree
import Johnson.Desc.ProofFile.Honest.K9.GateArms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.K9 (Where)

/-- **"Good" without a yes and without a length, at a feed-forward segment**, from the walk's premises and "good" on
data in front of the draw. -/
theorem goodW_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat) (p : Where) (s : S)
    (a₀ : LayOwn) (w : Walk L p4 nU s a₀) (n : Nat) (good : GoodLayers p4 s a₀ n) :
    goodW p (claimsInBy L.each L.hear L.order) s n := fun x y hy =>
  goodW_of_goodS p _ s (runsLaw_layers L p4 nU p s a₀ w) n (goodS_layers L p4 nU p s a₀ w n good x y hy) x y hy

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.goodW_layers
