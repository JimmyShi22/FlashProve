-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RestPointPlan.lean: the binder hrest
of k01_law at the wider meaning, IN THE FORM TO CALL: `hrest_point` (RestAtPlus13.lean) with
hp, hs, hx replaced by the one test `planThreeB` (PlanThree.lean) and hSort by the one test
`sortB` (SortAtFifty.lean), all three in this folder.
  `hrest_point_plan`   PREMISES: hM · hfB · hft · `planThreeB dk Dm.N Z Bs.G₀ = true` ·
                   `sortB XV = true`; and two at this x, x', q alone, behind the accept and the
                   promise: `hhL d x'.2` (at the digits: nothing; at the reads: nothing is heard at
                   the digits' seat behind) and "K5.okAt | K5.plain of the segment is kept"
What is not claimed. The premises. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.PlanThree
import Johnson.Desc.K1.Law.SortAtFifty

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

theorem hrest_point_plan (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ BookFits B)
    (hft : dk.ft = (gpOf Z).firstTree) (hPlan : planThreeB dk Dm.N Z Bs.G₀ = true)
    (hX : sortB XV = true) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y q,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
        (noL l d) x y →
      hhL d x'.2 →
      (k5At l q = true → (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q x = true →
        (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q x' = true) →
      q ∈ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
          (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      q ∈ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
          (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      sevenItem q = false → (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q x' = true :=
  hrest_point Dm dk Mg₀ hM Z Bs hfB hft
    (fun l hl d => (goesOn_of (goesOn_at hPlan l hl d)).1)
    (fun l hl d => (goesOn_of (goesOn_at hPlan l hl d)).2.1)
    (fun l hl d => (goesOn_of (goesOn_at hPlan l hl d)).2.2) (hSort_of Dm hX)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hrest_point_plan
