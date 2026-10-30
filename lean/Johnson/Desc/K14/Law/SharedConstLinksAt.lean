-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstLinksAt.lean: THE FIRST CHAIN's ROW OF LINKS, IN THE GOALS' SCOPE,
    IS
THE WRITTEN ONE: twelve times (layers, attention), then the head: the term at which the
composed meaning's constant lays its letter links (fullLinks, Johnson/P5J/MeansQ.lean: the same
    text).
So "the first chain's pieces are as many as the table's places" (hlen of the two halves of the
    joint,
Johnson/Desc/K14/Law/SharedConstZeroAt.lean, SharedConstZeroMade.lean) holds at the seat where the
open letter links is laid at that term.

  Sh.linksFull         the term
  Sh.links_in_scope    in scope, at the second hash function itself, at an opening of what the
                       verifier makes: ProofFile.subsOf Z = linksFull
  Sh.hlen_in_scope     1 + T.l₁.length = (flatPlaces true linksFull true).length, under OfDesc F T
HOW. Calls: subs_all (Johnson/IMR/PlacesScope.lean) · inScope_readFiles
(Johnson/Desc/K12/Law/Sizes/StageSizesAtScope.lean) · Sh.hlen_of_open
(Johnson/Desc/K14/Law/FirstLenOfOpen.lean); the two spellings of the row are one by evaluation.
What is not claimed. No law. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.FirstLenOfOpen
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference.Desc (Block Chain FileDescription First.S)
open VerifiableInference.Desc.First (ModelPart flatPlaces)
open VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)

namespace Sh

/-- **The written row of links.** -/
def linksFull : List ModelPart := (List.range 12).flatMap (fun _ => [ModelPart.layers, ModelPart.attention]) ++
    [ModelPart.head]

variable {P : VerifierAndGoals.PublicFiles} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)} {c : Chain First.S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **In scope the first chain's row of links is the written one.** -/
theorem links_in_scope (hS : VerifierAndGoals.InScope P = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : ProofFile.subsOf Z = linksFull := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hS
  rw [IM.subs_all hS hR O]
  decide

/-- **hlen in scope.** -/
theorem hlen_in_scope {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    (hS : VerifierAndGoals.InScope P = true) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (T : ThreeAt C D all F X₁ X₂ W) (hO : OfDesc F T) :
    1 + T.l₁.length = (flatPlaces true linksFull true).length := by
  rw [← links_in_scope hS O]
  exact hlen_of_open O T hO

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.links_in_scope
#print axioms Desc.K14.Law.Sh.hlen_in_scope
