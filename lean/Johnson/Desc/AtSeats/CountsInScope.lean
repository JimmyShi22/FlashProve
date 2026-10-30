-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/CountsInScope.lean:
Johnson/Desc/AtSeats/CountsAtFour.lean's five statements WITHOUT THEIR PREMISE hps ("the
flat list's places are the written list"): it is paid in scope by LPFK9.blockPlaces_full
(Johnson/LPFK9R/SubsFull.lean). So, in the goals' scope, at the numbers closed over
the first chain's own sub-protocols (N.atBlocks s links c.blocksInOrder, any N s links), the two counts at
all 54 places of the kinds K1 and K13 go on as the callers' binders say, UNDER ONE PREMISE: hok:
every sub-protocol of the flat list passes its own test on its parameters (at 355 and 357: under
none). A law file; no running text imports it.
  fifty_in_scope, first_in_scope, at355_in_scope, at356_in_scope, at357_in_scope

What is not claimed. That the composed meaning's N (P5J.At.N, Johnson/P5J/LettersAt.lean) is the
numbers so closed. At 355 and 357 the sentence says only that nothing is declared there: no example.
Nothing on the verifier's state. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.CountsAtFour
import Johnson.LPFK9R.SubsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace HashBuild
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K1 (layOf gpOf firstPar parW)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  (N : Numbers) (s : OnBytes.Params.ReqShape) (links : List ModelPart)

/-- **hear_K1's binders trees and msgs.** -/
theorem fifty_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true) :
    (∀ l < 25, ∀ d : Bool,
      (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[no50 l d + 1]? =
        (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[no50 l d]? +
          (layOf (par50 Z Bs.G₀ l d)).shapes.size) ∧
    ∀ l < 25, ∀ d : Bool,
      (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[no50 l d + 1]? =
        (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[no50 l d]? +
          (par50 Z Bs.G₀ l d).sent.size :=
  counts_fifty N s links hS hR O hok (LPFK9.blockPlaces_full hS hR O)

/-- **RowG's trees and msgs**, at k = 2. -/
theorem first_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true) :
    (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[2 + 1]? =
        (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[2]? +
          (layOf (firstPar Bs.G₀.first (gpOf Z))).shapes.size ∧
      (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[2 + 1]? =
        (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[2]? +
          (firstPar Bs.G₀.first (gpOf Z)).sent.size :=
  counts_first N s links hS hR O hok (LPFK9.blockPlaces_full hS hR O)

/-- **RowM3's trees and msgs; k13_law_top's hNt and hNm.** -/
theorem at355_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[355 + 1]? =
        (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[355]? ∧
      (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[355 + 1]? =
        (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[355]? :=
  counts_355 N s links hS hR O (LPFK9.blockPlaces_full hS hR O)

/-- **RowM4's trees and msgs**, at k = 356. -/
theorem at356_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true) :
    ∃ msg, OnBytes.linMessageW Z.first.lin = some msg ∧
      (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[356 + 1]? =
        (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[356]? +
          (layOf (parW Z.first (gpOf Z) 4 msg)).shapes.size ∧
      (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[356 + 1]? =
        (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[356]? +
          (parW Z.first (gpOf Z) 4 msg).sent.size :=
  counts_356 N s links hS hR O hok (LPFK9.blockPlaces_full hS hR O)

/-- **At the chain's last sub-protocol.** -/
theorem at357_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[357 + 1]? =
        (N.atBlocks s links c.blocksInOrder).treesAt (flatPlacesOf linksFull true)[357]? ∧
      (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[357 + 1]? =
        (N.atBlocks s links c.blocksInOrder).msgsAt (flatPlacesOf linksFull true)[357]? :=
  counts_357 N s links hS hR O (LPFK9.blockPlaces_full hS hR O)

end HashBuild

#print axioms HashBuild.fifty_in_scope
#print axioms HashBuild.first_in_scope
#print axioms HashBuild.at355_in_scope
#print axioms HashBuild.at356_in_scope
#print axioms HashBuild.at357_in_scope
