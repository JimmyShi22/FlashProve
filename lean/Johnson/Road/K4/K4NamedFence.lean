-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4NamedFence.lean: THE NAMED TEST fence OF K4's ROW (fenceFit,
Johnson/Desc/First/FenceFit.lean) AT THE COMPOSED MEANING's CLOSED CONSTANT: A CLOSED FACT BY LEAN's
KERNEL AT WRITTEN VALUES, WITH ITS TIE. One statement with its proof: CALLS: no new argument,
nothing is evaluated here.

  `fence_const`: fenceFit accepts at the constant's own numbers and the written lists. Premises:
    hA (for the constant's name alone) · W : WrittenAt Zp (five parts of the public part are the
    written values) · hc: the first chain's cut is the written one. By the closed fact
    `P5T.fence_full` (Johnson/P5T/FenceFull.lean: one walk over 359 borders, 1,899 pairs, with
    negative tests beside it AT THE WALK: that a reject of the walk is a reject of fenceFit is
    typed nowhere) · `placesCut_is` (Johnson/Desc/First/CutWritten.lean) ·
    `N_written` (Johnson/Road/K4/K4PinsBook.lean) · "withRows turns a field
    that the test does not read" (rfl).
WHO PAYS W AND hc: both are conditions on the three public files alone. The rows madeRow and cutRow
of the verifier's entry tests (Johnson/Desc/Laid/ProofAsks.lean: fourteen rows in this tree) compare
them, and under the head (a member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction;
side library AtFullSide/Top/)) both are theorems (`written_of_head`, `cut_of_head`,
Johnson/Road/K4/K4HeadWritten.lean). This file calls neither: so here they are premises.
CAN THE PREMISES BE MET? Both rows were evaluated true at five sets of public files in the goals'
scope (a ride, by report): no theorem.
A LIMIT OF THE TEST ITSELF (fence_blind_kept, by the kernel, in that file): fenceFit bounds a
tenant's tree from above and says nothing else of it: with every kept tenant one tree higher, or
two, the walk still accepts. Whoever spends fence for more than "the tree has been told" leans on
nothing.
Limits. This file's cone wants some 11 GB of memory to compile (FenceFull). The full size alone.
K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.K4PinsBook
import Johnson.P5T.FenceFull
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.First (Numbers ModelPart flatPlacesOf fenceFit placesCut_is)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.PlanWritten (cutFirstFull)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **fence at the constant's own numbers**, where the plan and the cut are the written ones. -/
theorem fence_const (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (W : WrittenAt Zp)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) :
    fenceFit hA.𝔇.N linksFull (flatPlacesOf linksFull true) = true := by
  have e : ∀ (N : Numbers) (s : OnBytes.Params.ReqShape) (t : Nat → Nat) (n : Nat)
      (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)
      (told : List (List VerifiableInference.Desc.Oracle)),
      fenceFit ((N.withRows s t n).withTold ps told) links ps =
        fenceFit (N.withTold ps told) links ps := fun _ _ _ _ _ _ _ => rfl
  show fenceFit (P5J.At.N Zp cF) linksFull (flatPlacesOf linksFull true) = true
  rw [N_written W hc, e, ← placesCut_is]
  exact P5T.fence_full

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.fence_const
