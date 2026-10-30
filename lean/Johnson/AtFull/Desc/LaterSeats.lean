-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/LaterSeats.lean: THE LAST TWO STEPS OF `ProofFile.onlineDescription` (r₆, r₇ of the ledger
Johnson/AtFull/Desc/Ledger.lean): THE TWO LATER SEATS RETURN, AND THEIR CUTS INTO SUB-PROTOCOLS ARE
THE WRITTEN ONES OF THE FULL SIZE (`cutSharedFull`, 12 rows; `cutSecondFull`, 4 rows:
Johnson/Desc/Ok/PlanWritten/CutLit.lean). What their return and their cuts read of the public part
Z is said FIELD BY FIELD, as hypotheses; no test of the proof file's entry tests is a premise.
Theorems with their proofs.
What the two seats' return and their cuts read of Z.
  (1) Whether they return at all: `H2U.placesOfMade Z.made` returns (hN). By
    `laterShared_is`, `laterSecond_is` (Johnson/Loose/H2K12/LaterSeatsN.lean).
  (2) Of the numbers N that it returns: the parameters of the three proximity tests on the later
    chains: `pGu N`, `pGomega nO` (N.O = some nO), `pOwn N` (Johnson/Desc/K12/Law/SitsChains.lean).
    N.L is not read.
  (3) Of the planner's sizes of a proof file, z := Z.p.chains.made.sized.proof: three fields: z.set,
    z.codes, z.batch.
  The shared chain's first sub-protocol reads Z.p.chains in its test on the plan alone, which no row
    of a cut holds. The shared seat's own test on the file reads Z.p.X and Z.p.chains
    (`OkD.AtC.beside`: Johnson/Desc/ProofFile/Lot/K14SeatAtZ.lean): no row of a cut holds it either.
The written side.
  `piU`, `piO`, `piW`: the written parameters of the full size (`piUFull`, `piOFull`,
    `piWFull`, Johnson/Desc/K12/Law/PlacesFull.lean) at the seats' own places ⟨2, none, 9⟩, ⟨2,
    none, 10⟩, ⟨3, none, 2⟩ (the written ones bear the pieces 0, 1, 0).
  `proofSizedFull` (Johnson/Desc/Ok/PlanWritten/SizedLit.lean).
Theorems.
  `cutOf_retype_flat`: the cut of a chain that is carried to another type of claims (`Chain.retype`,
    which lays its links aside) and laid flat is the cut of its first sub-protocol, its front, its
    back and its last, in order: `Block.retype` and `Chain.blocksInOrder` turn a sub-protocol's test on the
    plan and its claims alone, which no row holds. The two later chains have no link.
  `later_return`: **r₆ and r₇ from hN**, at the values `sharedN Z N`, `P2Third.secondSeatOf Z N`.
  `second_rows`, `shared_rows`: the two closed facts at the written values: by Lean's kernel.
  `cut_second_written`, `cut_shared_written`: **the two cuts**, at every type of claims.
  `later_written`: all four in one sentence, in the ledger's letters.
  `places_of_members`, `later_of_members`: **hN AND THE THREE EQUATIONS ON N FOLLOW FROM THREE
    EQUATIONS ON Z.made ALONE**: that `H2U.p12FoldedOfMade Z.made 9`, `p12OmegaOfMade Z.made 10`,
    `p12OwnOfMade Z.made 2` (Johnson/Desc/K12/AtPlan.lean) are `piU`, `piO`, `piW`: each is a
    match on `placesOfMade`'s return (Omega's a second one, on N.O) and gives parameters without a
    stage where that refuses or N.O is none. So the
    ledger's last two steps with their cuts stand on SIX EQUATIONS: three on z, three on these
    members. The three on the members are the last three conjuncts of `H2K12.members_written`
    (Johnson/Loose/H2K12/K12MemberWritten.lean), there with `piU`, `piO`, `piW` spelled out.
  `second_bent`, `shared_bent`: the closed facts can fail: at a written parameter with one stage
    fewer the comparison says no.
Limits. The six equations
are PREMISES: nothing here shows that they
hold at any public files. The full size alone. A cut's row holds a sub-protocol's name, place,
number of rounds, the length of its field `oracles` (one entry a declared round), told trees and the
list before: no decision. That the seats'
tests on the plan and on the file pass, and that `ProofFile.onlineDescription` returns at all, is NOT shown here.
Nothing on soundness or on hiding.
-/
import Johnson.Loose.H2K12.LaterSeatsN
import Johnson.Desc.ProofFile.OnlineDescriptionBlocks
import Johnson.Desc.Ok.PlanWritten.CutTestLaws
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.PlanWritten
open VerifiableInference.Desc.K12.Seat (onGu onGomega onOwn)
open H2K.Member (piUFull piOFull piWFull)
open H2K.JointK (sharedN p14N secondN pGu pGomega pOwn)

/-- The written parameters of the folded row's test, at its seat's place. -/
def piU : P12 := { piUFull with place := ⟨2, none, 9, .K12⟩ }
/-- Of Omega's test. -/
def piO : P12 := { piOFull with place := ⟨2, none, 10, .K12⟩ }
/-- Of the request's own test. -/
def piW : P12 := { piWFull with place := ⟨3, none, 2, .K12⟩ }

/-- **The cut of a chain that is carried to another type of claims and laid flat.** -/
theorem cutOf_retype_flat {S Cl Cl' : Type} (c : Chain S Cl) :
    cutOf (c.retype (Cl' := Cl')).blocksInOrder = cutOf (c.first :: c.front ++ c.back ++ [c.last]) := by
  unfold cutOf Chain.blocksInOrder Chain.retype
  simp only [List.map_cons, List.map_append, List.map_map, List.flatMap_nil, List.append_nil,
    List.map_nil, List.cons_append]
  rfl

/-- **r₆ and r₇.** -/
theorem later_return (Z : ProofFile.Pub) (N : H2U.Places4) (hN : H2U.placesOfMade Z.made = .ok N) :
    ProofFile.onlineSharedChain Z = some (sharedN Z N) ∧
      ProofFile.onlineLastChain Z = some (P2Third.secondSeatOf Z N) :=
  ⟨H2K.JointK.laterShared_is Z N hN, H2K.JointK.laterSecond_is Z N hN⟩

/-- The last chain's sub-protocols at given parameters. -/
def secondAt (p : Third.P₁₄) (π : P12) : Chain Third.S₃ Unit :=
  (Third.last (XiPub := ProofFile.InstPub) p Third.firstOfS Third.sharedOfEnd
    (onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Unit))).chain

/-- The shared chain's sub-protocols behind its first, at given parameters. -/
def sharedBack (P : _root_.Desc.K14.P14) (πU πO : P12) : List (Block _root_.Desc.K14.St Unit) :=
  _root_.Desc.K14.blocksOr P ++ [onGu (proximityTestKind guardedProximityTestParts πU), onGomega (proximityTestKind guardedProximityTestParts πO)]

/-- The shared chain's written parameters: `p14Of`'s text at the written sizes; the message that
must stand before the shared point: `beforePointOf`'s text at the written own test. -/
def p14W : _root_.Desc.K14.P14 :=
  { set := proofSizedFull.set
    scope := if proofSizedFull.batch.lines.oneTime then .once else .shared
    codes := proofSizedFull.codes, S := proofSizedFull.batch.shape, item := 0
    beforePoint :=
      match (piW.before.filter fun m => m.1 == 1).map (·.2) with
      | [] => []
      | n :: l => [(1, l.foldl max n)] }

/-- **The last chain's four rows at the written values**: by Lean's kernel. -/
theorem second_rows :
    sameRows (cutOf
      ((secondAt (Third.p₁₄Z proofSizedFull.set proofSizedFull.codes proofSizedFull.batch)
          piW).first ::
        (secondAt (Third.p₁₄Z proofSizedFull.set proofSizedFull.codes proofSizedFull.batch)
            piW).front ++
        (secondAt (Third.p₁₄Z proofSizedFull.set proofSizedFull.codes proofSizedFull.batch)
            piW).back ++
        [(secondAt (Third.p₁₄Z proofSizedFull.set proofSizedFull.codes proofSizedFull.batch)
            piW).last]))
      cutSecondFull = true := by
  decide +kernel

/-- **The shared chain's eleven rows behind the first, at the written values**: by Lean's kernel. -/
theorem shared_rows :
    sameRows (cutOf (sharedBack p14W piU piO ++ [Seat.last (sharedBack p14W piU piO)]))
      cutSharedFull.tail = true := by
  decide +kernel

/-- The closed fact on the last chain can fail: with one stage fewer in the own test. -/
theorem second_bent :
    sameRows (cutOf
      (let c := secondAt (Third.p₁₄Z proofSizedFull.set proofSizedFull.codes proofSizedFull.batch)
        { piW with nums := { piW.nums with stages := piW.nums.stages.dropLast } }
       c.first :: c.front ++ c.back ++ [c.last]))
      cutSecondFull = false := by
  decide +kernel

/-- The closed fact on the shared chain can fail: with one stage fewer in Omega's test. -/
theorem shared_bent :
    sameRows (cutOf
      (let b := sharedBack p14W piU
        { piO with nums := { piO.nums with stages := piO.nums.stages.dropLast } }
       b ++ [Seat.last b]))
      cutSharedFull.tail = false := by
  decide +kernel

section
variable (Z : ProofFile.Pub) (N : H2U.Places4)
  (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
  (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
  (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
include hset hcodes hbatch

/-- **The last chain's cut is the written one.** -/
theorem cut_second_written (hW : pOwn N = piW) (Cl' : Type) :
    cutOf ((P2Third.secondSeatOf Z N).chain.retype (Cl' := Cl')).blocksInOrder = cutSecondFull := by
  rw [cutOf_retype_flat]
  have e : (P2Third.secondSeatOf Z N).chain =
      secondAt (Third.p₁₄Z Z.p.chains.made.sized.proof.set Z.p.chains.made.sized.proof.codes
        Z.p.chains.made.sized.proof.batch) (pOwn N) := rfl
  rw [e, hset, hcodes, hbatch, hW]
  exact (sameRows_iff _ _).1 second_rows

/-- **The shared chain's cut is the written one.** -/
theorem cut_shared_written (nO : H2U.PlaceNums) (hO : N.O = some nO) (hU : pGu N = piU)
    (hO' : pGomega nO = piO) (hW : pOwn N = piW) (Cl' : Type) :
    cutOf ((sharedN Z N).chain.retype (Cl' := Cl')).blocksInOrder = cutSharedFull := by
  rw [cutOf_retype_flat]
  have hW' : H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W = piW := hW
  have hU' : H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U = piU := hU
  have hO'' : H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO = piO := hO'
  have hP : p14N Z N = p14W := by
    unfold p14N _root_.Desc.K14.p14Of _root_.Desc.K14.beforePointOf p14W
    simp only [hset, hcodes, hbatch, hW']
    rfl
  have hT : Seat.tests N = [onGu (proximityTestKind guardedProximityTestParts piU), onGomega (proximityTestKind guardedProximityTestParts piO)] := by
    unfold Seat.tests
    rw [hO, hU']
    simp only [Option.toList, List.map_cons, List.map_nil, hO'', List.cons_append, List.nil_append]
  have e : (sharedN Z N).chain = _root_.Desc.K14.chainOf Z.p.chains (p14N Z N) (Seat.tests N)
      Seat.last := rfl
  rw [e, hP, hT]
  have r := (sameRows_iff _ _).1 shared_rows
  show _ :: cutOf (sharedBack p14W piU piO ++ [Seat.last (sharedBack p14W piU piO)]) = cutSharedFull
  rw [r]
  rfl

/-- **The ledger's last two steps with their cuts, in one sentence.** -/
theorem later_written (hN : H2U.placesOfMade Z.made = .ok N) (nO : H2U.PlaceNums)
    (hO : N.O = some nO) (hU : pGu N = piU) (hO' : pGomega nO = piO) (hW : pOwn N = piW) :
    ∃ (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat), ProofFile.onlineSharedChain Z = some A ∧
      ProofFile.onlineLastChain Z = some B ∧
      cutOf (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder = cutSharedFull ∧
      cutOf (B.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder = cutSecondFull :=
  ⟨_, _, (later_return Z N hN).1, (later_return Z N hN).2,
    cut_shared_written Z N hset hcodes hbatch nO hO hU hO' hW _,
    cut_second_written Z N hset hcodes hbatch hW _⟩

end

/-- The written parameters are not the empty ones: they have stages. -/
theorem piU_stages : piU.nums.stages ≠ [] := by decide +kernel
theorem piO_stages : piO.nums.stages ≠ [] := by decide +kernel

/-- **From the three members at the written values: the places are made, and the three equations
on them.** `H2U.p12FoldedOfMade`, `p12OmegaOfMade`, `p12OwnOfMade` (Johnson/Desc/K12/AtPlan.lean)
are each a match on `placesOfMade`'s return (Omega's a second one, on N.O), with the empty
parameters where it refuses or N.O is none. -/
theorem places_of_members (m : Johnson.G.OfPlan.Made) (e₁ : H2U.p12FoldedOfMade m 9 = piU)
    (e₂ : H2U.p12OmegaOfMade m 10 = piO) (e₃ : H2U.p12OwnOfMade m 2 = piW) :
    ∃ N nO, H2U.placesOfMade m = .ok N ∧ N.O = some nO ∧ pGu N = piU ∧ pGomega nO = piO ∧
      pOwn N = piW := by
  unfold H2U.p12FoldedOfMade at e₁
  unfold H2U.p12OmegaOfMade at e₂
  unfold H2U.p12OwnOfMade at e₃
  cases hN : H2U.placesOfMade m with
  | error w =>
    rw [hN] at e₁
    exact absurd (congrArg (·.nums.stages) e₁).symm piU_stages
  | ok N =>
    rw [hN] at e₁ e₂ e₃
    dsimp only at e₁ e₂ e₃
    cases hO : N.O with
    | none =>
      rw [hO] at e₂
      exact absurd (congrArg (·.nums.stages) e₂).symm piO_stages
    | some nO =>
      rw [hO] at e₂
      exact ⟨N, nO, rfl, hO, e₁, e₂, e₃⟩

/-- **The ledger's last two steps with their cuts, from the three members and the three fields.**
-/
theorem later_of_members (Z : ProofFile.Pub)
    (hset : Z.p.chains.made.sized.proof.set = proofSizedFull.set)
    (hcodes : Z.p.chains.made.sized.proof.codes = proofSizedFull.codes)
    (hbatch : Z.p.chains.made.sized.proof.batch = proofSizedFull.batch)
    (e₁ : H2U.p12FoldedOfMade Z.made 9 = piU) (e₂ : H2U.p12OmegaOfMade Z.made 10 = piO)
    (e₃ : H2U.p12OwnOfMade Z.made 2 = piW) :
    ∃ (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat), ProofFile.onlineSharedChain Z = some A ∧
      ProofFile.onlineLastChain Z = some B ∧
      cutOf (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder = cutSharedFull ∧
      cutOf (B.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder = cutSecondFull := by
  obtain ⟨N, nO, hN, hO, hU, hO', hW⟩ := places_of_members Z.made e₁ e₂ e₃
  exact later_written Z N hset hcodes hbatch hN nO hO hU hO' hW

end Johnson.AtFull.Desc

#print axioms Johnson.AtFull.Desc.cutOf_retype_flat
#print axioms Johnson.AtFull.Desc.later_return
#print axioms Johnson.AtFull.Desc.second_rows
#print axioms Johnson.AtFull.Desc.shared_rows
#print axioms Johnson.AtFull.Desc.second_bent
#print axioms Johnson.AtFull.Desc.shared_bent
#print axioms Johnson.AtFull.Desc.cut_second_written
#print axioms Johnson.AtFull.Desc.cut_shared_written
#print axioms Johnson.AtFull.Desc.later_written
#print axioms Johnson.AtFull.Desc.piU_stages
#print axioms Johnson.AtFull.Desc.piO_stages
#print axioms Johnson.AtFull.Desc.places_of_members
#print axioms Johnson.AtFull.Desc.later_of_members
