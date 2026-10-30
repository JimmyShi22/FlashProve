-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5Written.lean: **WHERE TWO COMPARISONS WITH WRITTEN VALUES ACCEPT, THE TABLE's SEATS OFF THE PLAN, WHAT THE SUB-PROTOCOLS TELL, AND THE TEST "fence" ARE TERMS WITHOUT A LETTER.** Kind-free.
The two comparisons: madeRow Zp (Johnson/Desc/Ok/PlanWritten/MadeTest.lean: the sizes, the first chain's parameters as read back, the proof file's three lists of what is sent, the shape part of the public parameters) and the written
cut of the first chain into sub-protocols (cutOf … = cutFirstFull | cutRow, Johnson/Desc/Ok/PlanWritten/CutTest.lean). THEY ARE PREMISES HERE. The verifier's list of entry tests has neither in its prefix that Johnson/Desc/Laid/ProofAsksFirstEightTests.lean pins (asksAt1), and both in its prefix that ProofAsksFirstThirteenTests.lean, beside it, pins (asksAt2).
Why. The kind's named condition at one head has a test, fence (fenceFit at the composed meaning's numbers: P5J.At.N, Johnson/P5J/LettersAt.lean), that would have to be run anew at each head. Under the two comparisons it equals fenceW, a Bool with no letter: one evaluation then serves
every head.

Main names:
  planSeatsBy c S rb: P5T.planSeats (Johnson/P5T/PlanSeats.lean), ITS OWN TEXT LIFTED BY PROGRAM, at the three things that it reads of the public part and the declared rounds. planSeats_by: the two are one, by unfolding.
  made_row_gives: an accept of madeRow gives the six equations on the first chain's parameters and the three lists of what is sent.
  pseatsW: the seats at the written values. **pseats_written**: under the head AtMg and madeRow's accept: At.pseats Zp = pseatsW.
  toldW: what the written cut's rows tell. told_written: where the first chain's cut is the written one: At.told cF = toldW.
  fenceFit_congr: the test reads of the numbers the sampled tenants and the trees by place alone.
  fenceW. **fence_written**: fenceFit (At.N Zp cF) At.links At.ps = fenceW. fence_written_row: the like from the row cutRow. fence_of_written: so fenceW = true gives the test's accept at every such head.
IS IT EMPTY HERE? Equations under the head and two Bools. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/); THAT fenceW IS true IS NOT SHOWN: IT HAS BEEN EVALUATED NOWHERE.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.RoundsWritten
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.Desc.First.CutAtNumbers
import Johnson.Desc.First.FenceFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc (FileDescription Chain Place Oracle)
open VerifiableInference.Desc.First (Numbers ModelPart Item fenceFit sampledIn)
open VerifiableInference.PlanWritten (madeRow FirstWritten first_of_is proofSends_of_is cutFirstFull cutRow cut_of_row proofSizedFull)
open OnBytes.Maker (WholeD)
open Johnson.G (dryProofFull proofSendsFull)
open P5J (AtMg F0T TS)
open P5T (PSeat segOf rolesOf)

/-- **The seats off the plan, at the three things that they read**: the first chain's sendings with their codes, the request's shape, and how many roots the rounds in front of a round send. -/
def planSeatsBy (c : Johnson.G.ChainSends) (S : OnBytes.Params.ReqShape) (rb : Nat → Nat) : List PSeat :=
  let groups := (OnBytes.reqGroups S).toList
  c.sends.zipIdx.flatMap fun s =>
    match OnBytes.layTrees c.codes s.1.sent.toArray with
    | none => []
    | some lay =>
      let seg := segOf (groups.length + 1) 16 s.1.label
      let roles := match seg with
        | some (l, m) => rolesOf S groups l m
        | none => []
      (List.range s.1.sent.length).map fun i =>
        { label := s.1.label, send := s.2, seg := seg, idx := i,
          j := rb (s.1.entry - 1) + lay.tree.getD i 0, t := lay.part.getD i 0,
          shape := (s.1.sent.getD i default).shape, role := roles.getD i .other }

/-- The two texts are one. -/
theorem planSeats_by (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) :
    P5T.planSeats Z dl = planSeatsBy Z.made.proof.1 Z.first.shape (P5T.rootsBefore dl) := rfl

/-- What an accept of the row on written values gives here. -/
theorem made_row_gives {Z : ProofFile.Pub} (h : madeRow Z = true) : FirstWritten Z.first ∧ Z.made.proof = proofSendsFull := by
  unfold madeRow at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨first_of_is h.1.1.2, proofSends_of_is h.1.2⟩

/-- **The seats at the written values.** No letter. -/
def pseatsW : List PSeat :=
  planSeatsBy proofSendsFull.1 proofSizedFull.request fun k => ((dryProofFull.1.map fun x => x.1.entry.roots).take k).sum

/-- **What the written cut's rows tell.** No letter. -/
def toldW : List (List Oracle) := cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)

/-- The test reads of the numbers the sampled tenants and the trees by place alone. -/
theorem fenceFit_congr {N N' : Numbers} (links : List ModelPart) (ps : List Place) (h1 : ∀ O, sampledIn N O = sampledIn N' O)
    (h2 : N.treesAt = N'.treesAt) : fenceFit N links ps = fenceFit N' links ps := by
  unfold fenceFit
  simp only [h1, h2]

/-- **The test at the written values.** No letter. -/
def fenceW : Bool := fenceFit ((P5T.numbersOf pseatsW).withTold P5J.At.ps toldW) P5J.At.links P5J.At.ps

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The composed meaning's seats (P5J.At.pseats) are the written ones.** -/
theorem pseats_written (h : AtMg o Z D r Zp Np cF) (hm : madeRow Zp = true) : P5J.At.pseats Zp = pseatsW := by
  obtain ⟨hf, hs⟩ := made_row_gives hm
  have hr : P5T.rootsBefore Zp.D.1 = fun k => ((dryProofFull.1.map fun x => x.1.entry.roots).take k).sum :=
    funext (rootsBefore_written h)
  unfold P5J.At.pseats pseatsW
  rw [planSeats_by, hs, hf.2.2.1, hr]

/-- **What the first chain's sub-protocols tell is what the written cut's rows tell.** -/
theorem told_written (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) : P5J.At.told cF = toldW := by
  have e : P5J.At.told cF = VerifiableInference.Desc.First.toldOf cF.blocksInOrder := by
    unfold P5J.At.told VerifiableInference.Desc.Sound.toldOf VerifiableInference.Desc.First.toldOf
    exact List.map_congr_left fun _ _ => List.flatMap_id
  unfold toldW
  rw [e, VerifiableInference.Desc.First.toldOf_cut, hc]

/-- **THE TEST AT THE COMPOSED MEANING's NUMBERS IS THE TEST AT THE WRITTEN VALUES.** -/
theorem fence_written (h : AtMg o Z D r Zp Np cF) (hm : madeRow Zp = true)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) :
    fenceFit (P5J.At.N Zp cF) P5J.At.links P5J.At.ps = fenceW := by
  have e : fenceFit (P5J.At.N Zp cF) P5J.At.links P5J.At.ps =
      fenceFit ((P5T.numbersOf (P5J.At.pseats Zp)).withTold P5J.At.ps (P5J.At.told cF)) P5J.At.links P5J.At.ps :=
    fenceFit_congr _ _ (fun _ => rfl) rfl
  unfold fenceW
  rw [e, pseats_written h hm, told_written hc]

/-- The like from the row for the entry tests. -/
theorem fence_written_row (h : AtMg o Z D r Zp Np cF) (hm : madeRow Zp = true) (hc : cutRow (F0T o Zp Np cF) Zp = true) :
    fenceFit (P5J.At.N Zp cF) P5J.At.links P5J.At.ps = fenceW :=
  fence_written h hm (cut_of_row hc).1

/-- So one evaluation serves every head at which the two comparisons accept. -/
theorem fence_of_written (hW : fenceW = true) (h : AtMg o Z D r Zp Np cF) (hm : madeRow Zp = true)
    (hc : cutRow (F0T o Zp Np cF) Zp = true) : fenceFit (P5J.At.N Zp cF) P5J.At.links P5J.At.ps = true :=
  (fence_written_row h hm hc).trans hW

end

end H2K5.Door

#print axioms H2K5.Door.planSeats_by
#print axioms H2K5.Door.made_row_gives
#print axioms H2K5.Door.fenceFit_congr
#print axioms H2K5.Door.pseats_written
#print axioms H2K5.Door.told_written
#print axioms H2K5.Door.fence_written
#print axioms H2K5.Door.fence_written_row
#print axioms H2K5.Door.fence_of_written
