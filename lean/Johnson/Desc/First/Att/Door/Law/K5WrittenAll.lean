-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/First/Att/Door/Law/K5WrittenAll.lean: **WHERE THE COMPARISON madeRow ACCEPTS, THE SEATS OF ALL THREE CHAINS OFF THE PLAN, AND WITH THEM THE WITNESS's NUMBERS OF THE MESSAGES (num · arr), ARE TERMS WITHOUT A LETTER.** Kind-free.
The like of pseats_written (Door/Law/K5Written.lean) for P5T.planSeatsAll (Johnson/P5T/PlanSeats.lean). madeRow's accept IS A PREMISE HERE: the verifier's list of entry tests asks it: it stands in its prefix that Johnson/Desc/Laid/ProofAsksFirstThirteenTests.lean pins (asksAt2).

Main names:
  chainSeatsBy chain base c rb: P5T.chainSeats' OWN TEXT, LIFTED BY PROGRAM, with the one thing that it reads of the declared rounds as a letter. chainSeats_by: the two are one, by unfolding.
  rootsW₁ | ₂ | ₃: how many roots the written rounds in front of the k-th send, chain by chain. pseatsAllW: the seats of all three chains at the written values. No letter.
  len_written: the public part's three lists of declared rounds are as long as the written lists.
  **pseatsAll_written**: under the head AtMg and madeRow's accept: At.pseatsAll Zp = pseatsAllW. **num_written · arr_written**: so At.num Zp and At.arr Zp are the functions off pseatsAllW.
IS IT EMPTY HERE? Equations under the head and one Bool. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND
zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (madeRow proofSizedFull)
open OnBytes.Maker (WholeD)
open Johnson.G (dryProofFull proofSendsFull)
open P5J (AtMg TS)
open P5T (PSeat)

/-- **The seats of another chain's oracle messages, at what they read.** -/
def chainSeatsBy (chain base : Nat) (c : Johnson.G.ChainSends) (rb : Nat → Nat) : List PSeat :=
  c.sends.zipIdx.flatMap fun s =>
    match OnBytes.layTrees c.codes s.1.sent.toArray with
    | none => []
    | some lay =>
      (List.range s.1.sent.length).map fun i =>
        { label := s!"chain {chain}, {s.1.label}", send := 1000 * chain + s.2, seg := none, idx := i,
          j := base + rb (s.1.entry - 1) + lay.tree.getD i 0, t := lay.part.getD i 0,
          shape := (s.1.sent.getD i default).shape, role := .other }

/-- The two texts are one. -/
theorem chainSeats_by (chain base : ℕ) (c : Johnson.G.ChainSends) (dl : List Fmt.DeclaredRound) :
    P5T.chainSeats chain base c dl = chainSeatsBy chain base c (P5T.rootsBefore dl) := rfl

/-- How many roots the written rounds in front of the k-th send: the first chain. -/
def rootsW₁ (k : ℕ) : ℕ := ((dryProofFull.1.map fun x => x.1.entry.roots).take k).sum
/-- The shared chain. -/
def rootsW₂ (k : ℕ) : ℕ := ((dryProofFull.2.1.map fun x => x.1.entry.roots).take k).sum
/-- The last chain. -/
def rootsW₃ (k : ℕ) : ℕ := ((dryProofFull.2.2.map fun x => x.1.entry.roots).take k).sum

/-- **The seats of all three chains at the written values.** No letter. -/
def pseatsAllW : List PSeat :=
  pseatsW ++ chainSeatsBy 1 (rootsW₁ dryProofFull.1.length) proofSendsFull.2.1 rootsW₂ ++
    chainSeatsBy 2 (rootsW₁ dryProofFull.1.length + rootsW₂ dryProofFull.2.1.length) proofSendsFull.2.2 rootsW₃

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The declared rounds are as many as the written ones, chain by chain. -/
theorem len_written (h : AtMg o Z D r Zp Np cF) :
    Zp.D.1.length = dryProofFull.1.length ∧ Zp.D.2.1.length = dryProofFull.2.1.length := by
  obtain ⟨e1, e2, -⟩ := entries_written h
  have a1 := congrArg List.length e1
  have a2 := congrArg List.length e2
  rw [List.length_map, List.length_map] at a1 a2
  exact ⟨a1, a2⟩

/-- **The composed meaning's seats of all three chains (P5J.At.pseatsAll) are the written ones.** -/
theorem pseatsAll_written (h : AtMg o Z D r Zp Np cF) (hm : madeRow Zp = true) : P5J.At.pseatsAll Zp = pseatsAllW := by
  have hs := (made_row_gives hm).2
  have r1 : P5T.rootsBefore Zp.D.1 = rootsW₁ := funext (rootsBefore_written h)
  have r2 : P5T.rootsBefore Zp.D.2.1 = rootsW₂ := funext (rootsBefore_written₂ h)
  have r3 : P5T.rootsBefore Zp.D.2.2 = rootsW₃ := funext (rootsBefore_written₃ h)
  have p1 : P5T.planSeats Zp Zp.D.1 = pseatsW := pseats_written h hm
  obtain ⟨l1, l2⟩ := len_written h
  show P5T.planSeats Zp Zp.D.1 ++ P5T.chainSeats 1 (P5T.rootsBefore Zp.D.1 Zp.D.1.length) Zp.made.proof.2.1 Zp.D.2.1 ++
      P5T.chainSeats 2 (P5T.rootsBefore Zp.D.1 Zp.D.1.length + P5T.rootsBefore Zp.D.2.1 Zp.D.2.1.length) Zp.made.proof.2.2
        Zp.D.2.2 = pseatsAllW
  unfold pseatsAllW
  rw [p1, chainSeats_by, chainSeats_by, r1, r2, r3, l1, l2, hs]

/-- **The witness's number of (link, message), off the written seats.** -/
theorem num_written (h : AtMg o Z D r Zp Np cF) (hm : madeRow Zp = true) : P5J.At.num Zp = P5T.numOfPlan pseatsAllW := by
  unfold P5J.At.num
  rw [pseatsAll_written h hm]

/-- **The number, in the witness, of the message at a seat, off the written seats.** -/
theorem arr_written (h : AtMg o Z D r Zp Np cF) (hm : madeRow Zp = true) : P5J.At.arr Zp = P5T.arrOf pseatsAllW := by
  unfold P5J.At.arr
  rw [pseatsAll_written h hm]

end

end H2K5.Door

#print axioms H2K5.Door.chainSeats_by
#print axioms H2K5.Door.len_written
#print axioms H2K5.Door.pseatsAll_written
#print axioms H2K5.Door.num_written
#print axioms H2K5.Door.arr_written
