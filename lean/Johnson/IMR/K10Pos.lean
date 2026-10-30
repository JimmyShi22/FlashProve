-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/IMR/K10Pos.lean: FOR THE CLOSING KIND
K10's PREMISE ON WHAT STANDS BEHIND THE CLOSING (hCar), NUMBER (6) OF K10's FILES' LIST OF CLOSED
FACTS ON THE PLAN (not in this library): "THE STAGE's POSITIONS ARE AT MOST THE SWITCH's" (hpos,
Johnson/Desc/First/Link/Law/HFOfDoor.lean): 2 ^ s.C.a ≤ 2 ^ (ProofFile.pAtK2 Z l).logN at s := stageOf
(gsAt l) 219, AT ALL 25 LINKS, UNDER THE ONE HEAD P5J.AtMg. Statements and proofs.

WHAT IT IS NOT, FIRST. A member of the head is proved at storedPublicFiles and zGap alone (at secondHashFunction, with
fixedConfigurationDigest in the digest's place; side library AtFullSide/Top/); so what rests on the head counts as
proved there alone. At the second hash function alone (the payer of "there is such a place" stands
there). The full size alone. It says nothing of (7) and (8) of that list. No soundness.

  prepOf_frames · numsAt_logN   two helpers, by unfolding: the records of the groups that prepOf
                    holds are the planner's framesOf at its sizes; the number logN that numsAt lays
                    is the main code's of the group in front, in the record of the numbers' group
  links_written     BY THE KERNEL: the written sized request has 25 links
  logN_at_head      under the head, at l < 25: (ProofFile.pAtK2 Zp l).logN = (gsAt l).main.logN
  **pos_at_head**   hpos, to the letter. IT HOLDS WITH EQUALITY.
  gs_logN_written   BY THE KERNEL: that number is 23 at all 25
  pos_fails_dead    A NEGATIVE LINE: at the numbers that pAtK2 lays where there is no such place
                    (ProofFile.deadP2: logN = 0) the sentence is false: so it is no idle word

THE ROAD. pAtK2 is the first of the description's K2 places whose group is l + 1. There is one
(P1K2.pAt_answers); it is made of prepOf's ground (spot_is); its sizes are the planner's (prepOf_z),
under the head the written ones (IM.pins); at the written sizes the record of group l + 1 bears the
written table's row l's group in front, whatever the sub-proofs' record is
(Johnson.G.rows_written_full). IT DOES NOT GO THROUGH ProofFile.rowAtK2 OR tableWrittenB.

-/
import Johnson.Top.H0.Opts.SpotsAnswer
import Johnson.Top.H0.Tw.K2C.GroupAtNums
import Johnson.G.SwitchRowsOfSized
import Johnson.LPFE1R.RowPubAt
import Johnson.Top.H.StageJ
import Johnson.IMR.SendsPinned
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM.K10

open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.K2Caller (spot_is tableFullLit)
open VerifiableInference.Desc.LinkJoin (gsAt)
open Johnson.Top.H (stageOf)
open OnBytes.Maker (WholeD)
open P1K2 (prepOf prepareAt numsAt Prep Nums prepOf_z)
open P5J

/-- The groups' records that prepOf holds are the planner's, at its sizes. -/
theorem prepOf_frames {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {P : Prep} (h : prepOf Z G₀ = some P) :
    ∃ sub, P.frames = Plan.framesOf P.z sub := by
  unfold prepOf prepareAt at h
  dsimp only at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, trees, _, rfl⟩ := h
    exact ⟨_, rfl⟩

/-- The number logN that numsAt lays. -/
theorem numsAt_logN {P : Prep} {link : Option Nat} {n : Nums} (h : numsAt P link = some n) :
    ∃ f, P.frames[n.grp]? = some f ∧ n.logN = f.before.main.logN := by
  unfold numsAt at h
  dsimp only at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, f, hf, lay, _, rd, _, rfl⟩ := h
    exact ⟨f, hf, rfl⟩

set_option maxRecDepth 1000000 in
/-- BY THE KERNEL. -/
theorem links_written : zW.request.link.length = 25 := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The switch's range of positions is the written group in front's main code's. -/
theorem logN_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : ℕ} (hl : l < 25) :
    (ProofFile.pAtK2 Zp l).logN = (gsAt l).main.logN := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hz := (pins h.pins.1).1
  have hL : Zp.p.chains.made.sized.proof.request.link.length = 25 := by
    rw [hz]
    exact links_written
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1
    (P1K2.pAt_answers h.scope h.reads O h.laid.planOk hL l hl)
  unfold ProofFile.pAtK2
  rw [hp]
  show p.logN = _
  unfold ProofFile.pAtK2? at hp
  obtain ⟨y, hf, rfl⟩ := Option.map_eq_some_iff.1 hp
  have hy := List.mem_of_find?_eq_some hf
  have hg : y.2.grp = l + 1 := by simpa using List.find?_some hf
  unfold ProofFile.k2SpotsAt at hy
  rw [O.blank] at hy
  obtain ⟨P, n, hP, hn, e⟩ := spot_is (G := Bs.G₀) hy
  obtain ⟨f, hf', eN⟩ := numsAt_logN hn
  obtain ⟨sub, eF⟩ := prepOf_frames hP
  have eg : n.grp = l + 1 := by
    rw [e] at hg
    exact hg
  rw [eg, eF, prepOf_z hP, hz] at hf'
  obtain ⟨f₀, R, -, hR⟩ := Johnson.G.frames_some_full sub l hl
  have eR := congrArg (·.g) ((Johnson.G.rows_written_full sub) l hl f hf' R hR).1
  have eB : f.before = R.g := eR
  rw [e]
  show n.logN = _
  rw [eN, eB]
  unfold gsAt
  rw [hR]
  rfl

/-- **(6), under the head: hpos, to the letter.** -/
theorem pos_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : ℕ} (hl : l < 25) :
    2 ^ (stageOf (gsAt l) 219).C.a ≤ 2 ^ (ProofFile.pAtK2 Zp l).logN := by
  rw [logN_at_head h hl]
  exact Nat.le_refl _

set_option maxRecDepth 1000000 in
/-- BY THE KERNEL: the number, at all 25. -/
theorem gs_logN_written : (List.range 25).all (fun l => (gsAt l).main.logN == 23) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative line: at the numbers that stand where there is no such place. -/
theorem pos_fails_dead : ¬ 2 ^ (stageOf (gsAt 0) 219).C.a ≤ 2 ^ ProofFile.deadP2.logN := by
  decide +kernel

end IM.K10

#print axioms IM.K10.prepOf_frames
#print axioms IM.K10.numsAt_logN
#print axioms IM.K10.links_written
#print axioms IM.K10.logN_at_head
#print axioms IM.K10.pos_at_head
#print axioms IM.K10.gs_logN_written
#print axioms IM.K10.pos_fails_dead
