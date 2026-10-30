--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/TwoTestsOfTheSharedChain.lean: THE TWO PROXIMITY TESTS OF
THE PROOF FILE's SHARED CHAIN (the kind K12, members 9 and 10): THE PROOFS OF THE STATEMENTS OF
Honest/K12/Part4/TwoTestsOfTheSharedChainStatements.lean: the book lends both their jobs; the new
trees of the first are the thread's tables.

WHAT IT IS NOT. What that file's head says: laysB is a public test; no depth, no carrying of a
letter, no acceptance; the third statement stands behind the invariant; all stands over another
house's files, which lie in no sealed tree. Closed facts are evaluated in Lean's kernel (nineWritten
with a control, stagesFoldWritten, and the other house's lays_U, lays_O); they are replayed by no
independent checker. Nothing on completeness, on soundness or on what a proof hides.

WHAT IS TYPED ANEW, AND WHY. testOnUIsWritten and testOnOmegaIsWritten have the text of
fourU_written and fourO_written (AtFullSide/K12/PaysAtHead.lean), a file that does not build whole.
newTreesOfTheTestOnUAreTheThreadsTables has the text of the third
limb of playsS_nine (Honest/K12/AtFile/PlaysNine.lean): that theorem ends in PlaysS, from which the
new trees come back only under "no part stops"; the limb itself asks no such thing. With it come
that file's small laws (member_at, rows_heard_U there) and its closed lines, gathered in
nineWritten: that file is NOT imported, because a file beneath it
(Honest/K12/AtFile/WordsTiedU.lean) did not build over the other house's working union at the bytes


WHAT IT IS. Calls and ties; no new mathematics.
  THE BOOK LENDS. laysB reads of a job its record, members and fresh table alone (laysB_congr,
  sealed); at the maker's book the test is the test at the short book (laysB_maker); there the
  kernel has said yes at the bare jobs (lays_U, lays_O); the seated records are the written ones at
  their places (p12_four_at_head, sealed).
  THE NEW TREES. trees_of_thr (Honest/K12/TreesOfThr.lean).
-/
import Johnson.Desc.ProofFile.Honest.K12.Part4.TwoTestsOfTheSharedChainStatements
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TreesAtShared
import Johnson.Desc.ProofFile.Honest.K12.TreesOfThr
import Johnson.Desc.ProofFile.Honest.K12.TablesAtFront
import Johnson.Desc.ProofFile.Honest.K12.StepsAtKey
import Johnson.Desc.ProofFile.Honest.Small.SaysYesOf
import Johnson.AtFull.Shape.TestNumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.Part4
open OnBytes (TableKey)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Alike₂)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12)
open Desc.K14 (St)
open P5J (TS)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open H2K.Member (piUFull piOFull)
open ProofFile.Honest.K14 (treesU)
open ProofFile.Honest.K12 (TestJob SeatOf proverSideOfProximityTest seedRound laysB laysB_congr testTbl trees_of_thr
  firstLen restLen RowsOfHeard rowsOfHeard_many)
open ProofFile.Honest.K12.Light (jobAtU jobAtOmega memOfSending written_at_head qAt_written nums_head_U)
open ProofFile.Honest.K12.AtProof (fourOf placeU placeO membersU membersO freshU freshO)
open ProofFile.Honest.K12.AtFile (tableShared sharedR roundsTrees trees_rounds decls_rounds rounds_alike
  treesU_head laysB_maker lays_U lays_O bookShort)

/-! ## 1 Closed facts -/

/-- CLOSED FACTS on the written shared list and the written test on G_u: member 9 declares 35 rounds
and 4 trees; 8 rounds and 3 trees stand in front of it; the test has five stages, and its two parts
count 35 rounds. -/
theorem nineWritten :
    (sharedR[9]?).map (fun x => (x.1.length, x.2)) = some (35, 4) ∧
    ((sharedR.take 9).flatMap (·.1)).length = 8 ∧ ((sharedR.take 9).map (·.2)).sum = 3 ∧
    piUFull.nums.stages.length = 5 ∧
    firstLen piUFull.nums.stages + restLen piUFull.nums.stages = 35 := by
  decide +kernel

/-- A control: member 10 has other numbers. -/
theorem nineWritten_control :
    (sharedR[10]?).map (fun x => (x.1.length, x.2)) ≠ some (35, 4) := by
  decide +kernel

/-- A CLOSED FACT: each stage of the written test on G_u folds no more rows than it has. -/
theorem stagesFoldWritten : ∀ a ∈ piUFull.nums.stages, a.h ≤ a.k := by decide +kernel

/-- What a list alike to the written one declares at a member. -/
theorem memberIsTheWrittenOne {S Cl : Type} {l : List (Block S Cl)}
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder l) {b : Nat} {blk : Block S Cl}
    (hb : l[b]? = some blk) : sharedR[b]? = some (roundsTrees blk) := by
  have e : sharedR = l.map roundsTrees := rounds_alike hl
  rw [e, List.getElem?_map, hb]
  rfl

variable {o : SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- Under the head the record of the test on G_u is the written one at its place. -/
theorem testOnUIsWritten (h : P5J.AtMg o Z D r Zp Np cF) :
    (fourOf Np).U = ({ piUFull with place := placeU } : P12) := by
  have e := (Johnson.AtFull.Shape.p12_four_at_head h).2.1
  have e' : H2U.p12FoldedOfMade Zp.made 9 = (fourOf Np).U := by
    unfold H2U.p12FoldedOfMade
    rw [h.laid.places] <;> rfl
  exact e'.symm.trans e

/-- Under the head the record of the test on G_omega is the written one at its place. -/
theorem testOnOmegaIsWritten (h : P5J.AtMg o Z D r Zp Np cF) {p : P12}
    (hp : (fourOf Np).O = some p) : p = ({ piOFull with place := placeO } : P12) := by
  have e := (Johnson.AtFull.Shape.p12_four_at_head h).2.2.1
  have hp' : Np.O.map (H2U.proximityTestParametersAt placeO) = some p := hp
  have e' : H2U.p12OmegaOfMade Zp.made 10 = p := by
    unfold H2U.p12OmegaOfMade
    rw [h.laid.places]
    show (Np.O.map (H2U.proximityTestParametersAt placeO)).getD (H2U.noP12 placeO) = p
    rw [hp'] <;> rfl
  exact e'.symm.trans e

/-! ## 2 The book lends -/

theorem bookLendsATestOnU : BookLendsATestOnU := by
  intro o Z D r Zp Np cF h Bk W X job hB hp hm hf
  obtain ⟨y, hy, Wr⟩ := written_at_head h
  have a := lays_U
  rw [hy] at a
  simp only [Option.all_some] at a
  have hp' : job.p = ({ piUFull with place := placeU } : P12) := hp.trans (testOnUIsWritten h)
  have hch : job.p.place.chain ≠ 1 := by
    rw [hp']
    decide
  rw [laysB_maker hB 1 job hch,
    laysB_congr bookShort 1 job (ProofFile.Honest.K12.AtFile.jobAtU ⟨K1.qAt Zp Np, 0⟩) hp' hm hf,
    qAt_written Wr Np]
  exact a

theorem bookLendsATestOnOmega : BookLendsATestOnOmega := by
  intro o Z D r Zp Np cF h Bk W X job record hB hO hp hm hf
  obtain ⟨y, hy, Wr⟩ := written_at_head h
  have a := lays_O
  rw [hy] at a
  simp only [Option.all_some] at a
  have hp' : job.p = ({ piOFull with place := placeO } : P12) :=
    hp.trans (testOnOmegaIsWritten h hO)
  have hch : job.p.place.chain ≠ 1 := by
    rw [hp']
    decide
  rw [laysB_maker hB 1 job hch,
    laysB_congr bookShort 1 job (ProofFile.Honest.K12.AtFile.jobAtO ⟨K1.qAt Zp Np, 0⟩) hp' hm hf,
    qAt_written Wr Np]
  exact a

theorem bookLendsTheJobOnU : BookLendsTheJobOnU := by
  intro o Z D r Zp Np cF h Bk W X door weights rand handed hB
  exact bookLendsATestOnU o Z D r Zp Np cF h Bk W X _ hB rfl rfl rfl

theorem bookLendsTheJobOnOmega : BookLendsTheJobOnOmega := by
  intro o Z D r Zp Np cF h Bk W X record door weights rand handed hB hO
  exact bookLendsATestOnOmega o Z D r Zp Np cF h Bk W X _ record hB hO rfl rfl rfl

/-! ## 3 The new trees -/

/-- The rows of the library's job of the test on G_u read of what stands in front the heard alone,
where no vector is handed in. -/
theorem rowsOfTheTestOnUReadTheHeardAlone {W X : Type} (A : ProofFile.Honest.K14.SendPub) (p : P12)
    (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand) :
    RowsOfHeard (jobAtU A p door weights rand none).toRun.toTest := by
  refine rowsOfHeard_many _ fun m hm w fr fr' c he => ?_
  simp only [jobAtU, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> simp only [memOfSending, he]

theorem newTreesOfTheTestOnUAreTheThreadsTables : NewTreesOfTheTestOnUAreTheThreadsTables := by
  intro o Z D r Zp Np cF h W₀ Rc X₀ Cl V Pb Bk T Said weights rand testOnOmega own₀ door block hl
    hblk hseat hf hch hah htb hfix
  obtain ⟨n9, nFront, nTrees, nStages, nCount⟩ := nineWritten
  have hu := treesU_head h
  have hfront : T.front = 0 := by
    unfold Thread.front
    rw [hah]
    rfl
  have hbt : treesTo T.bs 9 = 3 := by
    rw [trees_rounds, ← rounds_alike hl]
    exact nTrees
  have hrd : roundsTo T.bs 9 = 8 := by
    unfold roundsTo
    rw [decls_rounds, ← rounds_alike hl]
    exact nFront
  have hn := n9
  rw [memberIsTheWrittenOne hl hblk] at hn
  have hn' := Option.some.inj hn
  have hrl : block.rounds.length = 35 := congrArg (·.1) hn'
  have hcn : (block.oracles.flatMap id).length = 4 := congrArg (·.2) hn'
  have hst' : (fourOf Np).U.nums.stages = piUFull.nums.stages := by rw [nums_head_U h]
  obtain ⟨s₁, t₁, rest, hstg⟩ : ∃ a b l, (fourOf Np).U.nums.stages = a :: b :: l := by
    rw [hst']
    exact ⟨_, _, _, rfl⟩
  intro blk' hblk' k s m E ds y cols hA _ hd hMv
  obtain rfl : block = blk' := Option.some.inj (hblk.symm.trans hblk')
  refine trees_of_thr T hblk
    (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door (fun c => weights c.w₀) (fun c => rand c.rc)
      none).toRun.toTest rfl
    (rowsOfTheTestOnUReadTheHeardAlone _ _ door (fun c => weights c.w₀) fun c => rand c.rc) ?_ s₁ t₁
    rest hstg hseat.place ?_ ?_ ?_ own₀ ?_ ?_ k s m E ds y cols hA hd hMv
  · show ∀ a ∈ (fourOf Np).U.nums.stages, a.h ≤ a.k
    rw [hst']
    exact stagesFoldWritten
  · rw [hseat.place]
    exact hf
  · obtain ⟨⟨l, hl', -⟩, -⟩ := hMv
    have ho := (ProofFile.Honest.Small.member_lengths (by rw [hseat.place]; exact hf) hl').1
    show (block.rounds.zip block.oracles).length =
      firstLen (fourOf Np).U.nums.stages + restLen (fourOf Np).U.nums.stages
    rw [List.length_zip, ho, Nat.min_self, hrl, hst', nCount]
  · show (block.oracles.flatMap id).length + 1 = (fourOf Np).U.nums.stages.length
    rw [hcn, hst', nStages]
  · intro τ hτ
    have hτ' : τ + 1 < 5 := by
      have e : (fourOf Np).U.nums.stages.length = 5 := by rw [hst', nStages]
      have hτ₂ : τ + 1 < (fourOf Np).U.nums.stages.length := hτ
      omega
    rw [hbt, hfront, hrd, hch, htb, Nat.zero_add]
    show (if 3 + τ < treesU (K1.qAt Zp Np) then _ else if 3 + τ < 3 then _ else
      if 3 + τ < 7 then testTbl 1 _ own₀ 8 (fun _ _ _ => true) (3 + τ - 3) else _) = _
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  · intro τ hτ
    have hτ' : τ + 1 < 5 := by
      have e : (fourOf Np).U.nums.stages.length = 5 := by rw [hst', nStages]
      have hτ₂ : τ + 1 < (fourOf Np).U.nums.stages.length := hτ
      omega
    rw [hbt, hfront, hrd, hfix τ hτ', Nat.zero_add]
    show _ = 8 + seedRound (fourOf Np).U.nums.stages τ
    rw [hst']

end ProofFile.Honest.K12.Part4

end

#print axioms ProofFile.Honest.K12.Part4.nineWritten
#print axioms ProofFile.Honest.K12.Part4.nineWritten_control
#print axioms ProofFile.Honest.K12.Part4.stagesFoldWritten
#print axioms ProofFile.Honest.K12.Part4.memberIsTheWrittenOne
#print axioms ProofFile.Honest.K12.Part4.testOnUIsWritten
#print axioms ProofFile.Honest.K12.Part4.testOnOmegaIsWritten
#print axioms ProofFile.Honest.K12.Part4.bookLendsATestOnU
#print axioms ProofFile.Honest.K12.Part4.bookLendsATestOnOmega
#print axioms ProofFile.Honest.K12.Part4.bookLendsTheJobOnU
#print axioms ProofFile.Honest.K12.Part4.bookLendsTheJobOnOmega
#print axioms ProofFile.Honest.K12.Part4.rowsOfTheTestOnUReadTheHeardAlone
#print axioms ProofFile.Honest.K12.Part4.newTreesOfTheTestOnUAreTheThreadsTables
