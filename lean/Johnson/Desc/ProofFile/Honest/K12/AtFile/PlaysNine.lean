-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/PlaysNine.lean: `PlaysS` at member 9 of the proof file's shared
thread, at the job at the seated place: `playsS_at_test` with its premises paid.

  `member_at`    what the list declares at a member is the written list's, through `Alike₂`
  `rounds_nine`, `rounds_ten`, `front_rounds`, `rounds_count`   closed lines: 35 rounds and 4 trees at
                 member 9, 24 and 4 at member 10, 8 rounds in front
  `hk_U`, `len_U`  closed lines on the place's stages
  `rows_heard_U`  the job's rows read the heard alone
  `playsS_nine`  the statement

The premises. As `acceptedS_head_U` (AcceptedHead.lean), and hfix: the thread's count at own 3 to 6 is the
round of the test's tree: `fixedShared` with `sent_shared` and `seed_U` (TableLines.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS.
- A sentence from a stand: that a stand is reached is not said here.
- `hT` is the second half of the conclusion: it is paid here by `trees_of_thr`, not assumed.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.AcceptedAtNine
import Johnson.Desc.ProofFile.Honest.Small.SaysYesOf
import Johnson.Desc.ProofFile.Honest.K12.TreesOfThr

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Alike₂)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks)
open ProofFile.Honest
open ProofFile.Honest.K14 (jobU jobOmega sendPlace treesU)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (fourOf)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open H2K.Member (piUFull)
open H2K.Pub (sgOf)

/-- What a list alike to the written one declares at a member. -/
theorem member_at {S Cl : Type} {l : List (Block S Cl)} (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder l)
    {b : ℕ} {blk : Block S Cl} (hb : l[b]? = some blk) : sharedR[b]? = some (roundsTrees blk) := by
  have e : sharedR = l.map roundsTrees := rounds_alike hl
  rw [e, List.getElem?_map, hb]
  rfl

/-- Member 9 declares 35 rounds and 4 trees. -/
theorem rounds_nine : (sharedR[9]?).map (fun x => (x.1.length, x.2)) = some (35, 4) := by decide +kernel

/-- Control: member 10 has 24 rounds. -/
theorem rounds_ten : (sharedR[10]?).map (fun x => (x.1.length, x.2)) = some (24, 4) := by decide +kernel

/-- Eight rounds stand in front of member 9. -/
theorem front_rounds : ((sharedR.take 9).flatMap (·.1)).length = 8 := by decide +kernel

theorem hk_U : ∀ a ∈ piUFull.nums.stages, a.h ≤ a.k := by decide +kernel

theorem len_U : piUFull.nums.stages.length = 5 := by decide +kernel

theorem rounds_count : firstLen piUFull.nums.stages + restLen piUFull.nums.stages = 35 := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {W₀ Rc X₀ Cl V Pb : Type} {Bk : ProverCoinCounts}

/-- The job's rows read the heard alone. -/
theorem rows_heard_U (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (bs : List (Block St Unit)) :
    RowsOfHeard (jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).toRun.toTest := by
  refine rowsOfHeard_many _ fun m hm w fr fr' c he => ?_
  simp only [jobDoorU, jobAtU, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> simp only [memOfSending, he]

/-- **It plays at member 9, and its new trees are the thread's tables.** -/
theorem playsS_nine (h : P5J.AtMg o Z D r Zp Np cF)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb) (Said : ℕ → Coins Bk → Mid _ X₀ → Prop)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder T.bs)
    (wts : W₀ → Weights) (rnd : Rc → TableRand) (JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (bs : List (Block St Unit))
    {blk : Block St Cl} (hblk : T.bs[9]? = some blk)
    (hseat : SeatOf blk (jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).toRun.toTest
      (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
      VerifiableInference.Desc.K12.Seat.leave)
    (hf : (T.hs.find? fun g => g.place == (fourOf Np).U.place) =
      some (proverSideOfProximityTest (jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).toRun.toTest))
    (ht : T.taken = []) (hch : T.chain = 1) (hah : T.ahead = [])
    (htb : T.table = tableShared (K1.qAt Zp Np) wts rnd
      (jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).toRun.toTest JO own₀)
    (hu : treesU (K1.qAt Zp Np) = 1)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (hfix : ∀ τ, τ + 1 < 5 → T.fixed (.own (3 + τ)) = 8 + seedRound piUFull.nums.stages τ) :
    PlaysS T Said 9 := by
  have hfront : T.front = 0 := by
    unfold Thread.front
    rw [hah]
    rfl
  have hbt : treesTo T.bs 9 = 3 := by
    rw [trees_rounds, ← rounds_alike hl]
    exact trees_nine
  have hrd : roundsTo T.bs 9 = 8 := by
    unfold roundsTo
    rw [decls_rounds, ← rounds_alike hl]
    exact front_rounds
  have hm := member_at hl hblk
  have hn := rounds_nine
  rw [hm] at hn
  have hn' := Option.some.inj hn
  have hrl : blk.rounds.length = 35 := congrArg (·.1) hn'
  have hcn : (blk.oracles.flatMap id).length = 4 := congrArg (·.2) hn'
  have hnums := ProofFile.Honest.K12.Light.nums_head_U h
  obtain ⟨s₁, t₁, rest, hstg₀⟩ := stages_head_U h
  have hstg : (jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).toRun.toTest.p.nums.stages =
      s₁ :: t₁ :: rest := hstg₀
  have hk : s₁.k = (sgOf s₁).h + (sgOf s₁).g := by
    have e := k_head_U h
    rw [hstg₀] at e
    exact e
  have hst' : (fourOf Np).U.nums.stages = piUFull.nums.stages := by rw [hnums]
  refine playsS_at_test T Said hblk _ _ _ hseat s₁ t₁ rest hstg hk hf 3
    (planPlays_head_U h _ rfl rfl s₁ (t₁ :: rest) hstg) hbt ?_ ?_ ?_
  · intro k s m E c u hc
    rw [hch] at hc
    exact agree_head_U h hB _ (fun c => wts c.w₀) (fun c => rnd c.rc) _ _ c hc _ _
  · intro k s m E u
    exact old_head_U h T wts rnd _ JO own₀ hbt ht htb c2 c5 (by omega) u.1
  · intro k s m E ds y cols u hd hMv
    refine trees_of_thr T hblk _ rfl (rows_heard_U wts rnd st bs) ?_ s₁ t₁ rest hstg hseat.place ?_ ?_ ?_
      own₀ ?_ ?_ k s m E ds y cols u.1 hd hMv
    · show ∀ a ∈ (fourOf Np).U.nums.stages, a.h ≤ a.k
      rw [hst']
      exact hk_U
    · rw [hseat.place]
      exact hf
    · obtain ⟨⟨l, hl', -⟩, -⟩ := hMv
      have ho := (ProofFile.Honest.Small.member_lengths (by rw [hseat.place]; exact hf) hl').1
      show (blk.rounds.zip blk.oracles).length =
        firstLen (fourOf Np).U.nums.stages + restLen (fourOf Np).U.nums.stages
      rw [List.length_zip, ho, Nat.min_self, hrl, hst', rounds_count]
    · show (blk.oracles.flatMap id).length + 1 = (fourOf Np).U.nums.stages.length
      rw [hcn, hst', len_U]
    · intro τ hτ
      have hτ' : τ + 1 < 5 := by
        have e : (fourOf Np).U.nums.stages.length = 5 := by rw [hst', len_U]
        have hτ₂ : τ + 1 < (fourOf Np).U.nums.stages.length := hτ
        omega
      rw [hbt, hfront, hrd, hch, htb, Nat.zero_add]
      show (if 3 + τ < treesU (K1.qAt Zp Np) then _ else if 3 + τ < 3 then _ else
        if 3 + τ < 7 then testTbl 1 _ own₀ 8 (fun _ _ _ => true) (3 + τ - 3) else _) = _
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
    · intro τ hτ
      have hτ' : τ + 1 < 5 := by
        have e : (fourOf Np).U.nums.stages.length = 5 := by rw [hst', len_U]
        have hτ₂ : τ + 1 < (fourOf Np).U.nums.stages.length := hτ
        omega
      rw [hbt, hfront, hrd, hfix τ hτ', Nat.zero_add]
      show _ = 8 + seedRound (fourOf Np).U.nums.stages τ
      rw [hst']

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.member_at
#print axioms ProofFile.Honest.K12.AtFile.rounds_nine
#print axioms ProofFile.Honest.K12.AtFile.rounds_ten
#print axioms ProofFile.Honest.K12.AtFile.front_rounds
#print axioms ProofFile.Honest.K12.AtFile.rows_heard_U
#print axioms ProofFile.Honest.K12.AtFile.playsS_nine
