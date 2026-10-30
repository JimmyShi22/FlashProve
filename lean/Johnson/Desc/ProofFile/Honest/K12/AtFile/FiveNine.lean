-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/FiveNine.lean: the five sentences of the frame at member 9 of the proof
file's shared thread, at one thread and one letter: `PlaysS`, `BehindS`, `ExchangeS`, `RidesPastS`, `AcceptedS`.

  `LaidU`        what the thread's letters must be, gathered: each field is met by laying the letter
  `five_nine`    the five sentences, at any letters so laid: `rides` at 10 stays a premise

Each of the five is had above: `playsS_nine` (PlaysNine.lean); `behindS_nine`, `exchangeS_nine`,
`ridesPastS_nine` (FiveAtNine.lean); `acceptedS_head_U` with `says_head_U` (AcceptedHead.lean, AcceptedAtNine.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS: all five have `ThrS` as a premise.
- hoth and hrd speak of member 10, behind a step: what the test on G_omega reads on entry is asked there,
  and these two must be laid to serve that test too.
- THAT A STAND AT 9 IS REACHED IS NOT SAID HERE. It stands on the thread's start and on the sentences at
  members 0 to 8 of this same thread.
- At the base prover: the half is `proverSideOfProximityTest`, not read through.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.FiveAtNine
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlaysNine
import Johnson.Desc.ProofFile.Honest.K12.AtFile.StandNine
import Johnson.Desc.ProofFile.Honest.K12.AtFile.BookLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TreesAtShared
import Johnson.Desc.ProofFile.Honest.K12.AtFile.AcceptedHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey)
open OnBytes.Means (InOrder Words)
open VerifiableInference.Desc (Block Alike₂)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.Shared (MeaningS)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks frontBlock withU first)
open Desc.K14.Honest (Like)
open ProofFile.Honest
open ProofFile.Honest.K14 (mgWords form2 WitLens holds2 witAll treesU)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (fourOf)
open P2Law.ProofPlan (WP)
open H2K.Member (piUFull)
open VerifiableInference.Desc.K1 (realSized)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc X₀ P₁ Wt : Type}

/-- **What the shared thread's letters must be at member 9.** Each field is a letter or a closed fact on the
description. b1 to b8: the eight; st, wts, rnd: the job's
readers; JO, own₀: the next test's job and a value of the prover's own state. -/
structure LaidU (Zp : ProofFile.Pub) (Np : H2U.Places4) (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt)
    (ℓ : WitLens Wt) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt) (other : ℕ → St → Bool)
    (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Words Cb.Gl.E)
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (c₀ : OnBytes.Model.Verify.Chains)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (blk : Block St Cl) : Prop where
  alike : List.Forall₂ Alike₂ WP.shared.blocksInOrder L.bs
  split : L.split = true
  meaning : L.Mg = fun w => mgWords ℓ (K1.qAt Zp Np) L.N (Mg₀ w)
  shape : L.shape = form2 (K1.qAt Zp Np) other
  order : ∀ s, L.order s ↔ OnBytes.Means.InOrder s.st
  wit : ∀ k w hd, ℓ.get (L.wit k w hd) = witAll (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
    (holds2 (K1.qAt Zp Np) wts rnd) rest k w hd
  first : ∀ key, L.first key = first (K1.qAt Zp Np).codes key
  stored : ∀ w, L.stored w = st w.w₀ w.rc
  eight : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]
  front : List.Forall₂ Like (L.thread.bs.take 9) [frontBlock c₀, b1, b2, b3, b4, b5, b6, b7, b8]
  member : L.thread.bs[9]? = some blk
  seat : SeatOf blk (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest
    (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
    VerifiableInference.Desc.K12.Seat.leave
  half : (L.thread.hs.find? fun g => g.place == (fourOf Np).U.place) =
    some (proverSideOfProximityTest (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest)
  table : L.thread.table = tableShared (K1.qAt Zp Np) wts rnd
    (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest JO own₀
  fixed₀ : 1 ≤ L.thread.fixed (.own 0)
  fixedAt : ∀ τ, τ + 1 < 5 → L.thread.fixed (.own (3 + τ)) = 8 + seedRound piUFull.nums.stages τ

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- The codes' lengths are in order at the written codes. -/
theorem codes_lengths : (realSized.all fun q => q.2.lengthsOk) = true := by decide +kernel

/-- **The five sentences at member 9.** -/
theorem five_nine (h : P5J.AtMg o Z D r Zp Np cF) {x₀ : VerifiableInference.Desc.First.Look.Place}
    (hA : P5J.AtMgA o Z D r Zp Np cF x₀)
    (hBW : bookWhole WP Johnson.G.proofSendsFull.1 Johnson.G.proofSendsFull.2.1
      Johnson.G.proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok Bk)
    (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt) (ℓ : WitLens Wt)
    (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt) (other : ℕ → St → Bool)
    (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Words Cb.Gl.E)
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (c₀ : OnBytes.Model.Verify.Chains)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (blk : Block St Cl) (G : LaidU Zp Np L ℓ Mg₀ other wts rnd rest st c₀ b1 b2 b3 b4 b5 b6 b7 b8 JO own₀ blk)
    (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hrd : ∀ k s m E ds y cols s', ThrS L.thread Said 9 k s m E →
      L.thread.Stepped blk k s m E ds y cols s' → L.thread.rides 10 y.2.st.input s')
    (hoth : ∀ k s m E ds y cols s', ThrS L.thread Said 9 k s m E →
      L.thread.Stepped blk k s m E ds y cols s' → other 10 s' = true)
    (hkp : ∀ k s m E ds y cols s', ThrS L.thread Said 9 k s m E →
      L.thread.Stepped blk k s m E ds y cols s' → L.thread.keeps 9 s s')
    (hku : ∀ k s m E s', ThrS L.thread Said 9 k s m E → L.thread.keeps 9 s s' →
      keepsU (fourOf Np).U s s')
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    PlaysS L.thread Said 9 ∧ BehindS L.thread Said 9 ∧ ExchangeS L.thread Said 9 ∧
      RidesPastS L.thread Said 9 ∧ AcceptedS L.thread Said fall 9 := by
  have hB := ProofFile.Honest.K14.bookWhole_same_at_laid hBW h.scope h.laid
  obtain ⟨c2, c5, n2, n5⟩ := covers_head h hBW
  have hu := treesU_head h
  obtain ⟨hS, hM, hU⟩ := facts_at_head h
  have hbeg : ∀ k w hd s₀, L.thread.begun k w hd s₀ → s₀ = first (K1.qAt Zp Np).codes w.key :=
    fun _ w _ s₀ e => e.trans (G.first w.key)
  have hB9 : ∀ k s m E, Thr L.thread 9 k s m E → ProofFile.Honest.K12.Light.Behind (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) s :=
    fun k s m E u => ProofFile.Honest.K12.Light.behind_fold (K1.qAt Zp Np) _ G.eight hS hM _ hU _ _ _ (s, [], [])
      (stand_at_nine L.thread c₀ _ _ b1 b2 b3 b4 b5 b6 b7 b8 G.eight hU G.front rfl rfl rfl hbeg st
        G.stored u).2.2
  have hsz : (sentOf (K1.qAt Zp Np).S ++ Desc.K14.withOmega (K1.qAt Zp Np).S).size = 4 := by
    obtain ⟨sentU, layO, hQ'⟩ := ProofFile.Honest.K14.plan2_at_head hA
    have hs : sentU = sentOf (K1.qAt Zp Np).S := by
      have e : withU (K1.qAt Zp Np).S = some sentU := hQ'.facts.goes
      rw [e] at hU
      exact Option.some.inj hU
    have h2 : sentU.size = 2 := hQ'.facts.goesTwo
    rw [Array.size_append, (Desc.K14.Honest.withOmega_two hS).1, ← hs, h2]
  have hcl : ∀ k s m E, Thr L.thread 9 k s m E → s.st.codes.lengthsOk = true := fun k s m E u => by
    obtain ⟨x, hx, Wr⟩ := written_at_head h
    have q := codes_lengths
    rw [hx] at q
    simp only [Option.all_some] at q
    rw [(hB9 k s m E u).mid.codes, qAt_written Wr Np]
    exact q
  have he : (fourOf Np).U.early = true := H2K.JointK.early_of_planOk _ (planOk_head_U h)
  have ha : (fourOf Np).U.answers = 1 := H2K.JointK.answers_of_planOk _ (planOk_head_U h)
  obtain ⟨s₁, t₁, rl, hstg₀⟩ := stages_head_U h
  have hm := member_at G.alike G.member
  have hn := rounds_nine
  rw [hm] at hn
  have hrl : blk.rounds.length = 35 := congrArg (·.1) (Option.some.inj hn)
  have hrs : (blk.rounds.zip blk.oracles).length =
      firstLen (fourOf Np).U.nums.stages + restLen (fourOf Np).U.nums.stages := by
    have hz := zip_laid (fourOf Np).U (planOk_head_U h)
    have hlen := congrArg List.length (laid_head_U h)
    rw [List.length_map] at hlen
    rw [G.seat.rounds, G.seat.oracles]
    show ((proximityTestKind guardedProximityTestParts (fourOf Np).U : Block T12 Unit).rounds.zip
      (proximityTestKind guardedProximityTestParts (fourOf Np).U : Block T12 Unit).oracles).length = _
    have h35 : (proximityTestKind guardedProximityTestParts (fourOf Np).U : Block T12 Unit).rounds.length = 35 := by
      rw [← hrl]
      exact (congrArg List.length G.seat.rounds).symm
    rw [hz, hlen, h35, ProofFile.Honest.K12.Light.nums_head_U h, rounds_count]
  have hbt : treesTo L.thread.bs 9 = 3 := by
    have e : sharedR = L.thread.bs.map roundsTrees := rounds_alike G.alike
    rw [trees_rounds, ← e]
    exact trees_nine
  refine ⟨playsS_nine h hB L.thread Said G.alike wts rnd JO own₀ st _ G.member G.seat G.half rfl rfl rfl
      G.table hu c2 c5 G.fixedAt,
    behindS_nine L (K1.qAt Zp Np) Said G.split G.member _ G.seat other G.shape hoth G.order hrd hkp hcl,
    exchangeS_nine L (K1.qAt Zp Np) _ Said ℓ Mg₀ G.meaning G.split G.member _ G.seat
      (by rw [G.seat.place]; exact G.half) s₁ t₁ rl hstg₀ hrs he ha hB9 hsz (fun s => (G.order s).1),
    ridesPastS_nine L (K1.qAt Zp Np) _ Said (fourOf Np).U ℓ Mg₀ G.meaning G.split he ha hku hB9 hsz
      (fun s => (G.order s).1),
    acceptedS_head_U h hB L.thread Said wts rnd _ JO own₀ st c₀ b1 b2 b3 b4 b5 b6 b7 b8 G.eight hU
      G.front rfl rfl rfl hbeg G.stored G.member G.seat G.half hbt rfl G.table G.fixed₀ hu c2 c5 fall
      fun k s m E c u hc => says_head_U h hA hB L ℓ Mg₀ other G.alike G.split G.meaning G.shape
        (fun s => (G.order s).1) wts rnd rest G.wit G.first st G.stored c₀ b1 b2 b3 b4 b5 b6 b7 b8
        G.eight hU G.front c2 c5 n2 n5 u.1 c hc⟩

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.codes_lengths
#print axioms ProofFile.Honest.K12.AtFile.five_nine
