-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/AcceptedAtNine.lean: `AcceptedS` at member 9 of the proof file's
shared thread, from the thread's letters as the proof file lays them: the premise on values of
`acceptedS_head_U` (AcceptedHead.lean) paid by `saysAt_U` (SaysAtU.lean), `items_at_U`, `words_tied_U`.

  `trees_nine`   three trees stand in front of member 9: a closed line at the written list
  `members_head_U`   the group under test has the members 0 and 3
  `says_head_U`  `SaysAt` at a stand, at every coin lent: with it hsay of `acceptedS_head_U` is paid

The letters, and who lays them. L is a shared thread's letters (`Letters`, Honest/Thread/Shared.lean):
hbs, hsp: the description's list, split; hMg, hsh, ho, hwit: the meaning `mgWords`, the form `form2`, the
order `InOrder`, the witness (`asked_laid`, Honest/K14/AskedAtShared.lean); hfirst: the kind's first state;
hsto: the stored columns; htb, hf1: the table and the count (TableShared.lean). The book: hB the maker's;
c2, c5, n2, n5: its rows at the two sendings: closed lines at `bookShort` (LaysLines.lean) are still to be
carried to it. hpre: the first nine members are the front block and the eight: `flatOf_carried`.
hseat, hf: the member and the half. Each can be met by laying; none holds a value of a run.

Limits.
- NOT IN FRONT OF A LAW OVER COINS.
- At the base prover: the half is `proverSideOfProximityTest`, not read through.
- That a stand at 9 is reached is not said here: `AcceptedS` is a sentence from `ThrS`.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.SaysAtU
import Johnson.Desc.ProofFile.Honest.K12.OpenKindsAtEight
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey Group)
open OnBytes.Slice (GE)
open OnBytes.Means (AllSay OpenKinds InOrder layoutOf Words)
open VerifiableInference.Desc (Block Alike₂)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.Shared (MeaningS)
open Desc.K14 (St blocks frontBlock withU first)
open Desc.K14.Honest (Like)
open ProofFile.Honest
open ProofFile.Honest.K14 (jobU jobOmega sendPlace sendingPart treesU mgWords form2 WitLens holds2 witAll)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (fourOf)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- Three trees stand in front of member 9. -/
theorem trees_nine : ((sharedR.take 9).map (·.2)).sum = 3 := by decide +kernel

/-- Control: four behind it. -/
theorem trees_nine_bent : ((sharedR.take 10).map (·.2)).sum = 7 := by decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {W₀ Rc X₀ Cl P₁ Wt : Type} {Bk : ProverCoinCounts}

/-- **The group under test has the members 0 and 3.** -/
theorem members_head_U (h : P5J.AtMg o Z D r Zp Np cF) (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) (w : Common W₀ Rc TableKey) (fr : Front X₀) (G : Group)
    (hG : ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ w fr).st.groups[
      ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ w fr).g]? = some G) :
    G.members.toList = [0, 3] := by
  obtain ⟨x₀, hx₀, Wr⟩ := written_at_head h
  have hsh : ProofFile.Honest.Sh.testSh ((jobDoorU (X₀ := X₀) Zp Np bs st wts rnd).rec₀ w fr) =
      doorAt ⟨K1.qAt Zp Np, 0⟩ := shape_head_UF h bs hb _ _ _ _
  have hdoor : doorAt ⟨K1.qAt Zp Np, 0⟩ = doorAt (ProofFile.Honest.K12.Light.planOf Johnson.G.codesFull2 x₀.shape) := by
    unfold doorAt
    rw [qAt_written Wr Np]
    rfl
  have k₁ := members_U
  rw [hx₀] at k₁
  simp only [Option.all_some, beq_iff_eq] at k₁
  exact members_of_shape _ _ (hsh.trans hdoor) _ k₁ G hG

/-- **`SaysAt` at a stand, at every coin lent.** -/
theorem says_head_U (h : P5J.AtMg o Z D r Zp Np cF) {x₀ : VerifiableInference.Desc.First.Look.Place}
    (hA : P5J.AtMgA o Z D r Zp Np cF x₀)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt) (ℓ : WitLens Wt)
    (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt) (other : ℕ → St → Bool)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder L.bs) (hsp : L.split = true)
    (hMg : L.Mg = fun w => mgWords ℓ (K1.qAt Zp Np) L.N (Mg₀ w))
    (hsh : L.shape = form2 (K1.qAt Zp Np) other) (ho : ∀ s, L.order s → OnBytes.Means.InOrder s.st)
    (wts : W₀ → Weights) (rnd : Rc → TableRand) (rest : Coins Bk → Common W₀ Rc TableKey →
      List Fmt.Drawn → Words Cb.Gl.E)
    (hwit : ∀ k w hd, ℓ.get (L.wit k w hd) = witAll (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
      (holds2 (K1.qAt Zp Np) wts rnd) rest k w hd)
    (hfirst : ∀ key, L.first key = first (K1.qAt Zp Np).codes key)
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (hsto : ∀ w, L.stored w = st w.w₀ w.rc)
    (c₀ : OnBytes.Model.Verify.Chains) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hU : withU (K1.qAt Zp Np).S = some (sentOf (K1.qAt Zp Np).S))
    (hpre : List.Forall₂ Like (L.thread.bs.take 9) [frontBlock c₀, b1, b2, b3, b4, b5, b6, b7, b8])
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (n2 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 2, 0⟩).e = (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)).takes.e)
    (n5 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
      (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)).takes.e)
    {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr L.thread 9 k s m E)
    (c : RowCoins
      [(firstPart (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest :
        Part Empty _ _),
      restPart (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest])
    (hc : lendRow Bk (Bk.rowsOf 1) (k.look 1) (fourOf Np).U.place
      [(firstPart (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest :
        Part Empty _ _),
      restPart (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest]
        0 = .ok c) :
    SaysAt (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd) m.st.input (frontOf m)
      (restCoins (jobDoorU (X₀ := X₀) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] st wts rnd).toRun.toTest
        c.2.1) := by
  have hbeg : ∀ k' w hd s₀, L.thread.begun k' w hd s₀ → s₀ = first (K1.qAt Zp Np).codes w.key :=
    fun _ w _ s₀ e => e.trans (hfirst w.key)
  obtain ⟨⟨vr, vo, rest', more, hf8⟩, hen, -⟩ := stand_at_nine L.thread c₀ (K1.qAt Zp Np)
    (sentOf (K1.qAt Zp Np).S) b1 b2 b3 b4 b5 b6 b7 b8 hb hU hpre rfl rfl rfl hbeg st hsto u
  have hrec := Except.ok.inj hen
  have hK : OpenKinds s.st := openKinds_behind_eight (K1.qAt Zp Np) _ hb _ 0 vr vo (s, rest', more) hf8
  have hs := items_at_U L (K1.qAt Zp Np) ℓ Mg₀ hMg hsp u []
  rw [hwit] at hs
  refine saysAt_U _ _ _ _ (K1.qAt Zp Np) s _ (congrArg (·.st) hrec).symm (congrArg (·.g) hrec).symm
    (order_at_U L ho u) hK (rows_at_U L (K1.qAt Zp Np) other hsh u) hs
    (members_head_U h wts rnd st _ hb _ _) fun G hG => ?_
  exact words_tied_U h hA hB L.thread hl rfl wts rnd st _ hb c2 c5 n2 n5 rest u [] c.2.1
    (lendRow_second hc) G hG

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.trees_nine
#print axioms ProofFile.Honest.K12.AtFile.trees_nine_bent
#print axioms ProofFile.Honest.K12.AtFile.members_head_U
#print axioms ProofFile.Honest.K12.AtFile.says_head_U
