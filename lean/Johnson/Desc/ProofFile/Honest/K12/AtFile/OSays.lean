-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OSays.lean: `SaysAt` at the test on G_omega at the proof file's shared
thread, at a stand, from what the thread's items say at border 10 and `words_tied_O`: the premise hsay of
`acceptedS_head_O`. At border 10 the form says nothing of the rows: the group's row count comes from the door's
shape (`group_head_O`).

  `SaysO`        what the open items say at border 10, of a state and a witness's words
  `saysAt_O`     `SaysAt` from these, at a state that the seat's way in reads
  `items_at_O`   at a stand of a shared thread whose meaning is `mgWords`, the items say `SaysO`
  `order_at_O`   the statement is in order
  `fold_at_ten`, `openKinds_at_ten`   at a stand the fold over the eight and the test on G_u returns s; no open
                 row of s is marked as a sample row
  `says_head_O`  `SaysAt` at a stand, at every coin lent

The premises of `says_head_O`. L is a shared thread's letters (`Letters`, Honest/Thread/Shared.lean): hl, hsp: the
description's list, split; hMg, ho, hwit: the meaning `mgWords`, the order `InOrder`, the witness; hfirst: the kind's
first state; hpre: the first ten members are the front block, the eight and the test on G_u; hfield: the field
holds the columns that the fold read. The book: hB the maker's; c5, n5: its row at the sending.

Limits.
- NOT IN FRONT OF A LAW OVER COINS.
- At the base prover: the half behind the guard is `proverSideOfProximityTest`'s, not read through.
- That a stand at 10 is reached is not said here: it wants member 9 stepped, and `keeps` at member 9 must hold what
  the rows of member 10 ask, as `RidesPast` has no step.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OWords
import Johnson.Desc.ProofFile.Honest.K12.AtFile.SaysAtU
import Johnson.RunOne.KeyWalkAny
import Johnson.Desc.K12.Seat.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey Group GroupLayout)
open OnBytes.Slice (rdE GE)
open OnBytes.Means (AllSay OpenKinds OpenSays SampleSays InOrder rowAt_iff layoutOf sampleItem
  groundKeeps_openKinds Words)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks Alike₂)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Shared (NumbersS MeaningS ItemS)
open Desc.K14 (P14 St blocks frontBlock withU first)
open Desc.K14.Law (rowsOn RowsO)
open Desc.K14.Honest (SmpOwn Like fold_like peel_front)
open ProofFile.Honest
open ProofFile.Honest.K14 (num jobU jobOmega sendPlace sendingPart mgWords WitLens holds2 witAll)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light.ItemLaws (saysAt_of_items allSay_three)
open ProofFile.Honest.SharedThread (Letters)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- What the open items say at border 10, of a state and a witness's words. -/
def SaysO (s : St) (w : Words GE) : Prop :=
  SmpOwn (num .oOmega) s w ∧ SmpOwn (num .oSp) s w ∧ RowsO rdE 0 1 s w

/-- **`SaysAt` at the job, at a state that the seat's way in reads**, from the items and the tie. -/
theorem saysAt_O {W X : Type} (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (s : St) (m : Words GE)
    (hst : (A.rec₀ w fr).st = s.st) (hg : (A.rec₀ w fr).g = s.loc.gOmega)
    (hI : OnBytes.Means.InOrder s.st) (hK : OpenKinds s.st)
    (hrows : (rowsOn s s.loc.gOmega).length ≤ 1)
    (hs : SaysO s m)
    (hmem : ∀ G, (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? = some G → G.members.toList = [2, 3])
    (hw : ∀ G, (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? = some G →
      WordsTied (A.rec₀ w fr).st (A.rec₀ w fr).g G m (layoutOf (A.rec₀ w fr).st G)
        (plainMany A w fr C)) :
    SaysAt A w fr C := by
  obtain ⟨sO, sS, r1⟩ := hs
  have hall : AllSay rdE s.st (rowsOn s s.loc.gOmega) m :=
    allSay_three rdE s.st _ _ 1 0 0 hrows r1 (fun r hr => by simp at hr) (fun r hr => by simp at hr)
  refine saysAt_of_items _ _ _ C _ (by rw [hst]; exact hI) (by rw [hst]; exact hK)
    (by rw [hst, hg]; exact open_of_rowsOn hall) (fun G hG => ?_) hw
  rw [hmem G hG, hst]
  intro o ho
  rcases List.mem_cons.1 ho with rfl | ho
  · exact samples_of_smp sO
  · rcases List.mem_cons.1 ho with rfl | ho
    · exact samples_of_smp sS
    · cases ho

/-- **The fold over the eight and the test on G_u keeps "no open row is marked as a sample row".** -/
theorem openKinds_at_ten (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs) (p : P12)
    (key : TableKey) (ft : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (out : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)])
      (first Q.codes key) rs cols = .ok out) : OpenKinds out.1.st :=
  VerifiableInference.Desc.Keeps.foldBlocks_keeps
    (VerifiableInference.Desc.Ground.By (fun a b => OpenKinds a → OpenKinds b) Desc.K14.stOf)
    (fun _ k => k) (fun _ _ _ k₁ k₂ x => k₂ (k₁ x)) ft _
    (fun b hm => by
      rcases List.mem_append.1 hm with hm | hm
      · exact Desc.K14.blocks_keep groundKeeps_openKinds Q bs hb b hm
      · rcases List.mem_cons.1 hm with rfl | hm
        · exact VerifiableInference.Desc.K12.Seat.onGu_keeps
            (R := fun a b => OpenKinds a.st → OpenKinds b.st) _
            (Johnson.RunOne.KeyWalk.k12_decides_any groundKeeps_openKinds
              Johnson.RunOne.KeyWalk.begin_openKinds _)
        · cases hm) _ rs cols out h (OpenKinds.start Q.codes)

section
variable {Bk : ProverCoinCounts} {Cl V Pb W₀ Rc X₀ : Type}

/-- **At a stand at 10 the fold over the eight and the test on G_u returns the stand's state.** -/
theorem fold_at_ten (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (c : OnBytes.Model.Verify.Chains) (Q : P14) (bs : List (Block St Unit)) (pU : P12)
    (hpre : List.Forall₂ Like (T.bs.take 10) (frontBlock c ::
      (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts pU)])))
    (hah : T.ahead = []) (hft : T.ft = 0)
    (hbeg : ∀ k w h s₀, T.begun k w h s₀ → s₀ = first Q.codes w.key)
    {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 10 k s m E) :
    ∃ cols, foldBlocks 0 (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts pU)])
      (first Q.codes m.st.input.key) m.seen cols = .ok (s, [], []) := by
  obtain ⟨-, -, -, -, made, -, -⟩ := u
  obtain ⟨-, -, -, -, s₀, cols, hbeg', -, hfold⟩ := made
  obtain rfl := hbeg _ _ _ _ hbeg'
  have hfront : T.front = 0 := by
    unfold Thread.front
    rw [hah]
    rfl
  have hfold' : foldBlocks 0 (T.bs.take 10) (first Q.codes m.st.input.key) m.seen cols =
      .ok (s, [], []) := by
    have e := hfold
    rw [hfront, List.drop_zero, hft] at e
    exact e
  exact ⟨cols, peel_front c 0 _ _ _ _ _ (fold_like 0 _ _ hpre _ _ _ _ hfold')⟩

end

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc X₀ P₁ Wt : Type}
  (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt) (Q : P14)

/-- **The items at border 10**, at a shared thread whose meaning is `mgWords`. -/
theorem items_at_O (ℓ : WitLens Wt) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
    (hMg : L.Mg = fun w => mgWords ℓ Q L.N (Mg₀ w)) (hsp : L.split = true) {k : Coins Bk} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr L.thread 10 k s m E)
    (ds : List Fmt.Drawn) :
    SaysO s (ℓ.get (L.wit k m.st.input (m.st.heard ++ ds))) := by
  have hI := u.2.2.2.1 ds
  have key : ∀ i, i ∈ L.thread.opened 10 → ItemS.holdsSh L.N (mgWords ℓ Q L.N (Mg₀ m.st.input)) i s
      (L.thread.strs E) (L.wit k m.st.input (m.st.heard ++ ds)) := fun i hi => by
    have e := hI i hi
    change ItemS.holdsSh L.N (L.Mg m.st.input) i s (L.thread.strs E)
      (L.wit k m.st.input (m.st.heard ++ ds)) at e
    rw [hMg] at e
    exact e
  have hop : ∀ i, i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 10 → i ∈ L.thread.opened 10 :=
    fun i hi => by
      show i ∈ fwdOpen SharedRows.start (SharedRows.rows L.split) 10
      rw [hsp]
      exact hi
  refine ⟨key (ItemS.row (.sample .oOmega)) (hop _ ?_), key (ItemS.row (.sample .oSp)) (hop _ ?_),
    key (ItemS.row .foldOmega) (hop _ ?_)⟩
  all_goals decide

/-- The statement is in order, at a shared thread whose order is that. -/
theorem order_at_O (ho : ∀ s, L.order s → OnBytes.Means.InOrder s.st) {k : Coins Bk} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr L.thread 10 k s m E) : OnBytes.Means.InOrder s.st :=
  ho s u.2.2.1.2

end

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}
  {W₀ Rc X₀ Cl P₁ Wt : Type} {Bk : ProverCoinCounts}

set_option maxHeartbeats 1000000 in
/-- **`SaysAt` at a stand, at every coin lent.** -/
theorem says_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    {x₀ : VerifiableInference.Desc.First.Look.Place} (hA : P5J.AtMgA o Z D r Zp Np cF x₀)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt) (ℓ : WitLens Wt)
    (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder L.bs) (hsp : L.split = true)
    (hMg : L.Mg = fun w => mgWords ℓ (K1.qAt Zp Np) L.N (Mg₀ w))
    (ho : ∀ s, L.order s → OnBytes.Means.InOrder s.st)
    (wts : W₀ → Weights) (rnd : Rc → TableRand) (rest : Coins Bk → Common W₀ Rc TableKey →
      List Fmt.Drawn → Words Cb.Gl.E)
    (hwit : ∀ k w hd, ℓ.get (L.wit k w hd) = witAll (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)
      (holds2 (K1.qAt Zp Np) wts rnd) rest k w hd)
    (hfirst : ∀ key, L.first key = first (K1.qAt Zp Np).codes key)
    (c₀ : OnBytes.Model.Verify.Chains) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs)
    (hpre : List.Forall₂ Like (L.thread.bs.take 10) (frontBlock c₀ ::
      (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts (fourOf Np).U)])))
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (n5 : (dueAt (Bk.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
      (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)).takes.e)
    {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr L.thread 10 k s m E)
    (hfield : ∀ cols, L.thread.colsTo 10 m E = .ok cols → m.opened = some cols)
    (c : RowCoins
      [(firstPart (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest : Part Empty _ _),
      restPart (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest])
    (hc : lendRow Bk (Bk.rowsOf 1) (k.look 1) pO.place
      [(firstPart (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest : Part Empty _ _),
      restPart (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest] 0 = .ok c) :
    SaysAt (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd) m.st.input (frontOf m)
      (restCoins (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest c.2.1) := by
  have hbeg : ∀ k' w hd s₀, L.thread.begun k' w hd s₀ → s₀ = first (K1.qAt Zp Np).codes w.key :=
    fun _ w _ s₀ e => e.trans (hfirst w.key)
  have hen := enters_at_ten L.thread c₀ (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U hpre
    rfl rfl hbeg u hfield
  have hrec := Except.ok.inj hen
  obtain ⟨cols, hf⟩ := fold_at_ten L.thread c₀ (K1.qAt Zp Np) bs (fourOf Np).U hpre rfl rfl hbeg u
  have hK : OpenKinds s.st := openKinds_at_ten (K1.qAt Zp Np) bs hb (fourOf Np).U _ 0 _ cols
    (s, [], []) hf
  have hs := items_at_O L (K1.qAt Zp Np) ℓ Mg₀ hMg hsp u []
  rw [hwit] at hs
  have hstE : ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).st = s.st := by
    rw [rec_door]
    exact (congrArg (·.st) hrec).symm
  have hgE : ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).g = s.loc.gOmega := by
    rw [rec_door]
    exact (congrArg (·.g) hrec).symm
  have hsh : ProofFile.Honest.Sh.testSh ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)) =
      headShape Zp Np := by
    rw [rec_door]
    exact shape_head_OmegaF h bs hb _ _ _ _
  have hrows : (rowsOn s s.loc.gOmega).length ≤ 1 := by
    unfold rowsOn
    cases hG : s.st.groups[s.loc.gOmega]? with
    | none => exact Nat.zero_le _
    | some G =>
      have hG' : ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).st.groups[
          ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ m.st.input (frontOf m)).g]? = some G := by
        rw [hstE, hgE]
        exact hG
      exact Nat.le_of_eq (group_at_stand h _ hsh G hG').1
  refine saysAt_O _ _ _ _ s _ hstE hgE (order_at_O L ho u) hK hrows hs
    (fun G hG => (group_at_stand h _ hsh G hG).2) fun G hG => ?_
  exact words_tied_O h hO hA hB L.thread hl rfl wts rnd bs hb c5 n5 rest u [] c.2.1
    (lendRow_second hc) G hG

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.SaysO
#print axioms ProofFile.Honest.K12.AtFile.saysAt_O
#print axioms ProofFile.Honest.K12.AtFile.openKinds_at_ten
#print axioms ProofFile.Honest.K12.AtFile.fold_at_ten
#print axioms ProofFile.Honest.K12.AtFile.items_at_O
#print axioms ProofFile.Honest.K12.AtFile.order_at_O
#print axioms ProofFile.Honest.K12.AtFile.says_head_O
