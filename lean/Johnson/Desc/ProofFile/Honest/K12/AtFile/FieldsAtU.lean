-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/FieldsAtU.lean: three of the five fields of `K12At`
(K12/SaysYesK12.lean) at the test on G_u, at a stand of the thread: `enters`, `agree`, `count`.

  `stand_at_nine`, `enters_at_nine`   at a stand at border 9 of a shared thread whose first nine members
                 are like the front block and the eight, the fold over the eight returns the stand's
                 state, also at the door's own columns, and the seat's way in is the job's state on entry
                 (`doorUF`): so at such a stand the door takes no fall-back. General in the thread
  `first_k_U`, `k_head_U`   k = h + g at the first stage
  `agree_head_U`   the two parts' readers agree at the coins that the frame lends: `agree_of_ties_letter`
                 (K12/AgreeAtKey.lean) at the book's ties under the head (`hT_head_U`)
  `count_of_plan`   the term has as many rounds as the block declares: `length_test` and `PlanPlays.count`

By what. `door_of_called` (K12/DoorAnyRun.lean), with `Thread.Made`'s fold: what the walk hands
`called_at_run`, the thread holds at a stand: the fold in front of the test and the columns it read.

The premises of `enters_at_nine`. hpre: the first nine members are alike to the front block and the eight
(`Like`, Johnson/Desc/K14/Honest/FlatForm.lean): `flatOf_carried`. hah, hch, hft: the thread has no round
in front, its number is 1, its first tree's number is 0. hbeg: it begins at the kind's first state.
hst: its stored columns are st's.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `enters_at_nine` and `agree_head_U` stand at a stand or at coins lent.
- `enters_at_nine` says that the state on entry is the verifier's where the thread stands: that the
  thread stands is not said.
- `agree_head_U` takes the book as the maker's (hB); that a filling's book is that book is not said.
- The two other fields, `opens` and `accepts`, are not here.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorAnyRun
import Johnson.Desc.ProofFile.Honest.K12.DoorAtWalk
import Johnson.Desc.ProofFile.Honest.K12.AgreeAtKey
import Johnson.Desc.ProofFile.Honest.K12.OnFreeTAtHeadU
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12
import Johnson.Desc.ProofFile.Honest.K12.TermLen
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFirstAtU
import AtFullSide.K12.TiesAtHeadU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open OnBytes (TableKey OracleNotice)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (P14 St blocks withU first frontBlock)
open Desc.K14.Honest (Like)
open H2K.Pub (sgOf)
open H2K.Member (piUFull)
open Johnson.G (proofSendsFull)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (doorUF colsLoc door_of_called door_of_cols jobAtU nums_head_U rowsMu_many)

section
variable {Cl V Pb W₀ Rc X₀ : Type} {Bk : ProverCoinCounts}

/-- **At a stand at border 9 the fold over the eight returns the stand's state, and the seat's way in is
the job's state on entry.** -/
theorem stand_at_nine (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (c : OnBytes.Model.Verify.Chains) (Q : P14) (sentU : Array OracleNotice)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU Q.S = some sentU)
    (hpre : List.Forall₂ Like (T.bs.take 9) [frontBlock c, b1, b2, b3, b4, b5, b6, b7, b8])
    (hah : T.ahead = []) (hch : T.chain = 1) (hft : T.ft = 0)
    (hbeg : ∀ k w h s₀, T.begun k w h s₀ → s₀ = first Q.codes w.key)
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (hst : ∀ w, T.stored w = st w.w₀ w.rc)
    {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 9 k s m E) :
    (∃ vr vo rest' more, foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8]
        (first Q.codes m.st.input.key) vr vo = .ok (s, rest', more)) ∧
      VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask) s =
        .ok (doorUF Q sentU [b1, b2, b3, b4, b5, b6, b7, b8] (fun w => w.key)
          (fun w fr => colsLoc Q (st w.w₀ w.rc) fr.seen.rounds) m.st.input (frontOf m)) ∧
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first Q.codes m.st.input.key)
        (frontOf m).seen.rounds
        (colsLoc Q (st m.st.input.w₀ m.st.input.rc) (frontOf m).seen.rounds) = .ok (s, [], []) := by
  obtain ⟨hand, hfit, -, -, made, -, -⟩ := u
  obtain ⟨hsm, -, -, -, s₀, cols, hbeg', hcols, hfold⟩ := made
  obtain rfl := hbeg _ _ _ _ hbeg'
  have hfront : T.front = 0 := by
    unfold Thread.front
    rw [hah]
    rfl
  have hd : T.ahead ++ declsTo T.bs 9 = (T.bs.take 9).flatMap (·.rounds) := by
    rw [hah, List.nil_append]
    rfl
  have hlen : m.seen.length = ((T.bs.take 9).flatMap (·.rounds)).length := by
    have e := drawsFit_length _ _ hfit
    have e2 := congrArg List.length hsm
    rw [List.length_map] at e2
    exact e2.trans (e.trans (congrArg List.length hd))
  have htk : m.seen.take ((T.bs.take 9).flatMap (·.rounds)).length = m.seen := by
    rw [← hlen]
    exact List.take_length
  have hstE : E.stored = st m.st.input.w₀ m.st.input.rc :=
    funext fun i => funext fun p => by rw [hand.1 i p, hst]
  have hfold' : foldBlocks 0 (T.bs.take 9) (first Q.codes m.st.input.key)
      (m.seen.take ((T.bs.take 9).flatMap (·.rounds)).length) cols = .ok (s, [], []) := by
    rw [htk]
    have e := hfold
    rw [hfront, List.drop_zero, hft] at e
    exact e
  have hfill : fillCols (readsOf 1 0 E.stored E.tree ((T.bs.take 9).flatMap (·.rounds))
      ((m.seen.take ((T.bs.take 9).flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cols := by
    rw [htk, hsm, ← hd, hah, List.nil_append]
    have e := hcols
    unfold Thread.colsTo at e
    rw [hfront, List.drop_zero, hch, hft] at e
    exact e
  obtain ⟨⟨rest', hf8⟩, eR, hdoor⟩ := door_of_called (V := Common W₀ Rc TableKey) (X := X₀) c Q sentU
    b1 b2 b3 b4 b5 b6 b7 b8 hb hU (T.bs.take 9) hpre E.stored E.tree m.st.input.key m.seen [] m.seen
    cols [] cols s (List.append_nil _).symm (List.append_nil _).symm hfold' hfill
  have hfill' := hfill
  rw [eR] at hfill'
  have hfold'' := hfold'
  rw [eR] at hfold''
  have hC := (door_of_cols (V := Common W₀ Rc TableKey) (X := X₀) c Q sentU b1 b2 b3 b4 b5 b6 b7 b8 hb
    hU _ hpre 1 E.stored E.tree m.st.input.key _ cols s hfold'' hfill').1
  rw [← eR, htk, hstE] at hC
  exact ⟨⟨_, _, _, _, hf8⟩,
    hdoor (fun v => v.key) (fun v => st v.w₀ v.rc) m.st.input (frontOf m) rfl hstE.symm htk.symm, hC⟩

/-- **At a stand at border 9 the seat's way in is the job's state on entry.** -/
theorem enters_at_nine (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (c : OnBytes.Model.Verify.Chains) (Q : P14) (sentU : Array OracleNotice)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU Q.S = some sentU)
    (hpre : List.Forall₂ Like (T.bs.take 9) [frontBlock c, b1, b2, b3, b4, b5, b6, b7, b8])
    (hah : T.ahead = []) (hch : T.chain = 1) (hft : T.ft = 0)
    (hbeg : ∀ k w h s₀, T.begun k w h s₀ → s₀ = first Q.codes w.key)
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64)) (hst : ∀ w, T.stored w = st w.w₀ w.rc)
    {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 9 k s m E) :
    VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask) s =
      .ok (doorUF Q sentU [b1, b2, b3, b4, b5, b6, b7, b8] (fun w => w.key)
        (fun w fr => colsLoc Q (st w.w₀ w.rc) fr.seen.rounds) m.st.input (frontOf m)) :=
  (stand_at_nine T c Q sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hU hpre hah hch hft hbeg st hst u).2.1

end

/-- k = h + g at the first stage of the written place. By the kernel. -/
theorem first_k_U : (piUFull.nums.stages.headD default).k =
    (sgOf (piUFull.nums.stages.headD default)).h + (sgOf (piUFull.nums.stages.headD default)).g := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- Under the head k = h + g at the first stage of the seated place. -/
theorem k_head_U (h : P5J.AtMg o Z D r Zp Np cF) :
    ((fourOf Np).U.nums.stages.headD default).k =
      (sgOf ((fourOf Np).U.nums.stages.headD default)).h +
        (sgOf ((fourOf Np).U.nums.stages.headD default)).g := by
  rw [nums_head_U h]
  exact first_k_U

/-- **`RunPlays.agree` and `K12At.agree` at the job at the seated place**, at every door and reader, at
every coin that the frame lends, at whatever book the maker returns at the proof file's own
description. -/
theorem agree_head_U {V W₀ Rc X₀ : Type} (h : P5J.AtMg o Z D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (door : Common W₀ Rc TableKey → Front X₀ → T12)
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins
      [(firstPart (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand none).toRun.toTest :
        Part V _ _),
      restPart (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand none).toRun.toTest])
    (hc : lendRow Bk rows look (fourOf Np).U.place
      [(firstPart (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand none).toRun.toTest :
        Part V _ _),
      restPart (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand none).toRun.toTest] 0 = .ok c)
    (w : Common W₀ Rc TableKey) (fr : Front X₀) :
    Agree (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand none).toRun.toTest w fr
      (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand none).toRun.toTest.s₀
      (firstRd (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand none).toRun.toTest c.1)
      (restCoins (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand none).toRun.toTest c.2.1) :=
  agree_of_ties_letter _ (⟨ProofFile.Honest.K14.sendPlace 2, 0⟩, 1) rfl Bk rows look c hc w fr
    (AtFullSide.K12.hT_head_U h hB [] (fun _ _ _ _ => none) weights rand (none : Option (_ → Front X₀ → _)))
    (k_head_U h) fun mem mem' e => rowsMu_many _ _ w fr mem mem' e

/-- **`K12At.count`**: the term has as many rounds as the block declares. -/
theorem count_of_plan {W X : Type} (J : TestJob W X) (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (sent : ℕ) (P : PlanPlays J s rest sent) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) :
    (testAll J w fr C D).rs.length = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length :=
  (length_test J w fr C D).trans P.count

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.stand_at_nine
#print axioms ProofFile.Honest.K12.AtFile.enters_at_nine
#print axioms ProofFile.Honest.K12.AtFile.first_k_U
#print axioms ProofFile.Honest.K12.AtFile.k_head_U
#print axioms ProofFile.Honest.K12.AtFile.agree_head_U
#print axioms ProofFile.Honest.K12.AtFile.count_of_plan
