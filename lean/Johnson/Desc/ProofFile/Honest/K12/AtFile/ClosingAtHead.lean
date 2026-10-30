-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingAtHead.lean: the laws on the first chain's closing
proximity test called at the library's own thread (`lettersHead`, Honest/Thread/FirstHead.lean), at
member 354, at the job `jobL` at the filled door.

  `step_of_member`, `keeps_of_step`   an accepting step of the member is an accept of the test
                      (`K12Step`), and gives `K12KeepsFirst`
  `exchangeS_head_L`  `ExchangeS`: the test owes nothing behind it
  `behindS_head_L`    `BehindS`: it pays the form and the reply, and takes keeps and the riders as premises
  `acceptedS_head_L`  `AcceptedS`
  `plays_head_L`      `Plays`

By what. `letterAtL_head` (ClosingHead.lean), `acceptedS_at_L` (ClosingAtL.lean), `plays_jobL`
(ClosingPlays.lean), `exchangeS_at_L` (ClosingExchange.lean), `k12_form_behind` (K12/Law/FormBehind.lean),
`k12KeepsFirst_of_yes` (Johnson/Desc/K12/Honest/Shape/TestKeepsFirst.lean), `IM.at_354`,
`planPlays_head_L` (ClosingLinesHead.lean), `treesTo_354` (K12/OffAt354.lean).

Hypotheses. h: the head. hh: the side at the test's place is the job's half. `behindS_head_L`: hK: the
letter Kp holds behind the member's step at a stand; hb0: from the border b₀ on, which lies at or in front of the
test, the reply is the one asked; hRd: the letter Rd goes past what the member keeps.
`acceptedS_head_L`: hs: what is asked at a stand. `plays_head_L`: the premises of `plays_jobL` but for
the plan and the trees in front.

Limits.
- Every premise of `acceptedS_at_L` and `plays_jobL` on a stand stays a premise here: so these say
  nothing of a run until those are paid. Where one stand fails hs, `acceptedS_head_L` says nothing of
  any run.
- Full size, the format's own hash alone.
- Nothing on completeness of the chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `behindS_head_L`, `acceptedS_head_L`, `plays_head_L` and
`exchangeS_head_L` bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: the thread from `ThrS` or `Thr` as a premise.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingPile
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingClosed
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingExchange
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingPlays
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingLinesHead
import Johnson.Desc.ProofFile.Honest.K12.Law.FormBehind
import Johnson.Desc.K12.Honest.Shape.TestKeepsAt354
import Johnson.Desc.ProofFile.Honest.K12.OffAt354

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block Chain Place OpenedColumn Strs)
open VerifiableInference.Desc.K12 (T12 enterFinish proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open H2K.Pub (sgOf)
open H2K.JointK (outCore)
open ProofFile.Honest.FirstThread (lettersHead Script WtF head_keeps head_rest)
open ProofFile.Honest.K12.AtProof (jobL doorAtL placeL numbersL_at_head)
open ProofFile.Honest.Sh (K12KeepsFirst k12KeepsFirst_of_yes answers_at_head)
open ProofFile.Honest.K12.AtFile (planPlays_head_L)
open P5J (AtMg AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **An accepting step of the member is an accept of the test**, at whatever rounds. -/
theorem step_of_member (h : AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF) {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[354]? = some blk) (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (e : blk.step ft s rs cols = .ok (s', cols.length)) :
    K12Step (H2U.p12OfMade Zp.made) s s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨⟨rs', gs, hd⟩, -, -⟩ := IM.at_354 h.scope h.reads O hb e
  exact ⟨rs', gs, hd⟩

/-- An accept of the test gives `K12KeepsFirst`. -/
theorem keeps_of_step (h : AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF) {s s' : S}
    (Y : K12Step (H2U.p12OfMade Zp.made) s s') : K12KeepsFirst (H2U.p12OfMade Zp.made) s s' := by
  obtain ⟨rs', gs, hd⟩ := Y
  exact k12KeepsFirst_of_yes _ (answers_at_head h) s s' rs' gs hd

section
variable (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **`ExchangeS` at the member.** -/
theorem exchangeS_head_L :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 354 :=
  exchangeS_at_L _ Said ps_354

/-- **`BehindS` at the member.** -/
theorem behindS_head_L
    (hK : ∀ blk, cF.blocksInOrder[354]? = some blk → ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 354 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y cols
        s' → Kp placeL s s')
    (hb0 : b₀ ≤ 354)
    (hRd : ∀ v s s', K12KeepsFirst (H2U.p12OfMade Zp.made) s s' → Rd 354 v s → Rd (354 + 1) v s') :
    BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 354 := by
  intro blk hb k s m E ds y cols s' hT hd hS
  have hbk : cF.blocksInOrder[354]? = some blk := hb
  have Y := step_of_member h.toAtMg hbk _ s s' _ cols hS.2
  have K := keeps_of_step h.toAtMg Y
  refine ⟨k12_form_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w blk hbk k s m E ds y cols s'
    hT.1 hS, ?_, (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w ps_354 s s').2
      (hK blk hbk k s m E ds y cols s' hT hd hS)⟩
  obtain ⟨⟨st, -, hyp⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hyp
  have h' := hT.1
  unfold Thr at h'
  obtain ⟨-, -, -, -, -, hR0, -⟩ := h'
  have hR1 := (head_rest h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).1 hR0
  rw [ei]
  refine (head_rest h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).2 ⟨fun _ => ?_, hRd _ s s' K hR1.2⟩
  rw [K.out]
  exact hR1.1 hb0

variable (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
  (closing : K2.Closing) (pl : K2.SwitchPlace)
  (hh : (H.first.find? fun g => g.place == (H2U.p12OfMade Zp.made).place) =
    some (proverSideOfProximityTest (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl)))
include hh

/-- **`AcceptedS` at the member**, from what is asked at a stand. -/
theorem acceptedS_head_L
    (hs : ∀ k st m E R (J' : TestJob (Local W₀ Rc ProofFile.Inst Tr) X),
      J' = atStand (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) m.st.input
        (frontOf m) R →
      ∀ c : RowCoins [(firstPart J' :
          Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X), restPart J'],
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 354 k st m E →
      enterFinish st = .ok R →
      lendRow Bk (Bk.rowsOf (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain)
        (k.look (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain) J'.p.place
        [(firstPart J' : Part (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X), restPart J'] 0 =
          .ok c →
      FrontAtT J' (outCore ProofFile.sameReply) st m E c)
    (fl : ℕ → S → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fl 354 := by
  obtain ⟨blk, pre, t, hm, HL⟩ := letterAtL_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w D readers
    closing pl hh
  exact acceptedS_at_L HL hm Said hs fl

/-- **`Plays` at the member**, from what `plays_jobL` asks but for the plan and the trees in front. -/
theorem plays_head_L
    (hT : tiesB Bk (H2U.p12OfMade Zp.made).place (AtProof.membersL pl).length = true)
    (hold : ∀ k st m E, Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k st
        m E → ∀ d ∈ (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Zp.made) : Block T12 Unit).rounds,
        ∀ o ∈ d.opens, oldSrc E.sent o.2 = true → ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W)
    (own₀ : X)
    (htable : ∀ τ, τ + 1 < (H2U.p12OfMade Zp.made).nums.stages.length →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.table
          (.own (treesTo cF.blocksInOrder 354 + τ)) =
        testTbl (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain
          (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) own₀
          ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front +
            roundsTo cF.blocksInOrder 354) (fun _ _ _ => true) τ)
    (hfixed : ∀ τ, τ + 1 < (H2U.p12OfMade Zp.made).nums.stages.length →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.fixed
          (.own (treesTo cF.blocksInOrder 354 + τ)) =
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front +
            roundsTo cF.blocksInOrder 354 +
          seedRound (H2U.p12OfMade Zp.made).nums.stages τ) :
    Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 := by
  obtain ⟨blk, pre, t, hm, HL⟩ := letterAtL_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w D readers
    closing pl hh
  obtain ⟨s, u, rest, hst, hk⟩ := HL.stages
  obtain ⟨nm, hm'⟩ := member_354 h
  obtain rfl := Option.some.inj (hm.symm.trans hm')
  have hq := Johnson.AtFull.Shape.p12_at_head h.toAtMg
  have hks : ∀ a ∈ (H2U.p12OfMade Zp.made).nums.stages, a.h ≤ a.k := by
    rw [hq]
    exact AtFile.hk_L
  have hrs : ((proximityTestKind guardedProximityTestParts (H2U.p12OfMade Zp.made) : Block T12 Unit).rounds.zip
      (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Zp.made) : Block T12 Unit).oracles).length =
      firstLen (H2U.p12OfMade Zp.made).nums.stages +
        restLen (H2U.p12OfMade Zp.made).nums.stages := by
    rw [hq]
    exact AtFile.zip_L
  have hcount : ((proximityTestKind guardedProximityTestParts (H2U.p12OfMade Zp.made) : Block T12 Unit).oracles.flatMap id).length +
      1 = (H2U.p12OfMade Zp.made).nums.stages.length := by
    rw [hq]
    exact AtFile.sends_L
  exact plays_jobL _ _ _ D readers closing pl HL hm s u rest hst hk 77
    (planPlays_head_L h.toAtMg _ (numbersL_at_head h.toAtMg) rfl s (u :: rest) hst)
    (ProofFile.Honest.K12.treesTo_354 h.toAtMg) hT hold hks hrs hcount HL.seat.place own₀
    htable hfixed

end

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.step_of_member
#print axioms ProofFile.Honest.K12.keeps_of_step
#print axioms ProofFile.Honest.K12.exchangeS_head_L
#print axioms ProofFile.Honest.K12.behindS_head_L
#print axioms ProofFile.Honest.K12.acceptedS_head_L
#print axioms ProofFile.Honest.K12.plays_head_L
