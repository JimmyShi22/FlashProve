-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/PlaysAtJoin.lean: the kind "the code switch" (K2): THE DEBT "IT PLAYS", ASKED FROM THE
PAIR (`PlaysS`), AT THE JOINED SCRIPT, AT EACH OF THE KIND's 25 SWITCHES, AT EVERY LETTER `Said`,
WITHOUT `PlayedTo`, AT THE BOOK THAT `onlineProverFromPublicFiles` RETURNS, WHERE IT YIELDS. A join: one statement with
its proof; no definition; nothing is evaluated here.

  `playsS_at_join`   `switch_playsS_at` (Honest/K2/Law/PlaysAtArms.lean), its premises Sc and hW
                    paid: `k2Script_at_join` at `rootsW` (PlaysAtArms.lean), `widths_at_switch`; the
                    latter's hcoins, hlend and hcl paid: `coins_at_head` (Honest/Thread/
                    JoinAtHead.lean), `lend_at_pure`, `closing_at_head` (Honest/K2/Law/
                    ClosingAtHead.lean)

WHICH SLOT IT IS FOR. Honest/K2/Law/PlaysAtArms.lean says it: `PlaysS` by number, premises hPhear
and hP353 and their like of the frame's gather of the first chain's debts, where the Script is the
joined one.

Limits. THE HEAD AND THE OPENING ARE HYPOTHESES, AND hA, THAT `onlineProverFromPublicFiles` YIELDS, IS THE HEAVY ONE:
THIS FILE SHOWS THEM MET BY NOTHING: WHERE NOTHING MEETS THEM THE LAW HOLDS EMPTILY. F AND hin ARE
PREMISES (payer at the full share: `joinFit_full`, AtFullSide/K2/JoinFitFull.lean: not called here).
hhalf (the letter H has the switch's half) IS A PREMISE: H IS ANY PROVER: the law takes nothing from
A but A.B, and nothing here ties H to A's own; where H is A's, payers stand in
Honest/K2/Law/HalfAtArms.lean and beside it. hv (`publicOk` at the run's input under Vd, at every
switch, which is more than the debt asks) IS A PREMISE. K1's 52 jobs are the joined list's; the
letters no, Dt and Dd are free. On returning and on which tables are at hand, as in `switch_playsS`:
nothing on what a table holds, nor on whether the verifier's step says yes. NOT IN FRONT OF A LAW
OVER COINS. The full size and the format's second hash function alone. Nothing on any property.
-/
import AtFullSide.K2.LendAtPure
import Johnson.Desc.ProofFile.Honest.K2.Law.PlaysAtArms
import Johnson.Desc.ProofFile.Honest.K2.Law.WidthsAtSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P1K2 (Prep Nums numsAt prepOf)
open IM (k2P)
open P5J (AtMgA CellsM TS F0T)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)} {p : SwitchPlace}
  {W₀ Rc Ky Tr X₀ X Xj Xo Ya Yb : Type}
  {P : OnlineProverParts W₀ Rc Tr Ya Yb} {A : OnlineProverWithDescription W₀ Rc Tr Ya Yb}
  {wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn Xj} {own₀ : Xo}
  {Oth : Others A.B (Local W₀ Rc ProofFile.Inst Tr)} {D : RowDataOf ProofFile.Inst}
  {readers : Local W₀ Rc ProofFile.Inst Tr → Readers}
  {rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr)}

/-- **THE DEBT "IT PLAYS" AT THE JOINED SCRIPT, AT EACH OF THE 25 SWITCHES.** hA, F, hin, hhalf AND
hv ARE PREMISES. NOT IN FRONT OF A LAW OVER COINS. -/
theorem playsS_at_join (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hp : p ∈ switchPlaces Zp Bs.G₀) (no : Place → Nat)
    (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xj)
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀
      (byNo cF.blocksInOrder (k1Jobs (X := Xo) no Dt Dd Zp Bs.G₀)) Oth)
    (hin : ShareIn (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ D readers rest) Oth)
    (cells : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp p.place.link = some n)
    (hhalf : (H.first.find? fun a => a.place == p.place) =
      some (switchHalf (coreSender freshTable) D readers
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p))
    (hv : Vd w → ∀ p' ∈ switchPlaces Zp Bs.G₀,
      publicOk D Bs.G₀.first.layout p' ((segmentsOf Zp Bs.G₀).take p'.link) w.x = true) :
    PlaysS (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (k1Jobs (X := Xo) no Dt Dd Zp Bs.G₀)) Oth) test carryX item n₁ n₂ b₀ Vd
        Rd Kp w).thread Said (P5J.At.ps.findIdx (· == p.place)) := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have a₁ : (numsW p.place.link).any (fun n =>
      (P1K2.oraclesAt n.grp n.codes n.sent).length == n.roots + 0) = true :=
    List.all_eq_true.1 rootsW p hpW
  rw [numsW_at_head h.toAtMg O hP, hn] at a₁
  have hr : (P1K2.oraclesAt n.grp n.codes n.sent).length = n.roots := beq_iff_eq.1 a₁
  exact switch_playsS_at h O H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w Said D readers hp hP hn hhalf
    (fun nm st => k2Script_at_join h O hp F hin cells tok H test carryX item n₁ n₂ b₀ Vd Rd Kp w hP
      hn p.place nm st hr)
    (widths_at_switch h O hp no Dt Dd F hin cells tok H test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
      hP hn (coins_at_head h O no Dt Dd hA) (lend_at_pure h O hA)
      (closing_at_head h.toAtMg O) hv)
    (fun hV => hv hV p hp)

end AtFullSide.K2

#print axioms AtFullSide.K2.playsS_at_join
