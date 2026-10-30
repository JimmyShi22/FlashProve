-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/ExchangeStep.lean: the kind "the code switch" (K2): `k2_exchange_full`
(ExchangeFull.lean of this folder) WITH `LockAsks` GONE FROM ITS PREMISES: in its stead stand the
two records of Honest/K2/Law/LockAsksAtStep.lean, by `StepAsks`. One statement with its proof: two
calls.

WHICH SLOT IT IS FOR. The same: the hypothesis hXk of the frame's gather at the kind K2.

  `k2_exchange_step`   `k2_exchange_full`'s end, at `StepAsks` at each written switch

WHAT IS LEFT. As in ExchangeFull.lean's head, with left: `StepAsks` (Honest/K2/Law/StepLeft.lean).

Limits. AN IMPLICATION. All limits of ExchangeFull.lean stand. `StepAsks` is shown of no prover and
no Script. One run's coins: never quoted for a law. NOT IN FRONT OF A LAW OVER COINS.
Nothing on any property.
-/
import AtFullSide.K2.ExchangeFull
import Johnson.Desc.ProofFile.Honest.K2.Law.StepLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block KindName Strs)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT allOf EAll)
open OnBytes.HonestTrace (Sz)
open OnBytes.SendSim.Seat (wJobs)
open OnBytes.Maker (WholeD)
open Johnson.G (proofSendsFull)
open P5J (AtMgA CellsM TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K1 (seatAtMember)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X Y X₂ : Type} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- h, O, hA AND EVERY BINDER NAMED IN ExchangeFull.lean's HEAD ARE PREMISES; the rest are
letters. **K2's WHOLE DEBT UNDER "THE EXCHANGE", AT `StepAsks`.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem k2_exchange_step {Wj Xj : Type} (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (no : VerifiableInference.Desc.Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : Y)
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr)) (ch : Nat)
    (Jt : K12.TestJob (Local W₀ Rc ProofFile.Inst Tr) X₂) (hJ : Jt.p.nums.stages.length = 6)
    (own₂ : X₂) (n₀ : Nat)
    (ok : Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
    (Oth : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (hO : Oth = (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp
               Bs.G₀)
      (fun v => (wit v).R) rest).add
        (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂))
    (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread.stored v i x = some u →
      ∀ a ∈ u, a < fieldPrimeWord)
    (y₀ : (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (switchLot (X := X) (withSwitchData Sz.ref (K1.lotData
      Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R)).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K2) ∨
      M.halves A.Z A.G = (switchLot (X := X) (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
        (fun v => (wit v).R)).halves A.Z A.G)
    (hR4 : ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v →
      ReadsLight Zp Bs.G₀ v.x)
    (hD1 : ∀ p₀ ∈ switchPlaces Zp Bs.G₀, ∀ p ∈ switchPlaces Zp Bs.G₀, p₀.link + 1 = p.link →
      ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v →
      ∀ s m a, s < p₀.link → p.addrs s m = some a →
        (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀ v.x).heardAt a ≤ 0 + roundsTo cF.blocksInOrder
          (switchNo p₀))
    (hI : ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v → (wit v).x = v.x)
    (left : ∀ p ∈ placesW, StepAsks Wj Xj (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ
      (P5J.At.arr
      Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w) Said Zp Bs cF (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R) Bs.G₀.first.layout p) :
    ∀ b p₀, P5J.At.ps[b]? = some p₀ → p₀.kind = KindName.K2 →
      ∀ j : VerifiableInference.Desc.First.Item, j ∈ ((lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ
        tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread.opened b →
        (∀ m t, j ≠ VerifiableInference.Desc.First.Item.pin m t) ∧ j ≠
          VerifiableInference.Desc.First.Item.pinI ∧ j ≠ VerifiableInference.Desc.First.Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ VerifiableInference.Desc.First.Item.constr m q) →
      ExchangeAtS (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread Said b j :=
  k2_exchange_full h O hA no Dd cellsQ tokQ wit own₀ rest ch Jt hJ own₂ n₀ ok codes sh sh₁ rest₂ Oth
    hO test item n₁ n₂ b₀ Vd Rd Kp w hOk hst y₀ hex ho hR4 hD1 hI fun p hp =>
      valuesAsks_of_step (Wj := Wj) (Xj := Xj) h A.H _ test item n₁ n₂ b₀ Vd Rd Kp w O hOk hst y₀ hp
        (left p hp)

end AtFullSide.K2

#print axioms AtFullSide.K2.k2_exchange_step
