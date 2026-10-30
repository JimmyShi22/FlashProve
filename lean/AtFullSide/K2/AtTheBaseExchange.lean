-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/AtTheBaseExchange.lean: the third of the code switch's debts at the base prover, beside
AtTheBaseStatement.lean of this folder: K2Asks, what the senders in front laid; K2Exchange, that every
item that a member's row owes is true behind it; K2AsksPaid, what is left of it. So the kind's debt is
not paid before K2AsksPaid is. This file states; it proves nothing. The limits of AtTheBaseStatement.lean stand.
-/
import AtFullSide.K2.AtTheBaseStatement
import AtFullSide.K2.ExchangeLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Base
open VerifiableInference.Desc (Chain Block Place KindName Strs)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open OnBytes.SendSim.Seat (wJobs)
open P5J (AtMgA CellsM TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

variable {W₀ : Type}

/-- **What the run's script and input say at the members of the kind.** start: the description's
first test accepts the run's input's instance. asks: at each switch, under the thread's sentence,
behind a step that says yes, what JoinAsks lists. -/
structure K2Asks {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (A : BaseReturn W₀)
    (Bs : ProofFile.PureBase) (Wj Xj : Type)
    (Q : Script A.B (Input W₀) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat) (Vd : Input W₀ → Prop)
    (Rd : Nat → Input W₀ → TS → Prop) (Kp : Place → TS → TS → Prop) (w : Input W₀)
    (Said : Nat → Coins A.B → Mid (Input W₀) Unit → Prop) : Prop where
  start : Vd w → (F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true
  asks : ∀ p ∈ placesW, JoinAsks Wj Xj (baseLetters h A Q test item n₁ n₂ b₀ Vd Rd Kp w) Said Zp Bs cF
    (rowsAt Zp Bs) (reader I Zp) Bs.G₀.first.layout p

/-- **What the row owes is true behind the member, at every member of the kind**, under K2Asks. -/
def K2Exchange : Prop :=
  ∀ {W₀ : Type} (I : WiderIn W₀) (Oh : OnlineProverArguments) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) (A : BaseReturn W₀) (Bs : ProofFile.PureBase)
    (base : List (Block TS ProofFile.Cl)),
    Returns I Oh Z A →
    ∀ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
      (_ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
        (seatZ Zp Np) (secondAt Zp Np))
      {Y X₂ : Type} (S : ScriptLetters I A Zp Bs cF Y X₂)
      (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat) (Vd : Input W₀ → Prop)
      (Rd : Nat → Input W₀ → TS → Prop) (Kp : Place → TS → TS → Prop) (w : Input W₀)
      (Said : Nat → Coins A.B → Mid (Input W₀) Unit → Prop),
      (∀ b k m, Said b k m → SaidOk b k m) →
      K2Asks h I A Bs (K1.PlaceIn ProofFile.Inst) Y S.Q test item n₁ n₂ b₀ Vd Rd Kp w Said →
      ∀ b q, P5J.At.ps[b]? = some q → q.kind = KindName.K2 →
        ExchangeS (baseLetters h A S.Q test item n₁ n₂ b₀ Vd Rd Kp w).thread Said b

/-- **What is left of K2Exchange**: K2Asks at every script of the form S, at a run whose instance
passes the description's first test and is a typed one. -/
def K2AsksPaid : Prop :=
  ∀ {W₀ : Type} (I : WiderIn W₀) (Oh : OnlineProverArguments) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) (A : BaseReturn W₀) (Bs : ProofFile.PureBase)
    (base : List (Block TS ProofFile.Cl)),
    Returns I Oh Z A →
    ∀ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
      (_ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
        (seatZ Zp Np) (secondAt Zp Np))
      {Y X₂ : Type} (S : ScriptLetters I A Zp Bs cF Y X₂)
      (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat) (Vd : Input W₀ → Prop)
      (Rd : Nat → Input W₀ → TS → Prop) (Kp : Place → TS → TS → Prop) (w : Input W₀)
      (Said : Nat → Coins A.B → Mid (Input W₀) Unit → Prop),
      (∀ b k m, Said b k m → SaidOk b k m) →
      (Vd w → (F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true) →
      (Vd w → ∃ z : LPFD.Full.XF × OnBytes.Flat.RecFull, w.x.pub = (LPFD.Full.instanceAsPlainRecord z).pub) →
      K2Asks h I A Bs (K1.PlaceIn ProofFile.Inst) Y S.Q test item n₁ n₂ b₀ Vd Rd Kp w Said

end AtFullSide.K2.Base
