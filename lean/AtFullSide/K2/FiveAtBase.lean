-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/FiveAtBase.lean: the five debts of the code switch, joined, at each of its 25 members of
the first chain: at the base prover, at the thread's own value of the reply's border, of the riders and
of keeps.

  k2_five   FiveAtBorder at each member of the kind, under the library's head, the opening, the
            maker's return, hOk (what the laws read of Said), the run's first test and K2Asks

Limits. K2Asks is a premise here. Where the maker does not return, or no head stands at the public
files, the theorem holds of nothing.
-/
import AtFullSide.K2.ExchangeAtTheBase
import AtFullSide.K2.KeepsBehind
import AtFullSide.K2.RidesPast
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Base
open VerifiableInference.Desc (Chain Block Place KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open AtFullSide.K2.Term

/-- **The five debts at each member of the kind.** -/
theorem k2_five {W₀ : Type} (I : WiderIn W₀) (Oh : OnlineProverArguments) {Z : VerifierAndGoals.PublicFiles} {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} {A : BaseReturn W₀} {Bs : ProofFile.PureBase}
    {base : List (Block TS ProofFile.Cl)} (hA : Returns I Oh Z A)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Y X₂ : Type} (S : ScriptLetters I A Zp Bs cF Y X₂) (test : Nat → TS → Option String)
    (item n₁ n₂ : Nat) (Vd : Input W₀ → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (w : Input W₀)
    (Said : Nat → Coins A.B → Mid (Input W₀) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (K : K2Asks h I A Bs (K1.PlaceIn ProofFile.Inst) Y S.Q test item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w Said)
    {b : Nat} {q : Place} (hb : P5J.At.ps[b]? = some q) (hq : q.kind = KindName.K2) :
    FiveAtBorder (baseLetters h A S.Q test item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said fall b :=
  { plays := k2Plays I Oh Z D r Zp Np cF x A Bs base hA h O S test item n₁ n₂ 339 Vd _ _ w Said K.start
      b q hb hq
    behind := k2_behindS h A.H S.Q test _ item n₁ n₂ Vd ν st R G take P11 p12 P13 w Said hOk hb hq
    exchange := k2Exchange I Oh Z D r Zp Np cF x A Bs base hA h O S test item n₁ n₂ 339 Vd _ _ w Said
      hOk K b q hb hq
    ridesPast := k2_ridesPastS h A.H S.Q test _ item n₁ n₂ Vd ν st R G take P11 p12 P13 w Said hb hq
    accepted := k2Accepted I Oh Z D r Zp Np cF x A Bs base hA h O S.Q test item n₁ n₂ 339 Vd _ _ w Said
      hOk b q hb hq fall }

end AtFullSide.K2.Base

#print axioms AtFullSide.K2.Base.k2_five
