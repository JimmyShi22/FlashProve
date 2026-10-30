-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/PinsAtDraw.lean: the two pins of a segment at the smallness test's draw: the draw's row owes
pin l 0 and pin l 1, and both are open in front of it; the draw leaves the statement, so what each pin
says in front it says behind.

  k8_exchangeAtS_pins        at the letters of the head: the exchange at both pins
  k8_exchangeAtS_pins_first  the same at the first thread, at a return of the maker

Limits. Nothing here says that a pin holds at any state, or that any stand meets the thread. Nothing is
claimed on completeness, soundness or hiding.
-/
import AtFullSide.K8.AtFirstThread
import Johnson.Desc.ProofFile.Honest.K8.ExchangeByKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc (Chain KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K8 (blind_st)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest
open ProofFile.Honest.FirstThread

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The exchange at the two pins of segment l, at the draw of that segment.** -/
theorem k8_exchangeAtS_pins (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {b : Nat} {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8)
    {l : Nat} (hl : l < 25) (hb : b = 14 * l + (if l = 24 then 5 else 4) + 2) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
        (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said b (Item.pin l 0) ∧
      ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
        (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said b (Item.pin l 1) := by
  have hst : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.keeps b s s' → s'.st = s.st :=
    fun s s' hK => blind_st s s' (drawn_of_keeps
      (k8_keepsM h H Q test carryX item n₁ n₂ Vd ν st R G take P11 p12 P13 w ha hk hK).1)
  have hB := k8_behindS h H Q test carryX item n₁ n₂ Vd ν st R G take P11 p12 P13 w Said ha hk
  obtain ⟨p0, p1⟩ := ProofFile.Honest.K8.k8_pins_fwd hl
  subst hb
  exact ⟨exchangeAtS_pin h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w l 0 Said hst p0 hB,
    exchangeAtS_pin h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w l 1 Said hst p1 hB⟩

end

section
variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The same at the first thread, at a return of the maker.** -/
theorem k8_exchangeAtS_pins_first (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {b : Nat} {pl : VerifiableInference.Desc.Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8)
    {l : Nat} (hl : l < 25) (hb : b = 14 * l + (if l = 24 then 5 else 4) + 2) :
    ExchangeAtS (firstThread h parts w) Said b (Item.pin l 0) ∧
      ExchangeAtS (firstThread h parts w) Said b (Item.pin l 1) := by
  exact k8_exchangeAtS_pins h.head A.H parts.script _ _ _ _ _ _ _ _ _ _ _ _ _ _ w Said ha hk hl hb

end

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.k8_exchangeAtS_pins
#print axioms AtFullSide.K8.Term.k8_exchangeAtS_pins_first
