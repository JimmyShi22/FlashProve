-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/TailAtThread.lean: the smallness test's named tests on values behind the batching, in
the terms of the member behind it: at a stand of the first chain's thread there, under "what is said
is below the prime", where the kind's share of the tests is silent.

  k8_valsS_at_thread   at the state behind the run "K8.lsTail"
  k8_valsS_free_at     at the layers, behind the run "free-slot" too

Limits. Said is read through hOk: at a Said that does not give SaidOk these laws cannot be called.
The share's silence is a premise. The law speaks of every state that accepting steps reach, honest or
not. That a stand exists is not shown.
-/
import AtFullSide.K8.TailAtSorts
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.TailClaims.Law.Tests (bareRun valsS)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open OnBytes.Model.Stages (LinkH)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K8 (k8Share)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
  (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {Bk : ProverCoinCounts}
  {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
include h hB

/-- The state at a stand behind the batching is one that the wrapped blocks reach. -/
theorem reach_at_behind (hOk : ∀ b k m, Said b k m → SaidOk b k m) {l : Nat} (hl : l < 25)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 11 else 9) + 1) k s m E) :
    Reach 0 (cF.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Zp)
      (14 * l + (if l = 24 then 11 else 9) + 1) (m.st.input.x.pub, s) := by
  refine thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w ?_ ⟨hT.1, hOk _ _ _ hT.2⟩
  rw [head_len h]
  split <;> omega

/-- **The named tests accept at a stand behind the batching**, behind the run "K8.lsTail". -/
theorem k8_valsS_at_thread (hOk : ∀ b k m, Said b k m → SaidOk b k m) {l : Nat} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {k : Coins Bk} {s s₁ : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 11 else 9) + 1) k s m E)
    (hsh : k8Share (ProofFile.k8NU Bs.G₀ Xl) s = none)
    (h₁ : bareRun VerifiableInference.Desc.First.TailClaims.k8LsTail.2 s = .ok s₁) :
    valsS (ProofFile.k8NU Bs.G₀ Xl) s₁ = true := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O.made)
  exact k8_valsS_behind h.scope h.reads O h.laid.planOk hl e3
    (reach_at_behind h hB H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hOk hl hT) hsh h₁

/-- **The same at a layers' link, behind the run "free-slot".** -/
theorem k8_valsS_free_at (hOk : ∀ b k m, Said b k m → SaidOk b k m) {l : Nat} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {k : Coins Bk} {s s₁ s₂ : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {hp : OnBytes.Model.Layer.HPlan2}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 11 else 9) + 1) k s m E)
    (hsh : k8Share (ProofFile.k8NU Bs.G₀ Xl) s = none)
    (h₁ : bareRun VerifiableInference.Desc.First.TailClaims.k8LsTail.2 s = .ok s₁)
    (h₂ : Johnson.AtFull.Shape.freeRunH hp s₁ = .ok s₂) :
    valsS (ProofFile.k8NU Bs.G₀ Xl) s₂ = true := by
  rw [valsS_free h₂]
  exact k8_valsS_at_thread h hB H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hOk hl e3 hT hsh h₁

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.reach_at_behind
#print axioms AtFullSide.K8.Term.k8_valsS_at_thread
#print axioms AtFullSide.K8.Term.k8_valsS_free_at
