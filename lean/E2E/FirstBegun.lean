-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/FirstBegun.lean: THE RULE's DEBT AT THE FIRST CHAIN's START, at a return of the maker: the first
state has the written shape (`shapeJ … startShA 0`), by `first_chain_start`
(Johnson/AtFull/Shape/RuleAtTable.lean). Statements and proofs.

  `first_at_start`      where the description's first test says yes of x, at `start₁ (pub x)`: the
                        form of the field `j₁` of `FromThreadsJ`
  `okStart_at_named`, `first_at_named`   at `VerifierAndGoals.NamedFiles`, at `instanceAsPlainRecord z`: that test says yes,
                        so the same form with no premise on the test
  `first_begun_first`   at `firstThread` (Honest/Thread/TheFirstThread.lean), behind `valid` and
                        `begun`: no premise: `valid` holds `ReadyInput`, whose first clause is that test

Limits. Nothing on whether a run stands at such an input. Nothing on any property.
-/
import E2E.StartReqOk
import Johnson.AtFull.Shape.RuleAtTable
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import AtFullSide.E2E.StartAtWrittenFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtPublicFiles.Start
open Johnson.AtFull.Shape
open ProofFile.Honest ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J

variable {W₀ Rc Tr X₀ X : Type}

/-- **The form of the field `j₁`.** -/
theorem first_at_start {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (x : ProofFile.Inst)
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart x = true)
    (g : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    shapeJ (firstZA g vals) startShA 0
      ((F0T OnBytes.secondHashFunction Zp Np cF).start₁ ((F0T OnBytes.secondHashFunction Zp Np cF).pub x)) :=
  first_chain_start h x.pub (reqOk_of_okStart hx) g vals

/-- **Behind `valid` and `begun` the first thread's first state has the written shape.** -/
theorem first_begun_first {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (g : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (k : Coins A.B) (v : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn) (s₀ : S)
    (h₁ : (firstThread h parts w).valid v) (h₂ : (firstThread h parts w).begun k v hd s₀) :
    shapeJ (firstZA g vals) startShA 0 s₀ := by
  have e : s₀ = ProofFile.startS A.Z v.x.pub := h₂
  rw [e]
  exact first_at_start h.head v.x h₁.2.1 g vals

/-- **At the two named sets of files the first test says yes at every instance of the type.** -/
theorem okStart_at_named {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} (hZ : VerifierAndGoals.NamedFiles Z)
    (Ld : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) (z : LPFD.Full.XF × OnBytes.Flat.RecFull) :
    (F0T OnBytes.secondHashFunction Zp Np cF).okStart (LPFD.Full.instanceAsPlainRecord z) = true := by
  rcases hZ with rfl | rfl
  · exact okStart_zFull Ld z
  · exact okStart_zGap Ld z

/-- **So the field `j₁`, at the two named sets of files, at an instance of the type.** -/
theorem first_at_named {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (hZ : VerifierAndGoals.NamedFiles Z)
    (z : LPFD.Full.XF × OnBytes.Flat.RecFull)
    (g : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    shapeJ (firstZA g vals) startShA 0
      ((F0T OnBytes.secondHashFunction Zp Np cF).start₁ ((F0T OnBytes.secondHashFunction Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z))) :=
  first_at_start h _ (okStart_at_named hZ h.toAtMg.laid z) g vals

end AtPublicFiles.Start

#print axioms AtPublicFiles.Start.okStart_at_named
#print axioms AtPublicFiles.Start.first_at_named
#print axioms AtPublicFiles.Start.first_at_start
#print axioms AtPublicFiles.Start.first_begun_first
