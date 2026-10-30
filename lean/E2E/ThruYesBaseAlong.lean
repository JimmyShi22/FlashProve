-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ThruYesBaseAlong.lean: YesAt at the rows' prover, from ThreadsP and the yes at the run, both at the
filling's prover: the road by which a place states at the filling's prover and crosses once, by the
run's value. The rule's end is a sentence on runC's value, so nothing of the rule is carried over.

  yesAt_of_base_along  by YesAlong
  yesAt_of_base_alongJ by YesAlongJ

By what. yesAt_of_base (E2E/ThruYesBase.lean), runC_returns, runC_accepts_along,
runC_accepts_alongJ.

Limits. As E2E/ThruYesBase.lean. Nothing on completeness, soundness or hiding.
-/
import E2E.ThruYesBase
import Johnson.Desc.ProofFile.Honest.ThruAlongJ

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.Bridge
open Iop Prob AtPublicFiles.Along
open OnBytes.Maker (WholeD chainsOf wiresOf view₁ view₂ view₃)
open TypedOracleCompiler.Iop (RoundsQueryLayout)
open _root_.Run.PQ (CK SgX)
open ProofFile.Honest (batchOf honestBatchProverOfFile Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse Sides fallAt drawsAt drawsLo drawsSh runC
  viewsFall silentAt Tied DataFits halvedAll Committer CommittedColumns ready PlanServes sealPlain
  ThreadsP YesAlong YesAlongJ)

section Base
variable {Xi W₀ W₀' Rc Rc' Ky Tr X₀ X Sd Sc Xc TF TJ T3 R₂ R₃ : Type} (C : CK) (D : WholeD)
  (tF : TF) (tJ : TJ) (t3 : T3) (F : VerifiableInference.Desc.FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts) (G : Sides F B W₀' Rc' Ky Tr X₀ X)
  (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (Cm : Committer W₀' Rc' Sc Xc Xi Ky) (item₀ : ℕ)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages W₀' Rc' Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (ext : W₀' × Rc' × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

/-- **YesAt at the rows' prover, from ThreadsP and YesAlong at the filling's prover.** -/
theorem yesAt_of_base_along (hp : F.planOk = true) (hq : sealPlain F = true) (hD : DataFits F D)
    (h4 : halvedAll F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) = true)
    (hdue : ∀ ρ, (drawsAt C D tF tJ t3 ρ).due F = true)
    (hd : H.inRange (g d) = H.inRange H.dummy)
    (hrows : G.prover (H.thru g rd d) = H.thru g rd d) (hk : Cm.key = H.key)
    {pubJ : ℕ → R₂ → R₃ → Xi → TF × TJ × T3} {Rel : W₀' → Rc' → Xi → Prop}
    {TiedX : ℕ → W₀' × Rc' × Sd → Xi → Prop} (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (hT : ∀ n w x, TiedX n w x →
      Tied D F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) (J n) ext (pubJ n) sh Rel w x)
    (hcols : ∀ n w x, TiedX n w x → CommittedColumns Cm item₀ H g rd w.1 w.2.1)
    (htr : ∀ n w x, TiedX n w x → (H.trace (g w.1) x).isSome = true)
    (hdebt : ∀ n w x (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)),
      TiedX n w x → F.okStart x = true ∧
      ∃ R, ready F B H (g w.1) (rd w.2.1) x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R ∧
        PlanServes H (g w.1) (rd w.2.1) R ∧
        ∃ T : ThreadsP F B H (g w.1) (rd w.2.1) x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R,
          ∀ ρ, silentAt F H (g w.1) (rd w.2.1) x (drawsAt C D tF tJ t3 ρ) = none →
          ∀ r, runC F B H (g w.1) (rd w.2.1) x ⟨c.2.1.1, c.1.1, c.2.1.2⟩
              (drawsAt C D tF tJ t3 ρ) = .ok r →
            viewsFall F G.falls₁ G.falls₂ G.falls₃ x r.run.views = none →
            YesAlong (drawsAt C D tF tJ t3 ρ) r T G.falls₁ G.falls₂ G.falls₃) :
    YesAt C D tF tJ t3 F silent B G (Cm.proverAt item₀ (H.thru g rd d)) J sh ext K chal TiedX := by
  refine yesAt_of_base C D tF tJ t3 F silent B G g rd d Cm item₀ H J sh ext hp hD h4 hd hrows hk K chal
    hT hcols htr ?_
  intro n w x c ρ hx hsil hfall
  obtain ⟨h0, R, hR, hP, T, Y⟩ := hdebt n w x c hx
  obtain ⟨r, hr⟩ := ProofFile.Honest.runC_returns hR hq (hdue ρ) hsil hP T.I₁ T.I₂ T.I₃ T.h₁ T.h₂ T.h₃ T.a₁
    T.a₂ T.a₃
  exact ⟨r, hr, (ProofFile.Honest.runC_accepts_along hr hR hp h0 (hdue ρ) hsil T G.falls₁ G.falls₂ G.falls₃
    (Y ρ hsil r hr (hfall r hr)) (hfall r hr)).2⟩

/-- **The same by YesAlongJ.** -/
theorem yesAt_of_base_alongJ (hp : F.planOk = true) (hq : sealPlain F = true) (hD : DataFits F D)
    (h4 : halvedAll F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) = true)
    (hdue : ∀ ρ, (drawsAt C D tF tJ t3 ρ).due F = true)
    (hd : H.inRange (g d) = H.inRange H.dummy)
    (hrows : G.prover (H.thru g rd d) = H.thru g rd d) (hk : Cm.key = H.key)
    {pubJ : ℕ → R₂ → R₃ → Xi → TF × TJ × T3} {Rel : W₀' → Rc' → Xi → Prop}
    {TiedX : ℕ → W₀' × Rc' × Sd → Xi → Prop} (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (hT : ∀ n w x, TiedX n w x →
      Tied D F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) (J n) ext (pubJ n) sh Rel w x)
    (hcols : ∀ n w x, TiedX n w x → CommittedColumns Cm item₀ H g rd w.1 w.2.1)
    (htr : ∀ n w x, TiedX n w x → (H.trace (g w.1) x).isSome = true)
    (hdebt : ∀ n w x (c : (Purse B.shared × R₂) × ((Purse B.first × Purse B.second) × R₃)),
      TiedX n w x → F.okStart x = true ∧
      ∃ R, ready F B H (g w.1) (rd w.2.1) x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R ∧
        PlanServes H (g w.1) (rd w.2.1) R ∧
        ∃ T : ThreadsP F B H (g w.1) (rd w.2.1) x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R,
          ∃ (J₁ : ℕ → F.S₁ → Prop) (J₂ : ℕ → F.S₂ → Prop) (J₃ : ℕ → F.S₃ → Prop),
          ∀ ρ, silentAt F H (g w.1) (rd w.2.1) x (drawsAt C D tF tJ t3 ρ) = none →
          ∀ r, runC F B H (g w.1) (rd w.2.1) x ⟨c.2.1.1, c.1.1, c.2.1.2⟩
              (drawsAt C D tF tJ t3 ρ) = .ok r →
            viewsFall F G.falls₁ G.falls₂ G.falls₃ x r.run.views = none →
            YesAlongJ (drawsAt C D tF tJ t3 ρ) r T G.falls₁ G.falls₂ G.falls₃ J₁ J₂ J₃) :
    YesAt C D tF tJ t3 F silent B G (Cm.proverAt item₀ (H.thru g rd d)) J sh ext K chal TiedX := by
  refine yesAt_of_base C D tF tJ t3 F silent B G g rd d Cm item₀ H J sh ext hp hD h4 hd hrows hk K chal
    hT hcols htr ?_
  intro n w x c ρ hx hsil hfall
  obtain ⟨h0, R, hR, hP, T, J₁, J₂, J₃, Y⟩ := hdebt n w x c hx
  obtain ⟨r, hr⟩ := ProofFile.Honest.runC_returns hR hq (hdue ρ) hsil hP T.I₁ T.I₂ T.I₃ T.h₁ T.h₂ T.h₃ T.a₁
    T.a₂ T.a₃
  exact ⟨r, hr, (ProofFile.Honest.runC_accepts_alongJ hr hR hp h0 (hdue ρ) hsil T G.falls₁ G.falls₂
    G.falls₃ J₁ J₂ J₃ (Y ρ hsil r hr (hfall r hr)) (hfall r hr)).2⟩

end Base

end AtPublicFiles.Bridge

#print axioms AtPublicFiles.Bridge.yesAt_of_base_along
#print axioms AtPublicFiles.Bridge.yesAt_of_base_alongJ
