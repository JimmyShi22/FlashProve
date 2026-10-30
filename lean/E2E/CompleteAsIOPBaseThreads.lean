-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPBaseThreads.lean: YesAt at the rows' prover, from ThreadsC at the prover that the
family reads through. This is where the invariants assembled at the base prover enter: threadsC_of
(E2E/DebtsOfThreads.lean) is general in the prover, so at the base it takes Enters₁ there, with
coins of the base's own type. It states no goal.

  yesAt_of_base_threads    by ThreadsC at the base, with the rows' falls
  yesAt_of_base_threadsJ   the same by ThreadsCJ: sentences on the verifier's state in hand

By what. ThreadsC.toP, ThreadsC.along (Honest/ThruAlongStand.lean); yesAt_of_base_along
(E2E/ThruYesBaseAlong.lean).

Limits. As E2E/ThruYesBase.lean. Nothing on completeness, soundness or hiding.
-/
import E2E.ThruYesBaseAlong
import Johnson.Desc.ProofFile.Honest.ThruAlongStand
import Johnson.Desc.ProofFile.Honest.ThruAlongFromJ

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.Bridge
open Iop Prob AtPublicFiles.Along
open OnBytes.Maker (WholeD)
open _root_.Run.PQ (CK SgX)
open ProofFile.Honest (Prover KeyAndJoiningRoundMessages ProverCoinCounts Purse Sides drawsAt ready PlanServes ThreadsC ThreadsCJ Tied halvedAll
  sealPlain DataFits Committer CommittedColumns)

section Base
variable {Xi W₀ W₀' Rc Rc' Ky Tr X₀ X Sd Sc Xc TF TJ T3 R₂ R₃ : Type} (C : CK) (D : WholeD)
  (tF : TF) (tJ : TJ) (t3 : T3) (F : VerifiableInference.Desc.FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool) (B : ProverCoinCounts) (G : Sides F B W₀' Rc' Ky Tr X₀ X)
  (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (Cm : Committer W₀' Rc' Sc Xc Xi Ky) (item₀ : ℕ)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages W₀' Rc' Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (ext : W₀' × Rc' × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

/-- **YesAt at the rows' prover, from ThreadsC at the base prover.** -/
theorem yesAt_of_base_threads (hp : F.planOk = true) (hq : sealPlain F = true) (hD : DataFits F D)
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
        ∃ T : ThreadsC F B H (g w.1) (rd w.2.1) x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R,
          T.f₁ = G.falls₁ ∧ T.f₂ = G.falls₂ ∧ T.f₃ = G.falls₃) :
    YesAt C D tF tJ t3 F silent B G (Cm.proverAt item₀ (H.thru g rd d)) J sh ext K chal TiedX := by
  refine yesAt_of_base_along C D tF tJ t3 F silent B G g rd d Cm item₀ H J sh ext hp hq hD h4 hdue hd
    hrows hk K chal hT hcols htr ?_
  intro n w x c hx
  obtain ⟨h0, R, hR, hP, T, e1, e2, e3⟩ := hdebt n w x c hx
  refine ⟨h0, R, hR, hP, T.toP, fun ρ _ r _ _ => ?_⟩
  have y := T.along (drawsAt C D tF tJ t3 ρ) r
  rw [e1, e2, e3] at y
  exact y

/-- **YesAt at the rows' prover, from ThreadsCJ at the base prover.** -/
theorem yesAt_of_base_threadsJ (hp : F.planOk = true) (hq : sealPlain F = true) (hD : DataFits F D)
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
        ∃ T : ThreadsCJ F B H (g w.1) (rd w.2.1) x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R,
          T.f₁ = G.falls₁ ∧ T.f₂ = G.falls₂ ∧ T.f₃ = G.falls₃) :
    YesAt C D tF tJ t3 F silent B G (Cm.proverAt item₀ (H.thru g rd d)) J sh ext K chal TiedX := by
  refine yesAt_of_base_alongJ C D tF tJ t3 F silent B G g rd d Cm item₀ H J sh ext hp hq hD h4 hdue hd
    hrows hk K chal hT hcols htr ?_
  intro n w x c hx
  obtain ⟨h0, R, hR, hP, T, e1, e2, e3⟩ := hdebt n w x c hx
  refine ⟨h0, R, hR, hP, T.toP, T.J₁, T.J₂, T.J₃, fun ρ _ r _ _ => ?_⟩
  have y := T.along (drawsAt C D tF tJ t3 ρ) r
  rw [e1, e2, e3] at y
  exact y

end Base

end AtPublicFiles.Bridge

#print axioms AtPublicFiles.Bridge.yesAt_of_base_threads
#print axioms AtPublicFiles.Bridge.yesAt_of_base_threadsJ
