-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/DeferRun/Lump.lean: a map of states that commutes with the moves which an ADMISSIBLE
adversary makes. One lemma in two forms, general in the family of oracles and in the two
challengers.

General lemmas. This file states no goal of the release.

interact_lump (Compile/Step1_defc_Gen.lean) asks that the map commute with every move from every
state of an invariant. Two challengers of the privacy experiment often part at moves that no
admissible adversary makes: a second setup, a batch before the setup. Here the adversary is
admissible (GAdm, Compile/Batch/SpecGlue.lean: one setup, first; then at most n batches, each
allowed), and the invariant has a flag that says whether the setup has been made.

  lump_gAdm   the law of (output, mapped state) against the first challenger is the law of (output,
              state) against the second.
  lump_gAdm_fst   the same for the outputs alone.
Sources. The statement and the proof of lump_gAdm follow those of interact_lump
(Compile/Step1_defc_Gen.lean), case by case; lump_gAdm_fst is read off lump_gAdm.

-/
import Compile.Step1_defc_Gen
import Compile.Batch.SpecGlue

set_option autoImplicit false

noncomputable section

namespace Compile
namespace DeferRun
open Rom Prob
open Compile.GlueB (GCall GIn GAdm)

variable {S : OSpec} {X Wn IVK Pf α : Type}

/-- **A map of states that commutes with an admissible adversary's moves.** Inv f s: the invariant;
f says whether the setup has been made. -/
theorem lump_gAdm (ok : ZKCP.Gen.Batch X Wn → Prop) (W₁ W₂ : World S (GCall X Wn) (GIn IVK Pf))
    (Φ : W₁.σ → W₂.σ) (Inv : Bool → W₁.σ → Prop)
    (ha : ∀ f s o q, Inv f s → (W₁.answer s o q).map (Prod.map id Φ) = W₂.answer (Φ s) o q)
    (ia : ∀ f s o q, Inv f s → ∀ x ∈ (W₁.answer s o q).support, Inv f x.2)
    (hs : ∀ s, Inv false s → (W₁.reply s .setup).map (Prod.map id Φ) = W₂.reply (Φ s) .setup)
    (is : ∀ s, Inv false s → ∀ x ∈ (W₁.reply s .setup).support, Inv true x.2)
    (hb : ∀ s b, ok b → Inv true s →
      (W₁.reply s (.batch b)).map (Prod.map id Φ) = W₂.reply (Φ s) (.batch b))
    (ib : ∀ s b, ok b → Inv true s → ∀ x ∈ (W₁.reply s (.batch b)).support, Inv true x.2)
    (A : Adv S (GCall X Wn) (GIn IVK Pf) α) :
    ∀ (f : Bool) (n : ℕ) (s : W₁.σ), GAdm ok A f n → Inv f s →
      (interact W₁ A s).map (Prod.map id Φ) = interact W₂ A (Φ s) := by
  induction A with
  | halt a =>
    intro f n s _ _
    simp only [interact, PMF.pure_map]
    rfl
  | sample m k ih =>
    intro f n s hA hI
    simp only [interact, PMF.map_bind]
    exact congrArg _ (funext fun r => ih r f n s (hA r) hI)
  | query o q k ih =>
    intro f n s hA hI
    simp only [interact, PMF.map_bind]
    rw [← ha f s o q hI, PMF.bind_map]
    refine bind_congr_support _ fun x hx => ?_
    exact ih _ f n _ (hA _) (ia f s o q hI x hx)
  | call c k ih =>
    intro f n s hA hI
    rcases c with _ | b
    · obtain ⟨rfl, hk⟩ := hA
      simp only [interact, PMF.map_bind]
      rw [← hs s hI, PMF.bind_map]
      refine bind_congr_support _ fun x hx => ?_
      exact ih _ true n _ (hk _) (is s hI x hx)
    · cases n with
      | zero => exact hA.elim
      | succ n =>
        obtain ⟨rfl, hok, hk⟩ := hA
        simp only [interact, PMF.map_bind]
        rw [← hb s b hok hI, PMF.bind_map]
        refine bind_congr_support _ fun x hx => ?_
        exact ih _ true n _ (hk _) (ib s b hok hI x hx)

/-- The same for the outputs alone. -/
theorem lump_gAdm_fst (ok : ZKCP.Gen.Batch X Wn → Prop)
    (W₁ W₂ : World S (GCall X Wn) (GIn IVK Pf)) (Φ : W₁.σ → W₂.σ) (Inv : Bool → W₁.σ → Prop)
    (ha : ∀ f s o q, Inv f s → (W₁.answer s o q).map (Prod.map id Φ) = W₂.answer (Φ s) o q)
    (ia : ∀ f s o q, Inv f s → ∀ x ∈ (W₁.answer s o q).support, Inv f x.2)
    (hs : ∀ s, Inv false s → (W₁.reply s .setup).map (Prod.map id Φ) = W₂.reply (Φ s) .setup)
    (is : ∀ s, Inv false s → ∀ x ∈ (W₁.reply s .setup).support, Inv true x.2)
    (hb : ∀ s b, ok b → Inv true s →
      (W₁.reply s (.batch b)).map (Prod.map id Φ) = W₂.reply (Φ s) (.batch b))
    (ib : ∀ s b, ok b → Inv true s → ∀ x ∈ (W₁.reply s (.batch b)).support, Inv true x.2)
    (A : Adv S (GCall X Wn) (GIn IVK Pf) α) (f : Bool) (n : ℕ) (s : W₁.σ)
    (hA : GAdm ok A f n) (hI : Inv f s) :
    (interact W₁ A s).map Prod.fst = (interact W₂ A (Φ s)).map Prod.fst := by
  rw [← lump_gAdm ok W₁ W₂ Φ Inv ha ia hs is hb ib A f n s hA hI, PMF.map_comp]
  rfl

end DeferRun
end Compile

#print axioms Compile.DeferRun.lump_gAdm
