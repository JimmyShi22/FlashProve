-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/SharesFile.lean: gates over a file's three chains. A set of typed
verifier's messages of the file's rounds that is covered by three lists of gates
(Honest/Law/SharesHeld.lean), one over each chain's data, has probability at most the sum of the
gates' numbers (`covered_le`). The hypotheses: `GatesHeld` for the first two lists from their
starts, and for the third at every list of challenges heard before its own at which no gate of the
first two has fired. This is the form in which a file's stops, falls and marks are counted.

What this is. Lemmas about the library's own probability (`Iop.prRho`) at the shape of a file's
rounds (`chainsOf`, OnBytes/Maker/Whole.lean). No description, no prover and no run occurs in this
file. None of the library's goals. Probabilities are over the verifier's messages, drawn uniformly
(`Iop.prRho`), at a fixed private input and instance, where a lemma names one.

Trivially met. At numbers that add up to 1 or more the bound says nothing. Whoever uses `covered_le`
has to prove the cover: a gate that always fires covers everything, and can be met with the number 1
alone.

  1  `skip_head`, `fibre2`, `three_le`   the probability at the front round, the first chain, the
     joining round, the shared chain, the seam, the second chain
  2  `spoken_le`, `covered_le`   the main lemma

Limits.
  * The kit C of verifier's messages is a parameter. How a probability over its typed challenges
    follows from a count of what they show depends on the kit, and is not treated here.
  * The lemmas prove no property of a prover or a protocol.
-/
import Iop.Compose
import OnBytes.Maker.Whole
import Johnson.Desc.ProofFile.Honest.Law.SharesChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open OnBytes.Maker (RDT WholeD uLT drawnT chainsOf)
open _root_.Run.PQ (CK)

/-! ## 1 The probability at a file's shape -/

theorem skip_head (r : Iop.Round) (s : Iop.Shape) (S : Set (Iop.Rho s)) :
    Iop.prRho {ρ : Iop.Rho (r :: s) | ρ.2 ∈ S} = Iop.prRho S := by
  have e : {ρ : Iop.Rho (r :: s) | ρ.2 ∈ S} = Iop.Rho.cylSnd [r] S := by
    ext ⟨c, a⟩
    rfl
  rw [e]
  exact Iop.prRho_cylSnd [r] S

/-- A first part in S, or a second part in the set that belongs to the first. -/
theorem fibre2 {s t : Iop.Shape} (S : Set (Iop.Rho s)) (U : Set (Iop.Rho (s ++ t)))
    (T : Iop.Rho s → Set (Iop.Rho t)) (q p : ℝ≥0∞) (hS : Iop.prRho S ≤ q)
    (hU : ∀ ρ ∈ U, Iop.Rho.fst ρ ∉ S → Iop.Rho.snd (s := s) ρ ∈ T (Iop.Rho.fst ρ))
    (hT : ∀ a, a ∉ S → Iop.prRho (T a) ≤ p) : Iop.prRho U ≤ q + p := by
  classical
  have hsub : U ⊆ Iop.Rho.cylFst t S ∪
      {ρ : Iop.Rho (s ++ t) | Iop.Rho.snd (s := s) ρ ∈ T (Iop.Rho.fst ρ)} := fun ρ hρ =>
    if h : Iop.Rho.fst ρ ∈ S then Or.inl h else Or.inr (hU ρ hρ h)
  exact le_trans (pr_mono _ hsub) (le_trans (Iop.prRho_fibre_le S T p hT) (add_le_add hS le_rfl))

/-- **Three chains.** `S₁`, `S₂`: sets of the first two chains' messages; `T₃`: a set of the
third's, for each pair of the first two. The third bound is asked only outside S₁ and S₂. -/
theorem three_le (G : Compile.Joined.Chains) (S₁ : Set (Iop.Rho G.s₁)) (S₂ : Set (Iop.Rho G.s₂))
    (T₃ : Iop.Rho G.s₁ → Iop.Rho G.s₂ → Set (Iop.Rho G.s₃)) (p₁ p₂ p₃ : ℝ≥0∞)
    (h₁ : Iop.prRho S₁ ≤ p₁) (h₂ : Iop.prRho S₂ ≤ p₂)
    (h₃ : ∀ a b, a ∉ S₁ → b ∉ S₂ → Iop.prRho (T₃ a b) ≤ p₃) (U : Set (Iop.Rho G.sh))
    (hU : ∀ ρ ∈ U, G.rho₁ ρ ∈ S₁ ∨ G.rho₂ ρ ∈ S₂ ∨ G.rho₃ ρ ∈ T₃ (G.rho₁ ρ) (G.rho₂ ρ)) :
    Iop.prRho U ≤ p₁ + (p₂ + p₃) := by
  classical
  -- after the seam
  have L3 : ∀ a b, a ∉ S₁ → b ∉ S₂ →
      Iop.prRho {σ : Iop.Rho G.sh₃ | σ.2 ∈ T₃ a b} ≤ p₃ := fun a b ha hb => by
    rw [skip_head]
    exact h₃ a b ha hb
  -- from the joining round on
  have LJ : ∀ a, a ∉ S₁ → Iop.prRho {σ : Iop.Rho G.shJ | Iop.Rho.fst σ.2 ∈ S₂ ∨
      (Iop.Rho.snd (s := G.s₂) σ.2).2 ∈ T₃ a (Iop.Rho.fst σ.2)} ≤ p₂ + p₃ := fun a ha => by
    have e := skip_head G.rJ (G.s₂ ++ G.sh₃) {σ : Iop.Rho (G.s₂ ++ G.sh₃) | Iop.Rho.fst σ ∈ S₂ ∨
      (Iop.Rho.snd (s := G.s₂) σ).2 ∈ T₃ a (Iop.Rho.fst σ)}
    refine le_trans (le_of_eq e) ?_
    refine fibre2 S₂ _ (fun b => {σ : Iop.Rho G.sh₃ | σ.2 ∈ T₃ a b}) p₂ p₃ h₂ ?_
      (fun b hb => L3 a b ha hb)
    intro σ hσ hn
    rcases hσ with g | g
    · exact absurd g hn
    · exact g
  -- the whole shape
  have e := skip_head G.rF (G.s₁ ++ G.shJ) {σ : Iop.Rho (G.s₁ ++ G.shJ) | Iop.Rho.fst σ ∈ S₁ ∨
    (Iop.Rho.fst (Iop.Rho.snd (s := G.s₁) σ).2 ∈ S₂ ∨
      (Iop.Rho.snd (s := G.s₂) (Iop.Rho.snd (s := G.s₁) σ).2).2 ∈
        T₃ (Iop.Rho.fst σ) (Iop.Rho.fst (Iop.Rho.snd (s := G.s₁) σ).2))}
  refine le_trans (pr_mono _ (fun ρ hρ => ?_)) (le_trans (le_of_eq e) ?_)
  · exact hU ρ hρ
  · refine fibre2 S₁ _ (fun a => {σ : Iop.Rho G.shJ | Iop.Rho.fst σ.2 ∈ S₂ ∨
      (Iop.Rho.snd (s := G.s₂) σ.2).2 ∈ T₃ a (Iop.Rho.fst σ.2)}) p₁ (p₂ + p₃) h₁ ?_ LJ
    intro σ hσ hn
    rcases hσ with g | g
    · exact absurd g hn
    · exact g

/-! ## 2 The main lemma -/

/-- `gates_le`, at a list of rounds that is equal to the gates' rounds in a row. -/
theorem spoken_le (C : CK) (gs : List Gate) (ds : List RDT) (e : gs.flatMap (·.ds) = ds)
    (fr : List Fmt.Drawn) (h : GatesHeld C gs fr) :
    Iop.prRho {ρ : Iop.Rho (uLT C ds) | spoken gs fr (drawnT C ds ρ) = true} ≤
      (gs.map (·.p)).sum := by
  have key := gates_le C gs fr h
  rw [prRho_ds C e (fun dr => spoken gs fr dr = true)] at key
  exact key

/-- **A set that three lists of gates cover.** `fr₃`: what the third chain's gates are given as the
challenges heard before their own, computed from the first two chains' challenges. -/
theorem covered_le (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
    (gs₁ gs₂ gs₃ : List Gate) (e₁ : gs₁.flatMap (·.ds) = D.ds₁)
    (e₂ : gs₂.flatMap (·.ds) = D.ds₂) (e₃ : gs₃.flatMap (·.ds) = D.ds₃)
    (fr₃ : List Fmt.Drawn → List Fmt.Drawn → List Fmt.Drawn)
    (U : Set (Iop.Rho (chainsOf C D tF tJ t3).sh))
    (cover : ∀ ρ ∈ U,
      spoken gs₁ [] (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ)) = true ∨
      spoken gs₂ [] (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ)) = true ∨
      spoken gs₃ (fr₃ (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ))
        (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ)))
        (drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ)) = true)
    (h₁ : GatesHeld C gs₁ []) (h₂ : GatesHeld C gs₂ [])
    (h₃ : ∀ (a : Iop.Rho (uLT C D.ds₁)) (b : Iop.Rho (uLT C D.ds₂)),
      spoken gs₁ [] (drawnT C D.ds₁ a) = false → spoken gs₂ [] (drawnT C D.ds₂ b) = false →
      GatesHeld C gs₃ (fr₃ (drawnT C D.ds₁ a) (drawnT C D.ds₂ b))) :
    Iop.prRho U ≤ (gs₁.map (·.p)).sum + ((gs₂.map (·.p)).sum + (gs₃.map (·.p)).sum) :=
  three_le (chainsOf C D tF tJ t3)
    {a | spoken gs₁ [] (drawnT C D.ds₁ a) = true} {b | spoken gs₂ [] (drawnT C D.ds₂ b) = true}
    (fun a b => {c | spoken gs₃ (fr₃ (drawnT C D.ds₁ a) (drawnT C D.ds₂ b))
      (drawnT C D.ds₃ c) = true}) _ _ _
    (spoken_le C gs₁ D.ds₁ e₁ [] h₁) (spoken_le C gs₂ D.ds₂ e₂ [] h₂)
    (fun a b ha hb => spoken_le C gs₃ D.ds₃ e₃ _ (h₃ a b
      (by
        cases hs : spoken gs₁ [] (drawnT C D.ds₁ a) with
        | false => rfl
        | true => exact absurd hs ha)
      (by
        cases hs : spoken gs₂ [] (drawnT C D.ds₂ b) with
        | false => rfl
        | true => exact absurd hs hb)))
    U cover

end ProofFile.Honest

#print axioms ProofFile.Honest.skip_head
#print axioms ProofFile.Honest.fibre2
#print axioms ProofFile.Honest.three_le
#print axioms ProofFile.Honest.spoken_le
#print axioms ProofFile.Honest.covered_le
