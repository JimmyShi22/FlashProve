-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- The proof of the statement `SpineOnce` of Johnson/Desc/Sound/SpineOnce.lean.
import Johnson.Desc.Sound.SpineOnce
import Johnson.Desc.Sound.SharedOnceProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString BTr Doomed)

variable {S Cl W ι : Type} {C : CK} {F : Frame}

theorem eachGoodIn_sh (on : ℕ → S × F.E.Str → Prop) (act : ℕ → BKey F S)
    (μ : ι → ∀ k, (act k).1 → W → Prop) (In Out : ℕ → ι → Prop) (O₀ : ι → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (k : ℕ), EachOwnSh on act μ In Out k l →
      EachFramesSh on act μ In (openAfter In Out O₀) k l →
      EachGoodIn on (fun j a w => ∀ i, openAfter In Out O₀ j i → μ i j ((act j).2 a) w) k l
  | [], _, _, _ => trivial
  | p :: l, k, ho, hf => by
    refine ⟨?_, eachGoodIn_sh on act μ In Out O₀ l (k + 1) ho.2 hf.2⟩
    intro a ha
    refine Doomed.mono _ _ ?_ (ho.1 a ha)
    intro τ hτ b hb
    obtain ⟨hon, hw⟩ := hτ b hb
    refine ⟨hon, fun w hall i hi => ?_⟩
    by_cases hin : In k i
    · exact hw w (fun j hj => hall j (Or.inr hj)) i hin
    · exact hf.1 a τ b w i ha hb hon hi hin (hall i (Or.inl ⟨hi, hin⟩))

theorem spineOnce : SpineOnce := by
  intro S S₀ Cl W ι C F get set lo N i₀ act p l on o μ Rc In Out O₀ ha ht g1 g2 hb ho hon hO hF he
    hk
  exact rowOnce S S₀ Cl W C F get set lo N i₀ act p l on o
    (fun k v w => ∀ i, openAfter In Out O₀ k i → μ i k v w) Rc ha ht g1 g2 hb ho hon
    (eachGoodIn_sh on act μ In Out O₀ (p :: l) i₀ hO hF) he hk

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.spineOnce
