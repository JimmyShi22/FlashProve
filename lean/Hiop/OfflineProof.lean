-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/OfflineProof.lean: small rules for a composition: an interactive oracle reduction followed by
an IOP of proximity.






















Limits: this file says nothing on the numbers of positions read or the probabilities of withheld
sets.

Terms: lean/GLOSSARY.md.
-/
import Hiop.ListNums
import Ior.ToProtoProofsSeq
import Ior.SeqProofs
import Ior.ExactSeq

set_option autoImplicit false

namespace Iop
open Prob

namespace Reduction
variable {A B WA WB : Type}

/-- If no output on the statements with `on` has a witness, knowledge soundness holds with any
errors, in particular with all errors 0. -/
theorem Know.of_no_witness {K : Reduction A B} {on : A → Prop} {RA : A → WA → Prop}
    {RB : B → WB → Prop} (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape)
    (h : ∀ a τ b w, on a → K.out a τ = some b → ¬ RB b w) : K.Know on RA RB ext ε :=
  fun a ha => Doomed.of_forall _ _ fun τ b w hb hw => absurd hw (h a τ b w ha hb)

/-- The composed extractor where the first verifier outputs b. -/
theorem extSeq_of_some {C WC : Type} (K₁ : Reduction A B) (K₂ : Reduction B C)
    (e₁ : A → Tr K₁.shape → WB → WA) (e₂ : B → Tr K₂.shape → WC → WB) (d : WA) (a : A)
    (τ : Tr (K₁.seq K₂).shape) (w : WC) (b : B) (h : K₁.out a (Tr.fst τ) = some b) :
    extSeq K₁ K₂ e₁ e₂ d a τ w = e₁ a (Tr.fst τ) (e₂ b (Tr.snd (s := K₁.shape) τ) w) := by
  simp only [extSeq, h]

end Reduction

namespace IOR
variable {X₁ X₂ X₃ Xi Xo : Type} {E₁ E₂ E₃ Ei Eo : ExtSpec}

/-- What an output of the reduction of an IOR is. -/
theorem red_out_some {R : IOR Xi Ei Xo Eo} {a : Xi × Ei.Str} {τ : Tr R.shape}
    {b : Xo × Eo.Str} (h : R.red.out a τ = some b) :
    R.out a.1 a.2 τ = some b.1 ∧ b.2 = R.imp a.2 τ := by
  obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨hxo, rfl⟩

/-- Given `hr`, knowledge soundness of the composed reductions gives knowledge soundness of the
composed IOR. -/
theorem know_seq_of (hr : Spec.red_seq) {WA WC : Type} {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃}
    {on : X₁ × E₁.Str → Prop} {RA : X₁ × E₁.Str → WA → Prop} {RC : X₃ × E₃.Str → WC → Prop}
    {ext : X₁ × E₁.Str → Tr (R₁.shape ++ R₂.shape) → WC → WA} {ε : Err (R₁.shape ++ R₂.shape)}
    (h : (R₁.red.seq R₂.red).Know on RA RC ext ε) :
    (R₁.seq R₂).red.Know on RA RC ext ε :=
  fun a ha =>
    Doomed.mono _ _
      (fun τ hτ b w hb hw => hτ b w ((hr _ _ _ _ _ _ R₁ R₂ a τ).symm.trans hb) hw) (h a ha)

end IOR
end Iop
