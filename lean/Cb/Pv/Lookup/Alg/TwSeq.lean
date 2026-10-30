-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Alg/TwSeq.lean.
The reduction of a composed interactive oracle reduction, and verifiers that never refuse.

Definitions, and theorems with their proofs, over the library's own types (Ior, Iop) alone.
Main names:
  `red_seq_eq`: the reduction of `R₁.seq R₂` is the two reductions joined by `Reduction.seq`, as an
    equation of reductions.
  `red_seq_app`: its out at a joined transcript.
  `red_post_out`, `red_pre_out`, `red_draw_out`: the out of a reduction with a step without rounds
    after or before it, where the step is a total map on the explicit part and leaves the oracles as
    they are; and the out of a draw. For all inputs.
  `Tot R f` (R with one `ExtSpec` in and out): the verifier R never refuses, puts out f of the
    explicit statement and the transcript, and copies the oracles.
  `Tot.red_out`, `seqV`, `seqV_app`, `Tot.seq`, `Tot.post`, `Tot.pre`, `Tot.draw`: its rules.
    `Tot.unique`: there is at most one such f, if there is an oracle string (`Ex.Str`) at all.
Limits: the verifier's side alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Ior.SeqProofs
import Ior.FrameProofs
import Ior.Draw

set_option autoImplicit false

namespace Tw
open Iop IOR

section
variable {X₁ X₂ X₃ Xi Xo : Type} {E₁ E₂ E₃ Ei Eo Ex : ExtSpec}

/-- The reduction of a composition is the composition of the reductions: as Reductions. -/
theorem red_seq_eq (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃) :
    (R₁.seq R₂).red = R₁.red.seq R₂.red :=
  congrArg (Reduction.mk (R₁.shape ++ R₂.shape))
    (funext fun a => funext fun τ => IOR.red_seq_out R₁ R₂ a τ)

/-- The composition's out at a concatenation. -/
theorem red_seq_app (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃) (a : X₁ × E₁.Str)
    (τ₁ : Tr R₁.shape) (τ₂ : Tr R₂.shape) :
    (R₁.seq R₂).red.out a (Tr.app τ₁ τ₂) = (R₁.red.out a τ₁).bind fun b => R₂.red.out b τ₂ :=
  (IOR.red_seq_out R₁ R₂ a (Tr.app τ₁ τ₂)).trans (Reduction.seq_out_app R₁.red R₂.red a τ₁ τ₂)

/-- A map on the explicit part after R: for all inputs. -/
theorem red_post_out (R : IOR X₁ Ei X₂ Eo) (φ : X₂ → X₃) (a : X₁ × Ei.Str) (τ : Tr R.shape) :
    (R.post (fun x => some (φ x)) (ExtMap.id Eo)).red.out a τ =
      (R.red.out a τ).map fun b => (φ b.1, b.2) := by
  show ((R.out a.1 a.2 τ).bind fun x => some (φ x)).map (fun xo => (xo, R.imp a.2 τ)) =
    ((R.out a.1 a.2 τ).map fun xo => (xo, R.imp a.2 τ)).map fun b => (φ b.1, b.2)
  cases R.out a.1 a.2 τ <;> rfl

/-- A map on the explicit part before R: for all inputs. -/
theorem red_pre_out (R : IOR X₂ Ei X₃ Eo) (φ : X₁ → X₂) (a : X₁ × Ei.Str) (τ : Tr R.shape) :
    (R.pre (fun x => some (φ x)) (ExtMap.id Ei)).red.out a τ = R.red.out (φ a.1, a.2) τ := rfl

/-- A draw: for all inputs. -/
theorem red_draw_out (D : Type) [Fintype D] [Nonempty D] (nx : X₁ → D → X₂) (a : X₁ × Ex.Str)
    (τ : Tr [drawRound D]) : (IOR.draw D nx Ex).red.out a τ = some (nx a.1 (drawn τ), a.2) := rfl

/-- The verifier never refuses, its value is f of the explicit part and the transcript, the oracles
are copied. -/
structure Tot (R : IOR Xi Ex Xo Ex) (f : Xi → Tr R.shape → Xo) : Prop where
  out : ∀ x y τ, R.out x y τ = some (f x τ)
  imp : ∀ y τ, R.imp y τ = y

theorem Tot.red_out {R : IOR Xi Ex Xo Ex} {f : Xi → Tr R.shape → Xo} (h : Tot R f)
    (a : Xi × Ex.Str) (τ : Tr R.shape) : R.red.out a τ = some (f a.1 τ, a.2) := by
  show (R.out a.1 a.2 τ).map (fun xo => (xo, R.imp a.2 τ)) = _
  rw [h.out, h.imp]
  rfl

/-- The value of a composition. -/
def seqV {s₁ s₂ : Shape} (f : X₁ → Tr s₁ → X₂) (g : X₂ → Tr s₂ → X₃) : X₁ → Tr (s₁ ++ s₂) → X₃ :=
  fun x τ => g (f x (Tr.fst τ)) (Tr.snd (s := s₁) τ)

theorem seqV_app {s₁ s₂ : Shape} (f : X₁ → Tr s₁ → X₂) (g : X₂ → Tr s₂ → X₃) (x : X₁) (τ₁ : Tr s₁)
    (τ₂ : Tr s₂) : seqV f g x (Tr.app τ₁ τ₂) = g (f x τ₁) τ₂ := by
  unfold seqV
  rw [Tr.fst_app, Tr.snd_app]

theorem Tot.seq {R₁ : IOR X₁ Ex X₂ Ex} {R₂ : IOR X₂ Ex X₃ Ex} {f : X₁ → Tr R₁.shape → X₂}
    {g : X₂ → Tr R₂.shape → X₃} (h₁ : Tot R₁ f) (h₂ : Tot R₂ g) : Tot (R₁.seq R₂) (seqV f g) :=
  ⟨fun x y τ => by
      show (R₁.out x y (Tr.fst τ)).bind (fun x₂ =>
        R₂.out x₂ (R₁.imp y (Tr.fst τ)) (Tr.snd (s := R₁.shape) τ)) = _
      rw [h₁.out, h₁.imp]
      exact h₂.out _ _ _,
    fun y τ => by
      show R₂.imp (R₁.imp y (Tr.fst τ)) (Tr.snd (s := R₁.shape) τ) = y
      rw [h₁.imp, h₂.imp]⟩

theorem Tot.post {R : IOR X₁ Ex X₂ Ex} {f : X₁ → Tr R.shape → X₂} (h : Tot R f) (φ : X₂ → X₃) :
    Tot (R.post (fun x => some (φ x)) (ExtMap.id Ex)) fun x τ => φ (f x τ) :=
  ⟨fun x y τ => by
      show (R.out x y τ).bind (fun x => some (φ x)) = _
      rw [h.out]
      rfl,
    fun y τ => h.imp y τ⟩

theorem Tot.pre {R : IOR X₂ Ex X₃ Ex} {f : X₂ → Tr R.shape → X₃} (h : Tot R f) (φ : X₁ → X₂) :
    Tot (R.pre (fun x => some (φ x)) (ExtMap.id Ex)) fun x τ => f (φ x) τ :=
  ⟨fun x y τ => h.out (φ x) y τ, fun y τ => h.imp y τ⟩

theorem Tot.draw (D : Type) [Fintype D] [Nonempty D] (nx : X₁ → D → X₂) :
    Tot (IOR.draw D nx Ex) fun x τ => nx x (drawn τ) :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- Two value functions of one verifier agree (if there is an oracle string at all). -/
theorem Tot.unique {R : IOR Xi Ex Xo Ex} {f g : Xi → Tr R.shape → Xo} (hf : Tot R f) (hg : Tot R g)
    (y : Ex.Str) : f = g :=
  funext fun x => funext fun τ => Option.some.inj ((hf.out x y τ).symm.trans (hg.out x y τ))

end
end Tw
#print axioms Tw.red_seq_eq
#print axioms Tw.red_seq_app
#print axioms Tw.red_post_out
#print axioms Tw.red_pre_out
#print axioms Tw.red_draw_out
#print axioms Tw.Tot.red_out
#print axioms Tw.seqV_app
#print axioms Tw.Tot.seq
#print axioms Tw.Tot.post
#print axioms Tw.Tot.pre
#print axioms Tw.Tot.draw
#print axioms Tw.Tot.unique
