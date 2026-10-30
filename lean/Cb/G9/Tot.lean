-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/G9/Tot.lean: the output of reductions joined by Reduction.seq, as one total function.

A verifier that never rejects is a function. This file says so of a reduction and carries the
statement through the library's ways of joining reductions.

Main names:
  Tot K v: the reduction K rejects nothing and its output is v: for all a and τ, K.out a τ = some (v
    a τ).
  seqV: two such functions, one after the other, on a joined transcript: v₂ (v₁ a (Tr.fst τ))
    (Tr.snd τ).
  Tot.seq: Tot K₁ v₁ and Tot K₂ v₂ give Tot (K₁.seq K₂) (seqV ..). Bracket longer chains to the
    right, as Reduction.seq asks.
  Tot.ior_seq: the same for the reduction of IOR.seq, through IOR.red_seq_out.
  Tot.draw, Tot.post, Tot.pre: the library's draw, and a step without rounds behind or before a
    block if that step rejects nothing.

To run: seqV calls Tr.fst and Tr.snd, which match on the shape when they run. Cb/G9/Split.lean has
the same rules with a split that does not.

Limits: verifiers that can reject are not covered. Nothing is said on soundness, knowledge soundness
or hiding.
-/
import Iop.Compose
import Ior.Draw
import Ior.Frame
import Ior.SeqProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TWhole.G9
open Iop

variable {A B C : Type}

/-- The reduction rejects nothing and puts out v. -/
def Tot (K : Reduction A B) (v : A → Tr K.shape → B) : Prop := ∀ a τ, K.out a τ = some (v a τ)

/-- Two total verifiers in turn, on a joined transcript. -/
def seqV (s₁ s₂ : Shape) (v₁ : A → Tr s₁ → B) (v₂ : B → Tr s₂ → C) (a : A) (τ : Tr (s₁ ++ s₂)) :
    C :=
  v₂ (v₁ a (Tr.fst τ)) (Tr.snd (s := s₁) τ)

theorem Tot.seq {K₁ : Reduction A B} {K₂ : Reduction B C} {v₁ : A → Tr K₁.shape → B}
    {v₂ : B → Tr K₂.shape → C} (h₁ : Tot K₁ v₁) (h₂ : Tot K₂ v₂) :
    Tot (K₁.seq K₂) (seqV K₁.shape K₂.shape v₁ v₂) := by
  intro a τ
  show (K₁.out a (Tr.fst τ)).bind (fun b => K₂.out b (Tr.snd (s := K₁.shape) τ)) = _
  rw [h₁, Option.bind_some, h₂]
  rfl

/-- On transcripts laid one behind the other. -/
theorem seqV_app (s₁ s₂ : Shape) (v₁ : A → Tr s₁ → B) (v₂ : B → Tr s₂ → C) (a : A) (τ₁ : Tr s₁)
    (τ₂ : Tr s₂) : seqV s₁ s₂ v₁ v₂ a (Tr.app τ₁ τ₂) = v₂ (v₁ a τ₁) τ₂ := by
  unfold seqV
  rw [Tr.fst_app, Tr.snd_app]

section Ior
variable {X₁ X₂ X₃ X X' : Type} {E₁ E₂ E₃ E : ExtSpec}

/-- The same for two IORs joined by the library's IOR.seq (which has no code): its .red puts out the
two .red's functions in turn. -/
theorem Tot.ior_seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃}
    {v₁ : X₁ × E₁.Str → Tr R₁.shape → X₂ × E₂.Str} {v₂ : X₂ × E₂.Str → Tr R₂.shape → X₃ × E₃.Str}
    (h₁ : Tot R₁.red v₁) (h₂ : Tot R₂.red v₂) :
    Tot (R₁.seq R₂).red (seqV R₁.shape R₂.shape v₁ v₂) := fun a τ =>
  (IOR.red_seq_out R₁ R₂ a τ).trans (Tot.seq h₁ h₂ a τ)

/-- The library's draw. -/
def drawV (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (E : ExtSpec) (a : X × E.Str)
    (τ : Tr [IOR.drawRound D]) : X' × E.Str := (nx a.1 (IOR.drawn τ), a.2)

theorem Tot.draw (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (E : ExtSpec) :
    Tot (IOR.draw D nx E).red (drawV D nx E) := fun _ _ => rfl

/-- A step without rounds behind a block, if it rejects nothing. -/
theorem Tot.post {R : IOR X₁ E₁ X₂ E₂} {v : X₁ × E₁.Str → Tr R.shape → X₂ × E₂.Str}
    (h : Tot R.red v)
    (f : X₂ → X₃) (g : ExtMap E₂ E₃) :
    Tot (R.post (fun x => some (f x)) g).red (fun a τ => (f (v a τ).1, g.map (v a τ).2)) := by
  intro a τ
  have h' := h a τ
  show ((R.out a.1 a.2 τ).bind fun x => some (f x)).map (fun xo => (xo, g.map (R.imp a.2 τ))) = _
  have h2 : (R.out a.1 a.2 τ).map (fun xo => (xo, R.imp a.2 τ)) = some (v a τ) := h'
  obtain ⟨x, hx, hv⟩ := Option.map_eq_some_iff.1 h2
  show _ = some (f (v a τ).1, g.map (v a τ).2)
  rw [hx, ← hv]
  rfl

/-- A step without rounds before a block, if it rejects nothing. -/
theorem Tot.pre {R : IOR X₂ E₂ X₃ E₃} {v : X₂ × E₂.Str → Tr R.shape → X₃ × E₃.Str} (h : Tot R.red v)
    (f : X₁ → X₂) (g : ExtMap E₁ E₂) :
    Tot (R.pre (fun x => some (f x)) g).red (fun a τ => v (f a.1, g.map a.2) τ) := fun a τ =>
  h (f a.1, g.map a.2) τ

end Ior

end TWhole.G9

#print axioms TWhole.G9.Tot.seq
#print axioms TWhole.G9.seqV_app
#print axioms TWhole.G9.Tot.ior_seq
#print axioms TWhole.G9.Tot.draw
#print axioms TWhole.G9.Tot.post
#print axioms TWhole.G9.Tot.pre
