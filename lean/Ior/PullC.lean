-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/PullC.lean: a pass: a reduction read behind maps of messages (`Carry`, Iop/Carry.lean):
round-by-round knowledge soundness is kept, each error count times the number w of its round.

Definitions and statements; the proofs are in Ior/PullCProofs.lean.
K is a reduction with a theorem; s is the shape of what is sent; for each input statement a, `F a`
maps the messages of s, round by round, to those of K. `K.pullC s F` has the rounds s: its verifier
forms the image of the transcript, rejects if there is none, and else decides and outputs as K does
on the image. Input and output statements, relations and the condition on statements are K's.
The maps may read the statement: what a prover does not send because it follows from the claim is
filled in from the claim.

Main names:
  `K.pullC s F` (K : `Reduction A B`); `K.extC s F ext d`: K's extractor on the image (d where there
    is none: nothing is output there).
  `Spec.know_pullC`: the rule: `K.Know on RA RB ext ε` and fibres of at most ws give
    `(K.pullC s F).Know on RA RB (K.extC s F ext d) (mulErr s K.shape ws ε)`.
  `Spec.know_pullC_seq`: how the rule meets the rule for two reductions in a row (`Know.seq`,
    Ior/Know.lean): compose first, then pass once along `(F a).app (G a)`: the maps of the second
    part may read the whole transcript of the first (so what the second needs may have been sent
    during the first); errors in a row.
  `IOR.Decl s Ei Eo`: what an IOR declares on positions, over the shape s.
  `R.pullC s F im V` (R : `IOR Xi Ei Xo Eo`): an IOR that carries `R.red.pullC s F`: the new
    implicit instance im and the declarations V are arguments.
  `Spec.red_pullC`: its reduction outputs what `R.red.pullC s F` outputs, if im is R's implicit
    instance on the image. `Spec.know_pullC_ior`: so the rule holds of it.
  `Spec.imp_pullC_app`, `Spec.know_pullC_seq_ior`: two IORs in a row behind `(F a).app (G a)`: the
    equation on the implicit instance from the two parts' equations (the second part's may read the
    transcript of the first); the rule for the carrier.
  `Spec.mulErr_toList`: the errors as a list: the products, in order. `Spec.mulErr_ones_toList`:
    at w = 1 in each round the same list.

Limits:
 (a) The new implicit instance is not "R's through F": by type an IOR's implicit instance does not
     see the explicit part of the statement, and F may. So im is an argument, with one equation as
     a premise.
 (b) The declarations on positions (blinded, extReads, reads, srcE, srcO, tie) do not go through a
     map of positions: five of them are functions of the verifier randomness of s, and a `Carry`
     has no map from it to that of K (its maps of verifier messages may read prover messages). They
     are plain arguments, and nothing is proved of them: not that `R.pullC s F im V` is local
     (`IOR.IsLocal`), tied, made of strings, or reads few positions.
 (c) Knowledge soundness reads an IOR's reduction alone (`IOR.red`), so it needs none of these:
     the rule is `Spec.know_pullC`, and the IOR is only its carrier, for statements whose type
     asks for an IOR.
 (d) Nothing on an honest prover: no completeness, no zero knowledge.
 (e) The rule holds for every F, also for maps under which no transcript has an image: then the
     verifier rejects everything, `Fib` holds with all w = 0, and the errors are 0. So the rule does
     not say that `K.pullC s F` is the verifier of a protocol that one has in mind: each use owes a
     closed form of its `out`. F may read the whole input statement, its implicit part too, and
     whole oracles: by type `K.pullC s F` is a function of the transcript, not a verifier with
     query access.
The error counts are the same only where all w are 1. As probabilities they are then the same only
if the two rounds have equally many verifier messages (`Rate`, `Spec.carry_below`, Iop/Carry.lean).

Terms: lean/GLOSSARY.md.

-/
import Iop.Carry
import Ior.Know
import Ior.Ior
import Ior.SeqProofs
import Ior.KnowCollRulesChainErr

set_option autoImplicit false

namespace Iop
open Prob

namespace Reduction
variable {A B WA WB : Type}

/-- K behind the maps F: the rounds s; the verifier forms the image of the transcript, rejects if
there is none, else does what K does on the image. -/
@[reducible] def pullC (K : Reduction A B) (s : Shape) (F : A → Carry s K.shape) :
    Reduction A B where
  shape := s
  out a τ := ((F a).tr τ).bind (K.out a)

/-- K's extractor on the image. Where there is no image nothing is output: the value is d. -/
def extC (K : Reduction A B) (s : Shape) (F : A → Carry s K.shape)
    (ext : A → Tr K.shape → WB → WA) (d : WA) : A → Tr s → WB → WA := fun a τ w =>
  match (F a).tr τ with
  | some τ' => ext a τ' w
  | none => d

end Reduction

namespace IOR
variable {Xi Xo : Type} {Ei Eo : ExtSpec}

/-- What an IOR declares on positions, over the shape s: the fields of `IOR` (Ior/Ior.lean) of the
same names. -/
structure Decl (s : Shape) (Ei Eo : ExtSpec) where
  blinded  : OPos s → Bool
  extReads : Rho s → Finset Ei.Pos
  reads    : Rho s → Finset (OPos s)
  srcE     : Rho s → Eo.Pos → Finset Ei.Pos
  srcO     : Rho s → Eo.Pos → Finset (OPos s)
  tie      : Rho s → OPos s → Finset Ei.Pos

/-- R behind the maps F, as an IOR: the new implicit instance and the declarations on positions are
arguments. -/
def pullC (R : IOR Xi Ei Xo Eo) (s : Shape) (F : Xi × Ei.Str → Carry s R.shape)
    (im : Ei.Str → Tr s → Eo.Str) (V : Decl s Ei Eo) : IOR Xi Ei Xo Eo where
  shape := s
  blinded := V.blinded
  extReads := V.extReads
  reads := V.reads
  out x y τ := ((F (x, y)).tr τ).bind (R.out x y)
  imp := im
  srcE := V.srcE
  srcO := V.srcO
  tie := V.tie

end IOR

namespace Spec
open Reduction

/-- The rule: knowledge soundness behind maps of messages: the same statements, relations and
condition; K's extractor on the image; each error count times the w of its round. -/
def know_pullC : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (s : Shape) (F : A → Carry s K.shape) (ws : Err s)
      (on : A → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
      (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape) (d : WA),
    K.Know on RA RB ext ε → (∀ a, on a → (F a).Fib ws) →
    (K.pullC s F).Know on RA RB (K.extC s F ext d) (mulErr s K.shape ws ε)

/-- Two reductions in a row, then the pass, once: the maps of the second part may read the
transcript of the first. -/
def know_pullC_seq : Prop :=
  ∀ (A B C WA WB WC : Type) (K₁ : Reduction A B) (K₂ : Reduction B C) (s₁ s₂ : Shape)
      (F : A → Carry s₁ K₁.shape) (G : A → Tr s₁ → Carry s₂ K₂.shape) (ws₁ : Err s₁)
      (ws₂ : Err s₂) (on₁ : A → Prop) (on₂ : B → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
      (RC : C → WC → Prop) (e₁ : A → Tr K₁.shape → WB → WA) (e₂ : B → Tr K₂.shape → WC → WB)
      (ε₁ : Err K₁.shape) (ε₂ : Err K₂.shape) (d : WA),
    K₁.Know on₁ RA RB e₁ ε₁ → K₂.Know on₂ RB RC e₂ ε₂ →
    (∀ a τ b, on₁ a → K₁.out a τ = some b → on₂ b) →
    (∀ a, on₁ a → (F a).Fib ws₁) → (∀ a τ, on₁ a → (G a τ).Fib ws₂) →
    ((K₁.seq K₂).pullC (s₁ ++ s₂) fun a => (F a).app (G a)).Know on₁ RA RC
      ((K₁.seq K₂).extC (s₁ ++ s₂) (fun a => (F a).app (G a)) (extSeq K₁ K₂ e₁ e₂ d) d)
      (Err.app (mulErr s₁ K₁.shape ws₁ ε₁) (mulErr s₂ K₂.shape ws₂ ε₂))

/-- The carrier's reduction outputs what the reduction behind the maps outputs, if im is R's
implicit instance on the image. -/
def red_pullC : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (s : Shape)
      (F : Xi × Ei.Str → Carry s R.shape) (im : Ei.Str → Tr s → Eo.Str) (V : IOR.Decl s Ei Eo),
    (∀ a τ τ', (F a).tr τ = some τ' → im a.2 τ = R.imp a.2 τ') →
    ∀ a τ, (R.pullC s F im V).red.out a τ = (R.red.pullC s F).out a τ

/-- The rule, for the carrier. -/
def know_pullC_ior : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (s : Shape)
      (F : Xi × Ei.Str → Carry s R.shape) (im : Ei.Str → Tr s → Eo.Str) (V : IOR.Decl s Ei Eo)
      (ws : Err s) (WA WB : Type) (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → WA → Prop)
      (RB : Xo × Eo.Str → WB → Prop) (ext : Xi × Ei.Str → Tr R.shape → WB → WA)
      (ε : Err R.shape) (d : WA),
    (∀ a τ τ', (F a).tr τ = some τ' → im a.2 τ = R.imp a.2 τ') →
    R.red.Know on RA RB ext ε → (∀ a, on a → (F a).Fib ws) →
    (R.pullC s F im V).red.Know on RA RB (R.red.extC s F ext d) (mulErr s R.shape ws ε)

/-- Two IORs in a row behind `(F a).app (G a)`: if im₁ is R₁'s implicit instance on the image, and
im₂, which may read the transcript of the first part, is R₂'s on the image, then the two in a row
are the implicit instance of `R₁.seq R₂` on the image. -/
def imp_pullC_app : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (s₁ s₂ : Shape) (F : X₁ × E₁.Str → Carry s₁ R₁.shape)
      (G : X₁ × E₁.Str → Tr s₁ → Carry s₂ R₂.shape) (im₁ : E₁.Str → Tr s₁ → E₂.Str)
      (im₂ : Tr s₁ → E₂.Str → Tr s₂ → E₃.Str),
    (∀ a τ₁ τ₁', (F a).tr τ₁ = some τ₁' → im₁ a.2 τ₁ = R₁.imp a.2 τ₁') →
    (∀ a τ₁ y₂ τ₂ τ₂', (G a τ₁).tr τ₂ = some τ₂' → im₂ τ₁ y₂ τ₂ = R₂.imp y₂ τ₂') →
    ∀ (a : X₁ × E₁.Str) (τ : Tr (s₁ ++ s₂)) (τ' : Tr (R₁.shape ++ R₂.shape)),
      ((F a).app (G a)).tr τ = some τ' →
      im₂ (Tr.fst τ) (im₁ a.2 (Tr.fst τ)) (Tr.snd (s := s₁) τ) = (R₁.seq R₂).imp a.2 τ'

/-- Two IORs in a row, then the pass, once: the rule for the carrier. -/
def know_pullC_seq_ior : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (s₁ s₂ : Shape) (F : X₁ × E₁.Str → Carry s₁ R₁.shape)
      (G : X₁ × E₁.Str → Tr s₁ → Carry s₂ R₂.shape) (im : E₁.Str → Tr (s₁ ++ s₂) → E₃.Str)
      (V : IOR.Decl (s₁ ++ s₂) E₁ E₃) (ws₁ : Err s₁) (ws₂ : Err s₂) (W₁ W₂ W₃ : Type)
      (on₁ : X₁ × E₁.Str → Prop) (on₂ : X₂ × E₂.Str → Prop) (RA : X₁ × E₁.Str → W₁ → Prop)
      (RB : X₂ × E₂.Str → W₂ → Prop) (RC : X₃ × E₃.Str → W₃ → Prop)
      (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁) (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂)
      (ε₁ : Err R₁.shape) (ε₂ : Err R₂.shape) (d : W₁),
    (∀ (a : X₁ × E₁.Str) (τ : Tr (s₁ ++ s₂)) (τ' : Tr (R₁.shape ++ R₂.shape)),
      ((F a).app (G a)).tr τ = some τ' → im a.2 τ = (R₁.seq R₂).imp a.2 τ') →
    R₁.red.Know on₁ RA RB e₁ ε₁ → R₂.red.Know on₂ RB RC e₂ ε₂ →
    (∀ a τ b, on₁ a → R₁.red.out a τ = some b → on₂ b) →
    (∀ a, on₁ a → (F a).Fib ws₁) → (∀ a τ, on₁ a → (G a τ).Fib ws₂) →
    ((R₁.seq R₂).pullC (s₁ ++ s₂) (fun a => (F a).app (G a)) im V).red.Know on₁ RA RC
      ((R₁.seq R₂).red.extC (s₁ ++ s₂) (fun a => (F a).app (G a)) (IOR.extSeq R₁ R₂ e₁ e₂ d) d)
      (Err.app (mulErr s₁ R₁.shape ws₁ ε₁) (mulErr s₂ R₂.shape ws₂ ε₂))

/-- The errors as a list, between shapes with a `Carry`: the products, in order. -/
def mulErr_toList : Prop :=
  ∀ (s s' : Shape), Carry s s' → ∀ (ws : Err s) (ε : Err s'),
    (mulErr s s' ws ε).toList = List.zipWith (· * ·) ε.toList ws.toList

/-- At w = 1 in each round the errors are the same, as lists. -/
def mulErr_ones_toList : Prop :=
  ∀ (s s' : Shape), Carry s s' → ∀ ε : Err s', (mulErr s s' (Err.ones s) ε).toList = ε.toList

end Spec
end Iop
