-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowWideB.lean: rules for `IOR.KnowB` (Ior/BatchSeq.lean), round-by-round knowledge soundness
for one link of a chain of IORs (interactive oracle reductions, Ior/Ior.lean) in a batch:
   a chain ends in the wide form;
   conditions that may fail;
   the decoder of the statement.

A definition, statements and proofs. No protocol occurs here.
The wide form is `SndBKT` (Ior/KnowWide.lean): round-by-round knowledge soundness for the instances
of a batch, with a witness map that may read the instance, the external oracle and the whole local
transcript.
`early`, `late`: how an instance is written into the hash chain of its slot: early x into the first
query, x itself into the query of the round late (see the docstring of `BatchInteractiveOracleProof.SndBL`,
Iop/Batch.lean).
"adm" says what the statements of one batch have in common (the shared oracles; the shared part of
the explicit statement). "on" is a condition on the input statements: the statements of which
soundness speaks.

Why: `KnowB` has a wide extractor (statement, transcript, later witness), but the rule that ends a
chain, `sndBK_of_knowB` (Ior/BatchSeq.lean), asks for a witness map on oracles.
`knowB_seq` asks that every output of the first link on a statement that meets the first link's
condition meets the condition of the second: false of a condition that fails with a bad event.

Main names:
  `Spec.sndBKT_of_knowB`: from `KnowB` of a chain that ends in the trivial statement to `SndBKT` of
    the batch IOP `BIOP.curry`, at early = id, late = none; see its docstring.
  `Spec.knowB_iff_orOff`: a condition on the input statements is an enlargement of the input
    relation.
  `Spec.knowBInto_seq_ext`: composition; see its docstring.
  `Spec.knowBInto_of_carry`: `KnowB` gives `KnowBInto` for a link that carries the condition: every
    output on a statement with "on" has "on'".
  `IOR.KnowBInto`, `Spec.knowB_of_det`, `sndBK_of_knowB_of_T`: see their docstrings.

Notation:
  `A` : `RoundSplits R.shape`: in `R.KnowB A N ...` (Ior/BatchSeq.lean) an annotation of its shape
    (Iop/Batch.lean: which rounds are shared, who speaks).
  `N` : ℕ: the number of slots (the head of Iop/Batch.lean).
  `RA` : `Xi × Ei.Str → Wi → Prop`, `RB` : `Xo × Eo.Str → Wo → Prop`, in `IOR.KnowBInto`: the input
    relation, the output relation.
  `on'` : `Xo × Eo.Str → Prop`.
Limits: what the head of Ior/BatchSeq.lean lists as not said is not said here either.
All of `KnowB`'s content hangs on "adm". At adm = "no vector" `KnowB` holds of every IOR with at
least one round (take all values as bad).
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowWide
import Ior.KnowColl
import Ior.BatchSeq

set_option autoImplicit false

namespace Iop
open Prob

/-- On the statements with "on", into the statements with "on'", for a link of a chain in a batch:
`KnowB` at the output relation enlarged by the statements outside on'. -/
def IOR.KnowBInto {Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} (R : IOR Xi Ei Xo Eo)
    (A : RoundSplits R.shape) (N : ℕ) (adm : (Fin N → Option (Xi × Ei.Str)) → Prop)
    (on : Xi × Ei.Str → Prop) (on' : Xo × Eo.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop)
    (RB : Xo × Eo.Str → Wo → Prop) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape) :
    Prop :=
  R.KnowB A N adm on RA (Reduction.orOff on' RB) ext ε

namespace Spec
open IOR

/-- States, under the hypotheses below: if a chain that ends in the trivial statement has `KnowB` on
statements that share the first implicit component (the adm), and R and wit are such that "on → RA
at the chain's extractor" gives R at wit, then the batch IOP with the slots' own oracles moved into
the instance has `SndBKT` for R and wit, at early = id, late = none. (`SndBKT` is (Snd-B) with a
witness, wide; (Snd-B): `BatchInteractiveOracleProof.SndB`, Iop/Batch.lean.) -/
def sndBKT_of_knowB : Prop :=
  ∀ (X W Wc : Type) (E0 Ej : ExtSpec) (Q : BIOP X (E0.prod Ej)) (N : ℕ)
      (on : X × (E0.prod Ej).Str → Prop) (RA : X × (E0.prod Ej).Str → Wc → Prop)
      (ext : X × (E0.prod Ej).Str → Tr Q.ior.shape → Unit → Wc) (ε : Err Q.ior.shape)
      (R : X × Ej.Str → E0.Str → W → Prop) (wit : X × Ej.Str → E0.Str → Tr Q.ior.shape → W),
    Q.ior.KnowB Q.ann N (SameKey fun a => a.2.1) on RA (fun _ (_ : Unit) => True) ext ε →
    (∀ (a : X × Ej.Str) (y0 : E0.Str) (τ : Tr Q.ior.shape),
      (on (a.1, (y0, a.2)) → RA (a.1, (y0, a.2)) (ext (a.1, (y0, a.2)) τ ())) →
      R a y0 (wit a y0 τ)) →
    Q.curry.SndBKT N id none R wit ε

/-- The plain case of `sndBKT_of_knowB`. -/
def sndBKT_of_knowB_ext : Prop :=
  ∀ (X Wc : Type) (E0 Ej : ExtSpec) (Q : BIOP X (E0.prod Ej)) (N : ℕ)
      (on : X × (E0.prod Ej).Str → Prop) (RA : X × (E0.prod Ej).Str → Wc → Prop)
      (ext : X × (E0.prod Ej).Str → Tr Q.ior.shape → Unit → Wc) (ε : Err Q.ior.shape),
    Q.ior.KnowB Q.ann N (SameKey fun a => a.2.1) on RA (fun _ (_ : Unit) => True) ext ε →
    Q.curry.SndBKT N id none (fun a y0 w => on (a.1, (y0, a.2)) → RA (a.1, (y0, a.2)) w)
      (fun a y0 τ => ext (a.1, (y0, a.2)) τ ()) ε

def knowB_iff_orOff : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (A : RoundSplits R.shape) (N : ℕ)
      (adm : (Fin N → Option (Xi × Ei.Str)) → Prop) (on : Xi × Ei.Str → Prop)
      (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape),
    R.KnowB A N adm on RA RB ext ε ↔
    R.KnowB A N adm (fun _ => True) (Reduction.orOff on RA) RB ext ε

def knowBInto_of_carry : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (A : RoundSplits R.shape) (N : ℕ)
      (adm : (Fin N → Option (Xi × Ei.Str)) → Prop) (on : Xi × Ei.Str → Prop)
      (on' : Xo × Eo.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape),
    (∀ a τ b, R.red.out a τ = some b → on a → on' b) →
    R.KnowB A N adm on RA RB ext ε → R.KnowBInto A N adm on on' RA RB ext ε

/-- States composition: on₁ into on₂, then on₂ into on₃, is on₁ into on₃ for `R₁.seq R₂`, errors in
a row,
   if the outputs of a vector with adm₁, on any transcript of the whole batch, have adm₂,
   and ext agrees with "e₂, then e₁" wherever the first verifier outputs a statement. -/
def knowBInto_seq_ext : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (W₁ W₂ W₃ : Type) (R₁ : IOR X₁ E₁ X₂ E₂)
      (R₂ : IOR X₂ E₂ X₃ E₃) (A₁ : RoundSplits R₁.shape) (A₂ : RoundSplits R₂.shape) (N : ℕ)
      (adm₁ : (Fin N → Option (X₁ × E₁.Str)) → Prop) (adm₂ : (Fin N → Option (X₂ × E₂.Str)) → Prop)
      (on₁ : X₁ × E₁.Str → Prop) (on₂ : X₂ × E₂.Str → Prop) (on₃ : X₃ × E₃.Str → Prop)
      (RA : X₁ × E₁.Str → W₁ → Prop) (RB : X₂ × E₂.Str → W₂ → Prop) (RC : X₃ × E₃.Str → W₃ → Prop)
      (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁) (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂)
      (ext : X₁ × E₁.Str → Tr (R₁.shape ++ R₂.shape) → W₃ → W₁) (ε₁ : Err R₁.shape)
      (ε₂ : Err R₂.shape),
    R₁.KnowBInto A₁ N adm₁ on₁ on₂ RA RB e₁ ε₁ → R₂.KnowBInto A₂ N adm₂ on₂ on₃ RB RC e₂ ε₂ →
    (∀ a, adm₁ a →
      ∀ τ : BTr N R₁.shape A₁, adm₂ fun j => (a j).bind fun aj => R₁.red.out aj (τ.slot j)) →
    (∀ a (τ : Tr (R₁.shape ++ R₂.shape)) b w, R₁.red.out a (Tr.fst τ) = some b →
      ext a τ w = e₁ a (Tr.fst τ) (e₂ b (Tr.snd (s := R₁.shape) τ) w)) →
    (R₁.seq R₂).KnowBInto (RoundSplits.app A₁ A₂) N adm₁ on₁ on₃ RA RC ext (Err.app ε₁ ε₂)

/-- States: where the relation determines its witness on the statements with "on", the extractor may
be replaced by the decoder d of the statement. -/
def knowB_of_det : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (A : RoundSplits R.shape) (N : ℕ)
      (adm : (Fin N → Option (Xi × Ei.Str)) → Prop) (on : Xi × Ei.Str → Prop)
      (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape) (d : Xi × Ei.Str → Wi),
    (∀ a w, on a → RA a w → w = d a) → R.KnowB A N adm on RA RB ext ε →
    R.KnowB A N adm on RA RB (fun a _ _ => d a) ε

end Spec

open IOR

theorem sndBKT_of_knowB : Spec.sndBKT_of_knowB := by
  intro X W Wc E0 Ej Q N on RA ext ε R wit ⟨bad, c, J⟩ hR
  refine (sndBP_iff_badFam _ _ Q.curry N _ ε).2 ⟨fun a y0 => bad (a.1, (y0, a.2)), ?_, ?_⟩
  · intro a y0 (τ : Tr Q.ior.shape) hτ hacc
    refine hR a y0 τ fun ha => ?_
    have hacc' : (Q.ior.out a.1 (y0, a.2) τ).isSome = true := hacc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hacc'
    exact c (a.1, (y0, a.2)) τ (u, Q.ior.imp (y0, a.2) τ) () ha hτ
      (by show (Q.ior.out a.1 (y0, a.2) τ).map _ = _; rw [hu]; rfl) trivial
  · intro y0 x
    have h := J (fun j => (x j).map fun a => (a.1, (y0, a.2))) (fun j j' aj aj' hj hj' => by
      obtain ⟨b, _, rfl⟩ := Option.map_eq_some_iff.mp hj
      obtain ⟨b', _, rfl⟩ := Option.map_eq_some_iff.mp hj'
      rfl)
    refine cast (congrArg (JWithin N _ _ _) ?_) h
    funext j
    beta_reduce
    cases x j <;> rfl

theorem sndBKT_of_knowB_ext : Spec.sndBKT_of_knowB_ext := fun X Wc E0 Ej Q N on RA ext ε h =>
  sndBKT_of_knowB X Wc Wc E0 Ej Q N on RA ext ε _ _ h fun _ _ _ hw => hw

/-- `Spec.sndBK_of_knowB`, proved again as an instance of `sndBKT_of_knowB`. -/
theorem sndBK_of_knowB_of_T : Spec.sndBK_of_knowB := fun X W Wc E0 Ej Q N on RA ext ε R wit h hR =>
  sndBKT_of_knowB X W Wc E0 Ej Q N on RA ext ε R (fun a _ τ => wit a τ.read) h hR

theorem knowB_iff_orOff : Spec.knowB_iff_orOff := by
  intro Xi Xo Ei Eo Wi Wo R A N adm on RA RB ext ε
  constructor
  · rintro ⟨bad, c, J⟩
    refine ⟨bad, fun a τ b w _ hτ hb hw => ?_, J⟩
    by_cases ha : on a
    · exact Or.inl (c a τ b w ha hτ hb hw)
    · exact Or.inr ha
  · rintro ⟨bad, c, J⟩
    exact ⟨bad,
      fun a τ b w ha hτ hb hw => (c a τ b w trivial hτ hb hw).elim id fun hn => absurd ha hn,
      J⟩

theorem knowBInto_of_carry : Spec.knowBInto_of_carry := by
  rintro Xi Xo Ei Eo Wi Wo R A N adm on on' RA RB ext ε hc ⟨bad, c, J⟩
  exact ⟨bad,
    fun a τ b w ha hτ hb hw => hw.elim (c a τ b w ha hτ hb) fun hn => absurd (hc a τ b hb ha) hn,
    J⟩

theorem knowBInto_seq_ext : Spec.knowBInto_seq_ext := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ W₁ W₂ W₃ R₁ R₂ A₁ A₂ N adm₁ adm₂ on₁ on₂ on₃ RA RB RC e₁
    e₂ ext ε₁ ε₂ h₁ h₂ hadm he
  exact knowB_seq_ext X₁ X₂ X₃ E₁ E₂ E₃ W₁ W₂ W₃ R₁ R₂ A₁ A₂ N adm₁ adm₂ on₁ (fun _ => True) RA
    (Reduction.orOff on₂ RB) (Reduction.orOff on₃ RC) e₁ e₂ ext ε₁ ε₂ h₁
    ((knowB_iff_orOff X₂ X₃ E₂ E₃ W₂ W₃ R₂ A₂ N adm₂ on₂ RB (Reduction.orOff on₃ RC) e₂ ε₂).1 h₂)
    (fun _ _ _ _ _ => trivial) hadm he

theorem knowB_of_det : Spec.knowB_of_det := by
  rintro Xi Xo Ei Eo Wi Wo R A N adm on RA RB ext ε d hd ⟨bad, c, J⟩
  refine ⟨bad, fun a τ b w ha hτ hb hw => ?_, J⟩
  have h1 := c a τ b w ha hτ hb hw
  show RA a (d a)
  rw [← hd a _ ha h1]
  exact h1

end Iop
