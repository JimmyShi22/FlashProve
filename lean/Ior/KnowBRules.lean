-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowBRules.lean: from knowledge soundness for one instance to knowledge soundness in a batch:
rules beside those of Ior/BatchSeq.lean.

Statements and proofs. No protocol occurs here.
A slot is one of the N places of a batch, each with one instance or empty, with its own local
transcript.
Ior/BatchSeq.lean has the notion (`KnowB`: by sets of bad values, for the admissible vectors of
statements) and the first rules, for a whole block (an IOR used as one step) or a whole chain at
once, among them `knowB_joining` (all verifier messages shared, whoever speaks), `knowB_seq`; with
conditions that may fail: Ior/KnowWideB.lean. Knowledge soundness for one instance is `Know`
(Ior/Know.lean), with an extractor that may read statement, transcript and later witness.

Main names:
  `Spec.knowB_shared`: a block run once by the shared part, on a statement that all slots hold: from
    `Know`, the errors once.
  `Spec.knowB_beside`: the frame rule in a batch, for any annotation: if R has `KnowB`, then
    `R.keep Z F` (Ior/Frame.lean), which hands a further explicit part and further oracles on, has
    `KnowB` between the joints "R's on the acting part, S on the carried part", for every S: same
    errors; a vector is admissible if its acting parts form an admissible vector; the extractor is
    R's on the acting part and copies the carried witness. The carried parts of the slots need have
    nothing in common. (One instance: Ior/KnowCollRulesFrame.lean: `goodT_beside`.)
  `Spec.knowB_shared_beside`: the two together: a block on what the slots share, run once, beside
    what each slot carries of its own: the errors once, for the vectors whose acting parts are
    equal.
  `Spec.sameKey_shared`, `Spec.sameKey_any`: which vectors come out (what `knowB_seq` asks between
    two links); see their docstrings.

Limits: all of `KnowB`'s content hangs on which vectors are admissible (Ior/BatchSeq.lean, the head,
Limits). This file says nothing on the honest side (Ior/LinkV.lean). No rule here makes a shared
round cheaper than N times if the slots' acting parts differ.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowWideB
import Ior.KnowCollRulesFrame

set_option autoImplicit false

namespace Iop
open Prob

namespace Spec
open IOR

/-- A block run once, on a statement that all slots hold. -/
def knowB_shared : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (N : ℕ)
      (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape),
    R.red.Know on RA RB ext ε →
    R.KnowB (RoundSplits.const (RAnn.ofShared .sh) R.shape) N (SameKey id) on RA RB ext ε

/-- The frame rule in a batch. -/
def knowB_beside : Prop :=
  ∀ (Xi Xo Z : Type) (Ei Eo F : ExtSpec) (Wi Wo Wz : Type) (R : IOR Xi Ei Xo Eo)
      (A : RoundSplits R.shape) (N : ℕ) (adm : (Fin N → Option (Xi × Ei.Str)) → Prop)
      (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop)
      (RB : Xo × Eo.Str → Wo → Prop) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (ε : Err R.shape) (onS : Z × F.Str → Prop) (RS : Z × F.Str → Wz → Prop),
    R.KnowB A N adm on RA RB ext ε →
    (R.keep Z F).KnowB A N (fun a => adm fun j => (a j).map fun aj => (aj.1.1, aj.2.1))
      (fun a => on (a.1.1, a.2.1) ∧ onS (a.1.2, a.2.2))
      (fun a (w : Wi × Wz) => RA (a.1.1, a.2.1) w.1 ∧ RS (a.1.2, a.2.2) w.2)
      (fun b (w : Wo × Wz) => RB (b.1.1, b.2.1) w.1 ∧ RS (b.1.2, b.2.2) w.2)
      (fun a τ w => (ext (a.1.1, a.2.1) τ w.1, w.2)) ε

/-- A block on what the slots share, run once, beside what each slot carries. -/
def knowB_shared_beside : Prop :=
  ∀ (Xi Xo Z : Type) (Ei Eo F : ExtSpec) (Wi Wo Wz : Type) (R : IOR Xi Ei Xo Eo) (N : ℕ)
      (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop)
      (RB : Xo × Eo.Str → Wo → Prop) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (ε : Err R.shape) (onS : Z × F.Str → Prop) (RS : Z × F.Str → Wz → Prop),
    R.red.Know on RA RB ext ε →
    (R.keep Z F).KnowB (RoundSplits.const (RAnn.ofShared .sh) R.shape) N (SameKey fun a => (a.1.1, a.2.1))
      (fun a => on (a.1.1, a.2.1) ∧ onS (a.1.2, a.2.2))
      (fun a (w : Wi × Wz) => RA (a.1.1, a.2.1) w.1 ∧ RS (a.1.2, a.2.2) w.2)
      (fun b (w : Wo × Wz) => RB (b.1.1, b.2.1) w.1 ∧ RS (b.1.2, b.2.2) w.2)
      (fun a τ w => (ext (a.1.1, a.2.1) τ w.1, w.2)) ε

/-- States: where only the shared part speaks and all verifier messages are shared, all slots see
one local transcript. -/
def slot_shared : Prop :=
  ∀ (N : ℕ) (s : Shape) (τ : BTr N s (RoundSplits.const (RAnn.ofShared .sh) s)) (j j' : Fin N),
    τ.slot j = τ.slot j'

/-- States: one key stays one key through a link in which only the shared part speaks and all
verifier messages are shared, if the new key is a function of the old key and the local
transcript. -/
def sameKey_shared : Prop :=
  ∀ (Xi Xo κ κ' : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (N : ℕ) (key : Xi × Ei.Str → κ)
      (key' : Xo × Eo.Str → κ') (g : κ → Tr R.shape → κ'),
    (∀ a τ b, R.red.out a τ = some b → key' b = g (key a) τ) →
    ∀ a : Fin N → Option (Xi × Ei.Str), SameKey key a →
      ∀ τ : BTr N R.shape (RoundSplits.const (RAnn.ofShared .sh) R.shape),
        SameKey key' fun j => (a j).bind fun aj => R.red.out aj (τ.slot j)

/-- The same through any link, if the new key is a function of the old key alone. -/
def sameKey_any : Prop :=
  ∀ (Xi Xo κ κ' : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (A : RoundSplits R.shape) (N : ℕ)
      (key : Xi × Ei.Str → κ) (key' : Xo × Eo.Str → κ') (g : κ → κ'),
    (∀ a τ b, R.red.out a τ = some b → key' b = g (key a)) →
    ∀ a : Fin N → Option (Xi × Ei.Str), SameKey key a →
      ∀ τ : BTr N R.shape A, SameKey key' fun j => (a j).bind fun aj => R.red.out aj (τ.slot j)

end Spec

open IOR

theorem knowB_shared : Spec.knowB_shared := fun Xi Xo Ei Eo Wi Wo R N on RA RB ext ε h =>
  knowB_of_lost Xi Xo (Xi × Ei.Str) Ei Eo Wi Wo R N id
    (fun a τ => ∀ b w, R.red.out a τ = some b → RB b w → RA a (ext a τ w))
    on RA RB ext ε h fun _ _ b w _ hl hb hw => hl b w hb hw

theorem knowB_beside : Spec.knowB_beside := by
  rintro Xi Xo Z Ei Eo F Wi Wo Wz R A N adm on RA RB ext ε onS RS ⟨bad, c, J⟩
  refine ⟨fun a => bad (a.1.1, a.2.1), ?_, fun a ha => ?_⟩
  · rintro ⟨⟨x, z⟩, ⟨y, f⟩⟩ τ b w ha hτ hb hw
    have hb' : ((R.out x y τ).map fun xo => (xo, z)).map (fun xo => (xo, (R.imp y τ, f))) =
        some b := hb
    cases hx : R.out x y τ with
    | none =>
      rw [hx] at hb'
      cases hb'
    | some xo =>
      rw [hx] at hb'
      obtain rfl : ((xo, z), (R.imp y τ, f)) = b := Option.some.inj hb'
      exact ⟨c (x, y) τ (xo, R.imp y τ) w.1 ha.1 hτ
          (by show (R.out x y τ).map _ = _; rw [hx]; rfl) hw.1,
        hw.2⟩
  · refine cast (congrArg (JWithin N _ _ _) ?_) (J _ ha)
    funext j
    beta_reduce
    cases a j <;> rfl

theorem knowB_shared_beside : Spec.knowB_shared_beside := by
  intro Xi Xo Z Ei Eo F Wi Wo Wz R N on RA RB ext ε onS RS h
  refine knowB_conseq _ _ _ _ _ _ (R.keep Z F) _ N _ _ _ _ _ _ _ _ _ ε
    (knowB_beside Xi Xo Z Ei Eo F Wi Wo Wz R _ N _ on RA RB ext ε onS RS
      (knowB_shared Xi Xo Ei Eo Wi Wo R N on RA RB ext ε h))
    ?_ (fun _ ha => ha) (fun _ _ _ hw => hw) (fun _ _ hw => hw)
  intro a ha j j' aj aj' hj hj'
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hj
  obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hj'
  exact ha j j' b b' hb hb'

theorem slot_shared : Spec.slot_shared
  | _, [], _, _, _ => rfl
  | N, r :: s, (m, v, τ), j, j' =>
    congrArg (fun z => (((RAnn.ofShared .sh r).join m.1 (m.2 j), v, z) : Tr (r :: s)))
      (slot_shared N s τ j j')

theorem sameKey_shared : Spec.sameKey_shared := by
  intro Xi Xo κ κ' Ei Eo R N key key' g hg a ha τ j j' b b' hb hb'
  obtain ⟨aj, haj, hbj⟩ := Option.bind_eq_some_iff.mp hb
  obtain ⟨aj', haj', hbj'⟩ := Option.bind_eq_some_iff.mp hb'
  rw [hg aj _ b hbj, hg aj' _ b' hbj', ha j j' aj aj' haj haj', slot_shared N R.shape τ j j']

theorem sameKey_any : Spec.sameKey_any := by
  intro Xi Xo κ κ' Ei Eo R A N key key' g hg a ha τ j j' b b' hb hb'
  obtain ⟨aj, haj, hbj⟩ := Option.bind_eq_some_iff.mp hb
  obtain ⟨aj', haj', hbj'⟩ := Option.bind_eq_some_iff.mp hb'
  rw [hg aj _ b hbj, hg aj' _ b' hbj', ha j j' aj aj' haj haj']

end Iop
