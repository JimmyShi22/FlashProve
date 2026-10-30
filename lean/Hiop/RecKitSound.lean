-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecKitSound.lean: book-keeping lemmas: round-by-round soundness and knowledge soundness of an
interactive oracle proof, or reduction, under a re-indexing of its explicit input or output.
In this library's words: the same protocol on other instances (Hiop/RecKit.lean): soundness and
knowledge soundness are carried along.

A definition, statements and proofs. No protocol of this library occurs here.

Why: a record joins the explicit instance of every protocol on its encoded index; so the same
verifier is looked at on instances (x, record) and, for a fixed record, on instances x. "x' is read
as f x'" changes no shape, no list of errors, no transcript.

Main names (the rules):
  `Spec.sound_comap`, `Spec.sound_comap_iff`: an IOP: round-by-round soundness for L gives it for "L
    at f x'"; both ways if every instance is some f x'.
  `Spec.sndBP_comap`, `Spec.sndBKT_comap`: a batch IOP (Ior/KnowWide.lean): the goal, the relation
    and the witness map are read at f x'. `early` may be any map on the new instances that f carries
    to the old one.
  `Spec.sndBP_comap_iff`, `Spec.sndBKT_comap_iff`: both ways, if moreover f has a section g that
    goes along with the two maps `early`.
  `Q.withAccept acc`, `Spec.sndBP_withAccept`: (Snd-B) (`SndBP`, Ior/KnowWide.lean) reads of a batch
    IOP its shape, its annotation and its decision, nothing else: a verifier that accepts less keeps
    it.
  `Spec.know_comapX`: an IOR whose explicit input is read through f: condition, input relation and
    extractor are read at (f x', y).
  `Spec.know_mapOut`: an IOR whose explicit output is mapped by g: the output relation is read at (g
    xo, y).
  `Spec.know_fix`: the two together, for a component that is handed on: F runs on (x, r) and outputs
    (xl, r') with r' = r ("passes"), and `F.red.Know on RA RB ext ε`. Then, for each fixed r, "F on
    x, with output xl" has knowledge soundness with all relations read at r.

Limits: this file says nothing on the honest side (Hiop/RecKitHonest.lean). It says nothing on
records: f, g, r are arbitrary.

Terms: lean/GLOSSARY.md.
-/
import Hiop.RecKit
import Ior.KnowWide
import Ior.KnowColl

set_option autoImplicit false

namespace Iop
open Prob

/-- the same batch IOP with another decision -/
def BatchInteractiveOracleProof.withAccept {X : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof X E)
    (acc : X → E.Str → Tr Q.loc.shape → Bool) : BatchInteractiveOracleProof X E :=
  ⟨{ Q.loc with accept := acc }, Q.ann⟩

namespace Spec

def sound_comap : Prop :=
  ∀ (X X' : Type) (E : ExtSpec) (Q : InteractiveOracleProof X E) (f : X' → X)
      (L : X → E.Str → Prop) (ε : Err Q.shape),
    Q.Sound L ε → (Q.comap f).Sound (fun x' y => L (f x') y) ε

def sound_comap_iff : Prop :=
  ∀ (X X' : Type) (E : ExtSpec) (Q : InteractiveOracleProof X E) (f : X' → X)
      (L : X → E.Str → Prop) (ε : Err Q.shape),
    Function.Surjective f → ((Q.comap f).Sound (fun x' y => L (f x') y) ε ↔ Q.Sound L ε)

def sndBP_comap : Prop :=
  ∀ (X X' : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (f : X' → X) (N : ℕ)
      (early : X → X) (early' : X' → X') (late : Option ℕ)
      (ok : X → E.Str → Tr Q.loc.shape → Prop) (ε : Err Q.loc.shape),
    (∀ x', f (early' x') = early (f x')) → Q.SndBP N early late ok ε →
    (Q.comap f).SndBP N early' late (fun x' y τ => ok (f x') y τ) ε

def sndBKT_comap : Prop :=
  ∀ (X X' W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (f : X' → X) (N : ℕ) (early : X → X)
      (early' : X' → X') (late : Option ℕ) (R : X → E.Str → W → Prop)
      (wit : X → E.Str → Tr Q.loc.shape → W) (ε : Err Q.loc.shape),
    (∀ x', f (early' x') = early (f x')) → Q.SndBKT N early late R wit ε →
    (Q.comap f).SndBKT N early' late (fun x' y w => R (f x') y w) (fun x' y τ => wit (f x') y τ) ε

def sndBP_comap_iff : Prop :=
  ∀ (X X' : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (f : X' → X) (g : X → X') (N : ℕ)
      (early : X → X) (early' : X' → X') (late : Option ℕ)
      (ok : X → E.Str → Tr Q.loc.shape → Prop) (ε : Err Q.loc.shape),
    (∀ x', f (early' x') = early (f x')) → (∀ x, f (g x) = x) → (∀ x, g (early x) = early' (g x)) →
    ((Q.comap f).SndBP N early' late (fun x' y τ => ok (f x') y τ) ε ↔ Q.SndBP N early late ok ε)

def sndBKT_comap_iff : Prop :=
  ∀ (X X' W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (f : X' → X) (g : X → X') (N : ℕ)
      (early : X → X) (early' : X' → X') (late : Option ℕ) (R : X → E.Str → W → Prop)
      (wit : X → E.Str → Tr Q.loc.shape → W) (ε : Err Q.loc.shape),
    (∀ x', f (early' x') = early (f x')) → (∀ x, f (g x) = x) → (∀ x, g (early x) = early' (g x)) →
    ((Q.comap f).SndBKT N early' late (fun x' y w => R (f x') y w)
        (fun x' y τ => wit (f x') y τ) ε ↔
      Q.SndBKT N early late R wit ε)

/-- A verifier that accepts less keeps (Snd-B) (`SndBP`, Ior/KnowWide.lean). -/
def sndBP_withAccept : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E)
      (acc : X → E.Str → Tr Q.loc.shape → Bool) (N : ℕ) (early : X → X) (late : Option ℕ)
      (ok : X → E.Str → Tr Q.loc.shape → Prop) (ε : Err Q.loc.shape),
    (∀ x y τ, acc x y τ = true → Q.loc.accept x y τ = true) → Q.SndBP N early late ok ε →
    (Q.withAccept acc).SndBP N early late ok ε

def know_comapX : Prop :=
  ∀ (Xi Xi' Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (f : Xi' → Xi)
      (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape),
    R.red.Know on RA RB ext ε →
    (R.comapX f).red.Know (fun a => on (f a.1, a.2)) (fun a w => RA (f a.1, a.2) w) RB
      (fun a τ w => ext (f a.1, a.2) τ w) ε

def know_mapOut : Prop :=
  ∀ (Xi Xo Xo' : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (g : Xo → Xo')
      (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop) (RB' : Xo' × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape),
    R.red.Know on RA (fun b w => RB' (g b.1, b.2) w) ext ε → (R.mapOut g).red.Know on RA RB' ext ε

/-- A component that is handed on, fixed. -/
def know_fix : Prop :=
  ∀ (X Xl Rc : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (F : IOR (X × Rc) Ei (Xl × Rc) Eo)
      (r : Rc) (on : (X × Rc) × Ei.Str → Prop) (RA : (X × Rc) × Ei.Str → Wi → Prop)
      (RB : (Xl × Rc) × Eo.Str → Wo → Prop)
      (ext : (X × Rc) × Ei.Str → Tr F.shape → Wo → Wi) (ε : Err F.shape),
    (∀ x y τ b, F.out x y τ = some b → b.2 = x.2) → F.red.Know on RA RB ext ε →
    ((F.comapX fun x : X => (x, r)).mapOut Prod.fst).red.Know (fun a => on ((a.1, r), a.2))
      (fun a w => RA ((a.1, r), a.2) w) (fun b w => RB ((b.1, r), b.2) w)
      (fun a τ w => ext ((a.1, r), a.2) τ w) ε

end Spec

theorem sound_comap : Spec.sound_comap := fun _ _ _ _ f _ _ h x' y hL => h (f x') y hL

theorem sound_comap_iff : Spec.sound_comap_iff := fun X X' E Q f L ε hf =>
  ⟨fun h x y hL => by
    obtain ⟨x', rfl⟩ := hf x
    exact h x' y hL, sound_comap X X' E Q f L ε⟩

theorem sndBP_comap : Spec.sndBP_comap := by
  intro X X' E Q f N early early' late ok ε he h
  obtain ⟨h0, State, h1, h2, h3, h4, h5⟩ := (sndBP_laws X E Q N early late ok ε).1 h
  refine (sndBP_laws X' E (Q.comap f) N early' late _ ε).2
    ⟨h0, fun y x' => State y (f x'), fun y x' => ?_, fun y x' => h2 y (f x'),
      fun y x' τ hl hs => ?_, fun y x' τ hs ha => ?_, fun y x' => ?_⟩
  · show State y (f (early' x')) _ = false
    rw [he]
    exact h1 y (f x')
  · have hs' : State y (f (early' x')) (.atP τ) = false := hs
    rw [he] at hs'
    exact h3 y (f x') τ hl hs'
  · refine h4 y (f x') τ ?_ ha
    have hs' : State y (f (if late.isSome then x' else early' x')) (.full τ) = false := hs
    rw [apply_ite f, he] at hs'
    exact hs'
  · have h6 := h5 y fun j => (x' j).map f
    refine cast (congrArg (JointLaw N Q.loc.shape Q.ann ε) ?_) h6
    funext j
    beta_reduce
    cases x' j <;> rfl

theorem sndBKT_comap : Spec.sndBKT_comap := fun X X' _ E Q f N early early' late _ _ ε he h =>
  sndBP_comap X X' E Q f N early early' late _ ε he h

theorem sndBP_comap_iff : Spec.sndBP_comap_iff := by
  intro X X' E Q f g N early early' late ok ε he hfg hge
  refine ⟨fun h => ?_, sndBP_comap X X' E Q f N early early' late ok ε he⟩
  obtain ⟨h0, State, h1, h2, h3, h4, h5⟩ := (sndBP_laws X' E (Q.comap f) N early' late _ ε).1 h
  refine (sndBP_laws X E Q N early late ok ε).2
    ⟨h0, fun y x => State y (g x), fun y x => ?_, fun y x => h2 y (g x), fun y x τ hl hs => ?_,
      fun y x τ hs ha => ?_, fun y x => ?_⟩
  · show State y (g (early x)) _ = false
    rw [hge]
    exact h1 y (g x)
  · have hs' : State y (g (early x)) (.atP τ) = false := hs
    rw [hge] at hs'
    exact h3 y (g x) τ hl hs'
  · have hs' : State y (g (if late.isSome then x else early x)) (.full τ) = false := hs
    rw [apply_ite g, hge] at hs'
    have ha' : (Q.comap f).loc.accept (g x) y τ = true := by
      show Q.loc.accept (f (g x)) y τ = true
      rw [hfg]
      exact ha
    have h6 : ok (f (g x)) y τ := h4 y (g x) τ hs' ha'
    rw [hfg] at h6
    exact h6
  · have h6 := h5 y fun j => (x j).map g
    refine cast (congrArg (JointLaw N Q.loc.shape Q.ann ε) ?_) h6
    funext j
    beta_reduce
    cases x j <;> rfl

theorem sndBKT_comap_iff :
    Spec.sndBKT_comap_iff := fun X X' _ E Q f g N early early' late R wit ε he hfg hge =>
  sndBP_comap_iff X X' E Q f g N early early' late (fun x y τ => R x y (wit x y τ)) ε he hfg hge

theorem sndBP_withAccept : Spec.sndBP_withAccept := by
  intro X E Q acc N early late ok ε ha h
  obtain ⟨h0, State, h1, h2, h3, h4, h5⟩ := (sndBP_laws X E Q N early late ok ε).1 h
  exact (sndBP_laws X E (Q.withAccept acc) N early late ok ε).2
    ⟨h0, State, h1, h2, h3, fun y x τ hs hacc => h4 y x τ hs (ha x y τ hacc), h5⟩

theorem know_comapX : Spec.know_comapX := fun _ _ _ _ _ _ _ _ f _ _ _ _ _ h a ha =>
  h (f a.1, a.2) ha

theorem know_mapOut : Spec.know_mapOut := by
  intro Xi Xo Xo' Ei Eo Wi Wo R g on RA RB' ext ε h a ha
  refine Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b' w hb hw
  have hb' : ((R.out a.1 a.2 τ).map g).map (fun xo => (xo, R.imp a.2 τ)) = some b' := hb
  cases ho : R.out a.1 a.2 τ with
  | none =>
    rw [ho] at hb'
    cases hb'
  | some xo =>
    rw [ho] at hb'
    obtain rfl : (g xo, R.imp a.2 τ) = b' := Option.some.inj hb'
    exact hτ (xo, R.imp a.2 τ) w (by show (R.out a.1 a.2 τ).map _ = _; rw [ho]; rfl) hw

theorem know_fix : Spec.know_fix := by
  intro X Xl Rc Ei Eo Wi Wo F r on RA RB ext ε hp h a ha
  refine Doomed.mono _ _ ?_ (h ((a.1, r), a.2) ha)
  intro τ hτ b' w hb hw
  have hb' : ((F.out (a.1, r) a.2 τ).map Prod.fst).map (fun xo => (xo, F.imp a.2 τ)) = some b' := hb
  cases ho : F.out (a.1, r) a.2 τ with
  | none =>
    rw [ho] at hb'
    cases hb'
  | some xo =>
    rw [ho] at hb'
    obtain rfl : (xo.1, F.imp a.2 τ) = b' := Option.some.inj hb'
    have e : xo = (xo.1, r) := Prod.ext rfl (hp (a.1, r) a.2 τ xo ho)
    refine hτ (xo, F.imp a.2 τ) w (by show (F.out (a.1, r) a.2 τ).map _ = _; rw [ho]; rfl) ?_
    rw [e]
    exact hw

end Iop
