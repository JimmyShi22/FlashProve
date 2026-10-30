-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowWide.lean: round-by-round knowledge soundness for the instances of a batch, with a witness
map that may read the whole local transcript (`SndBKT`).

Definitions, statements and proofs. No protocol occurs here.
A slot is one of the N places of a batch, each with one instance or empty, with its own local
transcript.

Why: Ior/Batch.lean's `SndBK` takes a witness map wit : X → Orcs s → W: the instance and the symbols
of the prover's oracles of a full local transcript; by type no verifier message, no plain part, no
external oracle. That serves where a witness is decoded from the oracles. Where an oracle has
several codewords near it, which of them is meant is told by a sample: a seed, which is a verifier
message, and an answer, which is a plain part; and extractors that go backwards from a later witness
may read a fold's coefficient. So here the witness map reads more. `SndBK` is the instance "forget".

Main names:
  `Q.guardP ok`, `Q.SndBP N early late ok ε`: the working form (see their docstrings).
  `witOf w`: a witness map given by parts: the form that an extractor of a compiled argument can
    feed.
  `Spec.sndBK_iff_T`: `SndBK` at wit is `SndBKT` at the map that applies wit to x and the oracles of
    τ, by definition.
  `Spec.sndBP_iff`: written out, when the whole instance stands in the first query (early = id, late
    = none).
  `Spec.sndBKT_of_det`: narrowing to a map d that reads less; see its docstring, and below.
  `Spec.sndBL_of_sndBP`, `Spec.sndBL_of_sndBKT`: from `SndBP` (for every language that holds
    wherever ok does), from `SndBKT` (for the language of the relation), to (Snd-B), late form
    (`BatchInteractiveOracleProof.SndBL`, Iop/Batch.lean), with the same errors.
  `Spec.one_of_sndBP`: the list for one fixed instance, for 0 < N, at early = id, late = none: the
    local protocol of one slot, in the form "the prover has lost at the start".

Where `Spec.sndBKT_of_det` bites: for a batch IOP whose instance names the oracles and their samples
(`BIOP.curry`: a slot's own oracles stand in the instance; a sample stands in the explicit part) and
whose relation speaks of them: there d = "the member of the list that agrees with the sample" reads
the instance alone.
Where it does not: a relation that names no oracle (index, request, cells) does not determine its
witness from oracles: a transcript accepted by luck may hold other cells [no theorem here]. So the
narrowing is made at the tail behind a sending, and the tail is then composed with what stands
before it (Ior/KnowWideOnline.lean).

Limits: what a slot's witness map may read, by type: its instance; the external oracle (shared by
the slots); its own local transcript: the slot's and the shared part's prover messages, the slot's
own verifier messages and the shared verifier messages. Not: another slot's instance, messages or
verifier messages.
This file says nothing on the honest side, on the verifier's queries (`reads`, `extReads`), on
running times. It says nothing on how an extractor of a compiled argument learns verifier messages.
It says nothing on "an IOR in every slot, then a batch IOP": see Ior/KnowWideOnline.lean.
Terms: lean/GLOSSARY.md: bad values, batch IOP, cells, external oracles, fold, honest side, index,
list, plain part, the prover has lost, request, sample, sending, (Snd-B), witness map.
-/
import Ior.BatchKProofsBad
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob

namespace BatchInteractiveOracleProof
variable {X W : Type} {E : ExtSpec}

open Classical in
/-- Q with a verifier that also rejects when "ok" holds. -/
def guardP (Q : BatchInteractiveOracleProof X E) (ok : X → E.Str → Tr Q.loc.shape → Prop) :
    BatchInteractiveOracleProof X E where
  loc := { Q.loc with accept := fun x y τ => Q.loc.accept x y τ && !decide (ok x y τ) }
  ann := Q.ann

/-- (Snd-B), late form, of `Q.guardP ok` for the empty language. In words: for every statement the
prover has lost, at the start, towards "the verifier rejects or ok" (as `Doomed`, for 0 < N at early
= id, late = none: `Spec.one_of_sndBP`). -/
def SndBP (Q : BatchInteractiveOracleProof X E) (N : ℕ) (early : X → X) (late : Option ℕ)
    (ok : X → E.Str → Tr Q.loc.shape → Prop) (ε : Err Q.loc.shape) : Prop :=
  (Q.guardP ok).SndBL N early late (fun _ _ => False) ε

/-- (Snd-B) with a witness, the witness map reading the instance, the external oracle and the whole
local transcript. -/
def SndBKT (Q : BatchInteractiveOracleProof X E) (N : ℕ) (early : X → X) (late : Option ℕ) (R : X → E.Str → W → Prop)
    (wit : X → E.Str → Tr Q.loc.shape → W) (ε : Err Q.loc.shape) : Prop :=
  Q.SndBP N early late (fun x y τ => R x y (wit x y τ)) ε

end BatchInteractiveOracleProof

/-- A witness map given by parts: the symbols of the oracles, the plain parts, the verifier
messages. -/
def witOf {X W : Type} {E : ExtSpec} {s : Shape} (w : X → E.Str → Orcs s → Plains s → Rho s → W) :
    X → E.Str → Tr s → W :=
  fun x y τ => w x y τ.read τ.plains τ.rho

namespace Spec

/-- States: `SndBK` is the instance "forget". -/
def sndBK_iff_T : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (early : X → X) (late : Option ℕ)
      (R : X → E.Str → W → Prop) (wit : X → Orcs Q.loc.shape → W) (ε : Err Q.loc.shape),
    Q.SndBK N early late R wit ε ↔ Q.SndBKT N early late R (fun x _ τ => wit x τ.read) ε

/-- Written out, when the whole instance stands in the first query. -/
def sndBP_iff : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ)
      (ok : X → E.Str → Tr Q.loc.shape → Prop) (ε : Err Q.loc.shape),
    Q.SndBP N id none ok ε ↔
    ∃ State : E.Str → X → PTr Q.loc.shape → Bool,
      (∀ y x, State y x (PTr.empty Q.loc.shape) = false) ∧
      (∀ y x (τ : AtP Q.loc.shape) (m : τ.round.Msg),
        State y x (.atP τ) = false → State y x (.atV (τ.snoc m)) = false) ∧
      (∀ y x (τ : Tr Q.loc.shape),
        State y x (.full τ) = false → Q.loc.accept x y τ = true → ok x y τ) ∧
      (∀ y (x : Fin N → Option X), JointLaw N Q.loc.shape Q.ann ε fun j => (x j).map (State y))

/-- Written out, in the late form. -/
def sndBP_laws : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (early : X → X) (late : Option ℕ)
      (ok : X → E.Str → Tr Q.loc.shape → Prop) (ε : Err Q.loc.shape),
    Q.SndBP N early late ok ε ↔
    (∀ n, late = some n → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann) ∧
    ∃ State : E.Str → X → PTr Q.loc.shape → Bool,
      (∀ y x, State y (early x) (PTr.empty Q.loc.shape) = false) ∧
      (∀ y x (τ : AtP Q.loc.shape) (m : τ.round.Msg),
        State y x (.atP τ) = false → State y x (.atV (τ.snoc m)) = false) ∧
      (∀ y x (τ : AtP Q.loc.shape),
        late = some τ.idx → State y (early x) (.atP τ) = false → State y x (.atP τ) = false) ∧
      (∀ y x (τ : Tr Q.loc.shape), State y (if late.isSome then x else early x) (.full τ) = false →
        Q.loc.accept x y τ = true → ok x y τ) ∧
      (∀ y (x : Fin N → Option X), JointLaw N Q.loc.shape Q.ann ε fun j => (x j).map (State y))

/-- the same for a relation and a witness map -/
def sndBKT_laws : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (early : X → X) (late : Option ℕ)
      (R : X → E.Str → W → Prop) (wit : X → E.Str → Tr Q.loc.shape → W) (ε : Err Q.loc.shape),
    Q.SndBKT N early late R wit ε ↔
    (∀ n, late = some n → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann) ∧
    ∃ State : E.Str → X → PTr Q.loc.shape → Bool,
      (∀ y x, State y (early x) (PTr.empty Q.loc.shape) = false) ∧
      (∀ y x (τ : AtP Q.loc.shape) (m : τ.round.Msg),
        State y x (.atP τ) = false → State y x (.atV (τ.snoc m)) = false) ∧
      (∀ y x (τ : AtP Q.loc.shape),
        late = some τ.idx → State y (early x) (.atP τ) = false → State y x (.atP τ) = false) ∧
      (∀ y x (τ : Tr Q.loc.shape), State y (if late.isSome then x else early x) (.full τ) = false →
        Q.loc.accept x y τ = true → R x y (wit x y τ)) ∧
      (∀ y (x : Fin N → Option X), JointLaw N Q.loc.shape Q.ann ε fun j => (x j).map (State y))

/-- A weaker goal. -/
def sndBP_mono : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (early : X → X) (late : Option ℕ)
      (ok ok' : X → E.Str → Tr Q.loc.shape → Prop) (ε : Err Q.loc.shape),
    (∀ x y τ, Q.loc.accept x y τ = true → ok x y τ → ok' x y τ) →
    Q.SndBP N early late ok ε → Q.SndBP N early late ok' ε

/-- A larger relation; another witness map that is valid wherever the old one is. -/
def sndBKT_conseq : Prop :=
  ∀ (X W W' : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (early : X → X) (late : Option ℕ)
      (R : X → E.Str → W → Prop) (R' : X → E.Str → W' → Prop) (wit : X → E.Str → Tr Q.loc.shape → W)
      (wit' : X → E.Str → Tr Q.loc.shape → W') (ε : Err Q.loc.shape),
    (∀ x y τ, Q.loc.accept x y τ = true → R x y (wit x y τ) → R' x y (wit' x y τ)) →
    Q.SndBKT N early late R wit ε → Q.SndBKT N early late R' wit' ε

/-- States: narrowing: where the relation determines its witness from what d reads, the witness map
may be replaced by d. -/
def sndBKT_of_det : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (early : X → X) (late : Option ℕ)
      (R : X → E.Str → W → Prop) (wit d : X → E.Str → Tr Q.loc.shape → W) (ε : Err Q.loc.shape),
    (∀ x y τ w, Q.loc.accept x y τ = true → R x y w → w = d x y τ) →
    Q.SndBKT N early late R wit ε → Q.SndBKT N early late R d ε

/-- From `SndBP`, (Snd-B), late form, for every language that holds wherever the goal does. -/
def sndBL_of_sndBP : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (early : X → X) (late : Option ℕ)
      (ok : X → E.Str → Tr Q.loc.shape → Prop) (L : X → E.Str → Prop) (ε : Err Q.loc.shape),
    (∀ x y τ, ok x y τ → L x y) → Q.SndBP N early late ok ε → Q.SndBL N early late L ε

def sndBL_of_sndBKT : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (early : X → X) (late : Option ℕ)
      (R : X → E.Str → W → Prop) (wit : X → E.Str → Tr Q.loc.shape → W) (ε : Err Q.loc.shape),
    Q.SndBKT N early late R wit ε → Q.SndBL N early late (fun x y => ∃ w, R x y w) ε

/-- States: at early = id, late = none, state functions and sets of bad values are the same
thing. -/
def sndBP_iff_badFam : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ)
      (ok : X → E.Str → Tr Q.loc.shape → Prop) (ε : Err Q.loc.shape),
    Q.SndBP N id none ok ε ↔
    ∃ bad : X → E.Str → BadFam Q.loc.shape,
      (∀ x y τ, (bad x y).Clean τ → Q.loc.accept x y τ = true → ok x y τ) ∧
      ∀ y (x : Fin N → Option X),
        JWithin N Q.loc.shape Q.ann ε fun j => (x j).map fun xj => (false, bad xj y)

/-- The list for one fixed instance. -/
def one_of_sndBP : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ)
      (ok : X → E.Str → Tr Q.loc.shape → Prop) (ε : Err Q.loc.shape),
    0 < N → Q.SndBP N id none ok ε →
    ∀ x y, Doomed Q.loc.shape ε (fun τ => Q.loc.accept x y τ = true → ok x y τ)

end Spec

open BatchK

/-- The guarded verifier rejects if and only if: should the verifier accept, "ok" holds. -/
theorem guardP_accept_false {X : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof X E)
    (ok : X → E.Str → Tr Q.loc.shape → Prop) (x : X) (y : E.Str) (τ : Tr Q.loc.shape) :
    (Q.guardP ok).loc.accept x y τ = false ↔ (Q.loc.accept x y τ = true → ok x y τ) := by
  classical
  show (Q.loc.accept x y τ && !decide (ok x y τ)) = false ↔ _
  cases Q.loc.accept x y τ <;> simp

theorem sndBK_iff_T : Spec.sndBK_iff_T := fun _ _ _ _ _ _ _ _ _ _ => Iff.rfl

theorem sndBP_iff : Spec.sndBP_iff := by
  intro X E Q N ok ε
  constructor
  · rintro ⟨-, State, h1, h2, -, h3, h4⟩
    exact ⟨State, fun y x => h1 y x id, h2,
      fun y x τ h0 => (guardP_accept_false Q ok x y τ).1 (h3 y x τ id h0), h4⟩
  · rintro ⟨State, h1, h2, h3, h4⟩
    exact ⟨fun n hn => (by cases hn), State, fun y x _ => h1 y x, h2,
      fun _ _ _ _ hn => (by cases hn),
      fun y x τ _ h0 => (guardP_accept_false Q ok x y τ).2 (h3 y x τ h0), h4⟩

theorem sndBP_laws : Spec.sndBP_laws := by
  intro X E Q N early late ok ε
  constructor
  · rintro ⟨h0, State, h1, h2, h3, h4, h5⟩
    exact ⟨h0, State, fun y x => h1 y x id, h2, fun y x τ => h3 y x τ id,
      fun y x τ hs => (guardP_accept_false Q ok x y τ).1 (h4 y x τ id hs), h5⟩
  · rintro ⟨h0, State, h1, h2, h3, h4, h5⟩
    exact ⟨h0, State, fun y x _ => h1 y x, h2, fun y x τ _ => h3 y x τ,
      fun y x τ _ hs => (guardP_accept_false Q ok x y τ).2 (h4 y x τ hs), h5⟩

theorem sndBKT_laws : Spec.sndBKT_laws := fun X _ E Q N early late _ _ ε =>
  sndBP_laws X E Q N early late _ ε

theorem sndBP_mono : Spec.sndBP_mono := by
  intro X E Q N early late ok ok' ε hk
  rintro ⟨h0, State, h1, h2, h3, h4, h5⟩
  exact ⟨h0, State, h1, h2, h3,
    fun y x τ hL hs =>
      (guardP_accept_false Q ok' x y τ).2 fun ha =>
        hk x y τ ha ((guardP_accept_false Q ok x y τ).1 (h4 y x τ hL hs) ha), h5⟩

theorem sndBKT_conseq : Spec.sndBKT_conseq := fun X _ _ E Q N early late _ _ _ _ ε hk h =>
  sndBP_mono X E Q N early late _ _ ε hk h

theorem sndBKT_of_det : Spec.sndBKT_of_det := fun X W E Q N early late R wit d ε hd h =>
  sndBKT_conseq X W W E Q N early late R R wit d ε (fun x y τ ha hw => hd x y τ _ ha hw ▸ hw) h

theorem sndBL_of_sndBP : Spec.sndBL_of_sndBP := by
  intro X E Q N early late ok L ε hk
  rintro ⟨h0, State, h1, h2, h3, h4, h5⟩
  refine ⟨h0, State, fun y x _ => h1 y x id, h2, fun y x τ _ => h3 y x τ id,
    fun y x τ hL hs => ?_, h5⟩
  have h6 := (guardP_accept_false Q ok x y τ).1 (h4 y x τ id hs)
  exact Bool.eq_false_iff.2 fun ha => hL (hk x y τ (h6 ha))

theorem sndBL_of_sndBKT : Spec.sndBL_of_sndBKT := fun X _ E Q N early late _ _ ε h =>
  sndBL_of_sndBP X E Q N early late _ _ ε (fun _ _ _ hw => ⟨_, hw⟩) h

theorem sndBP_iff_badFam : Spec.sndBP_iff_badFam := by
  intro X E Q N ok ε
  constructor
  · intro h
    obtain ⟨State, h1, h2, h3, h4⟩ := (sndBP_iff X E Q N ok ε).1 h
    refine ⟨fun x y => BadFam.ofState _ (State y x),
      fun x y τ hτ => h3 y x τ (ofState_clean _ _ (h2 y x) (h1 y x) τ hτ),
      fun y x => jWithin_ofState N _ _ ε _ _ (fun j => ?_) (h4 y x)⟩
    cases x j <;> rfl
  · rintro ⟨bad, hclean, hJ⟩
    refine (sndBP_iff X E Q N ok ε).2 ⟨fun y x => stOf (false, bad x y), fun y x => ?_,
      fun y x τ m h => ?_, fun y x τ h => ?_, fun y x => ?_⟩
    · show (false || (bad x y).dirty (PTr.empty _)) = false
      rw [BadFam.dirty_empty]
      rfl
    · show (false || (bad x y).dirty (.atV (τ.snoc m))) = false
      rw [BadFam.dirty_snoc]
      exact h
    · have h' : (false || (bad x y).dirty (.full τ)) = false := h
      rw [Bool.false_or] at h'
      exact hclean x y τ ((BadFam.dirty_full _ τ).mp h')
    · have h1 := jointLaw_of_jWithin N _ _ ε _ (hJ y x)
      have h2 : (fun j => ((x j).map fun xj => ((false : Bool), bad xj y)).map stOf) =
          fun j => (x j).map fun xj => stOf (false, bad xj y) := by
        funext j
        cases x j <;> rfl
      rw [h2] at h1
      exact h1

theorem one_of_sndBP : Spec.one_of_sndBP := by
  intro X E Q N ok ε hN h x y
  obtain ⟨State, h1, h2, h3, h4⟩ := (sndBP_iff X E Q N ok ε).1 h
  exact doomed_of_jointLaw ⟨0, hN⟩ _ Q.ann ε _ (State y x) _ rfl (h2 y x)
    (h4 y fun _ => some x) (h1 y x) (h3 y x)

end Iop
