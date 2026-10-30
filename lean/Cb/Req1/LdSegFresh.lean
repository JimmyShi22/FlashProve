-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFresh.lean: chains that start with masks in their input witness: the rule for masks
sent in advance, relative to what is fresh at the start.

Definitions, statements (Iop.Spec.*) and proofs. No protocol, no code occurs here.
A chain (`IOR.Chain`, Ior/KnowCollRulesChain.lean) is a non-empty list of `IOR.Link`, each a
reduction with its honest side, extractor and numbers. Names and paths: the whole bundle:
`IOR.GoodT` (Ior/KnowCollGood.lean); the bundle without its clause on zero knowledge: `IOR.GoodB`;
masked block: `IOR.GoodM` (both in Ior/Masked.lean); Blind ("does not look"): `Honest.Blind`
(Ior/KnowCollRulesMask.lean).
`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. (`Honest.Fresh`, `Honest.seen`,
Ior/KnowCollRulesMask.lean.) In this file it stands in the definition `c.FreshGiven base f` (of each
link's `l.H`) and in its two unfolding lemmas; `FreshGiven`, and `OkGiven`, which is defined with
it, stand in the statements below as premises and as conclusions.

Why: Ior/KnowCollRulesChain.lean has the rule for a whole chain: every link has the whole bundle, or
it is a masked block whose masks are fresh after the chain before it (`c.Ok`; `chain_ok`: then the
chain is honest-verifier zero knowledge (`GoodT.exact`: `Honest.Exact`, Ior/Honest.lean)). There the
part that sends the masks is in the chain.
A protocol that is cut into pieces of which each sends the masks of the next one is an append of
chains, and a piece alone starts with masks in its input witness. What a piece has is a property
relative to a set of facts "these masks are fresh at my start".
Ior/KnowCollPiece.lean has `c.OkFrom c₀`, for a chain c after the chain c₀: `(c₀.append c).Ok` if
and only if `c₀.Ok` and `c.OkFrom c₀`. Here a piece's property names no chain before it, only facts
at its start: so it can be stated for a piece alone, and pieces are put in a row.

Main names:
  `MaskFact W`: a reading kc of a witness, values Mk of some mask entries (a finite, non-empty
    type), put: how they are written into what is read.
  `c.FreshGiven base f`: as `c.FreshFor` (the last link sends the masks of f; or it does not look at
    them and they were fresh before it), and, at the first link: or it does not look at them and
    they are fresh at the start: a fact of "base".
  `c.OkGiven base`: as `c.Ok`, with `FreshGiven`; the first link may be a masked block whose masks
    are fresh at the start.
  `Spec.freshGiven_none`, `Spec.okGiven_none`: with no fact at the start these are `FreshFor` and
    `Ok`.
  `Spec.freshGiven_mono`, `Spec.okGiven_mono`: more facts at the start.
  `Spec.freshGiven_append`, `Spec.okGiven_append` (the second under `c₀.OkGiven base₀`): two pieces
    in a row: if the first piece, from base₀, makes every fact of "base" fresh, then what the second
    piece has from "base" the two together have from base₀.
  `Spec.freshFor_of_given`, `Spec.ok_of_given`: the same behind a chain that is Ok outright: the
    whole is Ok, so honest-verifier zero knowledge (`chain_ok`; `GoodT.exact`: `Honest.Exact`,
    Ior/Honest.lean).
  `Spec.allB_of_okGiven`: a piece that is OkGiven some base has the bundle without its clause on
    zero knowledge in every link.
  `Spec.blind_stepPure`: a step without rounds whose honest map commutes with the overwriting does
    not look at the masks.

Limits: no link that is Fresh or Blind is exhibited but a step without rounds. A piece alone is not
zero knowledge.
The rule restates this protocol's technical report (lean/CREDITS.md); the relative form stands in
this library's Lean text.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowCollRulesChain

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR

/-- A reading of a witness and some mask entries in it. -/
structure MaskFact (W : Type) : Type 1 where
  Kc  : Type
  kc  : W → Kc
  Mk  : Type
  [fin : Fintype Mk]
  [ne  : Nonempty Mk]
  put : Mk → Kc → Kc

attribute [instance] MaskFact.fin MaskFact.ne

/-- the fact that a masked block needs -/
@[reducible] def MaskData.fact
    {Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} {Wi : Type} (D : MaskData R Wi) :
    MaskFact Wi :=
  ⟨D.Kc, D.kc, D.Mk, D.put⟩

namespace Chain
variable {K : Type}

/-- For `(l : Link K A B)`, `(Chain.one l).FreshGiven base f` is
`l.H.Fresh A.rels.rel l.P.bud f.kc f.Mk f.put ∨`
`∃ (Kc' : Type) (kc' : A.W → Kc') (put' : f.Mk → Kc' → Kc'),`
`base ⟨Kc', kc', f.Mk, put'⟩ ∧ l.H.Blind kc' f.kc f.Mk put' f.put`, and, for
`(c : Chain K A B) (l : Link K B C)`, `(c.snoc l).FreshGiven base f` is
`l.H.Fresh B.rels.rel l.P.bud f.kc f.Mk f.put ∨`
`∃ (Kc' : Type) (kc' : B.W → Kc') (put' : f.Mk → Kc' → Kc'),`
`c.FreshGiven base ⟨Kc', kc', f.Mk, put'⟩ ∧ l.H.Blind kc' f.kc f.Mk put' f.put`.
`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. (`Honest.Fresh`, `Honest.seen`,
Ior/KnowCollRulesMask.lean.) `H.Blind kci kco Mk puti puto` (`Honest.Blind`) asks that, for all
input witnesses w and w', every M in `Mk`, every explicit part x of an input statement, all coins c
of the honest prover and every value ρ of the verifier's randomness, if `kci w' = puti M (kci w)`,
then the honest prover's runs from w' and from w, at x, c and ρ, have the same full transcript and
end with the same explicit part of the output statement, and `kco` of the output witness with which
the run from w' ends is `puto M` of `kco` of the output witness with which the run from w ends.
(`Iop.IOR.Honest.Blind`, Ior/KnowCollRulesMask.lean.) `l.H.Fresh` and `l.H.Blind` stand here inside
a definition. -/
def FreshGiven : {A B : Joint K} → Chain K A B → (MaskFact A.W → Prop) → MaskFact B.W → Prop
  | A, _, .one l, base, f =>
      l.H.Fresh A.rels.rel l.P.bud f.kc f.Mk f.put ∨
      ∃ (Kc' : Type) (kc' : A.W → Kc') (put' : f.Mk → Kc' → Kc'),
        base ⟨Kc', kc', f.Mk, put'⟩ ∧ l.H.Blind kc' f.kc f.Mk put' f.put
  | _, _, .snoc (B := B) c l, base, f =>
      l.H.Fresh B.rels.rel l.P.bud f.kc f.Mk f.put ∨
      ∃ (Kc' : Type) (kc' : B.W → Kc') (put' : f.Mk → Kc' → Kc'),
        c.FreshGiven base ⟨Kc', kc', f.Mk, put'⟩ ∧ l.H.Blind kc' f.kc f.Mk put' f.put

/-- Every link is of one of the two kinds, given the facts of "base" at the start. -/
def OkGiven : {A B : Joint K} → Chain K A B → (MaskFact A.W → Prop) → Prop
  | _, _, .one l, base => l.GoodT ∨ ∃ D : MaskData l.R _, l.GoodM D ∧ base D.fact
  | _, _, .snoc c l, base =>
    c.OkGiven base ∧ (l.GoodT ∨ ∃ D : MaskData l.R _, l.GoodM D ∧ c.FreshGiven base D.fact)

variable {A B C : Joint K}

theorem freshGiven_one (l : Link K A B) (base : MaskFact A.W → Prop) (f : MaskFact B.W) :
    (Chain.one l).FreshGiven base f ↔
    (l.H.Fresh A.rels.rel l.P.bud f.kc f.Mk f.put ∨
      ∃ (Kc' : Type) (kc' : A.W → Kc') (put' : f.Mk → Kc' → Kc'),
        base ⟨Kc', kc', f.Mk, put'⟩ ∧ l.H.Blind kc' f.kc f.Mk put' f.put) := by rw [FreshGiven]
theorem freshGiven_snoc (c : Chain K A B) (l : Link K B C)
    (base : MaskFact A.W → Prop) (f : MaskFact C.W) :
    (c.snoc l).FreshGiven base f ↔
    (l.H.Fresh B.rels.rel l.P.bud f.kc f.Mk f.put ∨
      ∃ (Kc' : Type) (kc' : B.W → Kc') (put' : f.Mk → Kc' → Kc'),
        c.FreshGiven base ⟨Kc', kc', f.Mk, put'⟩ ∧ l.H.Blind kc' f.kc f.Mk put' f.put) := by
  rw [FreshGiven]
theorem okGiven_one (l : Link K A B) (base : MaskFact A.W → Prop) :
    (Chain.one l).OkGiven base ↔ (l.GoodT ∨ ∃ D : MaskData l.R A.W, l.GoodM D ∧ base D.fact) := by
  rw [OkGiven]
theorem okGiven_snoc (c : Chain K A B) (l : Link K B C) (base : MaskFact A.W → Prop) :
    (c.snoc l).OkGiven base ↔
    c.OkGiven base ∧ (l.GoodT ∨ ∃ D : MaskData l.R B.W, l.GoodM D ∧ c.FreshGiven base D.fact) := by
  rw [OkGiven]

end Chain
end IOR

namespace Spec
open IOR

/-- With no fact at the start. -/
def freshGiven_none : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (f : MaskFact B.W),
    c.FreshGiven (fun _ => False) f ↔ c.FreshFor f.kc f.Mk f.put

def okGiven_none : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B), c.OkGiven (fun _ => False) ↔ c.Ok

/-- More facts at the start. -/
def freshGiven_mono : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B)
      (base base' : MaskFact A.W → Prop) (f : MaskFact B.W),
    (∀ g, base g → base' g) → c.FreshGiven base f → c.FreshGiven base' f

def okGiven_mono : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (base base' : MaskFact A.W → Prop),
    (∀ g, base g → base' g) → c.OkGiven base → c.OkGiven base'

/-- Two pieces in a row: what is fresh. -/
def freshGiven_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c₀ : Chain K A B) (c : Chain K B C) (base₀ : MaskFact A.W → Prop)
      (base : MaskFact B.W → Prop) (f : MaskFact C.W),
    (∀ g, base g → c₀.FreshGiven base₀ g) → c.FreshGiven base f → (c₀.append c).FreshGiven base₀ f

/-- Two pieces in a row. -/
def okGiven_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c₀ : Chain K A B) (c : Chain K B C)
      (base₀ : MaskFact A.W → Prop) (base : MaskFact B.W → Prop),
    c₀.OkGiven base₀ → (∀ g, base g → c₀.FreshGiven base₀ g) →
    c.OkGiven base → (c₀.append c).OkGiven base₀

/-- Behind a chain that stands by itself. -/
def freshFor_of_given : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c₀ : Chain K A B) (c : Chain K B C)
      (base : MaskFact B.W → Prop) (f : MaskFact C.W),
    (∀ g, base g → c₀.FreshFor g.kc g.Mk g.put) →
    c.FreshGiven base f → (c₀.append c).FreshFor f.kc f.Mk f.put

def ok_of_given : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c₀ : Chain K A B) (c : Chain K B C) (base : MaskFact B.W → Prop),
    c₀.Ok → (∀ g, base g → c₀.FreshFor g.kc g.Mk g.put) → c.OkGiven base → (c₀.append c).Ok

/-- A piece that is OkGiven some base has the bundle without its clause on zero knowledge in every
link. -/
def allB_of_okGiven : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (base : MaskFact A.W → Prop),
    c.OkGiven base → c.AllB

/-- A step without rounds does not look at masks with whose overwriting its honest map commutes. -/
def blind_stepPure : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (f : Xi → Option Xo) (g : ExtMap Ei Eo)
      (m : Xi × Wi → Xo × Wo) (Ki Ko : Type) (kci : Wi → Ki) (kco : Wo → Ko) (Mk : Type)
      (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko),
    (∀ x w w' M, kci w' = puti M (kci w) →
      (m (x, w')).1 = (m (x, w)).1 ∧ kco (m (x, w')).2 = puto M (kco (m (x, w)).2)) →
    (Honest.pure f g m).Blind kci kco Mk puti puto

end Spec

open IOR IOR.Chain

theorem freshGiven_none : Spec.freshGiven_none := by
  intro K A B c
  induction c with
  | one l =>
      intro f
      rw [freshGiven_one, freshFor_one]
      exact ⟨fun h => h.elim id fun ⟨_, _, _, hb, _⟩ => hb.elim, Or.inl⟩
  | snoc c l ih =>
      intro f
      rw [freshGiven_snoc, freshFor_snoc]
      constructor
      · rintro (h | ⟨Kc', kc', put', h, hb⟩)
        · exact Or.inl h
        · exact Or.inr ⟨Kc', kc', put', (ih ⟨Kc', kc', f.Mk, put'⟩).1 h, hb⟩
      · rintro (h | ⟨Kc', kc', put', h, hb⟩)
        · exact Or.inl h
        · exact Or.inr ⟨Kc', kc', put', (ih ⟨Kc', kc', f.Mk, put'⟩).2 h, hb⟩

theorem okGiven_none : Spec.okGiven_none := by
  intro K A B c
  induction c with
  | one l =>
      rw [okGiven_one, ok_one]
      exact ⟨fun h => h.elim id fun ⟨_, _, hb⟩ => hb.elim, Or.inl⟩
  | snoc c l ih =>
      rw [okGiven_snoc, ok_snoc, ih]
      constructor
      · rintro ⟨h1, h2 | ⟨D, h2, h3⟩⟩
        · exact ⟨h1, Or.inl h2⟩
        · exact ⟨h1, Or.inr ⟨D, h2, (freshGiven_none K _ _ c D.fact).1 h3⟩⟩
      · rintro ⟨h1, h2 | ⟨D, h2, h3⟩⟩
        · exact ⟨h1, Or.inl h2⟩
        · exact ⟨h1, Or.inr ⟨D, h2, (freshGiven_none K _ _ c D.fact).2 h3⟩⟩

theorem freshGiven_mono : Spec.freshGiven_mono := by
  intro K A B c base base'
  induction c with
  | one l =>
      intro f hb
      rw [freshGiven_one, freshGiven_one]
      rintro (h | ⟨Kc', kc', put', h, hl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨Kc', kc', put', hb _ h, hl⟩
  | snoc c l ih =>
      intro f hb
      rw [freshGiven_snoc, freshGiven_snoc]
      rintro (h | ⟨Kc', kc', put', h, hl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨Kc', kc', put', ih _ hb h, hl⟩

theorem okGiven_mono : Spec.okGiven_mono := by
  intro K A B c base base'
  induction c with
  | one l =>
      intro hb
      rw [okGiven_one, okGiven_one]
      rintro (h | ⟨D, h, h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨D, h, hb _ h'⟩
  | snoc c l ih =>
      intro hb
      rw [okGiven_snoc, okGiven_snoc]
      rintro ⟨h1, h2 | ⟨D, h2, h3⟩⟩
      · exact ⟨ih hb h1, Or.inl h2⟩
      · exact ⟨ih hb h1, Or.inr ⟨D, h2, freshGiven_mono K _ _ c base base' _ hb h3⟩⟩

theorem freshGiven_append : Spec.freshGiven_append := by
  intro K A B C c₀ c base₀ base
  induction c with
  | one l =>
      intro f hb
      rw [append_one, freshGiven_one, freshGiven_snoc]
      rintro (h | ⟨Kc', kc', put', h, hl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨Kc', kc', put', hb _ h, hl⟩
  | snoc c l ih =>
      intro f hb
      rw [append_snoc, freshGiven_snoc, freshGiven_snoc]
      rintro (h | ⟨Kc', kc', put', h, hl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨Kc', kc', put', ih _ hb h, hl⟩

theorem okGiven_append : Spec.okGiven_append := by
  intro K A B C c₀ c base₀ base
  induction c with
  | one l =>
      intro h0 hb
      rw [append_one, okGiven_one, okGiven_snoc]
      rintro (h | ⟨D, h, h'⟩)
      · exact ⟨h0, Or.inl h⟩
      · exact ⟨h0, Or.inr ⟨D, h, hb _ h'⟩⟩
  | snoc c l ih =>
      intro h0 hb
      rw [append_snoc, okGiven_snoc, okGiven_snoc]
      rintro ⟨h1, h2 | ⟨D, h2, h3⟩⟩
      · exact ⟨ih h0 hb h1, Or.inl h2⟩
      · exact ⟨ih h0 hb h1, Or.inr ⟨D, h2, freshGiven_append K _ _ _ c₀ c base₀ base _ hb h3⟩⟩

theorem freshFor_of_given : Spec.freshFor_of_given := by
  intro K A B C c₀ c base f hb h
  exact (freshGiven_none K _ _ _ f).1
    (freshGiven_append K _ _ _ c₀ c (fun _ => False) base f
      (fun g hg => (freshGiven_none K _ _ c₀ g).2 (hb g hg)) h)

theorem ok_of_given : Spec.ok_of_given := by
  intro K A B C c₀ c base h0 hb h
  exact (okGiven_none K _ _ _).1
    (okGiven_append K _ _ _ c₀ c (fun _ => False) base ((okGiven_none K _ _ c₀).2 h0)
      (fun g hg => (freshGiven_none K _ _ c₀ g).2 (hb g hg)) h)

theorem allB_of_okGiven : Spec.allB_of_okGiven := by
  intro K A B c base
  induction c with
  | one l =>
      rw [okGiven_one, allB_one]
      rintro (h | ⟨D, h, -⟩)
      · exact ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 h).1
      · exact h.base
  | snoc c l ih =>
      rw [okGiven_snoc, allB_snoc]
      rintro ⟨h1, h2 | ⟨D, h2, -⟩⟩
      · exact ⟨ih h1, ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 h2).1⟩
      · exact ⟨ih h1, h2.base⟩

theorem blind_stepPure : Spec.blind_stepPure := by
  intro Xi Xo Ei Eo Wi Wo f g m Ki Ko kci kco Mk puti puto h w w' M x c ρ hk
  exact ⟨rfl, (h x w w' M hk).1, (h x w w' M hk).2⟩

end Iop
