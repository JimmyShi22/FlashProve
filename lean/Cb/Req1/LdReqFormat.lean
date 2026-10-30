-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqFormat.lean: the formats of a preamble along a chain whose joints have the encoded
index at changing places.

Definitions, statements (in `Iop.Spec`) and proofs. No protocol, no code occurs here.
This file is book-keeping for a sequential composition of interactive oracle reductions (a chain:
`IOR.Chain`, Ior/KnowCollRulesChain.lean). It follows one input oracle, the encoded index, through
the composition. A format says where that oracle is among the oracles at each interface (a joint:
`IOR.Joint`).
Here the encoded index is an oracle of any kind E0; the record and the prover encoded index are
values of any types Rc, Pw.

Why: the list of a preamble (`PreListR`, Hiop/RecSubs.lean; the last item: `fitOff`, `fitOn` of
`HypH`, Hiop/RecBuild.lean) asks, beside the bundle of a chain: the verifier does not read the
encoded index; no oracle sent gives away a symbol of it (`PreListR.noTie`; `tie` is by type any map
from ρ and a position to a finite set of positions; it enters `given`, Ior/Honest.lean); it is
copied; the record is handed on; the honest prover hands its prover encoded index on; the budget
bears what follows. Cb/Ld/LdWfPre.lean has the first three link by link for joints whose oracles
are (index, others): `IdxPrefix`, `IdxStep`. A preamble that closes groups passes joints at which
the index is deeper: beside the word of a test that is open.

Main names:
  `IxAt E0 Ex`: where an oracle of the kind E0 is among oracles of the kind Ex: `pos` (its
    positions), `str` (its string).
  `R.IdxLink i₁ i₂`: the reduction R does not read it, ties nothing to it, copies it; a symbol of
    the copy comes from that symbol alone; no other new symbol comes from it (reads and sources are
    the declared sets `extReads`, `srcE`, `srcO`; `IOR.IsLocal`, Ior/Ior.lean, says that they are
    all; `IdxLink` does not ask it).
  `JFmt K E0 Rc Pw A`: the format of a joint: `ix` (where the index is), `rc` (what is read off the
    explicit part: the record), `px` (what is read off a witness: the prover encoded index), `q`
    (which sets of positions of its oracles may be asked for by what follows).
  `l.Fmt φ ψ`: a link has the format: `IdxLink`; rc is handed on (`Passes`); px is handed on by the
    honest prover (`Hands`) (`Passes`, `Hands`: Cb/Ld/LdWfPre.lean, under the conditions in these
    definitions); the link bears what follows (`Bears`, Ior/Bears.lean), from sets of
    positions within ψ.q to sets within φ.q. ("Nothing hidden is withheld" is not asked: a range
    check withholds in secret.) `H.withheld w x` is the union of two sets of verifier randomness
    that the honest side names: `H.Bad`, which takes no argument, and `H.Hid w x`, which takes the
    witness and the explicit statement. `R.Bears bud qi qo`: for every ρ and every set U of
    positions of the new implicit instance for which qo holds, `bud ρ` holds of the positions
    `R.srcO ρ q` for q in U, and qi holds of `R.need ρ U`. (`Bears` is a clause of `Link.Fmt`: in
    `Spec.chain_fmt` a premise and a conclusion.)
  `c.Fmt φ ψ`: every link of a chain has it, with some formats at the joints between.
  `Spec.chain_fmt`: then the chain as one link has it (asked: the bundle without its clause on zero
    knowledge, link by link, `c.AllB`, for completeness).
  `Spec.idxLink_seq`, `Spec.fmt_append`: if R₁ has `IdxLink` from i₁ to i₂ and R₂ from i₂ to i₃,
    `R₁.seq R₂` has it from i₁ to i₃; likewise `Fmt` of `c.append c'`.

Limits: this file does not say that any link has a format. It says nothing on relations. A bound to
that, at least: the joints' relations stand in `Link.Fmt.hands` (`A.rels.rel`) and, through the
premise `c.AllB`, in `Spec.chain_fmt`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfPre
import Ior.KnowCollRulesChain
import Ior.BearsProofs

set_option autoImplicit false

namespace Iop
open Prob

namespace IOR
variable {X₁ X₂ X₃ : Type} {E0 E₁ E₂ E₃ Ex F : ExtSpec}

/-- Where an oracle of the kind E0 is among oracles of the kind Ex. -/
structure IxAt (E0 Ex : ExtSpec) where
  pos : E0.Pos → Ex.Pos
  str : Ex.Str → E0.Str

/-- the oracle is the left part -/
def IxAt.left (E0 F : ExtSpec) : IxAt E0 (E0.prod F) := ⟨Sum.inl, Prod.fst⟩
/-- the oracle is, where i says, in the left part of a pair; `IxAt.inr`: in the right part -/
def IxAt.inl (i : IxAt E0 Ex) (F : ExtSpec) : IxAt E0 (Ex.prod F) :=
  ⟨fun p => Sum.inl (i.pos p), fun y => i.str y.1⟩
def IxAt.inr (i : IxAt E0 Ex) (F : ExtSpec) : IxAt E0 (F.prod Ex) :=
  ⟨fun p => Sum.inr (i.pos p), fun y => i.str y.2⟩

/-- The reduction leaves that oracle alone. -/
structure IdxLink (R : IOR X₁ E₁ X₂ E₂) (i₁ : IxAt E0 E₁) (i₂ : IxAt E0 E₂) : Prop where
  noIdx  : ∀ ρ p, i₁.pos p ∉ R.extReads ρ
  noTie  : ∀ ρ p q, i₁.pos q ∉ R.tie ρ p
  copy   : ∀ y τ, i₂.str (R.imp y τ) = i₁.str y
  srcIdx : ∀ ρ p, R.srcE ρ (i₂.pos p) = {i₁.pos p} ∧ R.srcO ρ (i₂.pos p) = ∅
  srcAux : ∀ ρ q, (∀ p, q ≠ i₂.pos p) → ∀ p, i₁.pos p ∉ R.srcE ρ q

/-- The format of a joint. -/
structure JFmt (K : Type) (E0 : ExtSpec) (Rc Pw : Type) (A : Joint K) where
  ix : IxAt E0 A.E
  rc : A.X → Rc
  px : A.W → Pw
  q  : Finset A.E.Pos → Prop

variable {K Rc Pw : Type}

/-- A link has the format. -/
structure Link.Fmt {A B : Joint K} (l : Link K A B)
    (φ : JFmt K E0 Rc Pw A) (ψ : JFmt K E0 Rc Pw B) : Prop where
  idx   : l.R.IdxLink φ.ix ψ.ix
  pass  : l.R.Passes φ.rc ψ.rc
  hands : l.H.Hands A.rels.rel φ.px ψ.px
  bears : l.R.Bears l.P.bud φ.q ψ.q

/-- Every link of a chain has the format, with some formats at the joints between. -/
def Chain.Fmt : {A B : Joint K} → Chain K A B → JFmt K E0 Rc Pw A → JFmt K E0 Rc Pw B → Prop
  | _, _, .one l, φ, ψ => l.Fmt φ ψ
  | _, _, .snoc (B := B) c l, φ, χ => ∃ ψ : JFmt K E0 Rc Pw B, c.Fmt φ ψ ∧ l.Fmt ψ χ

theorem Chain.fmt_one {A B : Joint K} (l : Link K A B)
    (φ : JFmt K E0 Rc Pw A) (ψ : JFmt K E0 Rc Pw B) :
    (Chain.one l).Fmt φ ψ ↔ l.Fmt φ ψ := by rw [Chain.Fmt]
theorem Chain.fmt_snoc {A B C : Joint K} (c : Chain K A B) (l : Link K B C)
    (φ : JFmt K E0 Rc Pw A) (χ : JFmt K E0 Rc Pw C) :
    (c.snoc l).Fmt φ χ ↔ ∃ ψ : JFmt K E0 Rc Pw B, c.Fmt φ ψ ∧ l.Fmt ψ χ := by rw [Chain.Fmt]

end IOR

namespace Spec
open IOR

/-- Two in a row. -/
def idxLink_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E0 E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (i₁ : IxAt E0 E₁) (i₂ : IxAt E0 E₂) (i₃ : IxAt E0 E₃),
    R₁.IdxLink i₁ i₂ → R₂.IdxLink i₂ i₃ → (R₁.seq R₂).IdxLink i₁ i₃

/-- At "left" on both sides: a step of Cb/Ld/LdWfPre.lean. -/
def idxLink_step : Prop :=
  ∀ (X₁ X₂ : Type) (E0 Ea Eb : ExtSpec) (R : IOR X₁ (E0.prod Ea) X₂ (E0.prod Eb)),
    R.IdxLink (IxAt.left E0 Ea) (IxAt.left E0 Eb) ↔ R.IdxStep

/-- States: if `c.AllB` and `c.Fmt φ ψ`, the chain as one link (`c.link d`) has the format. -/
def chain_fmt : Prop :=
  ∀ (K : Type) (E0 : ExtSpec) (Rc Pw : Type) (A B : Joint K) (c : Chain K A B) (d : A.W)
      (φ : JFmt K E0 Rc Pw A) (ψ : JFmt K E0 Rc Pw B),
    c.AllB → c.Fmt φ ψ → (c.link d).Fmt φ ψ

/-- Two chains in a row. -/
def fmt_append : Prop :=
  ∀ (K : Type) (E0 : ExtSpec) (Rc Pw : Type) (A B C : Joint K) (c : Chain K A B) (c' : Chain K B C)
      (φ : JFmt K E0 Rc Pw A) (ψ : JFmt K E0 Rc Pw B) (χ : JFmt K E0 Rc Pw C),
    c.Fmt φ ψ → c'.Fmt ψ χ → (c.append c').Fmt φ χ

end Spec

open IOR IOR.Chain

theorem idxLink_seq : Spec.idxLink_seq := by
  classical
  intro X₁ X₂ X₃ E0 E₁ E₂ E₃ F₁ F₂ i₁ i₂ i₃ h₁ h₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ρ p hp
    rcases (mem_seq_extReads F₁ F₂ ρ _).1 hp with h | ⟨q, hq, hpq⟩
    · exact h₁.noIdx _ _ h
    · by_cases hx : ∃ p', q = i₂.pos p'
      · obtain ⟨p', rfl⟩ := hx
        exact h₂.noIdx _ _ hq
      · exact h₁.srcAux _ q (fun p' hp' => hx ⟨p', hp'⟩) _ hpq
  · intro ρ
    refine OPos.forall_append (s := F₁.shape) (t := F₂.shape)
      (P := fun p => ∀ q, i₁.pos q ∉ (F₁.seq F₂).tie ρ p) (fun p q hq => ?_) (fun p u hu => ?_)
    · have hq : i₁.pos q ∈ (F₁.seq F₂).tie ρ (OPos.left p) := hq
      rw [seq_tie_left] at hq
      exact h₁.noTie _ _ _ hq
    · obtain ⟨q, hq, h⟩ := (mem_seq_tie_right F₁ F₂ ρ p _).1 hu
      by_cases hx : ∃ p', q = i₂.pos p'
      · obtain ⟨p', rfl⟩ := hx
        exact h₂.noTie _ _ _ hq
      · rcases h with h | ⟨p₁, _, h⟩
        · exact h₁.srcAux _ q (fun p' hp' => hx ⟨p', hp'⟩) _ h
        · exact h₁.noTie _ _ _ h
  · intro y τ
    rw [seq_imp, h₂.copy, h₁.copy]
  · intro ρ p
    refine ⟨Finset.ext fun u => ?_, Finset.eq_empty_of_forall_notMem ?_⟩
    · rw [mem_seq_srcE]
      constructor
      · rintro ⟨q, hq, hu⟩
        rw [(h₂.srcIdx _ p).1, Finset.mem_singleton] at hq
        subst hq
        rwa [(h₁.srcIdx _ p).1] at hu
      · intro hu
        exact ⟨i₂.pos p,
          by rw [(h₂.srcIdx _ p).1]; exact Finset.mem_singleton_self _,
          by rwa [(h₁.srcIdx _ p).1]⟩
    · refine OPos.forall_append (s := F₁.shape) (t := F₂.shape) (fun u hu => ?_) (fun u hu => ?_)
      · obtain ⟨q, hq, hu⟩ := (left_mem_seq_srcO F₁ F₂ ρ _ u).1 hu
        rw [(h₂.srcIdx _ p).1, Finset.mem_singleton] at hq
        subst hq
        rw [(h₁.srcIdx _ p).2] at hu
        exact Finset.notMem_empty _ hu
      · have hu := (right_mem_seq_srcO F₁ F₂ ρ _ u).1 hu
        rw [(h₂.srcIdx _ p).2] at hu
        exact Finset.notMem_empty _ hu
  · intro ρ q hq p hp
    obtain ⟨q', hq', hu⟩ := (mem_seq_srcE F₁ F₂ ρ _ _).1 hp
    by_cases hx : ∃ p', q' = i₂.pos p'
    · obtain ⟨p', rfl⟩ := hx
      exact h₂.srcAux _ q hq _ hq'
    · exact h₁.srcAux _ q' (fun p' hp' => hx ⟨p', hp'⟩) _ hu

theorem idxLink_step : Spec.idxLink_step := by
  intro X₁ X₂ E0 Ea Eb R
  constructor
  · intro h
    exact ⟨h.noIdx, h.noTie, h.copy, h.srcIdx,
      fun ρ q p hp => h.srcAux ρ (Sum.inr q) (fun p' hp' => by cases hp') p hp⟩
  · intro h
    refine ⟨h.noIdx, h.noTie, h.copy, h.srcIdx, fun ρ q hq p hp => ?_⟩
    cases q with
    | inl q => exact hq q rfl
    | inr q => exact h.srcAux ρ q p hp

theorem chain_fmt : Spec.chain_fmt := by
  intro K E0 Rc Pw A B c d φ
  induction c with
  | one l =>
      intro ψ _ h
      rw [link_one]
      exact (fmt_one l φ ψ).1 h
  | snoc c l ih =>
      intro χ hB h
      obtain ⟨ψ, h1, h2⟩ := (fmt_snoc c l φ χ).1 h
      have g := ih ψ ((allB_snoc c l).1 hB).1 h1
      have gB := chain_goodB K _ _ c d ((allB_snoc c l).1 hB).1
      rw [link_snoc]
      exact ⟨idxLink_seq _ _ _ _ _ _ _ _ _ _ _ _ g.idx h2.idx,
        g.pass.seq h2.pass,
        g.hands.seq gB.acc h2.hands,
        bears_seq _ _ _ _ _ _ _ _ _ _ _ _ _ g.bears h2.bears⟩

theorem fmt_append : Spec.fmt_append := by
  intro K E0 Rc Pw A B C c c' φ ψ
  induction c' with
  | one l =>
      intro χ h h'
      rw [append_one]
      exact (fmt_snoc c l φ χ).2 ⟨ψ, h, (fmt_one l ψ χ).1 h'⟩
  | snoc c' l ih =>
      intro χ h h'
      obtain ⟨ψ', h1, h2⟩ := (fmt_snoc c' l ψ χ).1 h'
      rw [append_snoc]
      exact (fmt_snoc _ l φ χ).2 ⟨ψ', ih ψ' h h1, h2⟩

end Iop
