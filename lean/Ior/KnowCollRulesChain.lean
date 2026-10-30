-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollRulesChain.lean: many reductions in a row: chains of links of different types, their
bundle, their numbers as sums, and the rule for masks sent in advance, iterated.

The matter is sequential composition of interactive oracle reductions (IORs, Ior/Ior.lean), for any
number of them: the properties and numbers of the whole from those of the parts.
Definitions, statements and proofs. No protocol, no code occurs here.
A bundle (here `GoodB`, `GoodM`, Ior/Masked.lean; `GoodT`, Ior/KnowCollGood.lean) is one record of
properties of an IOR between two joints, which the rules for chains carry along.
The rules for two in a row (`goodB_seq`, `goodT_seq`, `goodT_seq_masked`, `fresh_snd`, `fresh_seq`)
are iterated here.

Main names:
  `Joint K`: a joint of a chain with its types: explicit part, kind of oracles, witnesses, and what
    the chain says there (`Rels`).
  `Link K A B`: a link. `l.seq l' d`: two in a row (d: the extractor's value where the first
    verifier rejects).
  `Chain K A B`: the brackets are to the left: `c.link d` is ((first; second); third) .. A
    sub-protocol is a chain; two chains are put in a row by `c.append c'`, which gives the chain of
    all links, again bracketed to the left: nothing is re-bracketed by a proof.
The bundle:
  `c.AllB`, `c.AllT`: every link is `GoodB`, `GoodT`. `Spec.chain_goodB`, `Spec.chain_goodT`: then
    so is `c.link d`.
The numbers:
  `c.nAll`, `c.nVer` (the two numbers of rounds, Ior/KnowCollRulesRounds.lean), `c.pBad`, `c.pHid`
    (the numbers for the public and for the hidden withheld set; by definition sums of the links'
    numbers `Nums.pBad`, `Nums.pHid`, Ior/Chain.lean): sums over the links (`Spec.chain_nums`). The
    errors are in a row (by definition: `Nums.seq`).
Masks sent in advance (Ior/KnowCollRulesMask.lean), without positions:
  `c.FreshFor kc Mk put` (Mk non-empty): by recursion on the chain: the last link is Fresh on all
    its inputs (it sends the masks) (exactly: the doc comment of `Chain.FreshFor`, below); or the
    last link is Blind, from some reading kc' with put' to kc with put, and the chain before it is
    FreshFor kc', put'.
  `Spec.chain_fresh`, under `c.AllB`: then `c.link d` is Fresh, on the chain's input relation, at
    its budget.
  `c.Ok`: the first link is `GoodT`; every later link is `GoodT`, or it is `GoodM D` and the chain
    before it is FreshFor D's reading and masks.
  `Spec.chain_ok`: the flat statement: a chain each of whose links is of one of the two kinds, with
    these conditions, is `GoodT`: in particular honest-verifier zero knowledge in the exact form,
    with the sum of the links' probabilities as its error (`GoodT.exact`: `Honest.Exact`,
    Ior/Honest.lean).

Limits: the nested budget of a chain is not discharged here. The first link cannot be a masked
block (`c.Ok` asks `l.GoodT` of it; that a masked block is not `GoodT`: under the premises of
`Spec.masked_not_exact`, Ior/Masked.lean). This file says nothing on running times.
Terms: lean/GLOSSARY.md: budget, bundle, chain, explicit part, fresh, IOR, joint, link, mask,
numbers (of a reduction), withheld, zero knowledge.
-/
import Ior.KnowCollRulesMaskProofs
import Ior.KnowCollRulesRounds
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR

/-- A joint of a chain, with its types. -/
structure Joint (K : Type) : Type 1 where
  X : Type
  E : ExtSpec
  W : Type
  rels : Rels K X E W

/-- A link: a reduction with its honest side, extractor and numbers. -/
structure Link (K : Type) (A B : Joint K) : Type 1 where
  R : IOR A.X A.E B.X B.E
  H : R.Honest A.W B.W
  ext : A.X × A.E.Str → Tr R.shape → B.W → A.W
  P : Nums K R

namespace Link
variable {K : Type} {A B C : Joint K}

def GoodB (l : Link K A B) : Prop := IOR.GoodB l.R l.H A.rels B.rels l.ext l.P
def GoodT (l : Link K A B) : Prop := IOR.GoodT l.R l.H A.rels B.rels l.ext l.P
def GoodM (l : Link K A B) (D : MaskData l.R A.W) : Prop :=
  IOR.GoodM l.R l.H A.rels B.rels l.ext l.P D

/-- Two links in a row. -/
def seq (l : Link K A B) (l' : Link K B C) (d : A.W) : Link K A C where
  R := l.R.seq l'.R
  H := l.H.seq l'.H
  ext := IOR.extSeq l.R l'.R l.ext l'.ext d
  P := l.P.seq l'.P

end Link

/-- A chain of links, bracketed to the left. -/
inductive Chain (K : Type) : Joint K → Joint K → Type 1
  | one {A B : Joint K} (l : Link K A B) : Chain K A B
  | snoc {A B C : Joint K} (c : Chain K A B) (l : Link K B C) : Chain K A C

namespace Chain
variable {K : Type}

/-- The chain as one link. -/
def link : {A B : Joint K} → Chain K A B → A.W → Link K A B
  | _, _, .one l, _ => l
  | _, _, .snoc c l, d => (c.link d).seq l d

/-- Two chains in a row: the chain of all links. -/
def append : {A B C : Joint K} → Chain K A B → Chain K B C → Chain K A C
  | _, _, _, c, .one l => .snoc c l
  | _, _, _, c, .snoc c' l => .snoc (c.append c') l

/-- The chain of the links b 0 .. b n. -/
def fam (J : ℕ → Joint K) (b : ∀ l, Link K (J l) (J (l + 1))) : (n : ℕ) → Chain K (J 0) (J (n + 1))
  | 0 => .one (b 0)
  | n + 1 => .snoc (fam J b n) (b (n + 1))

def AllB : {A B : Joint K} → Chain K A B → Prop
  | _, _, .one l => l.GoodB
  | _, _, .snoc c l => c.AllB ∧ l.GoodB

def AllT : {A B : Joint K} → Chain K A B → Prop
  | _, _, .one l => l.GoodT
  | _, _, .snoc c l => c.AllT ∧ l.GoodT

def nAll : {A B : Joint K} → Chain K A B → ℕ
  | _, _, .one l => l.R.shape.nAll
  | _, _, .snoc c l => c.nAll + l.R.shape.nAll

def nVer : {A B : Joint K} → Chain K A B → ℕ
  | _, _, .one l => l.R.shape.nVer
  | _, _, .snoc c l => c.nVer + l.R.shape.nVer

def pBad : {A B : Joint K} → Chain K A B → ℝ≥0∞
  | _, _, .one l => l.P.pBad
  | _, _, .snoc c l => c.pBad + l.P.pBad

def pHid : {A B : Joint K} → Chain K A B → ℝ≥0∞
  | _, _, .one l => l.P.pHid
  | _, _, .snoc c l => c.pHid + l.P.pHid

/-- `c.FreshFor kc Mk put`, by recursion on the chain. One link l:
`l.H.Fresh A.rels.rel l.P.bud kc Mk put`. A chain c, then a link l, B the joint
between them:
`l.H.Fresh B.rels.rel l.P.bud kc Mk put ∨`
`∃ (Kc' : Type) (kc' : B.W → Kc') (put' : Mk → Kc' → Kc'),`
`c.FreshFor kc' Mk put' ∧ l.H.Blind kc' kc Mk put' put`.
`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M.
`H.Blind kci kco Mk puti puto` (`Honest.Blind`) asks that, for all input witnesses w and w', every
M in `Mk`, every explicit part x of an input statement, all coins c of the honest prover and every
value ρ of the verifier's randomness, if `kci w' = puti M (kci w)`, then the honest prover's runs
from w' and from w, at x, c and ρ, have the same full transcript and end with the same explicit
part of the output statement, and `kco` of the output witness with which the run from w' ends is
`puto M` of `kco` of the output witness with which the run from w ends. In this definition `Fresh`
and `Blind` stand as clauses: neither as a premise nor as a conclusion of a statement.
(`Spec.chain_fresh`: see its statement below, and its row in the head.) -/
def FreshFor :
    {A B : Joint K} → Chain K A B → {Kc : Type} → (B.W → Kc) → (Mk : Type) → [Fintype Mk] →
    [Nonempty Mk] → (Mk → Kc → Kc) → Prop
  | A, _, .one l, _, kc, Mk, _, _, put => l.H.Fresh A.rels.rel l.P.bud kc Mk put
  | _, _, .snoc (B := B) c l, _, kc, Mk, _, _, put =>
      l.H.Fresh B.rels.rel l.P.bud kc Mk put ∨
      ∃ (Kc' : Type) (kc' : B.W → Kc') (put' : Mk → Kc' → Kc'),
        c.FreshFor kc' Mk put' ∧ l.H.Blind kc' kc Mk put' put

/-- Every link is of one of the two kinds, and a masked link's masks are fresh after the chain
before it. (fresh after the chain: `Chain.FreshFor`) -/
def Ok : {A B : Joint K} → Chain K A B → Prop
  | _, _, .one l => l.GoodT
  | _, _, .snoc c l =>
    c.Ok ∧ (l.GoodT ∨ ∃ D : MaskData l.R _, l.GoodM D ∧ c.FreshFor D.kc D.Mk D.put)

end Chain
end IOR

namespace Spec
open IOR

def chain_goodB : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W), c.AllB → (c.link d).GoodB

def chain_goodT : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W), c.AllT → (c.link d).GoodT

def all_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : Chain K A B) (c' : Chain K B C),
    ((c.append c').AllB ↔ c.AllB ∧ c'.AllB) ∧ ((c.append c').AllT ↔ c.AllT ∧ c'.AllT)

/-- States: the numbers `nAll`, `nVer`, `pBad`, `pHid` of a chain as one link are the sums over its
links. -/
def chain_nums : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W),
    (c.link d).R.shape.nAll = c.nAll ∧
    (c.link d).R.shape.nVer = c.nVer ∧
    (c.link d).P.pBad = c.pBad ∧
    (c.link d).P.pHid = c.pHid

def nums_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : Chain K A B) (c' : Chain K B C),
    (c.append c').nAll = c.nAll + c'.nAll ∧
    (c.append c').nVer = c.nVer + c'.nVer ∧
    (c.append c').pBad = c.pBad + c'.pBad ∧
    (c.append c').pHid = c.pHid + c'.pHid

/-- States: a chain with the whole bundle in every link is a chain of the two kinds; a chain of the
two kinds has all of it but the clause on zero knowledge in every link. -/
def ok_of_allT : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B), (c.AllT → c.Ok) ∧ (c.Ok → c.AllB)

def chain_fresh : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W) (Kc : Type) (kc : B.W → Kc) (Mk : Type)
      [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc),
    c.AllB → c.FreshFor kc Mk put → (c.link d).H.Fresh A.rels.rel (c.link d).P.bud kc Mk put

/-- The flat statement: see the head. -/
def chain_ok : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W), c.Ok → (c.link d).GoodT

end Spec

open IOR

namespace IOR.Chain
variable {K : Type} {A B C : Joint K}

theorem link_one (l : Link K A B) (d : A.W) : (Chain.one l).link d = l := by rw [link]
theorem link_snoc (c : Chain K A B) (l : Link K B C) (d : A.W) :
    (c.snoc l).link d = (c.link d).seq l d := by rw [link]
theorem append_one (c : Chain K A B) (l : Link K B C) : c.append (.one l) = c.snoc l := by
  rw [append]
theorem append_snoc {D : Joint K} (c : Chain K A B) (c' : Chain K B C) (l : Link K C D) :
    c.append (c'.snoc l) = (c.append c').snoc l := by rw [append]
theorem allB_one (l : Link K A B) : (Chain.one l).AllB ↔ l.GoodB := by rw [AllB]
theorem allB_snoc (c : Chain K A B) (l : Link K B C) : (c.snoc l).AllB ↔ c.AllB ∧ l.GoodB := by
  rw [AllB]
theorem allT_one (l : Link K A B) : (Chain.one l).AllT ↔ l.GoodT := by rw [AllT]
theorem allT_snoc (c : Chain K A B) (l : Link K B C) : (c.snoc l).AllT ↔ c.AllT ∧ l.GoodT := by
  rw [AllT]
theorem nAll_one (l : Link K A B) : (Chain.one l).nAll = l.R.shape.nAll := by rw [nAll]
theorem nAll_snoc (c : Chain K A B) (l : Link K B C) :
    (c.snoc l).nAll = c.nAll + l.R.shape.nAll := by rw [nAll]
theorem nVer_one (l : Link K A B) : (Chain.one l).nVer = l.R.shape.nVer := by rw [nVer]
theorem nVer_snoc (c : Chain K A B) (l : Link K B C) :
    (c.snoc l).nVer = c.nVer + l.R.shape.nVer := by rw [nVer]
theorem pBad_one (l : Link K A B) : (Chain.one l).pBad = l.P.pBad := by rw [pBad]
theorem pBad_snoc (c : Chain K A B) (l : Link K B C) : (c.snoc l).pBad = c.pBad + l.P.pBad := by
  rw [pBad]
theorem pHid_one (l : Link K A B) : (Chain.one l).pHid = l.P.pHid := by rw [pHid]
theorem pHid_snoc (c : Chain K A B) (l : Link K B C) : (c.snoc l).pHid = c.pHid + l.P.pHid := by
  rw [pHid]
theorem freshFor_one (l : Link K A B) {Kc : Type} (kc : B.W → Kc) (Mk : Type) [Fintype Mk]
    [Nonempty Mk] (put : Mk → Kc → Kc) :
    (Chain.one l).FreshFor kc Mk put ↔ l.H.Fresh A.rels.rel l.P.bud kc Mk put := by rw [FreshFor]
theorem freshFor_snoc (c : Chain K A B) (l : Link K B C) {Kc : Type} (kc : C.W → Kc) (Mk : Type)
    [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc) :
    (c.snoc l).FreshFor kc Mk put ↔
    (l.H.Fresh B.rels.rel l.P.bud kc Mk put ∨
      ∃ (Kc' : Type) (kc' : B.W → Kc') (put' : Mk → Kc' → Kc'),
        c.FreshFor kc' Mk put' ∧ l.H.Blind kc' kc Mk put' put) := by
  rw [FreshFor]
theorem ok_one (l : Link K A B) : (Chain.one l).Ok ↔ l.GoodT := by rw [Ok]
theorem ok_snoc (c : Chain K A B) (l : Link K B C) :
    (c.snoc l).Ok ↔
    c.Ok ∧ (l.GoodT ∨ ∃ D : MaskData l.R B.W, l.GoodM D ∧ c.FreshFor D.kc D.Mk D.put) := by rw [Ok]

end IOR.Chain

open IOR.Chain

theorem chain_goodB : Spec.chain_goodB := by
  intro K A B c d
  induction c with
  | one l =>
      intro h
      rw [link_one]
      exact (allB_one l).1 h
  | snoc c l ih =>
      intro h
      rw [link_snoc]
      exact goodB_seq K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d _ _
        (ih ((allB_snoc c l).1 h).1) ((allB_snoc c l).1 h).2

theorem chain_goodT : Spec.chain_goodT := by
  intro K A B c d
  induction c with
  | one l =>
      intro h
      rw [link_one]
      exact (allT_one l).1 h
  | snoc c l ih =>
      intro h
      rw [link_snoc]
      exact goodT_seq K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d _ _
        (ih ((allT_snoc c l).1 h).1) ((allT_snoc c l).1 h).2

theorem all_append : Spec.all_append := by
  intro K A B C c c'
  induction c' with
  | one l =>
      rw [append_one, allB_snoc, allT_snoc, allB_one, allT_one]
      exact ⟨Iff.rfl, Iff.rfl⟩
  | snoc c' l ih =>
      rw [append_snoc, allB_snoc, allT_snoc, allB_snoc, allT_snoc, ih.1, ih.2]
      exact ⟨and_assoc, and_assoc⟩

theorem chain_nums : Spec.chain_nums := by
  intro K A B c d
  induction c with
  | one l =>
      rw [link_one, nAll_one, nVer_one, pBad_one, pHid_one]
      exact ⟨rfl, rfl, rfl, rfl⟩
  | snoc c l ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have r := rounds_app (c.link d).R.shape l.R.shape
      rw [link_snoc, nAll_snoc, nVer_snoc, pBad_snoc, pHid_snoc, ← h1, ← h2, ← h3, ← h4]
      exact ⟨r.1, r.2, rfl, rfl⟩

theorem nums_append : Spec.nums_append := by
  intro K A B C c c'
  induction c' with
  | one l =>
      rw [append_one, nAll_snoc, nVer_snoc, pBad_snoc, pHid_snoc, nAll_one,
        nVer_one, pBad_one, pHid_one]
      exact ⟨rfl, rfl, rfl, rfl⟩
  | snoc c' l ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      rw [append_snoc, nAll_snoc, nVer_snoc, pBad_snoc, pHid_snoc, nAll_snoc, nVer_snoc, pBad_snoc,
        pHid_snoc, h1, h2, h3, h4]
      exact ⟨Nat.add_assoc _ _ _, Nat.add_assoc _ _ _, add_assoc _ _ _, add_assoc _ _ _⟩

theorem ok_of_allT : Spec.ok_of_allT := by
  intro K A B c
  induction c with
  | one l =>
      rw [allT_one, ok_one, allB_one]
      exact ⟨fun h => h, fun h => ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 h).1⟩
  | snoc c l ih =>
      rw [allT_snoc, ok_snoc, allB_snoc]
      refine ⟨fun h => ⟨ih.1 h.1, Or.inl h.2⟩, fun h => ⟨ih.2 h.1, ?_⟩⟩
      rcases h.2 with h2 | ⟨D, h2, -⟩
      · exact ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 h2).1
      · exact h2.base

theorem chain_fresh : Spec.chain_fresh := by
  intro K A B c d
  induction c with
  | one l =>
      intro Kc kc Mk _ _ put _ h
      rw [link_one]
      exact (freshFor_one l kc Mk put).1 h
  | snoc c l ih =>
      intro Kc kc Mk _ _ put hB hF
      have gB := chain_goodB K _ _ c d ((allB_snoc c l).1 hB).1
      rw [link_snoc]
      rcases (freshFor_snoc c l kc Mk put).1 hF with hF | ⟨Kc', kc', put', hF, hBl⟩
      · exact fresh_snd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (c.link d).P.bud
          l.P.bud Kc kc Mk put gB.acc hF
      · exact fresh_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (c.link d).P.bud l.P.bud Kc' Kc kc' kc Mk put'
          put (ih Kc' kc' Mk put' ((allB_snoc c l).1 hB).1 hF) hBl

theorem chain_ok : Spec.chain_ok := by
  intro K A B c d
  induction c with
  | one l =>
      intro h
      rw [link_one]
      exact (ok_one l).1 h
  | snoc c l ih =>
      intro h
      obtain ⟨h1, h2⟩ := (ok_snoc c l).1 h
      rw [link_snoc]
      rcases h2 with h2 | ⟨D, h2, hF⟩
      · exact goodT_seq K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d _ _ (ih h1) h2
      · exact goodT_seq_masked K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d _ _ D (ih h1)
          (chain_fresh K _ _ c d _ D.kc D.Mk D.put ((ok_of_allT K _ _ c).2 h1) hF) h2

end Iop
