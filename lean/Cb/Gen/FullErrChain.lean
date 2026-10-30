-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/FullErrChain.lean: links and chains with their round errors overwritten by the full list
(`Err.full`, Cb/Gen/FullErr.lean): the analogue of that file for many reductions in a row (`Link`,
`Chain`, Ior/KnowCollRulesChain.lean).

In standard terms: the same replacement of the errors of round-by-round knowledge soundness by the
trivial ones (probability 1 in every round), for reductions composed in sequence.

Definitions, statements (in `Cb.Spec`) and proofs. Framework only: no protocol occurs. Nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
A link is a reduction with its honest side, extractor and numbers; a chain is links in a row.
`GoodT` is in Ior/KnowCollGood.lean, `GoodB` and `GoodM` in Ior/Masked.lean, `OkGiven` and
`FreshGiven` in Cb/Req1/LdSegFresh.lean, `Fmt` in Cb/Req1/LdReqFormat.lean. Each of the first three
has round-by-round knowledge soundness at the link's errors as one clause, know (`GoodM` inside its
field base); no other clause of them reads the errors.

Main names:
  `Spec.linkFull_seq`: (l.seq l' d).full = (l.full.seq l'.full d).full, by unfolding: "one after the
    other" reads the two error lists in the field err alone.
  `Spec.chainFull_link`: (c.full.link d).full = (c.link d).full: the chain as one link, but for its
    errors, is the overwritten chain's.
  `Spec.chainFull_all`: c.AllB | AllT | Ok → the same of `c.full`; c.OkGiven base →
    c.full.OkGiven base.
  `Spec.chainFull_blind`: what does not read the errors: for a finite non-empty Mk,
    c.full.FreshFor kc Mk put ↔ c.FreshFor kc Mk put;
    c.full.FreshGiven base f ↔ c.FreshGiven base f; c.full.Fmt φ ψ ↔ c.Fmt φ ψ.
    `Spec.linkFull_fmt`: l.full.Fmt φ ψ ↔ l.Fmt φ ψ.

Limits: c.full.Ok says of the chain c: every link has its point structure, is local, its honest
prover is accepted outside the two withheld sets, the two chances are below pBad, pHid, its honest
views are exact within the budget (`Honest.ExactWith`, Ior/Honest.lean: `ρ ∉ H.Hid w x →`) or it is
a masked block whose masks are fresh (and the fields `onOut`, `keeps`, `GoodM.mm`, `GoodM.claim`):
and nothing on the chance of a cheating prover in a link that has a round (a link without a round
keeps its plain implication). This file does not say that a chain has c.full.Ok without c.Ok: that
is for each kind of link. It says nothing on a protocol. It says nothing on numerals.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.FullErr
import Cb.Req1.LdSegFresh
import Cb.Req1.LdReqFormat

set_option autoImplicit false

namespace Iop
namespace IOR
variable {K : Type}

/-- the link with the full list for its errors; all else is its own -/
def Link.full {A B : Joint K} (l : Link K A B) : Link K A B := { l with P := l.P.full }

/-- the chain with every link's errors overwritten by the full list -/
def Chain.full : {A B : Joint K} → Chain K A B → Chain K A B
  | _, _, .one l => .one l.full
  | _, _, .snoc c l => .snoc c.full l.full

end IOR
end Iop

namespace Cb
open Iop Prob Iop.IOR Iop.IOR.Chain

namespace Spec

def linkFull_full : Prop := ∀ (K : Type) (A B : Joint K) (l : Link K A B), l.full.full = l.full

def linkFull_seq : Prop :=
  ∀ (K : Type) (A B C : Joint K) (l : Link K A B) (l' : Link K B C) (d : A.W),
    (l.seq l' d).full = (l.full.seq l'.full d).full

def chainFull_full : Prop := ∀ (K : Type) (A B : Joint K) (c : Chain K A B), c.full.full = c.full

def chainFull_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : Chain K A B) (c' : Chain K B C),
    (c.append c').full = c.full.append c'.full

/-- The chain as one link, but for its errors. -/
def chainFull_link : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W), (c.full.link d).full = (c.link d).full

def linkFull_good : Prop :=
  ∀ (K : Type) (A B : Joint K) (l : Link K A B),
    (l.GoodB → l.full.GoodB) ∧
    (l.GoodT → l.full.GoodT) ∧
    ∀ D : MaskData l.R A.W, l.GoodM D → l.full.GoodM D

def chainFull_all : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B),
    (c.AllB → c.full.AllB) ∧
    (c.AllT → c.full.AllT) ∧
    (c.Ok → c.full.Ok) ∧
    ∀ base : MaskFact A.W → Prop, c.OkGiven base → c.full.OkGiven base

/-- What does not read the errors. -/
def chainFull_blind : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B),
    (∀ (Kc : Type) (kc : B.W → Kc) (Mk : Type) [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc),
      c.full.FreshFor kc Mk put ↔ c.FreshFor kc Mk put) ∧
    (∀ (base : MaskFact A.W → Prop) (f : MaskFact B.W),
      c.full.FreshGiven base f ↔ c.FreshGiven base f) ∧
    ∀ (E0 : ExtSpec) (Rc Pw : Type) (φ : JFmt K E0 Rc Pw A) (ψ : JFmt K E0 Rc Pw B),
      c.full.Fmt φ ψ ↔ c.Fmt φ ψ

def linkFull_fmt : Prop :=
  ∀ (K : Type) (A B : Joint K) (l : Link K A B) (E0 : ExtSpec) (Rc Pw : Type)
      (φ : JFmt K E0 Rc Pw A) (ψ : JFmt K E0 Rc Pw B),
    l.full.Fmt φ ψ ↔ l.Fmt φ ψ

end Spec

section
variable {K : Type} {A B C : Joint K}

theorem full_one (l : Link K A B) : (Chain.one l).full = .one l.full := by rw [Chain.full]
theorem full_snoc (c : Chain K A B) (l : Link K B C) : (c.snoc l).full = c.full.snoc l.full := by
  rw [Chain.full]

end

theorem linkFull_full : Spec.linkFull_full := fun _ _ _ _ => rfl

theorem linkFull_seq : Spec.linkFull_seq := fun _ _ _ _ _ _ _ => rfl

theorem chainFull_full : Spec.chainFull_full := by
  intro K A B c
  induction c with
  | one l => rw [full_one, full_one, linkFull_full]
  | snoc c l ih => rw [full_snoc, full_snoc, ih, linkFull_full]

theorem chainFull_append : Spec.chainFull_append := by
  intro K A B C c c'
  induction c' with
  | one l => rw [append_one, full_snoc, full_one, append_one]
  | snoc c' l ih => rw [append_snoc, full_snoc, full_snoc, append_snoc, ih]

theorem chainFull_link : Spec.chainFull_link := by
  intro K A B c d
  induction c with
  | one l => rw [full_one, link_one, link_one, linkFull_full]
  | snoc c l ih =>
    rw [full_snoc, link_snoc, link_snoc, linkFull_seq, ih, linkFull_full, ← linkFull_seq]

/-- chains that are equal but for their errors are, as one link, equal but for their errors -/
theorem chainFull_linkOf {K : Type} {A B : Joint K} {c c' : Chain K A B}
    (h : c.full = c'.full) (d : A.W) :
    (c.link d).full = (c'.link d).full := by
  rw [← chainFull_link, h, chainFull_link]

theorem linkFull_good : Spec.linkFull_good := fun _ _ _ _ =>
  ⟨fun h => goodB_full _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    fun h => goodT_full _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    fun _ h => ⟨goodB_full _ _ _ _ _ _ _ _ _ _ _ _ _ h.base, h.mm, h.claim⟩⟩

theorem linkFull_fmt : Spec.linkFull_fmt := fun _ _ _ _ _ _ _ _ _ =>
  ⟨fun h => ⟨h.idx, h.pass, h.hands, h.bears⟩, fun h => ⟨h.idx, h.pass, h.hands, h.bears⟩⟩

theorem chainFull_blind : Spec.chainFull_blind := by
  intro K A B c
  induction c with
  | one l =>
      refine ⟨fun Kc kc Mk _ _ put => ?_, fun base f => ?_, fun E0 Rc Pw φ ψ => ?_⟩
      · rw [full_one, freshFor_one, freshFor_one]; exact Iff.rfl
      · rw [full_one, freshGiven_one, freshGiven_one]; exact Iff.rfl
      · rw [full_one, fmt_one, fmt_one]; exact linkFull_fmt _ _ _ l _ _ _ φ ψ
  | snoc c l ih =>
      obtain ⟨i1, i2, i3⟩ := ih
      refine ⟨fun Kc kc Mk _ _ put => ?_, fun base f => ?_, fun E0 Rc Pw φ ψ => ?_⟩
      · rw [full_snoc, freshFor_snoc, freshFor_snoc]
        exact or_congr Iff.rfl
          (exists_congr fun Kc' =>
            exists_congr fun kc' => exists_congr fun put' => and_congr (i1 Kc' kc' Mk put') Iff.rfl)
      · rw [full_snoc, freshGiven_snoc, freshGiven_snoc]
        exact or_congr Iff.rfl
          (exists_congr fun Kc' =>
            exists_congr fun kc' => exists_congr fun put' => and_congr (i2 base _) Iff.rfl)
      · rw [full_snoc, fmt_snoc, fmt_snoc]
        exact exists_congr fun χ => and_congr (i3 E0 Rc Pw φ χ) (linkFull_fmt _ _ _ l _ _ _ χ ψ)

theorem chainFull_all : Spec.chainFull_all := by
  intro K A B c
  induction c with
  | one l =>
      obtain ⟨g1, g2, g3⟩ := linkFull_good K _ _ l
      refine ⟨?_, ?_, ?_, fun base => ?_⟩
      · rw [full_one, allB_one, allB_one]; exact g1
      · rw [full_one, allT_one, allT_one]; exact g2
      · rw [full_one, ok_one, ok_one]; exact g2
      · rw [full_one, okGiven_one, okGiven_one]
        rintro (h | ⟨D, h, hb⟩)
        · exact Or.inl (g2 h)
        · exact Or.inr ⟨D, g3 D h, hb⟩
  | snoc c l ih =>
      obtain ⟨g1, g2, g3⟩ := linkFull_good K _ _ l
      obtain ⟨i1, i2, i3, i4⟩ := ih
      obtain ⟨b1, b2, -⟩ := chainFull_blind K _ _ c
      refine ⟨?_, ?_, ?_, fun base => ?_⟩
      · rw [full_snoc, allB_snoc, allB_snoc]; exact fun h => ⟨i1 h.1, g1 h.2⟩
      · rw [full_snoc, allT_snoc, allT_snoc]; exact fun h => ⟨i2 h.1, g2 h.2⟩
      · rw [full_snoc, ok_snoc, ok_snoc]
        rintro ⟨h1, h2 | ⟨D, h2, h3⟩⟩
        · exact ⟨i3 h1, Or.inl (g2 h2)⟩
        · exact ⟨i3 h1, Or.inr ⟨D, g3 D h2, (b1 _ D.kc D.Mk D.put).2 h3⟩⟩
      · rw [full_snoc, okGiven_snoc, okGiven_snoc]
        rintro ⟨h1, h2 | ⟨D, h2, h3⟩⟩
        · exact ⟨i4 base h1, Or.inl (g2 h2)⟩
        · exact ⟨i4 base h1, Or.inr ⟨D, g3 D h2, (b2 base _).2 h3⟩⟩

end Cb
