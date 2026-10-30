-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFreshS.lean: chains with masked blocks whose own masks were sent at different steps:
"fresh after the chain" as a property of the chain as one link.

Definitions and statements (Iop.Spec.chainS_*, freshS_*, okS_*); the proofs are in
Cb/Req1/LdSegFreshSProofs.lean. No protocol, no code occurs here.
It builds on Ior/KnowCollRulesChain.lean (chains of links: `IOR.Chain`, `IOR.Link`; `c.FreshFor`;
`c.Ok`; `chain_ok`), Cb/Req1/LdSegFresh.lean (facts; `c.FreshGiven base`; `c.OkGiven base`) and
Ior/FreshJoin.lean (two facts "fresh" at one reading join). The head of Cb/Req1/LdSegFresh.lean has
the Lean names and paths for "the whole bundle", "the bundle without its clause on zero knowledge",
"masked block" and "does not look". The types of masks (Mk, M₁, M₂, Mk') are finite and non-empty
wherever they occur here.

Why a second notion: `c.FreshFor` and `c.FreshGiven` are recursions on the list of links: "the last
link is Fresh for these masks, or it does not look at them and they were fresh before it". The own
masks of a block may come from two sendings (Ior/FreshJoin.lean). Of such a pair the last sending is
neither Fresh (a part stands in its input) nor does it not look (it sends the other part): the
pair's fact cannot be had in these recursions, though it is true.

Main names:
  `c.FreshS kc Mk put`: the property itself: the chain as one link (`c.link d`, for every default d
    of the extractor) is Fresh: given all that the chain shows, the masks are still uniform, and
    independent of the rest of what kc reads, in this sense:
    `H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and
    every T with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its
    third part is overwritten by `put M` at an independent uniform M. (`Honest.Fresh`,
    `Honest.seen`, Ior/KnowCollRulesMask.lean.) In this file `Fresh` stands in the definition
    `c.FreshS` (of `(c.link d).H`) and as a premise of `Spec.freshS_fresh` (on `l.H`); `FreshS`, and
    `OkS`, which is defined with it, stand in the statements below as premises and as conclusions.
  `c.OkS`: every link has the whole bundle, or is a masked block whose fact is FreshS after the
    chain before it.
  `X.JCl`: the closure of a set X of facts under: join (two facts with one reading); a coarser
    reading; another type for the same masks.
  `Spec.chainS_ok`: c.OkS ⇒ the chain as one link has the whole bundle, honest-verifier exact zero
    knowledge included (`GoodT.exact`: `Honest.Exact`, Ior/Honest.lean).
  `Spec.freshS_of_for`, `Spec.okS_of_ok`, `Spec.allB_of_okS`: `FreshFor` and `Ok` give `FreshS` and
    `OkS`; `OkS` gives `AllB`. (FreshFor gives FreshS for a chain all of whose links have the bundle
    without its clause on zero knowledge: c.AllB.)
  `Spec.freshS_join`, `Spec.freshS_conseq`, `Spec.freshS_equiv`: the three rules.
  `Spec.freshS_jcl`: if all facts of X are FreshS after c, so are all facts of X.JCl.
  `Spec.freshS_blind`, `Spec.freshS_fresh` (the second under `c.AllB`): through a link that does not
    look; at a link that is Fresh.
  `Spec.freshS_of_given` (under `c₀.AllB`, `c.AllB`), `Spec.okS_of_given` (under `c₀.OkS`):
    `FreshGiven` and `OkGiven` behind `FreshS` and `OkS`: a piece c with c.FreshGiven base f,
    c.OkGiven base, behind a chain c₀ after which all facts of "base" are FreshS. So the recursions
    can be started afresh at any joint from a set of facts that was closed under JCl there.

Limits: nothing on requests (Cb/Req1/LdReqS.lean). Nothing on batches.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegFresh
import Cb.Req1.LdSegCarryKit
import Ior.FreshJoin

set_option autoImplicit false

namespace Iop
open Prob

namespace IOR

/-- The closure of a set of facts: join, a coarser reading, another type for the same masks. -/
inductive MaskFact.JCl {W : Type} (X : MaskFact W → Prop) : MaskFact W → Prop
  | base (f : MaskFact W) : X f → JCl X f
  | join (Kc : Type) (kc : W → Kc) (M₁ M₂ : Type) [Fintype M₁] [Nonempty M₁] [Fintype M₂]
      [Nonempty M₂] (put₁ : M₁ → Kc → Kc) (put₂ : M₂ → Kc → Kc) :
      JCl X ⟨Kc, kc, M₁, put₁⟩ → JCl X ⟨Kc, kc, M₂, put₂⟩ →
      JCl X ⟨Kc, kc, M₁ × M₂, fun M k => put₁ M.1 (put₂ M.2 k)⟩
  | conseq (f : MaskFact W) (Kc' : Type) (g : f.Kc → Kc') (put' : f.Mk → Kc' → Kc') :
      (∀ M k, g (f.put M k) = put' M (g k)) → JCl X f → JCl X ⟨Kc', fun w => g (f.kc w), f.Mk, put'⟩
  | equiv (f : MaskFact W) (Mk' : Type) [Fintype Mk'] [Nonempty Mk'] (e : f.Mk ≃ Mk') :
      JCl X f → JCl X ⟨f.Kc, f.kc, Mk', fun M k => f.put (e.symm M) k⟩

namespace Chain
variable {K : Type}

/-- `c.FreshS kc Mk put` is `∀ d : A.W, (c.link d).H.Fresh A.rels.rel (c.link d).P.bud kc Mk put`.
`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. (`Honest.Fresh`, `Honest.seen`,
Ior/KnowCollRulesMask.lean.) `(c.link d).H.Fresh` stands here inside a definition. -/
def FreshS {A B : Joint K} (c : Chain K A B) {Kc : Type} (kc : B.W → Kc) (Mk : Type) [Fintype Mk]
    [Nonempty Mk] (put : Mk → Kc → Kc) : Prop :=
  ∀ d : A.W, (c.link d).H.Fresh A.rels.rel (c.link d).P.bud kc Mk put

/-- Every link is of one of the two kinds; a masked link's masks are fresh, in this sense, after the
chain before it. -/
def OkS : {A B : Joint K} → Chain K A B → Prop
  | _, _, .one l => l.GoodT
  | _, _, .snoc c l =>
    c.OkS ∧ (l.GoodT ∨ ∃ D : MaskData l.R _, l.GoodM D ∧ c.FreshS D.kc D.Mk D.put)

end Chain
end IOR

namespace Spec
open IOR

/-- The flat statement: c.OkS ⇒ the chain as one link has the whole bundle. -/
def chainS_ok : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W), c.OkS → (c.link d).GoodT

def allB_of_okS : Prop := ∀ (K : Type) (A B : Joint K) (c : Chain K A B), c.OkS → c.AllB

def freshS_of_for : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (Kc : Type) (kc : B.W → Kc) (Mk : Type)
      [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc),
    c.AllB → c.FreshFor kc Mk put → c.FreshS kc Mk put

def okS_of_ok : Prop := ∀ (K : Type) (A B : Joint K) (c : Chain K A B), c.Ok → c.OkS

/-- Two facts at one reading join. -/
def freshS_join : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (Kc : Type) (kc : B.W → Kc)
      (M₁ M₂ : Type) [Fintype M₁] [Nonempty M₁] [Fintype M₂] [Nonempty M₂]
      (put₁ : M₁ → Kc → Kc) (put₂ : M₂ → Kc → Kc),
    c.FreshS kc M₁ put₁ → c.FreshS kc M₂ put₂ →
    c.FreshS kc (M₁ × M₂) fun M k => put₁ M.1 (put₂ M.2 k)

def freshS_conseq : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (Kc Kc' : Type) (kc : B.W → Kc) (g : Kc → Kc')
      (Mk : Type) [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc) (put' : Mk → Kc' → Kc'),
    (∀ M k, g (put M k) = put' M (g k)) → c.FreshS kc Mk put → c.FreshS (fun w => g (kc w)) Mk put'

def freshS_equiv : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (Kc : Type) (kc : B.W → Kc) (Mk Mk' : Type)
      [Fintype Mk] [Nonempty Mk] [Fintype Mk'] [Nonempty Mk'] (e : Mk ≃ Mk') (put : Mk → Kc → Kc),
    c.FreshS kc Mk put → c.FreshS kc Mk' fun M k => put (e.symm M) k

/-- The closure. -/
def freshS_jcl : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (X : MaskFact B.W → Prop),
    (∀ g, X g → c.FreshS g.kc g.Mk g.put) → ∀ f, MaskFact.JCl X f → c.FreshS f.kc f.Mk f.put

/-- Through a link that does not look. -/
def freshS_blind : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : Chain K A B) (l : Link K B C) (Kc' Kc : Type)
      (kc' : B.W → Kc') (kc : C.W → Kc) (Mk : Type) [Fintype Mk] [Nonempty Mk]
      (put' : Mk → Kc' → Kc') (put : Mk → Kc → Kc),
    c.FreshS kc' Mk put' → l.H.Blind kc' kc Mk put' put → (c.snoc l).FreshS kc Mk put

/-- At a link that is Fresh. -/
def freshS_fresh : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : Chain K A B) (l : Link K B C) (Kc : Type) (kc : C.W → Kc)
      (Mk : Type) [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc),
    c.AllB → l.H.Fresh B.rels.rel l.P.bud kc Mk put → (c.snoc l).FreshS kc Mk put

/-- `FreshGiven` behind `FreshS`: what is fresh. -/
def freshS_of_given : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c₀ : Chain K A B) (c : Chain K B C)
      (base : MaskFact B.W → Prop) (f : MaskFact C.W),
    c₀.AllB → c.AllB → (∀ g, base g → c₀.FreshS g.kc g.Mk g.put) →
    c.FreshGiven base f → (c₀.append c).FreshS f.kc f.Mk f.put

/-- `OkGiven` behind `OkS`: the two kinds. -/
def okS_of_given : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c₀ : Chain K A B) (c : Chain K B C) (base : MaskFact B.W → Prop),
    c₀.OkS → (∀ g, base g → c₀.FreshS g.kc g.Mk g.put) → c.OkGiven base → (c₀.append c).OkS

end Spec
end Iop
