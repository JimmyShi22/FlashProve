-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowChain.lean: round-by-round knowledge soundness of a chain of links, from that of its links
and the clause on outputs; the rules have no condition on an honest prover.

The matter is sequential composition of interactive oracle reductions (IORs, Ior/Ior.lean), for any
number of them (`Chain`, Ior/KnowCollRulesChain.lean). The bundles that the rules of that file carry
(`GoodB`, Ior/Masked.lean; `GoodT`, Ior/KnowCollGood.lean) hold knowledge soundness together with
completeness, hiding and budgets. Here the two clauses that the rule for two in a row uses are taken
out of the bundle and carried along alone.
Definitions and statements. The proofs: Ior/KnowChainProofs.lean. No protocol, no code occurs here.

Main names:
  `l.KnowT`: the clause `know` of `GoodT` (Ior/KnowCollGood.lean) for the link l, to the letter: the
    reduction of l has `Know` on the statements `A.rels.on`, from `A.rels.relR` to `B.rels.relR`,
    with the extractor `l.ext` and the errors `l.P.err`.
  `l.OnOut`: the clause `onOut` of `GoodT`, to the letter: from a statement in `A.rels.on` every
    output of the verifier of l is in `B.rels.on`.
  `c.KnowT`, `c.OnOut`: every link of the chain c has it.
  `Spec.knowT_seq`, `Spec.onOut_seq`: two links in a row.
  `Spec.chain_knowT`, `Spec.chain_onOut`: the chain as one link, `c.link d`, for every d.
  `Spec.knowT_append`, `Spec.onOut_append`: a chain of two chains has it exactly if both have it.
  `Spec.knowT_of_goodT`, `Spec.onOut_of_goodT`: a link that is `GoodT` has both.
  `Spec.knowT_of_allT`, `Spec.onOut_of_allT`: a chain each of whose links is `GoodT` has both.

The errors of `c.link d` are those of the links in a row (`Nums.seq`, Ior/Chain.lean: by
definition), and its extractor is the composed one (`IOR.extSeq`, Ior/SeqProofs.lean).

Limits: nothing on completeness, hiding, budgets, the form of the rounds or locality of the
verifier: `c.KnowT` with `c.OnOut` is not said to give `GoodT`. A link holds an honest side `l.H` as
data. The six rules (`knowT_seq` to `onOut_append`) have no premise on it; the four statements
`.._of_goodT`, `.._of_allT` start from the whole bundle and so do. `Know` with errors that are not
small says little: no statement of this file bounds an error. This file says nothing on running
times.
Terms: lean/GLOSSARY.md: bundle, chain, extractor, IOR, joint, link, numbers (of a reduction).

-/
import Ior.KnowCollRulesChain

set_option autoImplicit false

namespace Iop
namespace IOR

namespace Link
variable {K : Type} {A B : Joint K}

/-- The link has round-by-round knowledge soundness: the clause `know` of `GoodT`, alone. -/
def KnowT (l : Link K A B) : Prop :=
  l.R.red.Know A.rels.on A.rels.relR B.rels.relR l.ext l.P.err

/-- Every output of the link's verifier on a statement of the first joint's set `on` is in the
second joint's set `on`: the clause `onOut` of `GoodT`, alone. -/
def OnOut (l : Link K A B) : Prop :=
  ∀ a τ b, A.rels.on a → l.R.red.out a τ = some b → B.rels.on b

end Link

namespace Chain
variable {K : Type}

/-- Every link of the chain has `Link.KnowT`. -/
def KnowT : {A B : Joint K} → Chain K A B → Prop
  | _, _, .one l => l.KnowT
  | _, _, .snoc c l => c.KnowT ∧ l.KnowT

/-- Every link of the chain has `Link.OnOut`. -/
def OnOut : {A B : Joint K} → Chain K A B → Prop
  | _, _, .one l => l.OnOut
  | _, _, .snoc c l => c.OnOut ∧ l.OnOut

end Chain
end IOR

namespace Spec
open IOR

/-- States: two links in a row have knowledge soundness if both have it and the outputs of the first
lie in the set of statements of which the second speaks. -/
def knowT_seq : Prop :=
  ∀ (K : Type) (A B C : Joint K) (l : Link K A B) (l' : Link K B C) (d : A.W),
    l.KnowT → l.OnOut → l'.KnowT → (l.seq l' d).KnowT

/-- States: the clause on outputs holds of two links in a row if it holds of both. -/
def onOut_seq : Prop :=
  ∀ (K : Type) (A B C : Joint K) (l : Link K A B) (l' : Link K B C) (d : A.W),
    l.OnOut → l'.OnOut → (l.seq l' d).OnOut

/-- States: a chain as one link has knowledge soundness if every link has it and every link has the
clause on outputs (of the last link the clause on outputs is not used). -/
def chain_knowT : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B), c.KnowT → c.OnOut → ∀ d : A.W, (c.link d).KnowT

/-- States: a chain as one link has the clause on outputs if every link has it. -/
def chain_onOut : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B), c.OnOut → ∀ d : A.W, (c.link d).OnOut

/-- States: every link of two chains in a row has knowledge soundness exactly if every link of
either has it. -/
def knowT_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : Chain K A B) (c' : Chain K B C),
    (c.append c').KnowT ↔ c.KnowT ∧ c'.KnowT

/-- States: every link of two chains in a row has the clause on outputs exactly if every link of
either has it. -/
def onOut_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : Chain K A B) (c' : Chain K B C),
    (c.append c').OnOut ↔ c.OnOut ∧ c'.OnOut

/-- States: a link with the whole bundle `GoodT` has knowledge soundness in the sense of this
file. -/
def knowT_of_goodT : Prop :=
  ∀ (K : Type) (A B : Joint K) (l : Link K A B), l.GoodT → l.KnowT

/-- States: a link with the whole bundle `GoodT` has the clause on outputs. -/
def onOut_of_goodT : Prop :=
  ∀ (K : Type) (A B : Joint K) (l : Link K A B), l.GoodT → l.OnOut

/-- States: in a chain each of whose links has the whole bundle `GoodT`, every link has knowledge
soundness in the sense of this file. -/
def knowT_of_allT : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B), c.AllT → c.KnowT

/-- States: in a chain each of whose links has the whole bundle `GoodT`, every link has the clause
on outputs. -/
def onOut_of_allT : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B), c.AllT → c.OnOut

end Spec
end Iop
