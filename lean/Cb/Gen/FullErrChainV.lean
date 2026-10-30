-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/FullErrChainV.lean: links and chains of a batch with all their round errors overwritten by
the full list (`Err.full`, Cb/Gen/FullErr.lean): the analogue of Cb/Gen/FullErrChain.lean. With
annotations and batch errors: `LinkA`, `ChainA`, Cb/Ld/LdLinChainB.lean; with the honest side of a
batch: `LinkV`, `ChainV`, Cb/Ld/LdLinChainV.lean.

In standard terms: the same replacement of the errors of round-by-round knowledge soundness by the
trivial ones, for reductions composed in sequence that are run on a batch of instances, some rounds
being shared by all instances.

Definitions, statements (in `Cb.Spec`) and proofs: equations between terms. Framework only: no
protocol occurs. Nothing assumed beyond the hypotheses of the statements and whatever the arguments
hold as proofs. With these equations a fact that reads no error list (which reduction, which
annotation, which honest side, which budget) is carried from one chain to every chain that is equal
to it but for the errors.
An annotation (`RoundSplits`, Iop/Batch.lean) says of each round whether its verifier message is shared by
the instances of a batch or local, and which part of the prover message is shared. The batch errors
(`LinkA.err`) are a second list of round errors.

Main names:
  `c.full`, for c : `ChainA`, c : `ChainV`: every link overwritten.
  `Spec.linkAFull_seq`, `Spec.linkVFull_seq`: (x.seq x' d).full = (x.full.seq x'.full d).full, by
    unfolding.
  `Spec.chainAFull_link`, `Spec.chainVFull_link`: (c.full.linkA d).full = (c.linkA d).full;
    (c.full.linkV d).full = (c.linkV d).full.
  `Spec.chainVFull_wh`: c.full.pWh = c.pWh: the bound on the withheld sets reads no error.

Notation: `Err.full s` : `Err s` (Cb/Gen/FullErr.lean): the full list, each entry is the number of
all values of that round's verifier message; `A`, `B`, `C` : `Joint K`
(Ior/KnowCollRulesChain.lean): a joint of a chain, with its types; `VA` : `JV N A`
(Cb/Ld/LdLinChainV.lean): what the honest side of a batch adds at a joint; `d` : A.W: in `Link.seq`
(Ior/KnowCollRulesChain.lean), the extractor's value where the first verifier rejects; `c.pWh` :
ℝ≥0∞ (Cb/Ld/LdLinBHonTop.lean): the sum of the probabilities of the links' withheld sets.

Limits: this file says nothing on whether a chain is in order, at any errors. It says nothing on a
protocol. It says nothing on numerals.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.FullErrChain
import Cb.Ld.LdLinBHonTop

set_option autoImplicit false

namespace Iop
namespace IOR
variable {K : Type} {N : ℕ}

/-- the link with annotation, its link's errors and its batch errors overwritten by the full list -/
def LinkA.full {A B : Joint K} (a : LinkA K A B) : LinkA K A B :=
  ⟨a.l.full, a.ann, Err.full a.l.R.shape⟩

/-- the link with the honest side of a batch, all errors overwritten by the full list -/
def LinkV.full {A B : Joint K} {VA : JV N A} {VB : JV N B} (v : LinkV K N VA VB) :
    LinkV K N VA VB :=
  ⟨v.a.full, v.hv, v.bud⟩

def ChainA.full : {A B : Joint K} → ChainA K A B → ChainA K A B
  | _, _, .one a => .one a.full
  | _, _, .snoc c a => .snoc c.full a.full

def ChainV.full :
    {A B : Joint K} → {VA : JV N A} → {VB : JV N B} → ChainV K N VA VB → ChainV K N VA VB
  | _, _, _, _, .one v => .one v.full
  | _, _, _, _, .snoc c v => .snoc c.full v.full

end IOR
end Iop

namespace Cb
open Iop Prob Iop.IOR

namespace Spec

def linkAFull_full : Prop := ∀ (K : Type) (A B : Joint K) (a : LinkA K A B), a.full.full = a.full

def linkVFull_full : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (v : LinkV K N VA VB),
    v.full.full = v.full

def linkAFull_seq : Prop :=
  ∀ (K : Type) (A B C : Joint K) (a : LinkA K A B) (a' : LinkA K B C) (d : A.W),
    (a.seq a' d).full = (a.full.seq a'.full d).full

def linkVFull_seq : Prop :=
  ∀ (K : Type) (N : ℕ) (A B C : Joint K) (VA : JV N A) (VB : JV N B) (VC : JV N C)
      (v : LinkV K N VA VB) (v' : LinkV K N VB VC) (d : A.W),
    (v.seq v' d).full = (v.full.seq v'.full d).full

def chainAFull_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : ChainA K A B) (c' : ChainA K B C),
    (c.append c').full = c.full.append c'.full

def chainVFull_append : Prop :=
  ∀ (K : Type) (N : ℕ) (A B C : Joint K) (VA : JV N A) (VB : JV N B) (VC : JV N C)
      (c : ChainV K N VA VB) (c' : ChainV K N VB VC),
    (c.append c').full = c.full.append c'.full

def chainAFull_forget : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : ChainA K A B), c.full.forget = c.forget.full

def chainVFull_forget : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB),
    c.full.forget = c.forget.full

/-- The chain as one link, but for its errors. -/
def chainAFull_link : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : ChainA K A B) (d : A.W),
    (c.full.linkA d).full = (c.linkA d).full

def chainVFull_link : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB) (d : A.W),
    (c.full.linkV d).full = (c.linkV d).full

def chainVFull_wh : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB),
    c.full.pWh = c.pWh

end Spec

section
variable {K : Type} {N : ℕ} {A B C : Joint K} {VA : JV N A} {VB : JV N B} {VC : JV N C}

theorem fullA_one (a : LinkA K A B) : (ChainA.one a).full = .one a.full := by rw [ChainA.full]
theorem fullA_snoc (c : ChainA K A B) (a : LinkA K B C) : (c.snoc a).full = c.full.snoc a.full := by
  rw [ChainA.full]
theorem fullV_one (v : LinkV K N VA VB) : (ChainV.one v).full = .one v.full := by rw [ChainV.full]
theorem fullV_snoc (c : ChainV K N VA VB) (v : LinkV K N VB VC) :
    (c.snoc v).full = c.full.snoc v.full := by rw [ChainV.full]

end

theorem linkAFull_full : Spec.linkAFull_full := fun _ _ _ _ => rfl

theorem linkVFull_full : Spec.linkVFull_full := fun _ _ _ _ _ _ _ => rfl

theorem linkAFull_seq : Spec.linkAFull_seq := fun _ _ _ _ _ _ _ => rfl

theorem linkVFull_seq : Spec.linkVFull_seq := fun _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem chainAFull_append : Spec.chainAFull_append := by
  intro K A B C c c'
  induction c' with
  | one a => rw [ChainA.append_one, fullA_snoc, fullA_one, ChainA.append_one]
  | snoc c' a ih => rw [ChainA.append_snoc, fullA_snoc, fullA_snoc, ChainA.append_snoc, ih]

theorem chainVFull_append : Spec.chainVFull_append := by
  intro K N A B C VA VB VC c c'
  induction c' with
  | one v => rw [ChainV.append_one, fullV_snoc, fullV_one, ChainV.append_one]
  | snoc c' v ih => rw [ChainV.append_snoc, fullV_snoc, fullV_snoc, ChainV.append_snoc, ih]

theorem chainAFull_forget : Spec.chainAFull_forget := by
  intro K A B c
  induction c with
  | one a => rw [fullA_one, ChainA.forget_one, ChainA.forget_one, full_one]; rfl
  | snoc c a ih => rw [fullA_snoc, ChainA.forget_snoc, ChainA.forget_snoc, full_snoc, ih]; rfl

theorem chainVFull_forget : Spec.chainVFull_forget := by
  intro K N A B VA VB c
  induction c with
  | one v => rw [fullV_one, ChainV.forget_one, ChainV.forget_one, fullA_one]; rfl
  | snoc c v ih => rw [fullV_snoc, ChainV.forget_snoc, ChainV.forget_snoc, fullA_snoc, ih]; rfl

theorem chainAFull_link : Spec.chainAFull_link := by
  intro K A B c d
  induction c with
  | one a => rw [fullA_one, ChainA.linkA_one, ChainA.linkA_one, linkAFull_full]
  | snoc c a ih =>
    rw [fullA_snoc, ChainA.linkA_snoc, ChainA.linkA_snoc, linkAFull_seq, ih,
      linkAFull_full, ← linkAFull_seq]

theorem chainVFull_link : Spec.chainVFull_link := by
  intro K N A B VA VB c d
  induction c with
  | one v => rw [fullV_one, ChainV.linkV_one, ChainV.linkV_one, linkVFull_full]
  | snoc c v ih =>
    rw [fullV_snoc, ChainV.linkV_snoc, ChainV.linkV_snoc, linkVFull_seq, ih,
      linkVFull_full, ← linkVFull_seq]

/-- chains that are equal but for their errors are, as one link, equal but for their errors -/
theorem chainVFull_linkOf {K : Type} {N : ℕ} {A B : Joint K} {VA : JV N A} {VB : JV N B}
    {c c' : ChainV K N VA VB} (h : c.full = c'.full) (d : A.W) :
    (c.linkV d).full = (c'.linkV d).full := by
  rw [← chainVFull_link, h, chainVFull_link]

theorem chainVFull_wh : Spec.chainVFull_wh := by
  intro K N A B VA VB c
  induction c with
  | one v => rw [fullV_one, ChainV.pWh_one, ChainV.pWh_one]; rfl
  | snoc c v ih => rw [fullV_snoc, ChainV.pWh_snoc, ChainV.pWh_snoc, ih]; rfl

end Cb
