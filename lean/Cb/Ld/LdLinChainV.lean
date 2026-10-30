-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinChainV.lean: the honest prover of a batch (several instances proved in one run) along a
sequence of interactive oracle reductions: definitions and lemmas that carry it through composition.

Definitions, statements (`Iop.Spec.chainV_link` to `Iop.Spec.chainV_end`) and proofs. Generic: no
protocol, no code occurs here. Cb/Ld/LdLinChainB.lean carries the annotation and the errors for a
batch along a chain; here the batch's honest side and its budget are carried in the same brackets.

Why: a test for N instances is defined on chains, bracketed to the left
(Ior/KnowCollRulesChain.lean: `Chain`; Cb/Ld/LdLinChainB.lean: `ChainA`). The recursion that makes
one link of a chain does not unfold by itself, so whatever belongs to the whole has to be put
together by the same recursion, so that one term has knowledge soundness for the instances of a
batch and the honest side of a batch.

Main names:
  `JV N J`: what the honest side of a batch adds at a joint J: the type W0 of the shared witness
    there (what the shared part of the prover holds), the tie between the shared witness and a
    slot's statement and witness, and the demand q on families of sets of positions
    (Ior/LinkVBears.lean: what may still be read of the joint's oracles, through all slots).
  `LinkV K N VA VB`: a link with annotation and errors (`LinkA`), the honest side of a batch on it
    (Ior/LinkV.lean: `HonestV`), and its budget for families.
  `ChainV K N VA VB`: a chain of such links, bracketed to the left. `c.linkV d`: the chain as one
    (d: any value of the first joint's type of witnesses; the composed extractor's value where the
    first verifier rejects). `c.forget`: the chain of Cb/Ld/LdLinChainB.lean. `c.append c'`.
  `v.PV`: the link is a piece (Ior/LinkVBears.lean: `PieceV`, with the four clauses `isLocal`,
    `acc`, `exact`, `bears`) between the two joints' relations (`JV.rel`) and demands, and the
    demand at its end is kept by subsets of the set of slots. `c.AllPV`: every link is.
  `Spec.chainV_link`, `Spec.chainV_forget_append`: `(c.linkV d).a` is `c.forget.linkA d`; forgetting
    commutes with append. So what is proved of the chain with annotations (knowledge soundness in a
    batch) holds of the same term.
  `Spec.chainV_piece`: a chain of pieces is a piece (`c.AllPV` ⇒ `(c.linkV d).PV`).
  `Spec.chainV_end`: under `c.AllPV`: what a whole chain has at the end, if its last demand holds of
    the empty family:
      local;
      complete for each slot (`HonestV.AccV`, Ior/LinkV.lean: outside `(c.linkV d).hv.withheld`);
      exactly honest-verifier zero knowledge for sets of slots at no further reads
        (`HonestV.ExactV`, Ior/LinkV.lean);
      what the simulator is given is within the first joint's demand.

Limits: links whose masks were sent earlier in the chain are no pieces (Ior/LinkVMasked.lean has the
rule for two; it is not folded here). This file says nothing on soundness. No chain is given here.
This file says nothing on running times: a simulator is any term of `SimV` (Ior/LinkV.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinChainB
import Ior.LinkVBears
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob

namespace IOR

/-- What the honest side of a batch adds at a joint. -/
structure JV {K : Type} (N : ℕ) (J : Joint K) : Type 1 where
  /-- the shared witness -/
  W0  : Type
  /-- how a slot's statement and witness are tied to it -/
  tie : W0 → J.X → J.E.Str → J.W → Prop
  /-- what may still be read of the joint's oracles, through all slots -/
  q   : QFam J.E N

/-- the joint's relation for a batch -/
def JV.rel {K : Type} {N : ℕ} {J : Joint K} (V : JV N J) : J.X → J.E.Str → V.W0 × J.W → Prop :=
  fun x y w => J.rels.rel x y w.2 ∧ V.tie w.1 x y w.2

/-- A link with the honest side of a batch. -/
structure LinkV (K : Type) (N : ℕ) {A B : Joint K} (VA : JV N A) (VB : JV N B) : Type 1 where
  a   : LinkA K A B
  hv  : a.l.R.HonestV a.ann VA.W0 A.W VB.W0 B.W
  bud : BudB a.l.R.shape N

/-- Two in a row. -/
def LinkV.seq {K : Type} {N : ℕ} {A B C : Joint K} {VA : JV N A} {VB : JV N B}
    {VC : JV N C} (v : LinkV K N VA VB) (v' : LinkV K N VB VC) (d : A.W) : LinkV K N VA VC :=
  ⟨v.a.seq v'.a d, v.hv.seqV v'.hv, budSeqV v.a.l.R v'.a.l.R v.bud v'.bud⟩

/-- Defines: the link is a piece. -/
def LinkV.PV {K : Type} {N : ℕ} {A B : Joint K} {VA : JV N A} {VB : JV N B} (v : LinkV K N VA VB) :
    Prop :=
  PieceV v.a.l.R v.a.ann v.hv N VA.rel VB.rel v.bud VA.q VB.q ∧ VB.q.Her

/-- A chain of such links, bracketed to the left. -/
inductive ChainV (K : Type) (N : ℕ) : {A B : Joint K} → JV N A → JV N B → Type 1
  | one {A B : Joint K} {VA : JV N A} {VB : JV N B} (v : LinkV K N VA VB) : ChainV K N VA VB
  | snoc {A B C : Joint K} {VA : JV N A} {VB : JV N B} {VC : JV N C}
      (c : ChainV K N VA VB) (v : LinkV K N VB VC) : ChainV K N VA VC

namespace ChainV
variable {K : Type} {N : ℕ}

def linkV :
    {A B : Joint K} → {VA : JV N A} → {VB : JV N B} → ChainV K N VA VB → A.W → LinkV K N VA VB
  | _, _, _, _, .one v, _ => v
  | _, _, _, _, .snoc c v, d => (c.linkV d).seq v d

def forget : {A B : Joint K} → {VA : JV N A} → {VB : JV N B} → ChainV K N VA VB → ChainA K A B
  | _, _, _, _, .one v => .one v.a
  | _, _, _, _, .snoc c v => .snoc c.forget v.a

def append :
    {A B C : Joint K} → {VA : JV N A} → {VB : JV N B} → {VC : JV N C} →
    ChainV K N VA VB → ChainV K N VB VC → ChainV K N VA VC
  | _, _, _, _, _, _, c, .one v => .snoc c v
  | _, _, _, _, _, _, c, .snoc c' v => .snoc (c.append c') v

def AllPV : {A B : Joint K} → {VA : JV N A} → {VB : JV N B} → ChainV K N VA VB → Prop
  | _, _, _, _, .one v => v.PV
  | _, _, _, _, .snoc c v => c.AllPV ∧ v.PV

variable {A B C D : Joint K} {VA : JV N A} {VB : JV N B} {VC : JV N C} {VD : JV N D}
theorem linkV_one (v : LinkV K N VA VB) (d : A.W) : (ChainV.one v).linkV d = v := by rw [linkV]
theorem linkV_snoc (c : ChainV K N VA VB) (v : LinkV K N VB VC) (d : A.W) :
    (c.snoc v).linkV d = (c.linkV d).seq v d := by rw [linkV]
theorem forget_one (v : LinkV K N VA VB) : (ChainV.one v).forget = .one v.a := by rw [forget]
theorem forget_snoc (c : ChainV K N VA VB) (v : LinkV K N VB VC) :
    (c.snoc v).forget = c.forget.snoc v.a := by rw [forget]
theorem append_one (c : ChainV K N VA VB) (v : LinkV K N VB VC) : c.append (.one v) = c.snoc v := by
  rw [append]
theorem append_snoc (c : ChainV K N VA VB) (c' : ChainV K N VB VC) (v : LinkV K N VC VD) :
    c.append (c'.snoc v) = (c.append c').snoc v := by rw [append]
theorem allPV_one (v : LinkV K N VA VB) : (ChainV.one v).AllPV ↔ v.PV := by rw [AllPV]
theorem allPV_snoc (c : ChainV K N VA VB) (v : LinkV K N VB VC) :
    (c.snoc v).AllPV ↔ c.AllPV ∧ v.PV := by rw [AllPV]

end ChainV
end IOR

namespace Spec
open IOR

/-- The chain as one link is, under its honest side, the chain with annotations as one link. -/
def chainV_link : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB) (d : A.W),
    (c.linkV d).a = c.forget.linkA d

def chainV_forget_append : Prop :=
  ∀ (K : Type) (N : ℕ) (A B C : Joint K) (VA : JV N A) (VB : JV N B) (VC : JV N C)
      (c : ChainV K N VA VB) (c' : ChainV K N VB VC),
    (c.append c').forget = c.forget.append c'.forget

/-- Two pieces in a row. -/
def linkV_seq : Prop :=
  ∀ (K : Type) (N : ℕ) (A B C : Joint K) (VA : JV N A) (VB : JV N B) (VC : JV N C)
      (v : LinkV K N VA VB) (v' : LinkV K N VB VC) (d : A.W),
    v.PV → v'.PV → (v.seq v' d).PV

/-- States: a chain of pieces is a piece. -/
def chainV_piece : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB) (d : A.W),
    c.AllPV → (c.linkV d).PV

def chainV_all_append : Prop :=
  ∀ (K : Type) (N : ℕ) (A B C : Joint K) (VA : JV N A) (VB : JV N B) (VC : JV N C)
      (c : ChainV K N VA VB) (c' : ChainV K N VB VC),
    (c.append c').AllPV ↔ c.AllPV ∧ c'.AllPV

/-- What a whole chain has at the end. -/
def chainV_end : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB) (d : A.W),
    c.AllPV → (∀ J, VB.q J fun _ => ∅) →
    (c.linkV d).a.l.R.IsLocal ∧
    (c.linkV d).hv.AccV VA.rel VB.rel ∧
    (c.linkV d).hv.ExactV N VA.rel (fun _ _ Ts => ∀ j, Ts j = ∅) ∧
    ∀ (J : Finset (Fin N)) (ρ : BRho N (c.linkV d).a.l.R.shape (c.linkV d).a.ann),
      VA.q J fun j => (c.linkV d).a.l.R.given (ρ.slot j.1) ∅

end Spec

open IOR IOR.ChainV

theorem chainV_link : Spec.chainV_link := by
  intro K N A B VA VB c d
  induction c with
  | one v => rw [linkV_one, forget_one, ChainA.linkA_one]
  | snoc c v ih =>
      rw [linkV_snoc, forget_snoc, ChainA.linkA_snoc, ← ih]
      rfl

theorem chainV_forget_append : Spec.chainV_forget_append := by
  intro K N A B C VA VB VC c c'
  induction c' with
  | one v => rw [append_one, forget_snoc, forget_one, ChainA.append_one]
  | snoc c' v ih => rw [append_snoc, forget_snoc, forget_snoc, ChainA.append_snoc, ih]

theorem linkV_seq : Spec.linkV_seq := fun _ N _ _ _ VA VB VC v v' _ h h' =>
  ⟨pieceV_seq _ _ _ _ _ _ v.a.l.R v'.a.l.R v.a.ann v'.a.ann _ _ _ _ _ _ v.hv v'.hv N VA.rel VB.rel
      VC.rel v.bud v'.bud VA.q VB.q VC.q h.1 h'.1 h'.2,
    h'.2⟩

theorem chainV_piece : Spec.chainV_piece := by
  intro K N A B VA VB c d h
  induction c with
  | one v =>
      rw [linkV_one]
      exact (allPV_one v).1 h
  | snoc c v ih =>
      rw [linkV_snoc]
      obtain ⟨h1, h2⟩ := (allPV_snoc c v).1 h
      exact linkV_seq _ _ _ _ _ _ _ _ _ _ d (ih h1) h2

theorem chainV_all_append : Spec.chainV_all_append := by
  intro K N A B C VA VB VC c c'
  induction c' with
  | one v => rw [append_one, allPV_snoc, allPV_one]
  | snoc c' v ih => rw [append_snoc, allPV_snoc, allPV_snoc, ih, and_assoc]

theorem chainV_end : Spec.chainV_end := fun K N A B VA VB c d h h0 =>
  pieceV_end _ _ _ _ _ _ _ _ _ _ (c.linkV d).hv N VA.rel VB.rel (c.linkV d).bud VA.q VB.q
    (chainV_piece K N A B VA VB c d h).1 h0

end Iop
