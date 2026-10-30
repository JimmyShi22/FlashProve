-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinChainB.lean: knowledge soundness of a sequence of interactive oracle reductions when
several instances are proved in one run (a batch), and its use for the test that an encoded index
meets linear constraints.

Definitions, statements (`Iop.Spec.chainA_link` to `Iop.Spec.chainA_kb_append`,
`Cb.Spec.ldLinCB_forget` to `Cb.Spec.ldLinCB_know`) and proofs. `KnowB` (Ior/BatchSeq.lean) is
round-by-round knowledge soundness for the instances of a batch, for one link of a chain, by sets of
bad values: it runs over the vectors of at most N statements that a predicate admits.
The errors (`Err`, Iop/Rbr.lean) are counts of values of one verifier message, one number for each
round, not probabilities.
An annotation (lean/GLOSSARY.md) tells, of the shape of a batch protocol: for each round whether it
is local or shared, and how a prover message of a local transcript splits into the shared part,
which is one for all slots of the batch, and the part of one slot. (`RAnn`, Iop/Batch.lean; `RoundSplits`,
Iop/Batch.lean) The slots: j : `Fin N` (`BTr`, Iop/Batch.lean).

Why: the test is defined on chains, bracketed to the left, with its closing a parameter chain
(Cb/Ld/LdLinChain.lean). A batch needs, beside each link, who speaks and which verifier messages are
shared (an annotation of the link's shape) and the link's errors for a batch (which differ from
those for one instance: the shared point). Both have to be put together in the same brackets as the
links, so that one term has all properties.

Main names, generic (no protocol):
  `LinkA K A B`: a link with what a batch needs.
  `ChainA K A B`: a chain of such links, bracketed to the left. `c.linkA d`: the chain as one.
    `c.forget`: the chain of the links alone. `c.append c'`.
  `a.KB N kA kB`: the link is knowledge sound for the vectors with one key (`JKey`), and takes them
    to vectors with one key.
  `c.KB N kA kB`: every link has this, along some keys at the joints between.
  `Spec.chainA_link`, `Spec.chainA_forget_append`: `(c.linkA d).l` is `c.forget.link d`; forgetting
    commutes with append: so what is proved of the chain of links (a tail, honest-verifier zero
    knowledge) holds of the same term.
  `Spec.chainA_kb`: if `c.KB N kA kB`, the chain as one link has it: errors in a row, annotations in
    a row, extractors composed.

Main names, the test (in these statements the type ι of positions is nonempty; the parameters `on0`,
`S`, `εf`, `d`, the seven blocks and W, G_u, Ω are told in the head of Cb/Ld/LdLinChain.lean):
  `P.chainA on0 S εf N`: the core, with who speaks and the errors for at most N instances.
  `P.linCA on0 S εf N cZ d`: the test for at most N instances, for any closing chain cZ with
    annotations.
  `Spec.ldLinCB_core`: under `P.FoldErr on0 εf`, injective `P.D.py` and `S.OK`: the core has `KB`
    from the key "encoded index and record" (`P.key0`) to the key after ζ (`P.key6`).
  `Spec.ldLinCB_know`: under `P.FoldErr on0 εf`, injective `P.D.py` and `S.OK`: for every closing
    chain with `KB` from the key after ζ: the test has `KnowB` for the vectors that share the
    encoded index and its record, on the statements with the condition (`(P.j0 on0).on`), to the
    trivial statement.

Limits: this file says nothing on the honest side of a batch (of the same term: `Spec.ldLinT_same`,
`Spec.ldLinT_all`, Cb/Ld/LdLinBHonTop.lean). No closing: the closing chain cZ is a parameter (a
closing chain with annotations, over a plan (`LdTcA`) that is a parameter: `LdLinC.cZA`,
Cb/Ld/LdBatchBlocksPlan.lean). All of `KnowB`'s content hangs on which vectors are admissible (the
head of Ior/BatchSeq.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinBProofs
import Cb.Ld.LdLinChain
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob

namespace IOR

/-- A link (Ior/KnowCollRulesChain.lean) with an annotation of its shape and a list of errors for a
batch. -/
structure LinkA (K : Type) (A B : Joint K) : Type 1 where
  l   : Link K A B
  ann : RoundSplits l.R.shape
  err : Err l.R.shape

/-- Two in a row. -/
def LinkA.seq {K : Type} {A B C : Joint K} (a : LinkA K A B)
    (a' : LinkA K B C) (d : A.W) : LinkA K A C :=
  ⟨a.l.seq a'.l d, RoundSplits.app a.ann a'.ann, Err.app a.err a'.err⟩

/-- A chain of such links, bracketed to the left. -/
inductive ChainA (K : Type) : Joint K → Joint K → Type 1
  | one {A B : Joint K} (a : LinkA K A B) : ChainA K A B
  | snoc {A B C : Joint K} (c : ChainA K A B) (a : LinkA K B C) : ChainA K A C

/-- A key at a joint: what the statements of one batch have in common there. -/
structure JKey {K : Type} (J : Joint K) : Type 1 where
  κ   : Type
  key : J.X × J.E.Str → κ

/-- Defines: the link is knowledge sound for the vectors of at most N statements with one key kA
(`KnowB`, between the joints' relaxed relations), and takes such vectors, on any transcript of the
whole batch, to vectors with one key kB. -/
def LinkA.KB {K : Type} {A B : Joint K} (a : LinkA K A B) (N : ℕ) (kA : JKey A) (kB : JKey B) :
    Prop :=
  ldk_LinkB a.l.R a.ann N kA.key kB.key A.rels.relR B.rels.relR a.l.ext a.err

namespace ChainA
variable {K : Type}

def linkA : {A B : Joint K} → ChainA K A B → A.W → LinkA K A B
  | _, _, .one a, _ => a
  | _, _, .snoc c a, d => (c.linkA d).seq a d

def forget : {A B : Joint K} → ChainA K A B → Chain K A B
  | _, _, .one a => .one a.l
  | _, _, .snoc c a => .snoc c.forget a.l

def append : {A B C : Joint K} → ChainA K A B → ChainA K B C → ChainA K A C
  | _, _, _, c, .one a => .snoc c a
  | _, _, _, c, .snoc c' a => .snoc (c.append c') a

def KB : {A B : Joint K} → ChainA K A B → ℕ → JKey A → JKey B → Prop
  | _, _, .one a, N, kA, kB => a.KB N kA kB
  | _, _, .snoc (B := B) c a, N, kA, kC => ∃ kB : JKey B, c.KB N kA kB ∧ a.KB N kB kC

variable {A B C D : Joint K}
theorem linkA_one (a : LinkA K A B) (d : A.W) : (ChainA.one a).linkA d = a := by rw [linkA]
theorem linkA_snoc (c : ChainA K A B) (a : LinkA K B C) (d : A.W) :
    (c.snoc a).linkA d = (c.linkA d).seq a d := by rw [linkA]
theorem forget_one (a : LinkA K A B) : (ChainA.one a).forget = .one a.l := by rw [forget]
theorem forget_snoc (c : ChainA K A B) (a : LinkA K B C) :
    (c.snoc a).forget = c.forget.snoc a.l := by rw [forget]
theorem append_one (c : ChainA K A B) (a : LinkA K B C) : c.append (.one a) = c.snoc a := by
  rw [append]
theorem append_snoc (c : ChainA K A B) (c' : ChainA K B C) (a : LinkA K C D) :
    c.append (c'.snoc a) = (c.append c').snoc a := by rw [append]
theorem kb_one (a : LinkA K A B) (N : ℕ) (kA : JKey A) (kB : JKey B) :
    (ChainA.one a).KB N kA kB ↔ a.KB N kA kB := by rw [KB]
theorem kb_snoc (c : ChainA K A B) (a : LinkA K B C) (N : ℕ) (kA : JKey A) (kC : JKey C) :
    (c.snoc a).KB N kA kC ↔ ∃ kB : JKey B, c.KB N kA kB ∧ a.KB N kB kC := by rw [KB]

end ChainA
end IOR

namespace Spec
open IOR

/-- The chain as one link is the chain of the links alone, as one link. -/
def chainA_link : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : ChainA K A B) (d : A.W), (c.linkA d).l = c.forget.link d

def chainA_forget_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : ChainA K A B) (c' : ChainA K B C),
    (c.append c').forget = c.forget.append c'.forget

/-- States: if every link of the chain has `KB`, along some keys, the chain as one link has it. -/
def chainA_kb : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : ChainA K A B) (d : A.W) (N : ℕ) (kA : JKey A) (kB : JKey B),
    c.KB N kA kB → (c.linkA d).KB N kA kB

def chainA_kb_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : ChainA K A B) (c' : ChainA K B C) (N : ℕ) (kA : JKey A)
      (kB : JKey B) (kC : JKey C),
    c.KB N kA kB → c'.KB N kB kC → (c.append c').KB N kA kC

end Spec

open IOR IOR.ChainA

theorem chainA_link : Spec.chainA_link := by
  intro K A B c d
  induction c with
  | one a => rw [linkA_one, forget_one, Chain.link_one]
  | snoc c a ih =>
      rw [linkA_snoc, forget_snoc, Chain.link_snoc, ← ih]
      rfl

theorem chainA_forget_append : Spec.chainA_forget_append := by
  intro K A B C c c'
  induction c' with
  | one a => rw [append_one, forget_snoc, forget_one, Chain.append_one]
  | snoc c' a ih => rw [append_snoc, forget_snoc, forget_snoc, Chain.append_snoc, ih]

theorem chainA_kb : Spec.chainA_kb := by
  intro K A B c d N
  induction c with
  | one a =>
      intro kA kB h
      rw [linkA_one]
      exact (kb_one a N kA kB).1 h
  | snoc c a ih =>
      intro kA kC h
      obtain ⟨kB, h1, h2⟩ := (kb_snoc c a N kA kC).1 h
      rw [linkA_snoc]
      exact ldk_linkB_seq d (ih kA kB h1) h2

theorem chainA_kb_append : Spec.chainA_kb_append := by
  intro K A B C c c' N
  induction c' with
  | one a =>
      intro kA kB kC h h'
      rw [append_one]
      exact (kb_snoc c a N kA kC).2 ⟨kB, h, (kb_one a N kB kC).1 h'⟩
  | snoc c' a ih =>
      intro kA kB kC h h'
      obtain ⟨k, h1, h2⟩ := (kb_snoc c' a N kB kC).1 h'
      rw [append_snoc]
      exact (kb_snoc _ a N kA kC).2 ⟨k, ih kA kB k h h1, h2⟩

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdLinP
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (P : LdLinP E ι κ J Y)
variable (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (S : P.Snd) (εf N : ℕ)

/-- The core of Cb/Ld/LdLinChain.lean, each of its seven links with Cb/Ld/LdLinB.lean's annotation
and errors. The annotation: in `step0` and `sW` each slot runs for itself (the slot sends its own
family with W, at its own seed); from `pt` on all is shared: one shared point; the families of G_u
and Ω are sent by the shared part alone; seeds, locations and ζ are shared. The errors are those for
one instance, but for the shared point's (`P.errPtB εf N`): there the fold's bad points count once,
the instances' N times. -/
def chainA : ChainA Unit (P.J0 on0) P.J6 :=
  ((((((ChainA.one ⟨P.lk0 on0, RoundSplits.allLocal _, ()⟩).snoc
              ⟨P.lkW on0 S, RoundSplits.allLocal _,
                (ldSendFamNums P.NW P.SdW P.X0 P.E0 Unit S.LW S.tW).err⟩).snoc
            ⟨P.lkPt on0 εf, shAnn _, ((P.errPtB εf N, ()) : ℕ × Unit)⟩).snoc
          ⟨P.lkU on0 S, shAnn _, (ldSendFamNums P.NU P.SdU P.X2 P.E1 Unit S.LU S.tU).err⟩).snoc
        ⟨P.lkLoc on0, shAnn _, ((P.errLoc, ()) : ℕ × Unit)⟩).snoc
      ⟨P.lkO S, shAnn _, (ldSendFamNums P.NO P.SdO P.X4 P.E4 Unit S.LO S.tO).err⟩).snoc
    ⟨P.lkZeta, shAnn _, ((P.errZeta, ()) : ℕ × Unit)⟩

/-- The test for at most N instances, with a closing chain. -/
def linCA (cZ : ChainA Unit P.J6 JT) (d : P.W0) : LinkA Unit (P.J0 on0) JT :=
  ((P.chainA on0 S εf N).append cZ).linkA d

/-- the keys at the two ends of the core -/
def key0 : JKey (P.J0 on0) := ⟨_, P.k0⟩
def key6 : JKey P.J6 := ⟨_, P.k6⟩

end LdLinP

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

def ldLinCB_forget : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd),
    (P.chainA on0 S εf N).forget = P.chain on0 S εf

/-- The links of the test for a batch are those of the test. -/
def ldLinCB_same : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd)
      (cZ : ChainA Unit P.J6 LdLinP.JT) (d : P.W0),
    (P.linCA on0 S εf N cZ d).l = P.linC on0 S εf cZ.forget d

def ldLinCB_core : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd),
    P.FoldErr on0 εf → Function.Injective P.D.py → S.OK →
    (P.chainA on0 S εf N).KB N (P.key0 on0) P.key6

/-- States, under the hypotheses below: the test for at most N instances, with any closing chain
that is knowledge sound for the vectors which share what the core makes them share, has `KnowB` for
the vectors that share the encoded index and its record, on the statements with the condition, to
the trivial statement. -/
def ldLinCB_know : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd)
      (cZ : ChainA Unit P.J6 LdLinP.JT) (kT : JKey LdLinP.JT) (d : P.W0),
    P.FoldErr on0 εf → Function.Injective P.D.py → S.OK → cZ.KB N P.key6 kT →
    (P.linCA on0 S εf N cZ d).l.R.KnowB (P.linCA on0 S εf N cZ d).ann N (SameKey P.k0)
      (P.j0 on0).on (P.j0 on0).relR (fun _ (_ : Unit) => True)
      (P.linCA on0 S εf N cZ d).l.ext (P.linCA on0 S εf N cZ d).err

end
end Spec

section
variable {E ι κ J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

theorem ldLinCB_forget : Spec.ldLinCB_forget E ι κ J Y := by
  intro P on0 εf N S
  unfold LdLinP.chainA LdLinP.chain
  simp only [ChainA.forget_snoc, ChainA.forget_one]

theorem ldLinCB_same : Spec.ldLinCB_same E ι κ J Y := by
  intro P on0 εf N S cZ d
  unfold LdLinP.linCA LdLinP.linC
  rw [chainA_link, chainA_forget_append, ldLinCB_forget]

theorem ldLinCB_core : Spec.ldLinCB_core E ι κ J Y := by
  intro P on0 εf N S hF hpy hS
  unfold LdLinP.chainA
  simp only [ChainA.kb_snoc, ChainA.kb_one]
  exact ⟨⟨_, P.k5⟩,
    ⟨⟨_, P.k4⟩,
      ⟨⟨_, P.k3⟩,
        ⟨⟨_, P.k2⟩,
          ⟨⟨_, P.k1⟩, ⟨⟨_, P.k0⟩, P.link0 on0 N, P.linkW on0 N S hS⟩, P.linkPt on0 N εf hF⟩,
          P.linkU on0 N S hS⟩,
        P.linkLoc on0 N⟩,
      P.linkO N S hS⟩,
    P.linkZeta N hpy⟩

theorem ldLinCB_know : Spec.ldLinCB_know E ι κ J Y := by
  intro P on0 εf N S cZ kT d hF hpy hS hZ
  have h := chainA_kb Unit _ _ _ d N _ _
    (chainA_kb_append Unit _ _ _ _ cZ N _ _ kT (ldLinCB_core P on0 εf N S hF hpy hS) hZ)
  exact (knowB_iff_orOff _ _ _ _ _ _ _ _ N _ (P.j0 on0).on (P.j0 on0).relR _ _ _).2 h.know

end
end Cb
