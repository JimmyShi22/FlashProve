-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpTree.lean: the product tree with masked claims and public targets, over oracle messages
with samples: one zero-knowledge sumcheck (a hypothesis (`IOR.GoodB`: `IOR.GoodT` without its clause
on zero knowledge): see `Spec.ldLkp_tree` below) and one line step (stated here, proved in
Cb/Ld/LdLkpTreeProofs.lean) for each level.
This file is about a product argument by a binary tree: a claim on level l is reduced to a claim on
level l + 1 by one sumcheck, which is a parameter here, and one step in which the verifier draws a
point on a line.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpTreeProofs.lean.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

The objects (mathematics: Cb/Gen/GpAlg.lean). 2^g products of 2^n factors each; the factors are one
vector `fac st m`, any function of the public state and of the messages, never sent;
index (b|θ) = b 2^g + θ. Level l of the tree (`Blocks.lvl`) has 2^(l+g) entries; level n is the
factors, level 0 the products.
The levels are virtual: nobody sends them. `ent m`: the entries of the messages that rows and mask
forms may read (masks; entries of short vectors that hold targets), named by a finite set N.
  `Row`: a linear row on the entries with a public target.
  `MCl`: a masked claim on a vector f with 2^k entries: (point, mask form, public target):
    (multilinear extension of f at the point) + (mask form at the entries) = target. The target is
    always public.
  `MCl2`: two masked claims at one point, on the lower and the upper half of a vector.
  `Tree`: the data: g, n, fac, ent; and `more`: what else is claimed of state and messages and rides
    along through all joints (claims that wait for their turn).
  `T.lev l`: the claim at level l, with the rows recorded so far: state (st, masked claim, rows).
  `T.sum l`: the same claim as a sum over the cube of l + g variables, with equality weights at the
    point, of the product of the two halves of level l + 1: the input form of a sumcheck for the
    summand Y₀ Y₁.
  `T.ends l`: two masked claims at one point on the two halves of level l + 1, with the rows
    recorded so far: what such a sumcheck ends with (its two end values, each under a mask of its
    own, are the public targets; its row on the hiding polynomial's coefficients has joined the
    rows).

The blocks. Their statements have two kinds of oracles: the oracle messages of a signature S, each
with its sample (a seed and the answers to it: `OMsg.Smp`, Cb/Ld/LdSig.lean), and further oracles
E₀, which are not sampled (an encoded index, say). A statement has an explicit part, which the
verifier holds, and an implicit part: oracles, which it reads by queries.
A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and of
witness: the honest relation; a second relation, called relaxed, of which round-by-round knowledge
soundness speaks; the set of statements of which that soundness speaks; and a map from a witness to
its core. Here the honest relation is called exact.
Every block stands between two joints `S.over ..`. The relaxed relation of such a joint says "the
messages are the decoding, and the claim holds of them" (the decoding: `S.decs`, Cb/Ld/LdSig.lean).
  `Ms`: M = `Ms S E₀` in the data of a tree: factors and entries may depend on the further oracles.
  `jt2`, `jt`: the joint of a claim, with its condition `on` and a further predicate `hon`. `on` and
    `hon` are the same before and after every block here. `hon` says what else holds on the honest
    side only, of explicit part, further oracles, messages and further witness. It stands in the
    exact relation, not in the relaxed one. It has two uses.
    (1) To say that the further witness accounts for the further oracles. An honest prover is given
        witness and explicit part, not the oracles. If a claim reads further oracles of which the
        witness knows nothing, no honest prover can name a public target, and a hypothesis "this
        block is complete" could not be met.
    (2) To hold what a later block's exact relation will ask and no extractor could give back (say
        that another vector is the multiplicities of another lookup).
    hon = "always" is the plain case.
  `lineR`: the line step: the verifier draws ρ from all of E; no prover message.
  `PscAt`: the data of a block from `T.sum l` to `T.ends l` (reduction, honest side, extractor,
    numbers): the sumcheck is a parameter.

Main names:
  `Spec.ldLkp_lev_iff_sum`: `T.lev l` and `T.sum l` say the same (l < n).
  `Spec.ldLkp_line_fwd`, `Spec.ldLkp_line_cnt`: the line step on vectors, for a fixed tuple of
    messages: true claims stay true at every ρ; if one of the two claims (or a row) is false,
    `T.lev (l + 1)` at the combined claim (`MCl2.line`) holds for at most one ρ.
  `Spec.ldLkp_lev_top`, `Spec.ldLkp_lev_zero`: level n is a masked claim on the factors themselves;
    at g = 0, level 0 says: the product of all factors, plus the mask form, is the target.
  `Spec.ldLkp_line`: the line step is a piece of a chain (`Piece`, Ior/Tail.lean) from `T.ends l` to
    `T.lev (l + 1)`: one round, error 1 (of the |E| values of ρ: a number, not a probability),
    perfectly complete, nothing to simulate, the identity extracts.
  `Spec.ldLkp_tree`: the tree: for n ≥ 1 (`T.n = n' + 1`): if for every level l < n the given block
    leads from `T.sum l` to `T.ends l` (`IOR.GoodB`: `IOR.GoodT` without its clause on zero
    knowledge), then the tree leads from `T.lev 0` to `T.lev T.n`. Errors: the blocks' errors and a
    1 for each level, in a row. `GoodB` is `IOR.GoodT` without its clause on zero knowledge. Here it
    is the hypothesis (on each level's block) and the conclusion (on the tree).
  `Spec.ldLkp_tree_rounds`: its rounds: the sum over the levels of (rounds of the sumcheck + 1).
    Nothing is merged.

Notation: `St`: the type of the public state; `Wp`: the type of the further witness; `p l`: the data
of a block (`PscAt`), used at level l; `d`: a value of `S.Wit × Wp`, the last argument of
`IOR.extSeq` in `level` and the second of `Bk.chain` in `tree`; `q`: a predicate on finite sets of
positions of the oracles (the arguments `qi`, `qo` of `Piece`).

Limits: what is declared on notation and choices: (a) A point is listed with the coordinate of the
top bit first: the line step puts ρ in front, (ρ | point), and the two halves of a vector are its
entries X and X + 2^k. A text or a program that lists the lowest bit first has the same points in
reverse order.
(b) The g bits that name the tree are the low bits of the index at every level: a choice of this
file.
(c) Collision-free (`S.CF`, in `on` of `S.over`: Cb/Ld/LdSig.lean) is handed on; it is not used
(the line step: `Spec.sig_draw`, Cb/Ld/LdLkpChain.lean).
This file says nothing on the sumcheck itself: that a block with the properties asked exists is
another file's matter.
Zero knowledge is not in the bundle (`GoodB`): the masks are sent in advance, inside oracle messages
of S, and zero knowledge is a property of a whole chain (Ior/Masked.lean).
That each mask entry is used once is not enforced here.
ρ is drawn from all of E.
Forests whose trees share rounds are the case g > 0; the point of g coordinates with which level 0
starts (a zerocheck) is not part of the tree.
The tree with one sumcheck and one line step a level is the field's; masked claims with public
targets follow advice (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpChain
import Cb.Gen.GpAlg
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.LdLkp
open Blocks Finset Cb.Gp Iop IOR

/-- A linear row with a public target. -/
structure Row (E N : Type) where
  cf : N → E
  tg : E

/-- A masked claim: point, mask form, public target. -/
structure MCl (E N : Type) where
  pt : ℕ → E
  mf : N → E
  tg : E

/-- Two masked claims at one point. -/
structure MCl2 (E N : Type) where
  pt  : ℕ → E
  mf₀ : N → E
  tg₀ : E
  mf₁ : N → E
  tg₁ : E

section
variable {E N : Type} [Field E]

def Row.Holds [Fintype N] (r : Row E N) (μ : N → E) : Prop := ∑ i, r.cf i * μ i = r.tg

def RowsHold [Fintype N] (rs : List (Row E N)) (μ : N → E) : Prop := ∀ r ∈ rs, r.Holds μ

/-- The claim holds of the vector f with 2^k entries, at the entries μ. -/
def MCl.Holds [Fintype N] (c : MCl E N) (k : ℕ) (f : ℕ → E) (μ : N → E) : Prop :=
  ext k f c.pt + ∑ i, c.mf i * μ i = c.tg

/-- The line step on claims. -/
def MCl2.line (c : MCl2 E N) (ρ : E) : MCl E N :=
  ⟨consPt ρ c.pt, fun i => (1 - ρ) * c.mf₀ i + ρ * c.mf₁ i, (1 - ρ) * c.tg₀ + ρ * c.tg₁⟩

end

/-- The data of a product tree. -/
structure Tree (E St M N : Type) where
  g   : ℕ
  n   : ℕ
  fac : St → M → ℕ → E
  ent : M → N → E
  /-- What else is claimed, and rides along. -/
  more : St → M → Prop

/-- The explicit parts: at a level; after a sumcheck. -/
abbrev TX (St E N : Type) : Type := St × MCl E N × List (Row E N)
abbrev EX (St E N : Type) : Type := St × MCl2 E N × List (Row E N)

/-- The line step on explicit parts. -/
def lineNx {St E N : Type} [Field E] : EX St E N → E → TX St E N := fun x ρ =>
  (x.1, x.2.1.line ρ, x.2.2)

namespace Tree
variable {E St M N : Type} [Field E] [Fintype N] (T : Tree E St M N)

/-- The claim at level l. -/
def lev (l : ℕ) : TX St E N → M → Prop := fun x m =>
  x.2.1.Holds (l + T.g) (lvl T.g T.n (T.fac x.1 m) l) (T.ent m) ∧
  RowsHold x.2.2 (T.ent m) ∧
  T.more x.1 m

/-- The same as a sum of products of the two halves of the next level. (for l < `T.n`:
`Spec.ldLkp_lev_iff_sum`) -/
def sum (l : ℕ) : TX St E N → M → Prop := fun x m =>
  (∑ X ∈ range (2 ^ (l + T.g)), eqN (l + T.g) 0 x.2.1.pt X *
        (lvl T.g T.n (T.fac x.1 m) (l + 1) X *
          up (l + T.g) (lvl T.g T.n (T.fac x.1 m) (l + 1)) X)) +
      ∑ i, x.2.1.mf i * T.ent m i = x.2.1.tg ∧
  RowsHold x.2.2 (T.ent m) ∧
  T.more x.1 m

/-- Two claims on the halves of level l + 1. -/
def ends (l : ℕ) : EX St E N → M → Prop := fun x m =>
  ext (l + T.g) (lvl T.g T.n (T.fac x.1 m) (l + 1)) x.2.1.pt + ∑ i, x.2.1.mf₀ i * T.ent m i =
    x.2.1.tg₀ ∧
  ext (l + T.g) (up (l + T.g) (lvl T.g T.n (T.fac x.1 m) (l + 1))) x.2.1.pt +
      ∑ i, x.2.1.mf₁ i * T.ent m i = x.2.1.tg₁ ∧
  RowsHold x.2.2 (T.ent m) ∧ T.more x.1 m

end Tree

/-! ## The blocks, over a signature -/

section Blocks
variable {E : Type} [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (St N Wp : Type)

/-- The oracles of all statements here: further oracles, which are not sampled, and the words of S.
-/
abbrev Ex : ExtSpec := E₀.prod S.ext

/-- What a claim reads beside the explicit part: the further oracles and the messages. -/
abbrev Ms : Type := E₀.Str × S.Msg

/-- The joint of a claim: exact form P, relaxed form PR; a condition `on` on explicit part and
further oracles; and `hon`: what else holds on the honest side only. -/
@[reducible] def jt2 {X : Type} (on : X × E₀.Str → Prop)
    (hon : X → Ms S E₀ → Wp → Prop) (P PR : X → Ms S E₀ → Prop) :
    Rels Unit (X × S.Smp) (Ex S E₀) (S.Wit × Wp) :=
  S.over ⟨fun x y w => P x (y, w.1) ∧ hon x (y, w.1) w.2,
    fun a w => PR a.1 (a.2, w.1), on, fun _ => ()⟩

/-- The same with one form of the claim. -/
@[reducible] def jt {X : Type} (on : X × E₀.Str → Prop)
    (hon : X → Ms S E₀ → Wp → Prop) (P : X → Ms S E₀ → Prop) :
    Rels Unit (X × S.Smp) (Ex S E₀) (S.Wit × Wp) :=
  jt2 S E₀ Wp on hon P P

variable {E₀ St} in
/-- A condition on (state, further oracles), read at an explicit part that begins with the state. -/
def onFst {Z : Type} (on : St × E₀.Str → Prop) : (St × Z) × E₀.Str → Prop := fun a =>
  on (a.1.1, a.2)

variable {S E₀ St Wp} in
/-- The same for what holds on the honest side only. -/
def honFst {Z : Type} (hon : St → Ms S E₀ → Wp → Prop) : St × Z → Ms S E₀ → Wp → Prop :=
  fun x ms wp => hon x.1 ms wp

/-- The line step. -/
abbrev lineR : IOR (EX St E N × S.Smp) (Ex S E₀) (TX St E N × S.Smp) (Ex S E₀) :=
  IOR.draw E (S.drawNx lineNx) (Ex S E₀)
abbrev lineH : (lineR S E₀ St N).Honest (S.Wit × Wp) (S.Wit × Wp) :=
  Honest.draw E (S.drawNx lineNx) (Ex S E₀) (S.Wit × Wp)
abbrev lineP : Nums Unit (lineR S E₀ St N) := Nums.draw Unit E (S.drawNx lineNx) (Ex S E₀) 1

/-- The data of a block from the sum at a level to the two end claims: the sumcheck, a parameter. -/
structure PscAt where
  R   : IOR (TX St E N × S.Smp) (Ex S E₀) (EX St E N × S.Smp) (Ex S E₀)
  H   : R.Honest (S.Wit × Wp) (S.Wit × Wp)
  ext : (TX St E N × S.Smp) × (Ex S E₀).Str → Tr R.shape → S.Wit × Wp → S.Wit × Wp
  P   : Nums Unit R

variable {S E₀ St N Wp}

/-- One level: the sumcheck, then the line step. -/
def level (p : PscAt S E₀ St N Wp) (d : S.Wit × Wp) :
    Bk Unit (TX St E N × S.Smp) (Ex S E₀) (S.Wit × Wp) :=
  ⟨p.R.seq (lineR S E₀ St N),
    p.H.seq (lineH S E₀ St N Wp),
    IOR.extSeq p.R (lineR S E₀ St N) p.ext (fun _ _ w => w) d,
    p.P.seq (lineP S E₀ St N)⟩

/-- The tree: the levels 0, .., n' in a row. -/
def tree (p : ℕ → PscAt S E₀ St N Wp) (d : S.Wit × Wp) (n' : ℕ) :
    Bk Unit (TX St E N × S.Smp) (Ex S E₀) (S.Wit × Wp) :=
  Bk.chain (fun l => level (p l) d) d n'

end Blocks
end Cb.LdLkp

namespace Cb.Spec
open Blocks Finset Prob Cb.Gp Cb.LdLkp Iop IOR

def ldLkp_lev_iff_sum : Prop :=
  ∀ (E St M N : Type) [Field E] [Fintype N] (T : Tree E St M N) (l : ℕ) (x : TX St E N) (m : M),
    l < T.n → (T.lev l x m ↔ T.sum l x m)

def ldLkp_line_fwd : Prop :=
  ∀ (E St M N : Type) [Field E] [Fintype N] (T : Tree E St M N) (l : ℕ)
      (x : EX St E N) (m : M) (ρ : E),
    T.ends l x m → T.lev (l + 1) (lineNx x ρ) m

/-- The line step, for a fixed tuple of messages: at most one bad ρ. -/
def ldLkp_line_cnt : Prop :=
  ∀ (E St M N : Type) [Field E] [Fintype E] [Fintype N] (T : Tree E St M N) (l : ℕ)
      (x : EX St E N) (m : M),
    cnt (fun ρ : E => T.lev (l + 1) (lineNx x ρ) m ∧ ¬ T.ends l x m) ≤ 1

def ldLkp_lev_top : Prop :=
  ∀ (E St M N : Type) [Field E] [Fintype N] (T : Tree E St M N) (x : TX St E N) (m : M),
    T.lev T.n x m ↔
    x.2.1.Holds (T.n + T.g) (T.fac x.1 m) (T.ent m) ∧ RowsHold x.2.2 (T.ent m) ∧ T.more x.1 m

def ldLkp_lev_zero : Prop :=
  ∀ (E St M N : Type) [Field E] [Fintype N] (T : Tree E St M N) (x : TX St E N) (m : M), T.g = 0 →
    (T.lev 0 x m ↔
      (∏ b ∈ range (2 ^ T.n), T.fac x.1 m b) + ∑ i, x.2.1.mf i * T.ent m i = x.2.1.tg ∧
      RowsHold x.2.2 (T.ent m) ∧
      T.more x.1 m)

/-- The line step is a piece of a chain. -/
def ldLkp_line : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (St N Wp : Type) [Fintype N]
      (T : Tree E St (Ms S E₀) N) (on : St × E₀.Str → Prop) (hon : St → Ms S E₀ → Wp → Prop)
      (l : ℕ) (q : Finset (Ex S E₀).Pos → Prop),
    Piece (lineR S E₀ St N) (lineH S E₀ St N Wp) (jt S E₀ Wp (onFst on) (honFst hon) (T.ends l))
      (jt S E₀ Wp (onFst on) (honFst hon) (T.lev (l + 1))) (fun _ _ w => w) (lineP S E₀ St N) q q

/-- The tree. States: under the hypotheses below, the tree leads (`Bk.GoodB`, Cb/Ld/LdLkpChain.lean)
from `T.lev 0` to `T.lev T.n`. -/
def ldLkp_tree : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (St N Wp : Type) [Fintype N]
      (T : Tree E St (Ms S E₀) N) (on : St × E₀.Str → Prop) (hon : St → Ms S E₀ → Wp → Prop)
      (p : ℕ → PscAt S E₀ St N Wp) (d : S.Wit × Wp) (n' : ℕ),
    T.n = n' + 1 →
    (∀ l ≤ n',
      GoodB (p l).R (p l).H (jt S E₀ Wp (onFst on) (honFst hon) (T.sum l))
        (jt S E₀ Wp (onFst on) (honFst hon) (T.ends l)) (p l).ext (p l).P) →
    (tree p d n').GoodB (jt S E₀ Wp (onFst on) (honFst hon) (T.lev 0))
      (jt S E₀ Wp (onFst on) (honFst hon) (T.lev T.n))

def ldLkp_tree_rounds : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (St N Wp : Type)
      (p : ℕ → PscAt S E₀ St N Wp) (d : S.Wit × Wp) (n' : ℕ),
    (tree p d n').R.shape.length = ∑ l ∈ range (n' + 1), ((p l).R.shape.length + 1)

end Cb.Spec
