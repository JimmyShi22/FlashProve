-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLink.lean: the link, an interactive oracle reduction for the claim that two oracles, each a
table of words (one linear code for both), decode to messages that agree on a fixed set of
coordinates. The radii may lie beyond unique decoding: each oracle is decoded with a sample (its
record).

Definitions and statements; the proofs are in Cb/Ld/LdLinkProofs.lean. The mathematics on plain
vectors is in Cb/Ld/LdLinkWords.lean and Cb/Ld/LdFoldEq.lean.
Encoded index, record, fold: the head of Cb/Ld/LdLinkWords.lean.

The statement. Explicit part: the two records (rec₀, rec₁). Oracles: the two encoded indices, of one
format. Neither is an oracle message: they are never closed, their samples lie outside, and they are
decoded by the statement, each with its own record.
  exact relation (`j0.rel`): each index is the table of the codewords of the witness's full
    messages, which have its record's answers; the two message parts agree on the layout (pads may
    differ).
  relaxed relation (`j0.relR`): both indices decode, each with its record, and what they decode to
    agrees on the layout. The witness is not read: nothing is extracted.
  conditions (`on0`, `on1`): parameters. In the use in view (`Spec.ldLk_foldErr`) `on0` says that
    the first index decodes, and `on1` that the further one has no collision at its record's seed.
    All that the chain uses of them is `P.FoldErr`: where `on0` holds, at most ε₀ points γ are bad
    for the fold of the first at the radius e₀; where `on1` holds, at most ε₁ for the fold of the
    further one at e₁.

The chain. Nothing is merged. In each row: the prover's message | the verifier's.
  `gam`, one round: nothing | γ. Nothing is read. The honest prover computes u₀, u₁: the folds at γ
    of the full messages of the rows.
  `snd`, two rounds: sending, in one prover message, of a family N of oracle messages with two named
    members G_u0 and G_u1, which hold u₀ and u₁ whole (message part, the index's folded pads, folded
    encoding randomness) at the places l₀, l₁; in the use in view their own pads are fresh | one
    joint seed; then all answers | nothing. The messages of the other members of N are free in all
    relations: they are what a closing may use (mask-only messages for its splittings); in the use
    in view the honest sender draws them from its coins. With no other member: the two oracle
    messages alone. The sender (`S.dS`) is a parameter; what is asked of it is `Snd.OK`.
  `loc`, one round: nothing | one verifier message (Q₀, Q₁): t₀ locations of the first index, t₁ of
    the further one. The verifier reads these columns, folds each at γ and keeps the folds.
  `phi`, one round: nothing | φ.
  T, the closing: any block from the joint `j4` to the trivial statement. A parameter; what is asked
    of it is `TailTr`.

The joints. `j1` (after γ): further witnesses u₀, u₁, full messages of one row. Relaxed, existential
on the two folded words: the codeword of u₀ is within e₀ positions of the fold of the first index,
that of u₁ within e₁ of the fold of the further one; each meets its record's row; u₀ and u₁ agree on
the layout. The tables are not read.
  `j2` = the joint over the family of the two oracle messages (`Sig.over`, Cb/Ld/LdSig.lean): all
    members decode with their samples to the witness's messages, and `j1` of what these hold.
  `j3` (after the locations): "within e₀, e₁" is replaced by: the codewords of u₀, u₁ have at the
    drawn locations the folds read.
  `j4` (after φ): the rows that are left: the record's row of each on its own fold, the values at
    the locations of each, and one equality row, restricted to the layout. All targets are public:
    0, functions of records and verifier messages, folds of symbols read. No row but the equality
    row couples u₀ and u₁. No row couples the two inputs before the sending.

The errors, counts of values of one verifier message (q = |E|, n = number of positions of an index):
  γ: ε₀ + ε₁ + v·q^(v-1) (`errGam`).
  joint seed: that of the sending: the sum over the members of mult · (L choose 2) · err.
  (Q₀, Q₁): the larger of (n - e₀ - 1)^t₀ · n^t₁ and n^t₀ · (n - e₁ - 1)^t₁ (`errLoc`): which of the
    two folds is far is fixed before the locations are drawn.
  φ: l·q^(l-1) (`errPhi`).
Here v is the number of row variables (`LdIx.v`, Cb/Ld/LdFoldEq.lean) and l the number of
coordinates of φ (`LdLkW.l`, Cb/Ld/LdLinkWords.lean). Of a member a of the family: `Seeds.Fair`
(Cb/Ld/LdSendFam.lean) asks that a seed of a comes from at most `mult a` joint seeds; `L a` is the
bound on its list that `Snd.OK` asks; err is the number of seeds at which a vector other than 0 may
have all answers 0 (`Sample.err`, Cb/Gen/OodDec.lean: a field, any number; of it `Snd.OK` asks
`OMsg.Evades`, Cb/Ld/LdSig.lean). eM, below, is the radius of decoding, in columns (`LdIx.eM`).

Main names. Wherever `loc` occurs (`Spec.ldLk_shape`, `Spec.ldLk_loc`, `Spec.ldLk_core` to
`Spec.ldLk_end`) ι is not empty. "The four" are the premises `P.FoldErr on0 on1 ε₀ ε₁`, `P.D.pl`
injective, `S.OK`, and `TailTr` of the closing from `j4.cf`, within `P.q3 S`. `Rels.cf`
(Ior/KnowCollGood.lean) is a joint in the form whose condition may fail.
  `Spec.ldLk_tail`: under the four, the link with a closing is a tail from `j0` to the trivial
    statement.
  `Spec.ldLk_know`: under the four, what a list of sub-protocols asks (`LinkKnowR`,
    Hiop/RecSubs.lean): knowledge soundness on the statements with the conditions, nothing
    extracted.
  `Spec.ldLk_end`: under the four: the other items of such a list (`LinkListR`, Hiop/RecSubs.lean):
    strings, local, perfectly complete outside a public set, nothing withheld in this sense:
    `∀ w x, (P.hLink S Z).Hid w x = ∅` (`Honest.withheld`: Ior/Honest.lean; of `Bad` the statement
    has `prRho (P.hLink S Z).Bad ≤ (P.numsLink S Z ε₀ ε₁).pBad`), honest-verifier exact zero
    knowledge of the verifier's view, tied, at most t₀ and t₁ positions read.
    In that list: strings: all rounds are point rounds (`Shape.IsPoint`, Iop/Shape.lean; a point
    round, `Round.IsPoint`: its oracle part is a string that is read symbol by symbol, over a finite
    set of positions). Local: the verifier's output and the symbols of the new implicit instance
    depend on the oracles only at the positions declared (`IOR.IsLocal`, Ior/Ior.lean). Tied, here a
    conclusion (`IOR.Tied`, Ior/Batch.lean): `R.Tied`: for every ρ and every position p that the
    verifier reads in the prover's oracles, `R.tie ρ p` lies within the positions that the verifier
    reads in the implicit instance.
  `P.FoldErr` comes from the fold lemma (Cb/Ld/LdFoldEq.lean: `Spec.ldFe_cnt`, the first regime;
    `Spec.ldFe_none`, the second) in two pairings, each under the hypotheses of its statement (a
    distance, the radii against eM, agreement and lists at the radii): `Spec.ldLk_foldErr_rec` is
    the general case, with records: neither index has a collision at its record's seed; in
    `Spec.ldLk_foldErr` the first index decodes and e₀ + eM is below the distance: no bad point; the
    further one by the first regime. That an index decodes does not by itself exclude a collision:
    the condition is what each pairing names.

Why. The bad event of the folds stands where it does in Cb/Ld/LdLin.lean. A note of ours that is not
in this repository keeps "γ is bad" as a disjunct of the state from the round of γ up to the draw of
locations. Here the relaxed relation between these two rounds is existential on the two folded words
(`j1`, `j2`), the bad γ are charged in the round of γ, and no condition has to be carried: the same
errors in the same rounds, the same relations at both ends. The note's sentence that the existential
form of a relaxation occurs only between a batching and the end of a test on a group is therefore
not kept to the letter.
The rounds agree with the note's count of all rounds: 1 + 2 + 1 + 1 = 5 before the closing, of which
four have a verifier message that is not empty.

A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and of
witness: the honest relation; a second relation, called relaxed, of which round-by-round knowledge
soundness speaks; the set of statements of which that soundness speaks; and a map from a witness to
its core. The fields, in this order: `rel`, `relR`, `on`, `core`; in this file `core` maps into
`Unit` (`core := fun _ => ()`). `PieceTr`, a piece of a chain, asks of a reduction between two
joints the bundle `IOR.GoodT` and three further clauses, `noHid`, `noTie` and `bears`, which
Cb/Ld/LdTowerKit.lean states (`bears` through `IOR.Bears`, Ior/Bears.lean); `IOR.Piece`
(Ior/Tail.lean) asks the same over `IOR.Good`. `TailTr`, a tail of a chain, asks of a reduction from
a joint to a joint whose statements have no oracles the bundle `IOR.GoodT` and three further
clauses, `noHid`, `tied` and `bears`, which Cb/Ld/LdTowerKit.lean states (through `IOR.Tied`,
Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean). `IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean)
bundles what is asked of one reduction, with its honest side, between two joints, at given numbers;
among its clauses: completeness between the honest relations, outside sets of verifier randomness
whose probabilities further clauses bound by the numbers; round-by-round knowledge soundness
(`Know`) between the relaxed relations, on the input joint's set of statements, with a given
extractor, at the numbers' list of errors; and one on honest-verifier zero knowledge.

Limits:
No closing is given (one as a chain, for `P.linkC`, with no splitting: `K.cZ d`, `Spec.ldLkC_tail`,
Cb/Ld/LdLinkClose.lean; its test `K.T` is a field there). This file says no bound on lists, on bad
points of a fold, on samples (`Spec.ldLk_foldErr_rec`, `Spec.ldLk_foldErr` bound the bad points of a
fold from bounds on agreement and lists, which are premises). It does not say that agreement on the
layout means "the same index": that is a law of the configuration. It says nothing on running times.
What `Spec.ldLk_tail` reaches: closings that are exactly zero knowledge by themselves, so closings
that send every mask which they use. It does not reach a closing whose splittings use mask-only
messages sent in the core (with G_u0, G_u1), as a write-up of ours (lean/CREDITS.md) has
it: such a closing is not zero knowledge by itself (Ior/Masked.lean: `masked_not_exact`, proved of
one masked block, under its premises; the step to such a closing is an argument in words).
For that form the link is defined on chains: Cb/Ld/LdLinkChain.lean.
Declared: the equality row reads the layout only (the support is a parameter: Λ, `lay`). The
write-up compares all entries of the message outside the pad, and asks for completeness
that the two prover encoded indices hold the same index and zeros outside layout and pad. The row
here is sound, complete without that law of the committer, and reads less. It is sound if `P.D.pl`
is injective (`Spec.ldLk_phi`). The write-up's form is the instance "Λ := all entries that
are no pad, lay := the identity" of this file: `j0`'s exact relation then asks agreement there,
which that law implies; over the configuration: head of Cb/Obj/LdObjectLink.lean.



Declared differences to that note. (1) The members of the family are free (any codes, samples,
radii); the note puts G_u0 and G_u1 into one group of one code, with one closing test: wider here.
(2) Zero knowledge in our exact form. (3) The witness of a relaxed relation has the type of
the exact one; its tables and encoding randomness are not read. (4) How the members read their seeds
off the joint seed is the sending's parameter; the note has one joint seed for the oracle messages
of one prover message, one answer for each, and errors that add over the members. (5) Both indices
have one format (one code, one sample map, one radius of decoding); the radii e₀, e₁ and the numbers
t₀, t₁ of locations may differ.
Terms: lean/GLOSSARY.md.
The link follows this protocol's technical report, which follows the work that this protocol builds
on (lean/CREDITS.md, "Further work").
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLinkWords
import Cb.Ld.LdLinKit
import Cb.Ld.LdSendFam
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

/-- The link: the data. -/
structure LdLkP (E ι κ J Λ : Type) where
  /-- the format of both indices, the layout -/
  D  : LdLkW E ι κ J Λ
  /-- a symbol (a column) of an encoded index as sent, and how it is read over E -/
  Sy : Type
  up : Sy → D.X.Row → E
  /-- the radii at which the two folds are tested; the numbers of locations -/
  e₀ : ℕ
  e₁ : ℕ
  t₀ : ℕ
  t₁ : ℕ
  /-- the family of oracle messages that is sent in one prover message; its two named members G_u0,
  G_u1, and where u₀, u₁ are in their messages -/
  N  : Sig E
  i₀ : N.O
  l₀ : κ → (N.om i₀).C.J
  i₁ : N.O
  l₁ : κ → (N.om i₁).C.J

namespace LdLkP
variable {E ι κ J Λ : Type} (P : LdLkP E ι κ J Λ)

/-- An encoded index as an oracle: a symbol is a column. -/
abbrev ix : ExtSpec := ⟨ι → P.Sy, ι, P.Sy, fun f j => f j⟩
/-- An encoded index as a table over E. -/
def tab (f : ι → P.Sy) : P.D.X.Row → ι → E := fun r j => P.up (f j) r
/-- Tables of full messages. -/
abbrev IxW : Type := P.D.X.Row → κ → E

/-! ### The types of the joints -/

abbrev Gam : Type := Fin P.D.X.v → E
abbrev X0 : Type := P.D.X.Rec × P.D.X.Rec
abbrev E0 : ExtSpec := P.ix.prod P.ix
abbrev W0 : Type := P.IxW × P.IxW
abbrev X1 : Type := P.X0 × P.Gam
abbrev W1 : Type := ((κ → E) × (κ → E)) × P.W0
abbrev X2 : Type := P.X1 × P.N.Smp
abbrev E2 : ExtSpec := P.E0.prod P.N.ext
abbrev W2 : Type := P.N.Wit × P.W0
/-- Drawn locations, and the folds of the columns read. -/
abbrev Loc (t : ℕ) : Type := (Fin t → ι) × (Fin t → E)
abbrev X3 : Type := P.X2 × (Loc (ι := ι) (E := E) P.t₀ × Loc (ι := ι) (E := E) P.t₁)
abbrev E3 : ExtSpec := P.N.ext
abbrev X4 : Type := P.X3 × (Fin P.D.l → E)

/-- The vectors that the messages of the two oracle messages hold. -/
def uv₀ (m : P.N.Msg) : κ → E := fun k => m P.i₀ (P.l₀ k)
def uv₁ (m : P.N.Msg) : κ → E := fun k => m P.i₁ (P.l₁ k)

def back (m : P.N.Msg) (w : P.W0) : P.W1 := ((P.uv₀ m, P.uv₁ m), w)

variable [Field E] [Fintype ι] [Fintype κ]

/-- The codeword of u has the values `lc.2` at the drawn locations `lc.1`. -/
def ColT {t : ℕ} (lc : Loc (ι := ι) (E := E) t) (u : κ → E) : Prop :=
  ∀ i, P.D.X.G.mulVec u (lc.1 i) = lc.2 i

variable [Fintype J]

/-- All that the chain uses of the conditions on the two indices. -/
def FoldErr [Finite E] (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (ε₀ ε₁ : ℕ) : Prop :=
  (∀ f rec, on0 f rec → cnt (P.D.X.Bad f rec P.e₀) ≤ ε₀) ∧
  ∀ f rec, on1 f rec → cnt (P.D.X.Bad f rec P.e₁) ≤ ε₁

/-! ### The joints -/

variable (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)

/-- The input joint. -/
def j0 : IOR.Rels Unit P.X0 P.E0 P.W0 where
  rel  := fun x y w =>
    (P.tab y.1 = (fun r => P.D.X.G.mulVec (w.1 r)) ∧ P.D.X.HasRec x.1 w.1) ∧
    (P.tab y.2 = (fun r => P.D.X.G.mulVec (w.2 r)) ∧ P.D.X.HasRec x.2 w.2) ∧
    P.D.SameOn (P.D.X.view w.1) (P.D.X.view w.2)
  relR := fun a _ =>
    ∃ U₀ U₁,
      P.D.X.dec (P.tab a.2.1) a.1.1 = some U₀ ∧
      P.D.X.dec (P.tab a.2.2) a.1.2 = some U₁ ∧
      P.D.SameOn U₀ U₁
  on   := fun a => on0 (P.tab a.2.1) a.1.1 ∧ on1 (P.tab a.2.2) a.1.2
  core := fun _ => ()

/-- After γ. -/
def j1 : IOR.Rels Unit P.X1 P.E0 P.W1 where
  rel  := fun x y w =>
    (P.j0 on0 on1).rel x.1 y w.2 ∧ w.1.1 = foldAll x.2 w.2.1 ∧ w.1.2 = foldAll x.2 w.2.2
  relR := fun a w =>
    (P.D.X.NearW P.e₀ (foldAll a.1.2 (P.tab a.2.1)) w.1.1 ∧ P.D.X.RecRow a.1.1.1 a.1.2 w.1.1) ∧
    (P.D.X.NearW P.e₁ (foldAll a.1.2 (P.tab a.2.2)) w.1.2 ∧ P.D.X.RecRow a.1.1.2 a.1.2 w.1.2) ∧
    P.D.layV w.1.1 = P.D.layV w.1.2
  on   := fun a => (P.j0 on0 on1).on (a.1.1, a.2)
  core := fun _ => ()

/-- After the sending of G_u0 and G_u1. -/
def j2 : IOR.Rels Unit P.X2 P.E2 P.W2 := P.N.over (P.N.pull (P.j1 on0 on1) P.back)

/-- After the locations: the two indices are gone. -/
def j3 : IOR.Rels Unit P.X3 P.E3 P.W2 where
  rel  := fun x y w =>
    P.N.Enc y w.1 ∧
    P.N.Ans x.1.2 (P.N.msgs w.1) ∧
    P.D.X.HasRec x.1.1.1.1 w.2.1 ∧
    P.D.X.HasRec x.1.1.1.2 w.2.2 ∧
    P.D.SameOn (P.D.X.view w.2.1) (P.D.X.view w.2.2) ∧
    P.uv₀ (P.N.msgs w.1) = foldAll x.1.1.2 w.2.1 ∧
    P.uv₁ (P.N.msgs w.1) = foldAll x.1.1.2 w.2.2 ∧
    P.ColT x.2.1 (P.uv₀ (P.N.msgs w.1)) ∧
    P.ColT x.2.2 (P.uv₁ (P.N.msgs w.1))
  relR := fun a w =>
    (∀ i, P.N.decs a.1.1.2 a.2 i = some (w.1 i).1) ∧
    (P.D.X.RecRow a.1.1.1.1.1 a.1.1.1.2 (P.uv₀ (P.N.msgs w.1)) ∧
      P.ColT a.1.2.1 (P.uv₀ (P.N.msgs w.1))) ∧
    (P.D.X.RecRow a.1.1.1.1.2 a.1.1.1.2 (P.uv₁ (P.N.msgs w.1)) ∧
      P.ColT a.1.2.2 (P.uv₁ (P.N.msgs w.1))) ∧
    P.D.layV (P.uv₀ (P.N.msgs w.1)) = P.D.layV (P.uv₁ (P.N.msgs w.1))
  on   := fun a => P.N.CF a.1.1.2 a.2
  core := fun _ => ()

variable [Fintype Λ]

/-- The rows that are left, on the vectors (u₀, u₁). -/
def Rows (x : P.X4) (u₀ u₁ : κ → E) : Prop :=
  (P.D.X.RecRow x.1.1.1.1.1 x.1.1.1.2 u₀ ∧ P.ColT x.1.2.1 u₀) ∧
  (P.D.X.RecRow x.1.1.1.1.2 x.1.1.1.2 u₁ ∧ P.ColT x.1.2.2 u₁) ∧
  P.D.EqRow x.2 u₀ u₁

/-- The last joint: what the closing has to test. -/
def j4 : IOR.Rels Unit P.X4 P.E3 P.W2 where
  rel  := fun x y w => P.j3.rel x.1 y w
  relR := fun a w =>
    (∀ i, P.N.decs a.1.1.1.2 a.2 i = some (w.1 i).1) ∧
    P.Rows a.1 (P.uv₀ (P.N.msgs w.1)) (P.uv₁ (P.N.msgs w.1))
  on   := fun a => P.j3.on (a.1.1, a.2)
  core := fun _ => ()

/-! ### The blocks of this file -/

variable [Fintype E]

omit [Fintype ι] [Fintype κ] [Fintype J] [Fintype Λ] in
/-- `gam`: the verifier draws γ and reads nothing. -/
def vGam : IOR.PeekV P.X0 P.E0 P.X1 P.E0 :=
  { D := P.Gam, rd := fun _ => ∅, out := fun x c _ => (x, c), g := ExtMap.id _ }
def gam : IOR P.X0 P.E0 P.X1 P.E0 := IOR.peek P.vGam
def hGam : P.gam.Honest P.W0 P.W1 :=
  IOR.Honest.peek P.vGam (fun x _ c => (x, c)) fun _ w c => ((foldAll c w.1, foldAll c w.2), w)

/-- The fold at γ of a symbol read in the first, in the further index. -/
def foldSym₀ (γ : P.Gam) : Option P.E2.Sym → E
  | some (.inl (.inl s)) => ∑ r, Alg.eqk γ r * P.up s r
  | _ => 0
def foldSym₁ (γ : P.Gam) : Option P.E2.Sym → E
  | some (.inl (.inr s)) => ∑ r, Alg.eqk γ r * P.up s r
  | _ => 0

/-- Both indices are dropped. -/
def dropIx : ExtMap P.E2 P.E3 where
  map y := y.2
  src q := {.inr q}

variable [Nonempty ι]

open Classical in
/-- `loc`: the two lists of locations, in one verifier message. -/
def vLoc : IOR.PeekV P.X2 P.E2 P.X3 P.E3 where
  D := (Fin P.t₀ → ι) × (Fin P.t₁ → ι)
  rd Q := (Finset.univ.image fun i => .inl (.inl (Q.1 i))) ∪
    Finset.univ.image fun i => .inl (.inr (Q.2 i))
  out x Q ans := (x,
    ((Q.1, fun i => P.foldSym₀ x.1.2 (ans (.inl (.inl (Q.1 i))))),
      (Q.2, fun i => P.foldSym₁ x.1.2 (ans (.inl (.inr (Q.2 i)))))))
  g := P.dropIx
def loc : IOR P.X2 P.E2 P.X3 P.E3 := IOR.peek P.vLoc
def hLoc : P.loc.Honest P.W2 P.W2 :=
  IOR.Honest.peek P.vLoc
    (fun x w Q =>
      (x, ((Q.1, fun i => P.D.X.G.mulVec (foldAll x.1.2 w.2.1) (Q.1 i)),
          (Q.2, fun i => P.D.X.G.mulVec (foldAll x.1.2 w.2.2) (Q.2 i))))) fun _ w _ => w

omit [Nonempty ι] in
/-- `phi`: the verifier draws φ and reads nothing. -/
def vPhi : IOR.PeekV P.X3 P.E3 P.X4 P.E3 :=
  { D := Fin P.D.l → E, rd := fun _ => ∅, out := fun x c _ => (x, c), g := ExtMap.id _ }
def phi : IOR P.X3 P.E3 P.X4 P.E3 := IOR.peek P.vPhi
def hPhi : P.phi.Honest P.W2 P.W2 := IOR.Honest.peek P.vPhi (fun x _ c => (x, c)) fun _ w _ => w

/-- The three errors of this file's rounds. -/
def errGam (ε₀ ε₁ : ℕ) : ℕ := ε₀ + ε₁ + P.D.X.v * Fintype.card E ^ (P.D.X.v - 1)
def errLoc : ℕ :=
  max ((Fintype.card ι - P.e₀ - 1) ^ P.t₀ * Fintype.card ι ^ P.t₁)
    (Fintype.card ι ^ P.t₀ * (Fintype.card ι - P.e₁ - 1) ^ P.t₁)
def errPhi : ℕ := P.D.l * Fintype.card E ^ (P.D.l - 1)

/-! ### The sending -/

/-- How the seeds are drawn, the honest sender, and the numbers of the sending: bounds on the lists,
numbers of long positions that the encodings bear. -/
structure Snd where
  Sd : P.N.Seeds
  dS : P.N.Sender P.W1 P.W0
  L  : P.N.O → ℕ
  t  : P.N.O → ℕ

/-- What the statement on the sending of a family (`Spec.ldSendFam_chain`, Cb/Ld/LdSendFam.lean)
asks. -/
structure Snd.OK (S : P.Snd) : Prop where
  laws : ∀ a, (P.N.om a).C.Laws
  fair : S.Sd.Fair
  list : ∀ a, (P.N.om a).ListLE (S.L a)
  ev   : ∀ a, (P.N.om a).Evades
  snd  : S.dS.Laws P.back
  bl   : S.dS.Blind S.Sd
  hid  : S.dS.Nn.Hides (P.N.budT S.t)

variable (S : P.Snd)

def snd : IOR P.X1 P.E0 P.X2 P.E2 := ldSendFam P.N S.Sd P.X1 P.E0

end LdLkP

/-! ### Positions: what may be needed of the oracles of a joint -/

/-- The long positions of the member a in a set of positions of a family. -/
def Sig.fib {E : Type} (N : Sig E) (U : Finset N.ext.Pos) (a : N.O) :
    Finset (N.om a).P :=
  U.preimage (fun x => (⟨a, x⟩ : N.ext.Pos)) fun _ _ _ _ h => eq_of_heq (Sigma.mk.inj h).2

/-- At most t a long positions of each member a. -/
def Sig.qT {E : Type} (N : Sig E) (t : N.O → ℕ) : Finset N.ext.Pos → Prop := fun U =>
  ∀ a, (N.fib U a).card ≤ t a

/-- Beside what "q" allows on the left, at most t a long positions of each member a of the family on
the right. -/
def Sig.qAdd {E : Type} (N : Sig E) {A : Type} (q : Finset A → Prop) (t : N.O → ℕ) :
    Finset (A ⊕ N.ext.Pos) → Prop :=
  fun U => q U.toLeft ∧ N.qT t U.toRight

namespace LdLkP
variable {E ι κ J Λ : Type} (P : LdLkP E ι κ J Λ) [Field E] [Fintype E] [Fintype ι] [Nonempty ι]
  [Fintype κ] [Fintype J] [Fintype Λ] (S : P.Snd)

/-- Of the input: at most t₀ positions of the first index, t₁ of the further one. -/
def q0 : Finset P.E0.Pos → Prop := fun U => U.toLeft.card ≤ P.t₀ ∧ U.toRight.card ≤ P.t₁
def q2 : Finset P.E2.Pos → Prop := P.N.qAdd P.q0 S.t
def q3 : Finset P.E3.Pos → Prop := P.N.qT S.t

/-! ### The chain -/

/-- The chain up to the rows that are left. -/
def core : IOR P.X0 P.E0 P.X4 P.E3 := P.gam.seq ((P.snd S).seq (P.loc.seq P.phi))

def hCore : (P.core S).Honest P.W0 P.W2 :=
  P.hGam.seq ((ldSendFamHon S.Sd P.X1 P.E0 S.dS).seq (P.hLoc.seq P.hPhi))

def numsCore (ε₀ ε₁ : ℕ) : IOR.Nums Unit (P.core S) :=
  (IOR.Nums.peek Unit P.vGam (P.errGam ε₀ ε₁)).seq
    ((ldSendFamNums P.N S.Sd P.X1 P.E0 Unit S.L S.t).seq
      ((IOR.Nums.peek Unit P.vLoc P.errLoc).seq (IOR.Nums.peek Unit P.vPhi P.errPhi)))

/-- Its extractor, backwards: each block's in turn; every one of them only drops or moves a part of
the later witness. d: fixed values, where a verifier has rejected (none of these verifiers ever
does). -/
def extCore (d : P.W0 × P.W1 × P.W2) :
    P.X0 × P.E0.Str → Tr (P.core S).shape → P.W2 → P.W0 :=
  IOR.extSeq P.gam _ (fun _ _ w => w.2)
    (IOR.extSeq (P.snd S) _ (fun _ _ w => P.back (P.N.msgs w.1) w.2)
      (IOR.extSeq P.loc P.phi (fun _ _ w => w) (fun _ _ w => w) d.2.2) d.2.1) d.1

/-- A closing: the data. -/
structure Closing where
  T   : IOR P.X4 P.E3 Unit extNone
  H   : T.Honest P.W2 Unit
  ext : P.X4 × P.E3.Str → Tr T.shape → Unit → P.W2
  N   : IOR.Nums Unit T

variable (Z : P.Closing)

/-- The link. -/
def link : IOR P.X0 P.E0 Unit extNone := (P.core S).seq Z.T
def hLink : (P.link S Z).Honest P.W0 Unit := (P.hCore S).seq Z.H
def numsLink (ε₀ ε₁ : ℕ) : IOR.Nums Unit (P.link S Z) := (P.numsCore S ε₀ ε₁).seq Z.N
def extLink (d : P.W0 × P.W1 × P.W2) :
    P.X0 × P.E0.Str → Tr (P.link S Z).shape → Unit → P.W0 :=
  IOR.extSeq (P.core S) Z.T (P.extCore S d) Z.ext d.1

end LdLkP

namespace Spec
open IOR
section
variable (E ι κ J Λ : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Λ]

/-- The rounds: those of the blocks, in a row. -/
def ldLk_shape : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (S : P.Snd) (Z : P.Closing), (P.link S Z).shape =
    [drawRound P.Gam] ++
      (P.N.sh S.Sd ++
        ([drawRound ((Fin P.t₀ → ι) × (Fin P.t₁ → ι))] ++ [drawRound (Fin P.D.l → E)])) ++ Z.T.shape

/-- γ: under `P.FoldErr on0 on1 ε₀ ε₁` the block `gam` is a piece of a chain. -/
def ldLk_gam : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
      (ε₀ ε₁ : ℕ) (q : Finset P.E0.Pos → Prop),
    P.FoldErr on0 on1 ε₀ ε₁ →
    PieceTr P.gam P.hGam (P.j0 on0 on1) (P.j1 on0 on1) (fun _ _ w => w.2)
      (Nums.peek Unit P.vGam (P.errGam ε₀ ε₁)) q q

/-- Under the seven premises below, the sending of a family is a piece of a chain, at the joints
whose conditions may fail. -/
def ldLk_send : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (X W W' : Type) (E₀ : ExtSpec) (A : Rels Unit X E₀ W)
      (back : N.Msg → W' → W) (D : N.Sender W W') (L t : N.O → ℕ) (q : Finset E₀.Pos → Prop),
    (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    D.Laws back → D.Blind Sd → D.Nn.Hides (N.budT t) →
    PieceTr (ldSendFam N Sd X E₀) (ldSendFamHon Sd X E₀ D) A.cf (N.over (N.pull A back)).cf
      (fun _ _ w => back (N.msgs w.1) w.2) (ldSendFamNums N Sd X E₀ Unit L t) q (N.qAdd q t)

/-- The locations: if ι is not empty, the block `loc` is a piece of a chain. -/
def ldLk_loc : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (S : P.Snd),
    PieceTr P.loc P.hLoc (P.j2 on0 on1) P.j3 (fun _ _ w => w)
      (Nums.peek Unit P.vLoc P.errLoc) (P.q2 S) (P.q3 S)

/-- φ: if `P.D.pl` is injective, the block `phi` is a piece of a chain. -/
def ldLk_phi : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (q : Finset P.E3.Pos → Prop), Function.Injective P.D.pl →
    PieceTr P.phi P.hPhi P.j3 P.j4 (fun _ _ w => w) (Nums.peek Unit P.vPhi P.errPhi) q q

/-- The chain up to the rows that are left is a piece of a chain, at the joints whose conditions may
fail (`Rels.cf`), for ι not empty and under the three premises below. -/
def ldLk_core : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (ε₀ ε₁ : ℕ)
      (S : P.Snd) (d : P.W0 × P.W1 × P.W2),
    P.FoldErr on0 on1 ε₀ ε₁ → Function.Injective P.D.pl → S.OK →
    PieceTr (P.core S) (P.hCore S) (P.j0 on0 on1).cf P.j4.cf (P.extCore S d)
      (P.numsCore S ε₀ ε₁) P.q0 (P.q3 S)

/-- The link, with any closing, for ι not empty and under the four premises below: a tail of a chain
from the claim on the two encoded indices to the trivial statement, on the statements with the
conditions. -/
def ldLk_tail : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (ε₀ ε₁ : ℕ) (S : P.Snd)
      (d : P.W0 × P.W1 × P.W2) (Z : P.Closing),
    P.FoldErr on0 on1 ε₀ ε₁ → Function.Injective P.D.pl → S.OK →
    TailTr Z.T Z.H P.j4.cf trivRels Z.ext Z.N (P.q3 S) →
    TailTr (P.link S Z) (P.hLink S Z) (P.j0 on0 on1) trivRels (P.extLink S Z d)
      (P.numsLink S Z ε₀ ε₁) P.q0

/-- Knowledge soundness on the statements with the conditions, with nothing extracted, for ι not
empty and under the four premises below: the relaxed relation does not read its witness, so any
extractor will do. -/
def ldLk_know : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (ε₀ ε₁ : ℕ)
      (S : P.Snd) (Z : P.Closing),
    P.FoldErr on0 on1 ε₀ ε₁ → Function.Injective P.D.pl → S.OK →
    TailTr Z.T Z.H P.j4.cf trivRels Z.ext Z.N (P.q3 S) →
    (P.link S Z).red.Know (P.j0 on0 on1).on
      (fun a (_ : Unit) =>
        ∃ U₀ U₁,
          P.D.X.dec (P.tab a.2.1) a.1.1 = some U₀ ∧
          P.D.X.dec (P.tab a.2.2) a.1.2 = some U₁ ∧
          P.D.SameOn U₀ U₁)
      (fun _ _ => True) (fun _ _ (_ : Unit) => ()) (P.numsLink S Z ε₀ ε₁).err

/-- What the whole link has at the end, beside knowledge soundness: the other items of a list of
sub-protocols. For ι not empty and under the hypotheses below, the verifier reads at most t₀
positions of the first index and t₁ of the further one. -/
def ldLk_end : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (ε₀ ε₁ : ℕ)
      (S : P.Snd) (Z : P.Closing),
    P.FoldErr on0 on1 ε₀ ε₁ → Function.Injective P.D.pl → S.OK →
    TailTr Z.T Z.H P.j4.cf trivRels Z.ext Z.N (P.q3 S) →
    Nonempty (P.link S Z).shape.IsPoint ∧
    (P.link S Z).IsLocal ∧
    (P.hLink S Z).Acc (P.j0 on0 on1).rel trivRels.rel ∧
    (∀ w x, (P.hLink S Z).Hid w x = ∅) ∧
    prRho (P.hLink S Z).Bad ≤ (P.numsLink S Z ε₀ ε₁).pBad ∧
    (P.hLink S Z).Exact (P.j0 on0 on1).rel (fun _ T => T = ∅) ∧
    (P.link S Z).Tied ∧
    ∀ ρ,
      ((P.link S Z).extReads ρ).toLeft.card ≤ P.t₀ ∧ ((P.link S Z).extReads ρ).toRight.card ≤ P.t₁

/-- The general case, with records, under the hypotheses below: neither index has a collision at its
record's seed; each fold by the first regime, at its own radius. -/
def ldLk_foldErr_rec : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (d bad₀ L₀ bad₁ L₁ : ℕ), HasDist P.D.X.G d → P.D.X.eM < d →
    P.e₀ ≤ P.D.X.eM → P.e₁ ≤ P.D.X.eM → P.D.X.MCAeq P.e₀ bad₀ →
    (∀ f : P.D.X.Row → ι → E, ListLE (DecodesTo P.D.X.G P.e₀ f) L₀) → P.D.X.MCAeq P.e₁ bad₁ →
    (∀ f : P.D.X.Row → ι → E, ListLE (DecodesTo P.D.X.G P.e₁ f) L₁) →
    P.FoldErr (fun f rec => ¬ P.D.X.Coll f rec.1) (fun f rec => ¬ P.D.X.Coll f rec.1)
      (bad₀ + L₀ * (P.D.X.v * Fintype.card E ^ (P.D.X.v - 1)))
      (bad₁ + L₁ * (P.D.X.v * Fintype.card E ^ (P.D.X.v - 1)))

/-- Another pairing, under the hypotheses below: the first index decodes and e₀ + eM is below the
distance: no bad point; the further one has no collision at its record's seed: the first regime's
count. -/
def ldLk_foldErr : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (d bad L : ℕ), HasDist P.D.X.G d → P.e₀ + P.D.X.eM < d → P.e₁ ≤ P.D.X.eM →
    P.D.X.MCAeq P.e₁ bad → (∀ f : P.D.X.Row → ι → E, ListLE (DecodesTo P.D.X.G P.e₁ f) L) →
    P.FoldErr (fun f rec => P.D.X.dec f rec ≠ none) (fun f rec => ¬ P.D.X.Coll f rec.1) 0
      (bad + L * (P.D.X.v * Fintype.card E ^ (P.D.X.v - 1)))

end
end Spec
end Cb
