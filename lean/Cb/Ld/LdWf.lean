-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWf.lean: the reduction from the claim that the encoded index is well-formed to linear claims
on the index's matrix and on the messages that the prover sends.
The preamble of weights-formedness, by composition only.

This file defines an interactive oracle reduction as a composition: the sending of
Cb/Ld/LdSendFam.lean, then one lookup argument for each group of keys computed from the index's
message, then the batching of Cb/Ld/LdBatt.lean; the first and the last at this file's data. Of
these three reductions the lookups alone are parameters (`Blk.sub`). The batching makes one tensor
row of the masked claims on the keys, one a forest; the rows that the lookups file stay beside that
row. The main statement, `Spec.ldWf`, is under the data's laws (`P.Laws`) and hypotheses on the
parts (`B.Hyp`).
The file has the data, the term, the hypotheses on its blocks, each in the form in which its own
file states it, and the statements (in `Cb.Spec`). Proofs: Cb/Ld/LdWfProofsRel.lean,
Cb/Ld/LdWfProofsLinks.lean, Cb/Ld/LdWfProofs.lean (the theorem), Cb/Ld/LdWfList.lean,
Cb/Ld/LdWfSide.lean (the list).

The statement. Explicit part: the record of an encoded index. Oracle: the encoded index. To be
shown: the index decoder answers, that is: the index has no collision at the record's seed and
decodes with its record to a message that holds an index of the index set. The index set is
described by lookups: a message holds an index if and only if, for each of n + 1 forests f, every
key of the forest lies in its table (`LdWfP.Laws.describes`).
The keys of a forest are a function `key f U` of the message U of the index; they are never sent.
How many forests there are and how the keys are cut into them is a parameter.

The protocol, nothing merged:
  send: one sending of a family S of oracle messages, each with its sample (Cb/Ld/LdSendFam.lean):
  they hold the vectors of multiplicities of all forests (`body`; its honest value `bodyOf`: a
  function of the index alone), all masks of all later blocks, pads. Two rounds.
  lkp f: for f = 0, .., n in turn: a lookup sub-protocol (Cb/Ld/LdLkp.lean: `Sub`; any block with
  `Sub.OK`) on the keys of forest f. It leaves a masked claim with public target on the multilinear
  extension of the keys at a point, and linear rows with public targets on entries of the messages
  sent (multiplicities, masks).
  (no message): claim and rows are filed in the state, by forest. The number `nR f` of rows of
  forest f is public, and so are the supports: `gC f`, the entries that the claim's mask form may
  read, `gR f b`, those that row b may read. What does not fit is rejected; that branch never fires
  (no lookup puts such a thing out: `Hyp.lkpN`, `lkpS`).
  Every use of a filed form or row reads it cut to its support (`P.clAt`, `P.rowAt`). So at every
  state the rows are a fixed finite family, and forms and rows are 0 outside public places:
  conditions such as "no incoming form reads an own entry of the batching" are then conditions on
  places (with free forms in the state they would be false).
  (no message): a key map is linear (`Laws.keyLin`): the extension of the keys of forest f at a
  point z is a public constant off f z plus a tensor form in the matrix of the index, < gOf f z ⊗
  eq(cOf f z, ·), mat U >. So each masked claim is a tensor row with masks and a public target.
  Notation: z is the point of a lookup's masked claim, listed as Cb/Ld/LdLkpTree.lean lists points
  (the coordinate of the top bit of a key's number first; extension: `Blocks.ext`); the tensor form
  is on the cube Fin k → Bool (extension: `Alg.mle`). `off`, `gOf`, `cOf` take z in the first order;
  the change of notation is theirs.
  batt: the batching of tensor rows (Cb/Ld/LdBatt.lean): coefficients, then a sumcheck without
  revealed map. It leaves one tensor row with masks and a public target.
  (no message): re-bracketing (Cb/Ld/LdWfClose.lean).
No verifier of the preamble reads an oracle, in this sense: the sending's and the batching's
verifiers read no oracle; a lookup's verifier does not read the index under `lkpI` and has no oracle
of its own under `lkpM`; that it reads none of the oracle messages of S is not asked in `B.Hyp`: it
follows only from the third hypothesis of `Spec.ldWf_side` (`need ρ U = U`).

The joints (`P.A l`, over S, in the form `(S.over ..).cf`) after l lookups. Exact: the index is the
encoding of the prover encoded index with this record; the claims of the forests < l and all filed
rows hold; the keys of the forests ≥ l lie in their tables, and the vectors held for them are the
multiplicities.
Relaxed: the statement decodes the index with its record, the messages are the decoding with their
samples; of these: the claims of the forests < l and the filed rows hold, the keys of the forests ≥
l lie in their tables. Nothing on multiplicities; no prover encoded index. Condition: no collision
of the index, none of an oracle message.

The hypotheses (`B.Hyp`):
  the sending: the seven hypotheses of Cb/Ld/LdSendFam.lean's statement, word for word.
  `lkp`: for each forest: `Sub.OK`, word for word, at the lookup claim `P.lk f`: keys read through
    the decoding of the index; carried part (`more` of `Lk`, Cb/Ld/LdLkp.lean): the claims filed and
    the forests to come; on the honest side only: the tie of the prover encoded index to the index,
    and the multiplicities of the forests to come.
  `lkpM`, `lkpC`: the zero-knowledge item of a lookup: "masked messages" (Ior/Masked.lean: `H.MM`),
    with letters Dm f: a hypothesis of this file (`Sub.OK` has none). So a lookup sends no oracle
    here.
  `lkpI`, `lkpP`, `lkpH`, `lkpN`, `lkpS`: formats of a lookup: the index is neither read nor tied
    and is copied; state and samples are handed on by the verifier; the witness by the honest
    prover; every explicit part that its verifier puts out lists exactly nR l rows, and its mask
    form and rows are 0 outside their public supports (`lkpS`).
  `fresh`, `freshB`: the conditions of the lemma on masks sent in advance, in its own letters
    (Ior/KnowCollRulesMask.lean), for each masked block (`B.Fr`): given all that the sending shows,
    the block's own masks are still uniform and independent of the rest (Fresh: from
    Cb/Ld/LdSendFresh.lean) (exactly: `Honest.Fresh`, Ior/KnowCollRulesMask.lean); no lookup before
    the block looks at them (`Blind`).
  Both are asked of a wider reading of the witness than the block's own (say: all entries but the
  pads, and the further witness), of which the block's reading is a function. For the block's own
  reading "does not look at them" would be false of an earlier lookup, whose messages depend on
  masks of its own that the later block does not read.
  the batching: the three conditions of Cb/Ld/LdBatt.lean's statements.

A parameter list is what is asked of one sub-protocol, in two parts: a record of all items but
round-by-round knowledge soundness (`PreListR`, Hiop/RecSubs.lean), and that item, which is a
definition of its own (`PreKnowR`, Hiop/RecSubs.lean).

Main names:
  `Spec.ldWf` (the theorem): under `P.Laws` and `B.Hyp`, the composition has the parameter list of
    the preamble of weights-formedness and its item on knowledge soundness (Hiop/RecSubs.lean:
    `PreListR`, `PreKnowR`; `HypH.wf`, `HypK.wf` of Hiop/RecBuild.lean): from weights-formedness, on
    statements without a collision of the index, with the relaxation "the index decoder answers",
    into the collision-free statements of the constraint relation of `P.left`. Nothing is extracted.
  `Spec.ldWf_prob`: completeness error and zero-knowledge error: the sums of the lookups' (the
    sending and the batching have 0), in this sense: the list's numbers `pBad`, `pHid` (what ties
    them to probabilities: `PreListR.prBad`, `prHid`, Hiop/RecSubs.lean; `Spec.ldWf`, under its
    hypotheses). Queries to the index: none (clauses `noReads`, `noTie` of the list, so under the
    hypotheses of `Spec.ldWf`).
  `Spec.ldWf_side`: under the hypotheses of its statement, what follows may read of each oracle
    message what its encoding bears (Ior/Bears.lean, Ior/KnowCollPiece.lean: the budgets' half).
  `Spec.ldWf_masks`: the number of mask entries used up: the sum.
    (not all hypotheses are named here: see its statement)

Limits: no lookup is given. This file says nothing on numbers: forests, tables, codes, lists,
degrees are parameters. That the hypotheses can be met together is not shown here. At toys: see the
head of Cb/Ld/LdWfEnd.lean.
These are the declared differences to a write-up of ours (lean/CREDITS.md).
(1) All oracle messages are sent in one prover message at the start; the write-up leaves
    open when mask messages are sent.
(2) A lookup sends no oracle and has the item "masked messages" as a whole (a hypothesis:
    `Hyp.lkpM`): so the write-up; the sub-protocol's interface
    (Cb/Ld/LdLkp.lean) would allow more.
(3) Honest-verifier zero knowledge in our exact form with sets of further positions.
(4) The one tensor row carries the factor ε of the batching's sumcheck on its tensor part.
(5) Running times, so "total extraction time", are not modelled.
(6) The filing step's rejecting branch is not in the write-up: an artefact of the lookup's
    read-out being a list with free coefficients; it never fires (`Hyp.lkpN`, `lkpS`).
The preamble follows this protocol's technical report, which follows the worked example named in
lean/CREDITS.md, the paper that this protocol builds on and advice.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdWfClose
import Cb.Ld.LdWfIdx
import Cb.Ld.LdLkp
import Cb.Ld.LdBatt
import Cb.Ld.LdSendFam
import Cb.Ld.LdSendPiece
import Ior.KnowCollPiece
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

open Classical in
/-- coefficients, cut to a set of places: 0 outside -/
def wfCut {E J : Type} [Zero E] (G : J → Prop) (c : J → E) : J → E := fun j =>
  if G j then c j else 0

/-- The preamble of weights-formedness: the data beside the blocks, over a configuration C with a
record. -/
structure LdWfP (E : Type) [Field E] [Fintype E] (C : ConfigurationWithOutOfDomainSample) : Type 1 where
  /-- the oracle messages that the preamble sends, and how their seeds are drawn -/
  S : Sig E
  Sd : S.Seeds
  /-- what of their messages is a function of the index: the vectors of multiplicities -/
  Body : Type
  body : S.Msg → Body
  bodyOf : C.Msg → Body
  /-- the entries of the messages that rows and mask forms may read -/
  N : Type
  [finN : Fintype N]
  ent : S.Msg → N → E
  /-- The forests 0, .., n: numbers of variables of keys and tables, key maps, tables, "the vector
  held is the multiplicities". -/
  n : ℕ
  v : ℕ → ℕ
  d : ℕ → ℕ
  key : ℕ → C.Msg → ℕ → E
  tab : ℕ → ℕ → E
  mult : ℕ → C.Msg → Body → Prop
  /-- the number of rows that the lookup on a forest files -/
  nR : ℕ → ℕ
  /-- public supports: the entries that the mask form of the claim of a forest may read; the entries
  that a row of a forest may read -/
  gC : ℕ → N → Prop
  gR : ∀ f, Fin (nR f) → N → Prop
  /-- the matrix of the index: rows Rw, columns on the cube of k variables -/
  Rw : Type
  [finRw : Fintype Rw]
  k : ℕ
  mat : C.Msg → Rw × (Fin k → Bool) → E
  /-- A key map is linear: constant, row factor and point of the column factor, at a point of the
  keys' cube. -/
  off : ℕ → (ℕ → E) → E
  gOf : ℕ → (ℕ → E) → Rw → E
  cOf : ℕ → (ℕ → E) → Fin k → E
  /-- the batching: coefficients, degree, where the coefficients of its hiding polynomial lie -/
  Z : Evader E (Fin (n + 1))
  deg : ℕ
  wAt : PIdx (List.replicate k (pfCube E deg)) → N

attribute [instance] LdWfP.finN LdWfP.finRw

namespace LdWfP
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} (P : LdWfP E C)

/-! ### Types -/

/-- The state: the record; the masked claims filed, by forest; the rows filed, by forest: nR f rows
for forest f. No list: at every state the rows are a fixed finite family. -/
abbrev WSt : Type := C.Rec × (ℕ → MCl E P.N) × (∀ f : ℕ, Fin (P.nR f) → Row E P.N)
/-- the further witness: the prover encoded index -/
abbrev Wp (_ : LdWfP E C) : Type := C.PIdx × Unit
/-- what a claim reads beside the explicit part: the index and the messages -/
abbrev M : Type := Ms P.S C.E0
abbrev X : Type := P.WSt × P.S.Smp
abbrev Ex : ExtSpec := C.E0.prod P.S.ext
abbrev W : Type := P.S.Wit × P.Wp

/-- the state at the start -/
def st0 (rec : C.Rec) : P.WSt :=
  (rec, fun _ => ⟨fun _ => 0, fun _ => 0, 0⟩, fun _ _ => ⟨fun _ => 0, 0⟩)

/-! ### Claims -/

/-- the keys of forest f lie in its table -/
def InT (f : ℕ) (U : C.Msg) : Prop := Lkp.InTable (P.v f) (P.d f) (P.key f U) (P.tab f)
/-- The claim and the rows of a forest, as they are read off a state: cut to their public supports.
So at every state the mask form and the rows are 0 outside the places that the data name. -/
def clAt (f : ℕ) (st : P.WSt) : MCl E P.N :=
  ⟨(st.2.1 f).pt, wfCut (P.gC f) (st.2.1 f).mf, (st.2.1 f).tg⟩
def rowAt (f : ℕ) (b : Fin (P.nR f)) (st : P.WSt) : Row E P.N :=
  ⟨wfCut (P.gR f b) (st.2.2 f b).cf, (st.2.2 f b).tg⟩
/-- the claims and the rows of the forests < l hold -/
def Done (l : ℕ) (st : P.WSt) (U : C.Msg) (m : P.S.Msg) : Prop :=
  ∀ f, f < l →
    (P.clAt f st).Holds (P.v f) (P.key f U) (P.ent m) ∧ ∀ b, (P.rowAt f b st).Holds (P.ent m)
/-- Q of the message to which the statement decodes the index; false if there is none -/
def via (_ : LdWfP E C) (rec : C.Rec) (y : C.E0.Str) (Q : C.Msg → Prop) : Prop :=
  ∃ U, C.dcd y rec = some U ∧ Q U

/-- The laws of the data. -/
structure Laws : Prop where
  /-- the lookups describe the index set -/
  describes : ∀ U, (C.held U).isSome ↔ ∀ f, f ≤ P.n → P.InT f U
  /-- two laws of the configuration (Hiop/RecConf.lean: Props) -/
  held_hold : ∀ i η, C.held (C.hold i η) = some i
  dcd_enc   : ∀ m r s, C.dcd (C.enc m r) (s, C.smp s m) = some m
  /-- the honest vectors are the multiplicities, where the keys lie in the table -/
  multOf    : ∀ U f, f ≤ P.n → P.InT f U → P.mult f U (P.bodyOf U)
  /-- a key map is linear -/
  keyLin    : ∀ f, f ≤ P.n →
    ∀ U z, Blocks.ext (P.v f) (P.key f U) z =
      P.off f z + Alg.mle (fun c => ∑ r, P.gOf f z r * P.mat U (r, c)) (P.cOf f z)

/-! ### The lookup claim of forest l, in the notation of Cb/Ld/LdLkp.lean -/

/-- the keys, read through the decoding of the index -/
def keyAt (l : ℕ) (st : P.WSt) (ym : P.M) : ℕ → E := fun b => match C.dcd ym.1 st.1 with
  | some U => P.key l U b
  | none => 0

def lk (l : ℕ) : Lk E P.WSt P.M :=
  ⟨P.v l, P.d l, P.keyAt l, fun _ => P.tab l,
    fun st ym => P.via st.1 ym.1 fun U => P.Done l st U ym.2 ∧ ∀ f, l < f → f ≤ P.n → P.InT f U⟩
def multAt (l : ℕ) : P.WSt → P.M → Prop := fun st ym =>
  P.via st.1 ym.1 fun U => P.mult l U (P.body ym.2)
/-- on the honest side only: the tie, and the multiplicities of the forests to come -/
def honAt (l : ℕ) : P.WSt → P.M → P.Wp → Prop := fun st ym wp =>
  C.Enc st.1 ym.1 wp.1 ∧ P.via st.1 ym.1 fun U => ∀ f, l < f → f ≤ P.n → P.mult f U (P.body ym.2)
def onW : P.WSt × C.E0.Str → Prop := fun a => ¬ C.coll a.2 a.1.1.1
def entM : P.M → P.N → E := fun ym => P.ent ym.2

/-- What a lookup puts out can be filed: the list has nR l rows; mask form and rows are 0 outside
their public supports. -/
def FileOK (l : ℕ) (x : TX P.WSt E P.N × P.S.Smp) : Prop :=
  x.1.2.2.length = P.nR l ∧
  (∀ n, ¬ P.gC l n → x.1.2.1.mf n = 0) ∧
  ∀ (b : Fin (P.nR l)) n, ¬ P.gR l b n → (x.1.2.2.getD b ⟨fun _ => 0, 0⟩).cf n = 0
open Classical in
/-- A lookup's claim and rows are filed. What cannot be filed is rejected. -/
def file (l : ℕ) (x : TX P.WSt E P.N × P.S.Smp) : Option P.X :=
  if P.FileOK l x then
    some ((x.1.1.1,
          Function.update x.1.1.2.1 l x.1.2.1,
          Function.update x.1.1.2.2 l fun b => x.1.2.2.getD b ⟨fun _ => 0, 0⟩),
        x.2)
  else none
/-- what the honest prover takes as the new explicit part -/
def fileD (l : ℕ) (x : TX P.WSt E P.N × P.S.Smp) : P.X :=
  (P.file l x).getD (x.1.1, x.2)

/-! ### The joints -/

/-- The base joint after l lookups. -/
def A (l : ℕ) : Rels Unit P.WSt C.E0 (P.S.Msg × P.Wp) where
  rel  := fun st y w =>
    C.Enc st.1 y w.2.1 ∧
    P.Done l st w.2.1.1.1 w.1 ∧
    ∀ f, l ≤ f → f ≤ P.n → P.InT f w.2.1.1.1 ∧ P.mult f w.2.1.1.1 (P.body w.1)
  relR := fun a w => P.via a.1.1 a.2 fun U => P.Done l a.1 U w.1 ∧ ∀ f, l ≤ f → f ≤ P.n → P.InT f U
  on   := P.onW
  core := fun _ => ()

@[reducible] def J (l : ℕ) : Joint Unit := ⟨P.X, P.Ex, P.W, (P.S.over (P.A l)).cf⟩

/-- The first joint: weights-formedness, on statements without a collision. -/
@[reducible] def jIn (_ : LdWfP E C) : Joint Unit :=
  ⟨C.Rec, C.E0, C.PIdx, ⟨C.Rwf, fun a _ => C.RwfR a (), C.free, fun _ => ()⟩⟩

/-- the joint before the sending: the vectors of multiplicities are a further witness -/
def A0 : Rels Unit P.WSt C.E0 (P.Body × P.Wp) where
  rel  := fun st y w =>
    C.Enc st.1 y w.2.1 ∧ ∀ f, f ≤ P.n → P.InT f w.2.1.1.1 ∧ P.mult f w.2.1.1.1 w.1
  relR := fun a _ => P.via a.1.1 a.2 fun U => ∀ f, f ≤ P.n → P.InT f U
  on   := P.onW
  core := fun _ => ()

def back (m : P.S.Msg) (w : P.Wp) : P.Body × P.Wp := (P.body m, w)

/-! ### The batching of tensor rows, in the notation of Cb/Ld/LdBatt.lean -/

/-- Its parameters: the entries are those of the matrix of the index beside those of the messages.
-/
def bt : BattPar E where
  St := P.WSt
  J := (P.Rw × (Fin P.k → Bool)) ⊕ P.N
  Rw := P.Rw
  k := P.k
  mAt := Sum.inl
  Q := Fin (P.n + 1)
  g := fun st q => P.gOf q (st.2.1 q).pt
  pt := fun st q => P.cOf q (st.2.1 q).pt
  slM := fun q st => Sum.elim (fun _ => 0) (P.clAt q st).mf
  Z := P.Z
  n := P.deg
  wAt := fun i => Sum.inr (P.wAt i)

/-- the entries, from the tuple (message of the index, messages) -/
def msg (um : C.Msg × P.S.Msg) : P.bt.J → E := Sum.elim (P.mat um.1) (P.ent um.2)

/-- the masked claims as tensor rows: the targets -/
def toBatt (x : P.X) : ((P.bt.Q → E) × P.bt.St) × P.S.Smp :=
  ((fun q : Fin (P.n + 1) => (x.1.2.1 q).tg - P.off q (x.1.2.1 q).pt, x.1), x.2)

/-- the state in the claim that the batching leaves -/
def stOf (z : P.bt.par.Mid) : P.WSt := (show P.WSt × P.Z.D from z.st).1

/-- what rides along: the filed rows -/
def RowsV (st : P.WSt) (m : P.S.Msg) : Prop := ∀ f, f ≤ P.n → ∀ b, (P.rowAt f b st).Holds (P.ent m)
def rows : Rels Unit P.bt.St C.E0 ((C.Msg × P.S.Msg) × Unit) :=
  ⟨fun st _ w => P.RowsV st w.1.2, fun a w => P.RowsV a.1 w.1.2, fun _ => True, fun _ => ()⟩

/-! ### What is left -/

abbrev Cl : Type := P.bt.par.Mid

/-- The claims that are left: one tensor row with masks and a public target; the rows filed. -/
def holds (cl : P.Cl) (_ : C.Rec) (U : C.Msg) (m : P.S.Msg) : Prop :=
  P.bt.RowHolds cl (P.msg (U, m)) ∧ P.RowsV (P.stOf cl) m

/-- What the preamble leaves. -/
@[reducible] def left : C.Left := sigLeft C P.S P.Cl P.holds

def lastB : Rels Unit (P.Cl × C.Rec) C.E0 (P.S.Msg × P.Wp) where
  rel  := fun x y w => C.Enc x.2 y w.2.1 ∧ P.holds x.1 x.2 w.2.1.1.1 w.1
  relR := fun a w => ∃ U, C.dcd a.2 a.1.2 = some U ∧ P.holds a.1.1 a.1.2 U w.1
  on   := fun a => ¬ C.coll a.2 a.1.2.1
  core := fun _ => ()

@[reducible] def jLast : Joint Unit := ⟨(P.Cl × C.Rec) × P.S.Smp, P.Ex, P.W, (P.S.over P.lastB).cf⟩

def toLast (x : P.Cl × P.S.Smp) : (P.Cl × C.Rec) × P.S.Smp := ((x.1, (P.stOf x.1).1), x.2)

/-! ### The blocks -/

/-- The batching of tensor rows, between two steps without rounds. -/
def lBatt : Link Unit (P.J (P.n + 1)) P.jLast where
  R := (((P.bt.batt C.E0).keep P.S.Smp P.S.ext).pre (fun x => some (P.toBatt x)) (ExtMap.id _)).post
    (fun x => some (P.toLast x)) (ExtMap.id _)
  H := ((P.S.liftH (idxH C (P.bt.hon C.E0 fun w : (C.Msg × P.S.Msg) × Unit => P.msg w.1))).pre
      _ _ fun a => (P.toBatt a.1, a.2)).post
    _ _ fun a => (P.toLast a.1, a.2)
  ext := fun _ _ w => w
  P := (((P.bt.nums C.E0 Unit).keep P.S.Smp P.S.ext).pre _ _).post _ _


/-- The blocks: the data. -/
structure Blk : Type 1 where
  /-- the honest sender; bounds for the lists; long positions that the encodings bear -/
  D  : P.S.Sender (P.Body × P.Wp) P.Wp
  L  : P.S.O → ℕ
  t  : P.S.O → ℕ
  /-- the lookups, and the parameters of their item "masked messages" -/
  sub : ℕ → Sub P.S P.S C.E0 P.WSt P.N P.Wp
  Dm  : ∀ l, MaskData (sub l).R P.W
  /-- the entries that the batching reads -/
  Rd  : P.bt.J → Prop
  /-- a fixed prover encoded index, fixed randomness: values of extractors that nobody reads -/
  p0 : C.PIdx
  r0 : P.S.Rnd

namespace Blk
variable {P} (B : P.Blk)

/-- The sending, after the step in which the honest prover computes the vectors of multiplicities.
-/
def lSend : Link Unit P.jIn (P.J 0) where
  R := (ldSendFam P.S P.Sd P.WSt C.E0).pre (fun rec => some (P.st0 rec)) (ExtMap.id _)
  H :=
    (ldSendFamHon P.Sd P.WSt C.E0 B.D).pre _ _ fun a => (P.st0 a.1, (P.bodyOf a.2.1.1, (a.2, ())))
  ext := fun _ _ w => w.2.1
  P := (ldSendFamNums P.S P.Sd P.WSt C.E0 Unit B.L B.t).pre _ _

/-- The lookup on forest l, then the filing. -/
def lLkp (l : ℕ) : Link Unit (P.J l) (P.J (l + 1)) where
  R := (B.sub l).R.post (P.file l) (ExtMap.id _)
  H := (B.sub l).H.post _ _ fun a => (P.fileD l a.1, a.2)
  ext := (B.sub l).ext
  P := (B.sub l).P.post _ _

/-- the parameters of the batching's item "masked messages" -/
def DmB : MaskData ((P.bt.batt C.E0).keep P.S.Smp P.S.ext) P.W :=
  idxMask C P.S (P.bt.maskData C.E0 (fun w : (C.Msg × P.S.Msg) × Unit => P.msg w.1) B.Rd)

/-- The chain up to and with the lookup on forest l. -/
def cLkp (l : ℕ) : Chain Unit P.jIn (P.J (l + 1)) :=
  (Chain.one B.lSend).append (Chain.fam P.J B.lLkp l)

/-- The chain. -/
def chain : Chain Unit P.jIn P.jLast := (B.cLkp P.n).snoc P.lBatt

def link : Link Unit P.jIn P.jLast := B.chain.link B.p0

/-- The preamble of weights-formedness, its honest side, its numbers. -/
def wf : IOR C.Rec C.E0 (P.left.Xl × C.Rec) P.left.El := closeF B.link.R
def hWf : B.wf.Honest C.PIdx (C.PIdx × P.left.WAux) := closeH Prod.fst B.link.H
def nums : PreNums B.wf := closeN B.link.P

/-- The masks (kc, Mk, put) of a block that stands behind the sending and the lookups j < l are
fresh when the block begins. Said of some wider reading kW of the witness, of which the block's own
reading kc is a function g that commutes with the overwriting of the masks:
given all that the sending shows, the masks are uniform and independent of the rest of kW (exactly:
`Honest.Fresh`, Ior/KnowCollRulesMask.lean); no lookup j < l looks at them: witnesses whose readings
kW differ by the masks alone give the same run (exactly: `Honest.Blind`, the same file). (For the
block's own, narrow reading the second clause would be false: a lookup's messages depend on its own
masks, which a later block does not read. On the other side kW has to forget the pad and the
encoding randomness of the oracle message that holds the masks, or the sending cannot be Fresh for
it.) -/
def Fr (l : ℕ) {Kc : Type} (kc : P.W → Kc) (Mk : Type) [Fintype Mk]
    [Nonempty Mk] (put : Mk → Kc → Kc) : Prop :=
  ∃ (KW : Type) (kW : P.W → KW) (putW : Mk → KW → KW) (g : KW → Kc),
    (∀ w, kc w = g (kW w)) ∧
    (∀ M k, g (putW M k) = put M (g k)) ∧
    (ldSendFamHon P.Sd P.WSt C.E0 B.D).Fresh
      P.A0.rel (ldSendFamNums P.S P.Sd P.WSt C.E0 Unit B.L B.t).bud kW Mk putW ∧
    ∀ j, j < l → (B.sub j).H.Blind kW kW Mk putW putW

/-- What is asked of the blocks. -/
structure Hyp : Prop where
  /-- the sending: the hypotheses of its own statement -/
  laws   : ∀ a, (P.S.om a).C.Laws
  fair   : P.Sd.Fair
  list   : ∀ a, (P.S.om a).ListLE (B.L a)
  evades : ∀ a, (P.S.om a).Evades
  sender : B.D.Laws P.back
  sBlind : B.D.Blind P.Sd
  hides  : B.D.Nn.Hides (P.S.budT B.t)
  /-- the lookups: the sub-protocol's own statement -/
  lkp    : ∀ l, l ≤ P.n → (B.sub l).OK (P.lk l) (P.multAt l) P.onW (P.honAt l) id P.entM
  /-- their zero-knowledge item -/
  lkpM   : ∀ l, l ≤ P.n → (B.sub l).H.MM (B.Dm l)
  lkpC   : ∀ l, l ≤ P.n →
    ∀ x y w, (jt2 P.S C.E0 P.Wp P.onW (P.honAt l) ((P.lk l).inP (P.multAt l)) (P.lk l).inR).rel
        x y w →
      (B.Dm l).Cl ((B.Dm l).pub x) ((B.Dm l).kc w)
  /-- their formats -/
  lkpI   : ∀ l, l ≤ P.n → (B.sub l).R.IdxStep
  lkpP   : ∀ l, l ≤ P.n → (B.sub l).R.Passes (fun x => x) (fun x => (x.1.1, x.2))
  lkpH   : ∀ l, l ≤ P.n → ∀ w x c ρ, (((B.sub l).H.strat w x c).run ρ).2.2 = w
  lkpN   : ∀ l, l ≤ P.n → ∀ x y τ x', (B.sub l).R.out x y τ = some x' → x'.1.2.2.length = P.nR l
  lkpS   : ∀ l, l ≤ P.n →
    ∀ x y τ x', (B.sub l).R.out x y τ = some x' →
      (∀ n, ¬ P.gC l n → x'.1.2.1.mf n = 0) ∧
      ∀ (b : Fin (P.nR l)) n, ¬ P.gR l b n → (x'.1.2.2.getD b ⟨fun _ => 0, 0⟩).cf n = 0
  /-- masks sent in advance -/
  fresh  : ∀ l, l ≤ P.n → B.Fr l (B.Dm l).kc (B.Dm l).Mk (B.Dm l).put
  freshB : B.Fr (P.n + 1) B.DmB.kc B.DmB.Mk B.DmB.put
  /-- the batching: the conditions of its own statements -/
  deg    : 2 ≤ P.deg
  zOK    : P.Z.OK
  own    : P.bt.OwnOK B.Rd

end Blk
end LdWfP

/-! ## The statements -/

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

/-- The theorem on the preamble of weights-formedness, conditional on its blocks (`B.Hyp`) and on
`P.Laws`. -/
def ldWf : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk), P.Laws → B.Hyp →
    PreListR P.left B.wf B.hWf id id C.Rwf B.nums ∧
    PreKnowR P.left B.wf C.free C.RwfR (fun _ _ _ => ()) B.nums.err

/-- The two numbers of rounds: sums over the blocks; nothing is merged. -/
def ldWf_rounds : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk),
    B.wf.shape.nAll = 2 + (∑ l ∈ Finset.range (P.n + 1), (B.sub l).R.shape.nAll) + (P.k + 2) ∧
    B.wf.shape.nVer =
      (P.S.sh P.Sd).nVer + (∑ l ∈ Finset.range (P.n + 1), (B.sub l).R.shape.nVer) +
        (P.bt.batt C.E0).shape.nVer

/-- The errors are in the order of the rounds: the sending's two, each lookup's in turn, the
batching's. -/
def ldWf_err : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk), B.nums.err.list =
    [ldSendFamErr P.S P.Sd B.L, 0] ++
      (List.range (P.n + 1)).flatMap (fun l => (B.sub l).P.err.list) ++
      (P.bt.nums C.E0 Unit).err.list

/-- The probabilities of the public and of the hidden withheld set: the sums of the lookups', in
this sense: the list's numbers `pBad`, `pHid` (what ties them to these probabilities:
`PreListR.prBad`, `prHid`, Hiop/RecSubs.lean; `Spec.ldWf`, under its hypotheses). -/
def ldWf_prob : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk),
    B.nums.pBad = ∑ l ∈ Finset.range (P.n + 1), (B.sub l).P.pBad ∧
    B.nums.pHid = ∑ l ∈ Finset.range (P.n + 1), (B.sub l).P.pHid

/-- Queries and further reads: under the hypotheses below, nothing hidden is withheld, nothing is
tied, and the preamble bears what follows: if what follows needs, of each oracle message a, at most
t a long positions, and of the index a set of positions within q, then the budget of the preamble
holds at the sources of these positions, and of the index exactly a set within q is needed. Asked of
each lookup: nothing hidden is withheld; its budget holds at the empty set; what it needs of its
input oracles is what is needed of its output oracles. -/
def ldWf_side : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk) (q : Finset C.E0.Pos → Prop), B.Hyp →
    (∀ l, l ≤ P.n → ∀ ρ, (B.sub l).P.bud ρ ∅) → (∀ l, l ≤ P.n → ∀ ρ U, (B.sub l).R.need ρ U = U) →
    Side B.wf B.hWf B.nums.bud q (P.S.qFam q B.t)

/-- The mask entries that the preamble uses up: the sum over the lookups, and k · deg + 1 for the
batching.
(not all hypotheses are named here: see the statement below) -/
def ldWf_masks : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk) (nm : ℕ → ℕ),
    (∀ l, l ≤ P.n → Fintype.card (B.Dm l).Mk = Fintype.card E ^ nm l) →
    Fintype.card ((∀ l : Fin (P.n + 1), (B.Dm l).Mk) × B.DmB.Mk) =
      Fintype.card E ^ ((∑ l ∈ Finset.range (P.n + 1), nm l) + (P.k * P.deg + 1))

end
end Spec
end Cb
