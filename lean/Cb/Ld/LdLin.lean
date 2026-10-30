-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLin.lean: the test for linear constraints on the encoded index, beyond unique decoding, as
a chain of interactive oracle reductions (one instance).

In standard terms: the encoded index is an oracle: a table of words under one linear code (`LdIx`,
Cb/Ld/LdFoldEq.lean). Beside it the statement has its record, a seed of a sample map with the
answers. The claim is on the index matrix: ⟨g ⊗ eq(ψ, ·), index matrix⟩ + rest = τ. Up to its
closing, the test reduces it to linear claims, beside what the preamble left, on three vectors that
the prover sends encoded:
  w = gᵀ·(index matrix);
  u, the fold, at a random γ, of the full messages of the code rows: its codeword is claimed to
    have, at t random positions, the folds of the columns that the verifier reads there;
  ω = (index matrix)·eq(ψ*, ·).

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLinProofs.lean and
Cb/Ld/LdLinProofsChain.lean. The mathematics on plain vectors is in Cb/Ld/LdLinWords.lean and
Cb/Ld/LdFoldEq.lean; the sending of a family of oracle messages in one prover message, each with its
sample, is the block of Cb/Ld/LdSendFam.lean; the rounds without a prover message are `IOR.peek`
(Cb/Ld/LdLinKit.lean).

The statement. Its explicit part is a pair: what the preamble left (claims and samples), and the
record of the encoded index. Its oracles are the encoded index and the oracles that the preamble
left. The encoded index is no oracle message: it is never closed, its sample lies outside, and it is
decoded by the statement: U = X.dec (index, record).
  Claimed: one tensor row ⟨g ⊗ eq(ψ, ·), index matrix of U⟩ + (a term "rest", `P.rest`: any
    function of the preamble's explicit part and witness; meant is a linear form on the message of
    the oracles left) = τ, and whatever joint `Aa` the preamble left on its own oracles (any joint:
    it is carried to the end untouched).
  Exact relation (`j0.rel`): the index is the table of the codewords of the witness's full messages
    M, M has the record's answers, `Aa.rel`, and the row holds of the message parts of M.
  Relaxed relation (`j0.relR`): `Aa.relR`, and the index decodes with its record and the row holds
    of what it decodes to. The part M of the witness is not read: no extractor produces it.
  Condition (`on0`, a parameter): first regime: no collision of the index at the record's seed.
    Second regime: the index decodes. All that the chain uses of it is `P.FoldErr on0 εf`: on these
    statements at most εf points γ are bad for the fold at the radius e' (`X.Bad`).

The chain. Nothing is merged; every number of rounds is that of the composition
(`Spec.ldLin_shape`). Each row has the block, its rounds, and round by round what the prover sends |
what the verifier sends.
  `step0`, no round: the honest prover computes w = gᵀ·(index matrix).
  `sW`, two rounds: sending of the family NW, whose member iW is the oracle message W, which holds
    w at the places lW | seed; then the answers | nothing.
  `pt`, one round: nothing | the shared point ψ* = (γ, ψlo).
  `sU`, two rounds: sending of the family NU, whose member iU is G_u, which holds at the places lU
    the whole folded full message u (message part, the index's folded pads, folded encoding
    randomness); its own pad is fresh (so it is meant: here the sender, `Snd.dU`, is a parameter) |
    seed; answers | nothing.
  `loc`, one round: nothing | t locations of the encoded index. The verifier reads these t columns,
    folds each at γ, and keeps the folds "tg". The encoded index is read nowhere else, and is
    dropped here.
  `sO`, two rounds: sending of the family NO, whose member iO is Ω, which holds
    ω = (index matrix)·eq(ψ*, ·) at the places lO | seed; answers | nothing.
  `zeta`, one round: nothing | ζ.
  T, the closing: any block from the joint j6 to the trivial statement (splittings, batchings, the
    tests on groups). A parameter; what is asked of it is `TailTr` (Cb/Ld/LdTowerKit.lean).

The families are parameters. Each of the three prover messages may hold further oracle messages
beside the named one, each with its own seed and answer (how the seeds are drawn is the sending's
parameter, `P.SdW` ..). Their messages are free in all relations here: they are the mask-only
messages from which a closing takes the masks of its splittings (an instance's with W, the shared
one with G_u or Ω), so this test sends its masks itself, and no round is added. That such a member
has no main rows, has a sample and pad of its own, and lies in both groups of its splitting is the
closing's matter. A family of one member (`Sig.one`) is the case without splittings.

The joints (`IOR.Rels`, Ior/Chain.lean). A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists
of, for one kind of statement and of witness: the honest relation; a second relation, called
relaxed, of which round-by-round knowledge soundness speaks; the set of statements of which that
soundness speaks; and a map from a witness to its core.
  `jA`: `j0` with w as a further witness. `j1` = the joint over the family NW (`Sig.over`,
    Cb/Ld/LdSig.lean; the output joint of the sending): every member decodes with its sample to the
    witness's message, and `jA` of what W's message holds.
  `j2` (after ψ*): a further witness u: a full message of one row of the index code. Relaxed: every
    member of NW decodes; `Aa.relR`; Eval; the codeword of u is within e' positions of the fold of
    the index at γ (existential: no decoder of the fold); the record's row holds of u; ⟨g, what is
    read off the message part of u⟩ = the extension of w at ψ*.
  `j3` = the joint over NU, of `j2`. `j4` (after the locations): "within e'" is replaced by `ColT`:
    the codeword of u has the values tg at the drawn locations; the index is gone; ω is a further
    witness (not read by the relaxation).
  `j5` = the joint over NO, of `j4`. `j6` (after ζ): the rows that are left (`Rows`): the record's
    row and `ColT` on u, FoldR on (ω, u), Eval on (w, oracles left), Dot on (ω, w); all members of
    the three families decode with their samples; `Aa.relR`. All targets are public: 0, functions of
    the record and of verifier messages, or folds of symbols read. (The target of Eval is
    `P.τ x.1`.)
  The conditions: `on0` up to the locations; `Aa.on`; "no collision" of each oracle message from
    its sending on (Ior/KnowCollGood.lean: the chain is made at the joints `.cf`).

The errors, counts of values of one verifier message (q = |E|, n = number of positions of the index;
v, klo, l = `P.D.X.v`, `P.D.klo`, `P.D.l`: numbers of variables, Cb/Ld/LdLinWords.lean (v:
Cb/Ld/LdFoldEq.lean); e' = `P.e'`, eM = `P.D.X.eM`: radii; d a distance of the index code; bad, L at
ψ*: numbers in the hypotheses of `Spec.ldLin_foldErr`):
  seeds: those of the three sendings: the sum over the members of mult·(L choose 2)·err
    (`ldSendFamErr`, Cb/Ld/LdSendFam.lean).
  ψ*: εf·q^klo + (v + klo)·q^(v+klo-1) [first regime (there e' ≤ eM < d): εf = bad + L·v·q^(v-1):
    `Spec.ldLin_foldErr`; second regime (there e' + eM < d): εf = 0: `Spec.ldLin_foldErr_far`].
  locations: (n - e' - 1)^t [second regime, at e' = d - eM - 1: this is (n + eM - d)^t:
    `Spec.ldLin_loc_far`].
  ζ: l·q^(l-1).

Main names (what each states, and under which hypotheses: its doc comment):
  `Spec.ldLin_core`: the chain up to `j6`: its conclusion is a `PieceTr`.
  `Spec.ldLin_tail`: the test with a closing: `TailTr` of the closing is a hypothesis, `TailTr` of
    the whole test the conclusion.

`PieceTr`, a piece of a chain, asks of a reduction between two joints the bundle `IOR.GoodT` and
three further clauses, `noHid`, `noTie` and `bears`, which Cb/Ld/LdTowerKit.lean states (`bears`
through `IOR.Bears`, Ior/Bears.lean); `IOR.Piece` (Ior/Tail.lean) asks the same over `IOR.Good`.
`TailTr`, a tail of a chain, asks of a reduction from a joint to a joint whose statements have no
oracles the bundle `IOR.GoodT` and three further clauses, `noHid`, `tied` and `bears`, which
Cb/Ld/LdTowerKit.lean states (through `IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

Why (where the bad event of the fold stands): this protocol's technical report keeps the event that
γ is bad as a disjunct of the state from the round of γ up to the draw of locations. Here the
relaxed relation between these two
rounds is existential on the folded word (`j2`). The bad γ are charged in the round of ψ*, and no
condition has to be carried. The errors are the same in the same rounds, the relations the same at
both ends. In shape the step is the technical report's (a switch of the folded word that keeps
its rows: a sending with the input's full message as further witness, then the locations). So the
relaxed relation between these two rounds is not the technical report's.

Limits: declared differences to this protocol's technical report. (1) Which further oracle messages
ride with W, G_u,
Ω is not fixed here (any families). (2) One instance here; the batch (shared point, shared G_u and
Ω) is in Cb/Ld/LdLinB*.lean. (3) Honest-verifier zero knowledge in our exact form. (4) The
witness of a relaxed relation has the type of the exact one; its parts M and encoding randomness are
not read.
What `Spec.ldLin_tail` reaches: closings that are exactly honest-verifier zero knowledge
(`GoodT.exact`: `Honest.Exact`, Ior/Honest.lean) by themselves, so closings that send every mask
which they use. (not all hypotheses are named here: see `Spec.ldLin_tail`) It does not reach a
closing whose splittings use mask-only messages sent in the core (with W, G_u or Ω), as this
protocol's technical report (lean/CREDITS.md) has it: such a closing is not zero knowledge by itself
(Ior/Masked.lean:
`masked_not_exact`, proved of one masked block, under its premises; the step to such a closing is an
argument in words). For that form the test is defined on chains: Cb/Ld/LdLinChain*.lean.
No closing is given (none of type `P.Closing`; closings of this test as chains: `LdLinC.cZ` at any
`Q : LdTc ..`, a parameter there, `Spec.ldLinCl_tail`, Cb/Ld/LdLinCloseLin.lean, under their
hypotheses). This file says nothing on a bound on lists, on "bad", on samples: where such numbers
occur (L, bad in `Spec.ldLin_foldErr`; `S.LW` ..) they are hypotheses or parameters. This file says
nothing on running times.
The test follows this protocol's technical report, which follows the worked example named in
lean/CREDITS.md and the paper that this protocol builds on.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinWords
import Cb.Ld.LdLinKit
import Cb.Ld.LdSendPiece
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

/-- The test: the data. -/
structure LdLinP (E ι κ J Y : Type) where
  /-- the index, its record, the layout of the index matrix -/
  D  : LdLinW E ι κ J Y
  /-- a symbol (a column) of the encoded index as sent, and how it is read over E -/
  Sy : Type
  up : Sy → D.X.Row → E
  /-- the radius at which the fold is tested; the number of locations -/
  e' : ℕ
  t  : ℕ
  /-- what a preamble leaves: oracles, explicit part, witnesses, a joint -/
  Ea : ExtSpec
  Xa : Type
  Wa : Type
  Aa : IOR.Rels Unit Xa Ea Wa
  /-- the tensor row -/
  g    : Xa → Y → E
  ψ    : Xa → D.Pt
  τ    : Xa → E
  rest : Xa → Wa → E
  /-- the three families of oracle messages, how their seeds are drawn, the members that hold w, u,
  ω, and where these stand in their messages -/
  NW  : Sig E
  SdW : NW.Seeds
  iW  : NW.O
  lW  : D.Col → (NW.om iW).C.J
  NU  : Sig E
  SdU : NU.Seeds
  iU  : NU.O
  lU  : κ → (NU.om iU).C.J
  NO  : Sig E
  SdO : NO.Seeds
  iO  : NO.O
  lO  : Y → (NO.om iO).C.J

/-- every member of the family decodes, with its sample, to its message in m -/
def Sig.DecTo {E : Type} [Field E] (N : Sig E) (σ : N.Smp) (y : N.ext.Str) (m : N.Msg) : Prop :=
  ∀ i, N.decs σ y i = some (m i)

namespace LdLinP
variable {E ι κ J Y : Type} (P : LdLinP E ι κ J Y)

/-- the encoded index as an oracle: a symbol is a column -/
abbrev ix : ExtSpec := ⟨ι → P.Sy, ι, P.Sy, fun f j => f j⟩
/-- the encoded index as a table over E -/
def tab (f : ι → P.Sy) : P.D.X.Row → ι → E := fun r j => P.up (f j) r
/-- tables of full messages -/
abbrev IxW : Type := P.D.X.Row → κ → E

/-! ### The types of the joints -/

abbrev X0 : Type := P.Xa × P.D.X.Rec
abbrev E0 : ExtSpec := P.ix.prod P.Ea
abbrev W0 : Type := P.IxW × P.Wa
abbrev WA : Type := (P.D.Col → E) × P.W0
abbrev X1 : Type := P.X0 × P.NW.Smp
abbrev E1 : ExtSpec := P.E0.prod P.NW.ext
abbrev W1 : Type := P.NW.Wit × P.W0
abbrev X2 : Type := P.X1 × P.D.Pt
abbrev W2 : Type := (κ → E) × P.W1
abbrev X3 : Type := P.X2 × P.NU.Smp
abbrev E3 : ExtSpec := P.E1.prod P.NU.ext
abbrev W3 : Type := P.NU.Wit × P.W1
/-- the drawn locations, and the folds of the columns read -/
abbrev Loc : Type := (Fin P.t → ι) × (Fin P.t → E)
abbrev X4 : Type := P.X3 × P.Loc
abbrev E4 : ExtSpec := (P.Ea.prod P.NW.ext).prod P.NU.ext
abbrev W4 : Type := (Y → E) × P.W3
abbrev X5 : Type := P.X4 × P.NO.Smp
abbrev E5 : ExtSpec := P.E4.prod P.NO.ext
abbrev W5 : Type := P.NO.Wit × P.W3
abbrev X6 : Type := P.X5 × (Fin P.D.l → E)

/-- the vectors that the messages of the three named members hold -/
def wv (m : P.NW.Msg) : P.D.Col → E := fun c => m P.iW (P.lW c)
def uv (m : P.NU.Msg) : κ → E := fun k => m P.iU (P.lU k)
def ov (m : P.NO.Msg) : Y → E := fun y => m P.iO (P.lO y)

def backW (m : P.NW.Msg) (w : P.W0) : P.WA := (P.wv m, w)
def backU (m : P.NU.Msg) (w : P.W1) : P.W2 := (P.uv m, w)
def backO (m : P.NO.Msg) (w : P.W3) : P.W4 := (P.ov m, w)

variable [Field E] [Fintype Y]

/-- the tensor row, on message parts U; the row Eval; ⟨g, what is read off u⟩ = the extension of w
at ψ* -/
def Cl (x : P.X0) (wa : P.Wa) (U : P.D.X.Row × J → E) : Prop :=
  P.D.Claim U (P.g x.1) (P.ψ x.1) (P.rest x.1 wa) (P.τ x.1)
def Ev (x : P.X0) (wa : P.Wa) (w : P.D.Col → E) : Prop :=
  P.D.Eval (P.ψ x.1) w (P.rest x.1 wa) (P.τ x.1)
def DotU (x : P.X0) (ψs : P.D.Pt) (u : κ → E) (w : P.D.Col → E) : Prop :=
  P.D.Dot (P.g x.1) (P.D.omU (P.D.X.msg u) ψs.2) ψs w

variable [Fintype ι] [Fintype κ] [Fintype J]

/-- the codeword of u has the values tg at the drawn locations -/
def ColT (lc : P.Loc) (u : κ → E) : Prop := ∀ i, P.D.X.G.mulVec u (lc.1 i) = lc.2 i

/-- All that the chain uses of the condition on the index. -/
def FoldErr [Finite E] (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ) : Prop :=
  ∀ f rec, on0 f rec → cnt (P.D.X.Bad f rec P.e') ≤ εf

/-! ### The joints -/

variable (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)

/-- The input joint. -/
def j0 : IOR.Rels Unit P.X0 P.E0 P.W0 where
  rel  := fun x y w =>
    P.tab y.1 = (fun r => P.D.X.G.mulVec (w.1 r)) ∧
    P.D.X.HasRec x.2 w.1 ∧
    P.Aa.rel x.1 y.2 w.2 ∧
    P.Cl x w.2 (P.D.X.view w.1)
  relR := fun a w =>
    P.Aa.relR (a.1.1, a.2.2) w.2 ∧ ∃ U, P.D.X.dec (P.tab a.2.1) a.1.2 = some U ∧ P.Cl a.1 w.2 U
  on   := fun a => on0 (P.tab a.2.1) a.1.2 ∧ P.Aa.on (a.1.1, a.2.2)
  core := fun _ => ()

/-- The same, with w as a further witness. -/
def jA : IOR.Rels Unit P.X0 P.E0 P.WA where
  rel  := fun x y w => (P.j0 on0).rel x y w.2 ∧ w.1 = P.D.wOf (P.D.X.view w.2.1) (P.g x.1)
  relR := fun a w => (P.j0 on0).relR a w.2
  on   := (P.j0 on0).on
  core := fun _ => ()

/-- After the sending of W. -/
def j1 : IOR.Rels Unit P.X1 P.E1 P.W1 := P.NW.over (P.NW.pull (P.jA on0) P.backW)

/-- After the shared point. -/
def j2 : IOR.Rels Unit P.X2 P.E1 P.W2 where
  rel  := fun x y w => (P.j1 on0).rel x.1 y w.2 ∧ w.1 = foldAll x.2.1 w.2.2.1
  relR := fun a w =>
    P.NW.DecTo a.1.1.2 a.2.2 (P.NW.msgs w.2.1) ∧
    P.Aa.relR (a.1.1.1.1, a.2.1.2) w.2.2.2 ∧
    P.Ev a.1.1.1 w.2.2.2 (P.wv (P.NW.msgs w.2.1)) ∧
    P.D.X.NearW P.e' (foldAll a.1.2.1 (P.tab a.2.1.1)) w.1 ∧
    P.D.X.RecRow a.1.1.1.2 a.1.2.1 w.1 ∧
    P.DotU a.1.1.1 a.1.2 w.1 (P.wv (P.NW.msgs w.2.1))
  on   := fun a => (P.j1 on0).on (a.1.1, a.2)
  core := fun _ => ()

/-- After the sending of G_u. -/
def j3 : IOR.Rels Unit P.X3 P.E3 P.W3 := P.NU.over (P.NU.pull (P.j2 on0) P.backU)

/-- After the locations: the encoded index is gone. -/
def j4 : IOR.Rels Unit P.X4 P.E4 P.W4 where
  rel  := fun x y w =>
    (P.NU.Enc y.2 w.2.1 ∧ P.NU.Ans x.1.2 (P.NU.msgs w.2.1)) ∧
    (P.NW.Enc y.1.2 w.2.2.1 ∧ P.NW.Ans x.1.1.1.2 (P.NW.msgs w.2.2.1)) ∧
    P.D.X.HasRec x.1.1.1.1.2 w.2.2.2.1 ∧
    P.Aa.rel x.1.1.1.1.1 y.1.1 w.2.2.2.2 ∧
    P.Cl x.1.1.1.1 w.2.2.2.2 (P.D.X.view w.2.2.2.1) ∧
    P.wv (P.NW.msgs w.2.2.1) = P.D.wOf (P.D.X.view w.2.2.2.1) (P.g x.1.1.1.1.1) ∧
    P.uv (P.NU.msgs w.2.1) = foldAll x.1.1.2.1 w.2.2.2.1 ∧
    P.ColT x.2 (P.uv (P.NU.msgs w.2.1)) ∧
    w.1 = P.D.omOf (P.D.X.view w.2.2.2.1) x.1.1.2
  relR := fun a w =>
    P.NU.DecTo a.1.1.2 a.2.2 (P.NU.msgs w.2.1) ∧
    P.NW.DecTo a.1.1.1.1.2 a.2.1.2 (P.NW.msgs w.2.2.1) ∧
    P.Aa.relR (a.1.1.1.1.1.1, a.2.1.1) w.2.2.2.2 ∧
    P.Ev a.1.1.1.1.1 w.2.2.2.2 (P.wv (P.NW.msgs w.2.2.1)) ∧
    P.D.X.RecRow a.1.1.1.1.1.2 a.1.1.1.2.1 (P.uv (P.NU.msgs w.2.1)) ∧
    P.DotU a.1.1.1.1.1 a.1.1.1.2 (P.uv (P.NU.msgs w.2.1)) (P.wv (P.NW.msgs w.2.2.1)) ∧
    P.ColT a.1.2 (P.uv (P.NU.msgs w.2.1))
  on   := fun a =>
    P.Aa.on (a.1.1.1.1.1.1, a.2.1.1) ∧ P.NW.CF a.1.1.1.1.2 a.2.1.2 ∧ P.NU.CF a.1.1.2 a.2.2
  core := fun _ => ()

/-- After the sending of Ω. -/
def j5 : IOR.Rels Unit P.X5 P.E5 P.W5 := P.NO.over (P.NO.pull P.j4 P.backO)

/-- The rows that are left, on the vectors (w, u, ω) and the witness of the oracles left. -/
def Rows (x : P.X6) (w : P.D.Col → E) (u : κ → E) (ω : Y → E) (wa : P.Wa) : Prop :=
  P.D.X.RecRow x.1.1.1.1.1.1.2 x.1.1.1.1.2.1 u ∧
  P.ColT x.1.1.2 u ∧
  P.D.FoldR x.2 x.1.1.1.1.2.2 (P.D.X.msg u) ω ∧
  P.Ev x.1.1.1.1.1.1 wa w ∧ P.D.Dot (P.g x.1.1.1.1.1.1.1) ω x.1.1.1.1.2 w

/-- The last joint: what the closing has to test. -/
def j6 : IOR.Rels Unit P.X6 P.E5 P.W5 where
  rel  := fun x y w => P.j5.rel x.1 y w
  relR := fun a w =>
    P.NO.DecTo a.1.1.2 a.2.2 (P.NO.msgs w.1) ∧
    P.NU.DecTo a.1.1.1.1.2 a.2.1.2 (P.NU.msgs w.2.1) ∧
    P.NW.DecTo a.1.1.1.1.1.1.2 a.2.1.1.2 (P.NW.msgs w.2.2.1) ∧
    P.Aa.relR (a.1.1.1.1.1.1.1.1, a.2.1.1.1) w.2.2.2.2 ∧
    P.Rows a.1 (P.wv (P.NW.msgs w.2.2.1)) (P.uv (P.NU.msgs w.2.1)) (P.ov (P.NO.msgs w.1)) w.2.2.2.2
  on   := fun a => P.j5.on (a.1.1, a.2)
  core := fun _ => ()

/-! ### The own blocks -/

/-- step0: no round; the honest prover computes w. -/
def step0 : IOR P.X0 P.E0 P.X0 P.E0 := IOR.pure some (ExtMap.id _)
def hStep0 : P.step0.Honest P.W0 P.WA :=
  IOR.Honest.pure some (ExtMap.id _) fun a => (a.1, (P.D.wOf (P.D.X.view a.2.1) (P.g a.1.1), a.2))

variable [Fintype E]

/-- pt: the shared point. -/
def vPt : IOR.PeekV P.X1 P.E1 P.X2 P.E1 :=
  { D := P.D.Pt, rd := fun _ => ∅, out := fun x c _ => (x, c), g := ExtMap.id _ }
def pt : IOR P.X1 P.E1 P.X2 P.E1 := IOR.peek P.vPt
def hPt : P.pt.Honest P.W1 P.W2 :=
  IOR.Honest.peek P.vPt (fun x _ c => (x, c)) fun _ w c => (foldAll c.1 w.2.1, w)

/-- the fold at γ of a symbol read in the encoded index -/
def foldSym (γ : Fin P.D.X.v → E) : Option P.E3.Sym → E
  | some (.inl (.inl (.inl s))) => ∑ r, Alg.eqk γ r * P.up s r
  | _ => 0

/-- the encoded index is dropped -/
def dropIx : ExtMap P.E3 P.E4 where
  map y := ((y.1.1.2, y.1.2), y.2)
  src q := match q with
    | .inl (.inl p) => {.inl (.inl (.inr p))}
    | .inl (.inr p) => {.inl (.inr p)}
    | .inr p => {.inr p}

variable [Nonempty ι]

open Classical in
/-- loc: the locations. -/
def vLoc : IOR.PeekV P.X3 P.E3 P.X4 P.E4 where
  D := Fin P.t → ι
  rd Q := Finset.univ.image fun i => .inl (.inl (.inl (Q i)))
  out x Q ans := (x, (Q, fun i => P.foldSym x.1.2.1 (ans (.inl (.inl (.inl (Q i)))))))
  g := P.dropIx
def loc : IOR P.X3 P.E3 P.X4 P.E4 := IOR.peek P.vLoc
def hLoc : P.loc.Honest P.W3 P.W4 :=
  IOR.Honest.peek P.vLoc
    (fun x w Q => (x, (Q, fun i => P.D.X.G.mulVec (foldAll x.1.2.1 w.2.2.1) (Q i))))
    fun x w _ => (P.D.omOf (P.D.X.view w.2.2.1) x.1.2, w)

omit [Nonempty ι] in
/-- zeta. -/
def vZeta : IOR.PeekV P.X5 P.E5 P.X6 P.E5 :=
  { D := Fin P.D.l → E, rd := fun _ => ∅, out := fun x c _ => (x, c), g := ExtMap.id _ }
def zeta : IOR P.X5 P.E5 P.X6 P.E5 := IOR.peek P.vZeta
def hZeta : P.zeta.Honest P.W5 P.W5 := IOR.Honest.peek P.vZeta (fun x _ c => (x, c)) fun _ w _ => w

/-- the three errors of the own rounds -/
def errPt (εf : ℕ) : ℕ :=
  εf * Fintype.card E ^ P.D.klo + (P.D.X.v + P.D.klo) * Fintype.card E ^ (P.D.X.v + P.D.klo - 1)
def errLoc : ℕ := (Fintype.card ι - P.e' - 1) ^ P.t
def errZeta : ℕ := P.D.l * Fintype.card E ^ (P.D.l - 1)

/-! ### The sendings -/

def sW : IOR P.X0 P.E0 P.X1 P.E1 := ldSendFam P.NW P.SdW P.X0 P.E0
def sU : IOR P.X2 P.E1 P.X3 P.E3 := ldSendFam P.NU P.SdU P.X2 P.E1
def sO : IOR P.X4 P.E4 P.X5 P.E5 := ldSendFam P.NO P.SdO P.X4 P.E4

/-- The honest senders, and the numbers of the three sendings: bounds on the lists, numbers of long
positions that the encodings bear. -/
structure Snd where
  dW : P.NW.Sender P.WA P.W0
  dU : P.NU.Sender P.W2 P.W1
  dO : P.NO.Sender P.W4 P.W3
  LW : P.NW.O → ℕ
  LU : P.NU.O → ℕ
  LO : P.NO.O → ℕ
  tW : P.NW.O → ℕ
  tU : P.NU.O → ℕ
  tO : P.NO.O → ℕ

/-- What `Spec.ldSendFam_piece` (Cb/Ld/LdSendPiece.lean) asks of a sending, three times. -/
structure Snd.OK (S : P.Snd) : Prop where
  lawsW : ∀ a, (P.NW.om a).C.Laws
  fairW : P.SdW.Fair
  listW : ∀ a, (P.NW.om a).ListLE (S.LW a)
  evW   : ∀ a, (P.NW.om a).Evades
  sndW  : S.dW.Laws P.backW
  blW   : S.dW.Blind P.SdW
  hidW  : S.dW.Nn.Hides (P.NW.budT S.tW)
  lawsU : ∀ a, (P.NU.om a).C.Laws
  fairU : P.SdU.Fair
  listU : ∀ a, (P.NU.om a).ListLE (S.LU a)
  evU   : ∀ a, (P.NU.om a).Evades
  sndU  : S.dU.Laws P.backU
  blU   : S.dU.Blind P.SdU
  hidU  : S.dU.Nn.Hides (P.NU.budT S.tU)
  lawsO : ∀ a, (P.NO.om a).C.Laws
  fairO : P.SdO.Fair
  listO : ∀ a, (P.NO.om a).ListLE (S.LO a)
  evO   : ∀ a, (P.NO.om a).Evades
  sndO  : S.dO.Laws P.backO
  blO   : S.dO.Blind P.SdO
  hidO  : S.dO.Nn.Hides (P.NO.budT S.tO)

/-! ### Positions: what may be needed of the oracles of a joint -/

variable (S : P.Snd) (qa : Finset P.Ea.Pos → Prop)

/-- of the input: at most t positions of the encoded index, and what qa allows of the oracles
left -/
def q0 : Finset P.E0.Pos → Prop := fun U => U.toLeft.card ≤ P.t ∧ qa U.toRight
def q1 : Finset P.E1.Pos → Prop := P.NW.qFam (P.q0 qa) S.tW
def q3 : Finset P.E3.Pos → Prop := P.NU.qFam (P.q1 S qa) S.tU
def q4 : Finset P.E4.Pos → Prop := P.NU.qFam (P.NW.qFam qa S.tW) S.tU
def q5 : Finset P.E5.Pos → Prop := P.NO.qFam (P.q4 S qa) S.tO

/-! ### The chain -/

/-- The chain up to the rows that are left. -/
def core : IOR P.X0 P.E0 P.X6 P.E5 :=
  P.step0.seq (P.sW.seq (P.pt.seq (P.sU.seq (P.loc.seq (P.sO.seq P.zeta)))))

def hCore : P.core.Honest P.W0 P.W5 :=
  P.hStep0.seq ((ldSendFamHon P.SdW P.X0 P.E0 S.dW).seq
    (P.hPt.seq
      ((ldSendFamHon P.SdU P.X2 P.E1 S.dU).seq
        (P.hLoc.seq ((ldSendFamHon P.SdO P.X4 P.E4 S.dO).seq P.hZeta)))))

def numsCore (εf : ℕ) : IOR.Nums Unit P.core :=
  (IOR.Nums.pure Unit some (ExtMap.id _)).seq
    ((ldSendFamNums P.NW P.SdW P.X0 P.E0 Unit S.LW S.tW).seq
      ((IOR.Nums.peek Unit P.vPt (P.errPt εf)).seq
        ((ldSendFamNums P.NU P.SdU P.X2 P.E1 Unit S.LU S.tU).seq
          ((IOR.Nums.peek Unit P.vLoc P.errLoc).seq
            ((ldSendFamNums P.NO P.SdO P.X4 P.E4 Unit S.LO S.tO).seq
              (IOR.Nums.peek Unit P.vZeta P.errZeta))))))

/-- Its extractor, backwards: each block's in turn; every one of them only drops or moves a part of
the later witness. d: fixed values, where a verifier has rejected (none of these verifiers ever
does). -/
def extCore (d : P.W0 × P.WA × P.W1 × P.W2 × P.W3 × P.W4) :
    P.X0 × P.E0.Str → Tr P.core.shape → P.W5 → P.W0 :=
  IOR.extSeq P.step0 _ (fun _ _ w => w.2)
    (IOR.extSeq P.sW _ (fun _ _ w => P.backW (P.NW.msgs w.1) w.2)
      (IOR.extSeq P.pt _ (fun _ _ w => w.2)
        (IOR.extSeq P.sU _ (fun _ _ w => P.backU (P.NU.msgs w.1) w.2)
          (IOR.extSeq P.loc _ (fun _ _ w => w.2)
            (IOR.extSeq P.sO P.zeta (fun _ _ w => P.backO (P.NO.msgs w.1) w.2)
              (fun _ _ w => w) d.2.2.2.2.2) d.2.2.2.2.1) d.2.2.2.1) d.2.2.1) d.2.1) d.1

/-- A closing: the data. -/
structure Closing where
  T   : IOR P.X6 P.E5 Unit extNone
  H   : T.Honest P.W5 Unit
  ext : P.X6 × P.E5.Str → Tr T.shape → Unit → P.W5
  N   : IOR.Nums Unit T

variable (Z : P.Closing)

/-- The test. -/
def lin : IOR P.X0 P.E0 Unit extNone := P.core.seq Z.T
def hLin : (P.lin Z).Honest P.W0 Unit := (P.hCore S).seq Z.H
def numsLin (εf : ℕ) : IOR.Nums Unit (P.lin Z) := (P.numsCore S εf).seq Z.N
def extLin (d : P.W0 × P.WA × P.W1 × P.W2 × P.W3 × P.W4) :
    P.X0 × P.E0.Str → Tr (P.lin Z).shape → Unit → P.W0 :=
  IOR.extSeq P.core Z.T (P.extCore d) Z.ext d.1

end LdLinP

namespace Spec
open IOR
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- States the rounds, for a nonempty ι: those of the blocks, in a row. -/
def ldLin_shape : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (Z : P.Closing), (P.lin Z).shape =
    P.NW.sh P.SdW ++
      ([drawRound P.D.Pt] ++
        (P.NU.sh P.SdU ++
          ([drawRound (Fin P.t → ι)] ++ (P.NO.sh P.SdO ++ [drawRound (Fin P.D.l → E)])))) ++
      Z.T.shape

/-- States: step0 is a piece of a chain, from `j0` to `jA`. -/
def ldLin_step0 : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
      (q : Finset P.E0.Pos → Prop),
    PieceTr P.step0 P.hStep0 (P.j0 on0) (P.jA on0) (fun _ _ w => w.2)
      (Nums.pure Unit some (ExtMap.id _)) q q

/-- The shared point. States: under `P.FoldErr on0 εf`, `pt` is a piece of a chain from `j1` to
`j2`, with the error `P.errPt εf`. -/
def ldLin_pt : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
      (εf : ℕ) (q : Finset P.E1.Pos → Prop),
    P.FoldErr on0 εf →
    PieceTr P.pt P.hPt (P.j1 on0) (P.j2 on0) (fun _ _ w => w.2)
      (Nums.peek Unit P.vPt (P.errPt εf)) q q

/-- The locations. States: for a nonempty ι, `loc` is a piece of a chain from `j3` to `j4`, with the
error `P.errLoc`. -/
def ldLin_loc : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
      (S : P.Snd) (qa : Finset P.Ea.Pos → Prop),
    PieceTr P.loc P.hLoc (P.j3 on0) P.j4 (fun _ _ w => w.2)
      (Nums.peek Unit P.vLoc P.errLoc) (P.q3 S qa) (P.q4 S qa)

/-- ζ. States: for an injective `P.D.py`, `zeta` is a piece of a chain from `j5` to `j6`, with the
error `P.errZeta`. -/
def ldLin_zeta : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (q : Finset P.E5.Pos → Prop), Function.Injective P.D.py →
    PieceTr P.zeta P.hZeta P.j5 P.j6 (fun _ _ w => w) (Nums.peek Unit P.vZeta P.errZeta) q q

/-- The chain up to the rows that are left. States: for a nonempty ι and under the three hypotheses
below it is a piece of a chain from `j0` to `j6`, at the joints `.cf`. -/
def ldLin_core : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ) (S : P.Snd)
      (qa : Finset P.Ea.Pos → Prop) (d : P.W0 × P.WA × P.W1 × P.W2 × P.W3 × P.W4),
    P.FoldErr on0 εf → Function.Injective P.D.py → S.OK →
    PieceTr P.core (P.hCore S) (P.j0 on0).cf P.j6.cf (P.extCore d)
      (P.numsCore S εf) (P.q0 qa) (P.q5 S qa)

/-- The test, with any closing. States: for a nonempty ι and under the four hypotheses below it is
a tail of a chain from the claim on the encoded index to the trivial statement, on the statements
with the condition. Which closings it reaches: the head, Limits. -/
def ldLin_tail : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ) (S : P.Snd)
      (qa : Finset P.Ea.Pos → Prop) (d : P.W0 × P.WA × P.W1 × P.W2 × P.W3 × P.W4) (Z : P.Closing),
    P.FoldErr on0 εf → Function.Injective P.D.py → S.OK →
    TailTr Z.T Z.H P.j6.cf trivRels Z.ext Z.N (P.q5 S qa) →
    TailTr (P.lin Z) (P.hLin S Z) (P.j0 on0) trivRels (P.extLin Z d) (P.numsLin S Z εf) (P.q0 qa)

/-- First regime: states `P.FoldErr`, under the hypotheses below, on the indices without a
collision at the record's seed. -/
def ldLin_foldErr : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (d bad L : ℕ), HasDist P.D.X.G d → P.D.X.eM < d → P.e' ≤ P.D.X.eM →
    P.D.X.MCAeq P.e' bad → (∀ f : P.D.X.Row → ι → E, ListLE (DecodesTo P.D.X.G P.e' f) L) →
    P.FoldErr (fun f rec => ¬ P.D.X.Coll f rec.1)
      (bad + L * (P.D.X.v * Fintype.card E ^ (P.D.X.v - 1)))

/-- Second regime: states `P.FoldErr` with 0, under the hypotheses below, on the indices that
decode. -/
def ldLin_foldErr_far : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (d : ℕ),
    HasDist P.D.X.G d → P.e' + P.D.X.eM < d → P.FoldErr (fun f rec => P.D.X.dec f rec ≠ none) 0

/-- States: in the second regime, at the largest radius allowed, the error of the locations is
(n + eM - d)^t. -/
def ldLin_loc_far : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (d : ℕ),
    P.e' + P.D.X.eM + 1 = d → P.errLoc = (Fintype.card ι + P.D.X.eM - d) ^ P.t

end
end Spec
end Cb
