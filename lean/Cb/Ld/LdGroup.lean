-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroup.lean: a run on a group is a part of a proximity test on several oracle messages at
once, as one step of a chain of reductions.

In standard terms: a group is a set of oracle messages that one proximity test takes as a single
word of their codes side by side, read at common positions, with one proximity radius, counted in
positions.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdGroupProofs.lean.
In all statements the group's set of common long positions, `G.P`, is nonempty.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

What a run is. A statement carries oracle messages with their samples (Cb/Ld/LdSig.lean); it claims
rows on the messages of a group G of them (`Grp`, Cb/Ld/LdBatSig.lean), and something more, A₀, of
the oracle messages that are kept.
 1. The bridge (`ldBridge`, Cb/Ld/LdBatSig.lean; one round: the seed of a zero-evader): all rows of
    the claim and all sample rows of all members become one form on the message of the group's
    complex; from here the members are spoken of existentially, at the joint radius; members that
    are not kept leave the statement.
 2. Then a block Bk of a proximity test (fold; fold then switch; several stages: any `LdBlock` of
    Cb/Ld/LdTower.lean that starts at the joint `G.joint`), run beside the kept oracle messages,
    their samples, the further oracles and A₀, which it does not touch.

Main names:
  `ldRunG`: the run as one reduction; `ldRunGH` its honest side; `ldRunGX` its extractor; `ldRunGN`
    its numbers.
  `Spec.ldGroup_run`: qi and qF are demands on sets of positions, of the input oracles and of the
    carried oracles (Cb/Ld/LdGroupKit.lean). If (1) every oracle message is a member or kept (hc),
    (2) the evader evades, (3) the complex has lists of at most L codewords at the joint radius
    (`G.C.ListAt G.e L`), (4) the joint radius implies each member's own (`G.Fits`), (5) Bk is a
    piece that needs at most t long positions of the complex when what follows needs at most t' of
    its output word, and (6) qi holds of the bridge's sources of every set within `besideQ` of "at
    most t" and qF, then the run is a piece of a chain (`PieceTr`)
      from `S.over` (rows on G, beside A₀ of the kept messages), relaxed by decoding with a sample,
        on collision-free statements (`Sig.CF`, Cb/Ld/LdSig.lean) that also meet the base joint's
        own condition (`on` of `Sig.over`, the same file),
      to (the output joint of Bk) beside (`(S.sub kp).over A₀`); left: relaxed existentially at Bk's
        output radius; right: relaxed by decoding with a sample,
      from sets within `besideQ` of "at most t'" and qF to sets within qi,
    with the bundle `IOR.GoodT`: complete as Bk is, knowledge sound round by round, honest-verifier
    exactly zero knowledge (`GoodT.exact`: `Honest.Exact`, Ior/Honest.lean).
  `Spec.ldGroup_run_data`: rounds: one more than Bk's. Errors in a row: err (in `Spec.ldGroup_run`:
    L · (the evader's number)), then Bk's; none is added to another. Nothing more is withheld than
    Bk withholds (stated of the numbers `pBad`, `pHid`).

Why an oracle message may be tested by several runs: it may be a member and kept. The run's
extractor returns for it the pair from the test; the carried relation says that the decoder returns
the carried message; on a collision-free statement the two hold one message, since the test took in
its sample rows (this is inside the bridge's theorem).

`PieceTr`, a piece of a chain, asks of a reduction between two joints the bundle `IOR.GoodT` and
three further clauses, `noHid`, `noTie` and `bears`, which Cb/Ld/LdTowerKit.lean states (`bears`
through `IOR.Bears`, Ior/Bears.lean); `IOR.Piece` (Ior/Tail.lean) asks the same over `IOR.Good`.

Limits:
This file says nothing on a bound on a list, but that `Spec.ldGroup_run` assumes one
(`G.C.ListAt G.e L`), and nothing on which groups a protocol forms.
Declared differences to a write-up of ours (lean/CREDITS.md). (a) There a run ends in the
trivial statement or in a switch whose new word is sampled; here it ends where Bk ends, at a joint
of the existential kind: the sending of the new word, its sample and the locations are blocks that
follow (Cb/Ld/LdSend.lean, Cb/Ld/LdSwitchLoc.lean), so that other words can go out in the same
prover message.
(b) The shape of the group (one base code, one mask code, rows on cubes, rows that are not sent,
kept rows) is not in this file: it enters through Bk, whose first step brings the complex into the
fold's shape (Cb/Ld/LdBatShape.lean, Cb/Ld/LdGroupFold.lean). (c) Radii and errors are counts; zero
knowledge is exact, with budgets of positions.
What this file calls a run is the first part of the write-up's: there both ends of a run are
relaxed by decoding. A run that ends in the trivial statement (a whole test on the group, also in
the middle of a chain) is Cb/Ld/LdLinCloseRun.lean's, on the closed pieces of
Cb/Ld/LdLinCloseKit.lean. A base case ties positions of its mask to positions of its input, so it is
no piece in the sense of Cb/Ld/LdTowerKit.lean. Every piece is a closed piece, and closed pieces
follow one another in any order.
The notion of a run follows this protocol's technical report, which follows a theorem of the paper
that this protocol builds on; the blocks follow that paper (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdBatSig
import Cb.Ld.LdTower
import Cb.Ld.LdGroupKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

section
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} (G : Grp S) [Nonempty G.P]
  (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
  (Z : Evader E (G.Row B)) (St₀ Wp : Type) (E₀ : ExtSpec)

/-- The joint at which a test on the group starts: the complex, the one batched form, the joint
radius. -/
abbrev Grp.joint : LdJoint E := ⟨G.P, G.C, (∀ ν, G.RowSt Sb ν) × Z.D, Slf.bat Z.ze (G.rows sl), G.e⟩

/-- what is carried beside the test: explicit part, oracles, witness -/
abbrev LdCarX : Type := St₀ × (S.sub kp).Smp
abbrev LdCarE : ExtSpec := E₀.prod (S.sub kp).ext
abbrev LdCarW : Type := (S.sub kp).Wit × Wp

variable {b : LdJoint E} (Bk : LdBlock (G.joint Sb sl Z) b)

/-- The run: the bridge, then the block beside the carried part. -/
def ldRunG :
    IOR ((((B → E) × (∀ b, Sb b)) × St₀) × S.Smp) (E₀.prod S.ext)
      (b.X × LdCarX kp St₀) (b.C.ext.prod (LdCarE kp E₀)) :=
  (ldBridge G kp Sb Z St₀ E₀).seq (Bk.R.keep (LdCarX kp St₀) (LdCarE kp E₀))

def ldRunGH :
    (ldRunG G kp Sb sl Z St₀ E₀ Bk).Honest (S.Wit × Wp) (b.W × LdCarW kp Wp) :=
  (ldBridgeH G kp Sb Z St₀ Wp E₀).seq
    ((Bk.H.keep (LdCarX kp St₀) (LdCarE kp E₀)).carry (LdCarW kp Wp))

/-- The extractor: the block's on the test's part, the carried witness copied; then the bridge's.
d: its value where nothing was output. -/
def ldRunGX (hc : ∀ o, G.mem o ∨ kp o) (d : S.Wit × Wp) :
    (((((B → E) × (∀ b, Sb b)) × St₀) × S.Smp) × (E₀.prod S.ext).Str) →
    Tr (ldRunG G kp Sb sl Z St₀ E₀ Bk).shape → b.W × LdCarW kp Wp → S.Wit × Wp :=
  IOR.extSeq (ldBridge G kp Sb Z St₀ E₀) (Bk.R.keep (LdCarX kp St₀) (LdCarE kp E₀))
    (fun _ _ w => ldBrBack G kp Wp hc w) (fun a τ w => (Bk.ext (a.1.1, a.2.1) τ w.1, w.2)) d

def ldRunGN (Kc : Type) (err : ℕ) : IOR.Nums Kc (ldRunG G kp Sb sl Z St₀ E₀ Bk) :=
  (ldBridgeN G kp Sb Z St₀ E₀ Kc err).seq (Bk.N.beside Kc (LdCarX kp St₀) (LdCarE kp E₀))

end

namespace Spec

open Classical in
/-- States: under the hypotheses below, a run on a group is a piece of a chain. -/
def ldGroup_run : Prop :=
  ∀ (E B Kc St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (L : ℕ) (E₀ : ExtSpec) (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
      (hc : ∀ o, G.mem o ∨ kp o) (d : S.Wit × Wp) (b : LdJoint E) (Bk : LdBlock (G.joint Sb sl Z) b)
      (t t' : ℕ) (qi : Finset (E₀.prod S.ext).Pos → Prop) (qF : Finset (LdCarE kp E₀).Pos → Prop),
    Z.OK → G.C.ListAt G.e L → G.Fits → Bk.OK t t' →
    (∀ U, besideQ ((G.joint Sb sl Z).atMost t) qF U → qi (U.biUnion (ldBrG G kp E₀).src)) →
    PieceTr (ldRunG G kp Sb sl Z St₀ E₀ Bk) (ldRunGH G kp Sb sl Z St₀ Wp E₀ Bk)
      (S.over
        (claimRels (fun x m => Slf.All sl x (G.msg m)) (onMsgRels (S.res (T := OMsg.Msg) kp) A₀)))
      (IOR.Rels.beside b.rels ((S.sub kp).over A₀)) (ldRunGX G kp Sb sl Z St₀ Wp E₀ Bk hc d)
      (ldRunGN G kp Sb sl Z St₀ E₀ Bk Kc (L * Z.err)) qi (besideQ (b.atMost t') qF)

/-- Rounds, errors, what is withheld. -/
def ldGroup_run_data : Prop :=
  ∀ (E B Kc St₀ : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S)
      [Nonempty G.P] (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (err : ℕ) (E₀ : ExtSpec)
      (b : LdJoint E) (Bk : LdBlock (G.joint Sb sl Z) b),
    (ldRunG G kp Sb sl Z St₀ E₀ Bk).shape.length = Bk.R.shape.length + 1 ∧
    (ldRunGN G kp Sb sl Z St₀ E₀ Bk Kc err).err =
      Err.app (s := (ldBridge G kp Sb Z St₀ E₀).shape) (t := Bk.R.shape) (err, ()) Bk.N.err ∧
    (ldRunGN G kp Sb sl Z St₀ E₀ Bk Kc err).pBad = 0 + Bk.N.pBad ∧
    (ldRunGN G kp Sb sl Z St₀ E₀ Bk Kc err).pHid = 0 + Bk.N.pHid

end Spec
end Cb
