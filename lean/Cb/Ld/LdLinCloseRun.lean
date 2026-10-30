-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseRun.lean: one proximity test on several oracles together (a whole test on a group),
as an interactive oracle reduction, run while the statement also holds other oracles and claims,
which the test passes on.

In standard terms: a group (`Grp`, Cb/Ld/LdBatSig.lean) is a set of whole oracle messages read at
common long positions, with one joint proximity radius. A zero-evader (`Evader`,
Cb/Gen/BatEvader.lean) is a seeded family of coefficient vectors with a number `err`; it evades
(`Evader.OK`, a hypothesis, not a field) if at most `err` seeds annihilate any given vector other
than 0: with it many linear claims are batched into one. "Relaxed by decoding with a sample"
(`Sig.over`, Cb/Ld/LdSig.lean): the relaxed relation asks that each oracle decodes, with its sample,
to the witness's message.
A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and of
witness: the honest relation; a second relation, called relaxed, of which round-by-round knowledge
soundness speaks; the set of statements of which that soundness speaks; and a map from a witness to
its core. That set of statements is the joint's condition. Samples and words are collision-free
(`Sig.CF`, Cb/Ld/LdSig.lean) if no oracle message has a collision at the seed of its sample: two
different messages of the list of its word with the same answers. It is a condition on statements,
not a part of either relation of `Sig.over`.

Definitions and statements; the proofs are in Cb/Ld/LdLinCloseRunProofs.lean.

A statement carries oracle messages with their samples (Cb/Ld/LdSig.lean); it claims rows on the
messages of a group G of them, and something more, A₀, of the oracle messages that are kept.
  1. The bridge (one round: the seed of a zero-evader): the rows of the claim and all sample rows of
     all members become one form on the message of the group's complex; the members that are not
     kept leave the statement.
  2. A whole proximity test "T" on the complex (any end block of Cb/Ld/LdTower.lean at the joint
     `G.joint`: stages and a base case), run beside the kept oracle messages, their samples, the
     further oracles and A₀, none of which it touches.
  3. A step without rounds: the trivial statement that the test leaves is dropped.

Main names:
  `ldRunE`: the three as one reduction; `ldRunEH` its honest side; `ldRunEX` its extractor;
    `ldRunEN` its numbers.
  `Spec.ldClose_run`: if G has a common long position (`Nonempty G.P`), the evader evades (`Z.OK`),
    the complex has lists of at most L members at the joint radius, the joint radius implies each
    member's own (`G.Fits`), every oracle message is a member of G or kept (`hc`), T is a tail that
    needs at most t long positions of the complex (`T.OK t`), and qi covers what is needed of the
    oracles (below), then the whole is a closed piece of a chain (`ClosedTr`,
    Cb/Ld/LdLinCloseKit.lean, there called a piece that may tie) from `S.over` (rows on G, beside A₀
    of the kept messages) to `(S.sub kp).over A₀`. Both ends relaxed by decoding with a sample, on
    collision-free statements with A₀'s own condition. So another such test, on another group of
    what is kept, can follow; an oracle message that is a member and kept is tested again later.
  What is needed of the oracles: at most t common long positions of the group (one position of each
    member for each of them), and, of the kept and further oracles, what follows needs (qF).
  `Spec.ldClose_run_data` states, for G with a common long position, that the rounds are one more
    than T's. Errors in a row: the number `err` given to `ldRunEN` (L · `Z.err` in
    `Spec.ldClose_run`), then T's. Nothing more is withheld than T withholds, in this sense: the
    numbers `pBad` and `pHid` of `ldRunEN` are T's.
    `P.pBad` is a number of the structure `Nums`; the clause `prBad` of `Good` asks that the
    probability of the set `H.Bad`, over the verifier's uniform randomness, is at most it. `P.cov k`
    is a set of verifier randomness for each value k of the core; `Good` asks that, for every w and
    x, in the relation or not, `H.Hid w x` lies in `P.cov (A.core w)` (`cover`), and that every
    `P.cov k` has probability at most `P.pHid` (`prCov`). Here the two numbers stand in the
    conclusion, in equations. `GoodT` (Ior/KnowCollGood.lean), the bundle in this file's statements,
    has the same three clauses.
  The end of a chain (`ldDone`, `Spec.ldClose_done`): a step without rounds from any joint with core
    type `Unit` that claims nothing any more (some fixed witness is in its relaxed relation on every
    statement with its condition) to the trivial statement: a tail, at every q (what is needed of
    the oracles) that allows the empty set. So test ; test ; .. ; `ldDone` is a tail, under the
    tests' hypotheses (Cb/Ld/LdLinCloseKit.lean: closed, then a tail, is a tail).

Limits: this file does not say that any bound on a list holds (L is a hypothesis:
`G.C.ListAt G.e L`; such a bound, under hypotheses of its own: `ldGroupJohn_list`,
Cb/Ld/LdGroupJohn.lean). It says nothing on which groups a protocol forms. That every oracle message
is closed by some test is seen from the types only at the end of a chain (the last signature is
empty).
Declared differences to a write-up of ours (lean/CREDITS.md; by a reading): those of
Cb/Ld/LdBatSig.lean and Cb/Ld/LdGroup.lean; the write-up's run that ends in the trivial
relation is this file's (which ends at `(S.sub kp).over A₀`, A₀ of the kept messages, not in the
trivial
relation: `Spec.ldClose_run`); its run that ends in a switch with a sample is Cb/Ld/LdGroup.lean's
run followed by a sending and the locations.
The notion of a run follows this protocol's technical report, which follows a theorem of the paper
that this protocol builds on; the blocks follow that paper (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdGroup
import Cb.Ld.LdLinCloseKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

section
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} (G : Grp S) [Nonempty G.P]
  (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
  (Z : Evader E (G.Row B)) (St₀ Wp : Type) (E₀ : ExtSpec) (T : LdEnd (G.joint Sb sl Z))

/-- the step without rounds that drops the trivial statement -/
def ldDropT :
    IOR (Unit × LdCarX kp St₀) (extNone.prod (LdCarE kp E₀)) (LdCarX kp St₀) (LdCarE kp E₀) :=
  IOR.pure (fun x => some x.2) (ExtMap.snd extNone (LdCarE kp E₀))

def ldDropTH : (ldDropT kp St₀ E₀).Honest (Unit × LdCarW kp Wp) (LdCarW kp Wp) :=
  IOR.Honest.pure _ _ fun a => (a.1.2, a.2.2)

/-- A whole test on a group, beside the carried part. -/
def ldRunE :
    IOR ((((B → E) × (∀ b, Sb b)) × St₀) × S.Smp) (E₀.prod S.ext) (LdCarX kp St₀) (LdCarE kp E₀) :=
  (ldBridge G kp Sb Z St₀ E₀).seq
    ((T.R.keep (LdCarX kp St₀) (LdCarE kp E₀)).seq (ldDropT kp St₀ E₀))

def ldRunEH : (ldRunE G kp Sb sl Z St₀ E₀ T).Honest (S.Wit × Wp) (LdCarW kp Wp) :=
  (ldBridgeH G kp Sb Z St₀ Wp E₀).seq
    (((T.H.keep (LdCarX kp St₀) (LdCarE kp E₀)).carry (LdCarW kp Wp)).seq (ldDropTH kp St₀ Wp E₀))

/-- The extractor: the carried witness is copied, the test's extractor gives a witness on the
complex; then the bridge's. d, d': values where nothing was output. -/
def ldRunEX (hc : ∀ o, G.mem o ∨ kp o) (d : S.Wit × Wp) (d' : LdBrW G kp Wp) :
    (((((B → E) × (∀ b, Sb b)) × St₀) × S.Smp) × (E₀.prod S.ext).Str) →
    Tr (ldRunE G kp Sb sl Z St₀ E₀ T).shape → LdCarW kp Wp → S.Wit × Wp :=
  IOR.extSeq (ldBridge G kp Sb Z St₀ E₀) _ (fun _ _ w => ldBrBack G kp Wp hc w)
    (IOR.extSeq (T.R.keep (LdCarX kp St₀) (LdCarE kp E₀)) (ldDropT kp St₀ E₀)
      (fun a τ w => (T.ext (a.1.1, a.2.1) τ w.1, w.2)) (fun _ _ w => ((), w)) d') d

def ldRunEN (Kc : Type) (err : ℕ) : IOR.Nums Kc (ldRunE G kp Sb sl Z St₀ E₀ T) :=
  (ldBridgeN G kp Sb Z St₀ E₀ Kc err).seq
    ((T.N.beside Kc (LdCarX kp St₀) (LdCarE kp E₀)).seq (IOR.Nums.pure Kc _ _))

end

/-- Nothing is left: a step without rounds to the trivial statement. -/
def ldDone (X : Type) (Eo : ExtSpec) : IOR X Eo Unit extNone :=
  IOR.pure (fun _ => some ()) (ExtMap.toNone Eo)

def ldDoneH (X W : Type) (Eo : ExtSpec) : (ldDone X Eo).Honest W Unit :=
  IOR.Honest.pure _ _ fun _ => ((), ())

namespace Spec

/-- The end of a chain. -/
def ldClose_done : Prop :=
  ∀ (X W : Type) (Eo : ExtSpec) (A : Rels Unit X Eo W) (w₀ : W) (q : Finset Eo.Pos → Prop),
    (∀ a, A.on a → A.relR a w₀) → q ∅ →
    TailTr (ldDone X Eo) (ldDoneH X W Eo) A trivRels (fun _ _ _ => w₀) (IOR.Nums.pure Unit _ _) q

open Classical in
/-- States, under the hypotheses below: a whole test on a group, beside what is carried, is a closed
piece of a chain (`ClosedTr`). -/
def ldClose_run : Prop :=
  ∀ (E B Kc St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (L : ℕ) (E₀ : ExtSpec) (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
      (hc : ∀ o, G.mem o ∨ kp o) (d : S.Wit × Wp) (d' : LdBrW G kp Wp) (T : LdEnd (G.joint Sb sl Z))
      (t : ℕ) (qi : Finset (E₀.prod S.ext).Pos → Prop) (qF : Finset (LdCarE kp E₀).Pos → Prop),
    Z.OK → G.C.ListAt G.e L → G.Fits → T.OK t →
    (∀ U, besideQ ((G.joint Sb sl Z).atMost t) qF U → qi (U.biUnion (ldBrG G kp E₀).src)) →
    ClosedTr (ldRunE G kp Sb sl Z St₀ E₀ T) (ldRunEH G kp Sb sl Z St₀ Wp E₀ T)
      (S.over
        (claimRels (fun x m => Slf.All sl x (G.msg m)) (onMsgRels (S.res (T := OMsg.Msg) kp) A₀)))
      ((S.sub kp).over A₀) (ldRunEX G kp Sb sl Z St₀ Wp E₀ T hc d d')
      (ldRunEN G kp Sb sl Z St₀ E₀ T Kc (L * Z.err)) qi qF

/-- Rounds, errors, what is withheld. -/
def ldClose_run_data : Prop :=
  ∀ (E B Kc St₀ : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
      (Z : Evader E (G.Row B)) (err : ℕ) (E₀ : ExtSpec) (T : LdEnd (G.joint Sb sl Z)),
    (ldRunE G kp Sb sl Z St₀ E₀ T).shape.length = T.R.shape.length + 1 ∧
    (ldRunEN G kp Sb sl Z St₀ E₀ T Kc err).err =
      Err.app (s := (ldBridge G kp Sb Z St₀ E₀).shape) (t := T.R.shape ++ []) (err, ())
        (Err.app (s := T.R.shape) (t := []) T.N.err ()) ∧
    (ldRunEN G kp Sb sl Z St₀ E₀ T Kc err).pBad = 0 + (T.N.pBad + 0) ∧
    (ldRunEN G kp Sb sl Z St₀ E₀ T Kc err).pHid = 0 + (T.N.pHid + 0)

end Spec
end Cb
