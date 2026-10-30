-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSend.lean: the sending of an oracle message with its sample, as an interactive oracle
reduction.

The sending is a two-round reduction that lets a protocol speak of the message of a word also beyond
the unique-decoding radius. The prover sends a word as an oracle, the verifier draws a seed, and the
honest prover answers with the linear functionals, determined by the seed, of the message that the
word encodes. Seed and answers become part of the statement; in the relaxed relation (`relR` of
`IOR.Rels`, Ior/Chain.lean) the witness's message is what the decoder `OMsg.dec` returns on the
word, the seed and these answers.

Definitions and statements (Cb.Spec.ldSend_*); the proofs are in Cb/Ld/LdSendProofs.lean. The joints
are those of Cb/Ld/LdSig.lean.

A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and of
witness: the honest relation; a second relation, called relaxed, of which round-by-round knowledge
soundness speaks; the set of statements of which that soundness speaks; and a map from a witness to
its core.
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

From any joint A (`Iop.IOR.Rels`): statements (x, y) of any kind, witnesses W. The oracles y are
only copied.
To `o.sent A back`: statement ((x, sample), (y, word)), witness ((message, randomness), w'): a part
of A's witness is now in the message of the oracle message o, and A is claimed of `back message w'`
(the function `back`, applied to the message and to w').
Two rounds, none merged.
  Round 1: the prover sends a word in the format of o, as an oracle. The verifier sends a seed of
  the sample map of o.
  Round 2: the prover sends, in the clear, one answer for each row of the sample. The verifier sends
  nothing (its message has one value).
  The verifier reads nothing, never rejects, and outputs the old explicit part with the sample
  (seed, answers). The new implicit instance is the old one and, beside it, the word sent, read
  under the transformation of o's code: a query to it costs the native queries that this
  transformation makes.
The extractor goes backwards and reads the witness of the output statement alone: `back message w'`.
It uses no decoding, no oracle and no verifier message.

Round-by-round knowledge soundness is "on the statements of A, into collision-free statements"
(Ior/KnowColl.lean: `KnowInto`). The errors are counts of values of one verifier message:
  round 1: (L choose 2) · Z.err. L bounds the lists of messages of o at its radius. As a probability
  at most L²/2 · (error of the sample).
  round 2: 0.
  The only bad values are the seeds with a collision for the word sent (`OMsg.Clash`). The backward
  step (a witness of the output statement in the relaxed relation gives one of the input statement)
  holds on every transcript (`Spec.ldSend_back`): the error is needed for the condition alone.
The state function (`ldSendState`) is for the literature's form of the notion (a knowledge state
function with round extractors: `HasRbrKnowledgeWith`, Ior/KnowCollLit.lean). It says:
  before the seed: the witness is in A's relaxed relation;
  after the seed, and after the answers: the state before, or a collision;
  at the end: the output statement is outside the condition, or the witness is in its relaxed
  relation (there the message is the decoding).

The honest side (`OMsg.Sender`: data).
  N: the encoding in the format of o (typed messages and randomness; for the plain format: that of
  the code), with upM, upR: how these are read over E.
  Mk: the coins that go into the message (masks, pad, free room).
  put: the message, from A's witness and these coins.
  rest: what remains a further witness.
  w0: a fixed witness, for the simulator.
  `Sender.Laws`: the encoding in the format is the code's; the extractor undoes "put". Nothing is
    withheld: completeness is perfect.
Honest-verifier zero knowledge, in our exact form with further reads (`Honest.ExactWith`,
Ior/Honest.lean), from two hypotheses:
  `D.Blind`: at every seed the law of the answers, over the coins Mk, does not depend on A's
    witness. Uniform answers (`D.Uniform`: what a pad under the sample gives) are a case:
    `Spec.ldSend_blind_of_uniform`; and uniform answers follow from privacy of the sample map, seed
    by seed, at every seed (Cb/Gen/OodDecPad.lean: `Private`), if the pad entries are coins that
    nothing else of "put" reads: `Spec.ldSend_uniform_of_private`.
  `D.N.Hides ..`: the native symbols of an encoding that are read for any t long positions have a
    law that does not depend on the message.
  The budget: the further positions are native positions read for at most t long positions of the
  new word. The simulator (`ldSendSim`) runs the honest prover on the fixed witness; it reads
  nothing of the input's oracles (it is given nothing of the input's oracles: the verifier reads
  nothing, nothing is tied; `IOR.given`, Ior/Honest.lean).

Main names, each under the hypotheses of its statement:
  `Spec.ldSend_data`: two rounds, the second verifier message has one value; the verifier reads
    nothing; which positions a query to the output's oracles reads (`srcE`, `srcO`); nothing is tied
    or withheld.
  `Spec.ldSend_acc`, `Spec.ldSend_into`, `Spec.ldSend_literal`, `Spec.ldSend_chain`: see their doc
    comments.
  `Spec.ldSend_exactWith`: exact honest-verifier zero knowledge with the simulator named, for every
    input relation.
  `Spec.ldSend_goodT`: the bundle `IOR.GoodT` from A to `(o.sent A back).cf`; `Spec.ldSend_good`:
    also `IOR.Good` (the extractor reads neither statement nor transcript).
What is asked: of the code, `o.C.Laws` (of these laws the proofs use one field alone, `loc`: its
transformation reads what it declares); of the oracle message, `o.ListLE L` and `o.Evades`
(Cb/Ld/LdSig.lean says where they come from). No range is asked of the radius: of the hypotheses,
`o.ListLE L` and `o.Evades` alone speak of it, through the lists at `o.e`. What `Laws`,
`ListLE`, `Evades`, `Blind` and `Hides` ask: the head of Cb/Ld/LdRng.lean ("What the sending's
hypotheses ask").

Notation: `o.C`: the code of o, read under a transformation; `o.Z`: the sample map, on all entries
of the message (`OMsg`, Cb/Ld/LdSig.lean); `Z.D`: the seeds (`Sample`, Cb/Gen/OodDec.lean); `Z.err`:
a number of seeds (`ℕ`; `o.Evades` speaks of it); `D`: the honest sender (`o.Sender W W'`); `Kc`:
the type of the cores of witnesses (`Rels.core`, Ior/Chain.lean); `A.cf`: the joint A with the
condition (`A.on`) moved into the relaxed relation (`Rels.cf`, Ior/KnowCollGood.lean).

Limits: the declared differences to a write-up of ours (lean/CREDITS.md) of the block are
these.
(1) The input joint is any joint, its oracles any oracles: the write-up's case is a
    constraint relation over the oracle messages sent before.
(2) Honest-verifier zero knowledge is exact and against every set of further positions within the
    budget, where the write-up has a statistical error of the encoding and uniform
    positions.
(3) One oracle message in a prover message; several in one prover message (one seed and one answer
    each, errors added) are not here.
(L choose 2) · Z.err at or above the number of seeds says nothing. This file says nothing on running
times or sizes. That a pad entry masks one shown scalar only is a matter of the protocol that uses
the block: here it is inside the hypothesis `Blind`.
The block follows the first step of a construction of the paper that this protocol builds on
(lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdSig
import Cb.Gen.OodDecSend
import Ior.KnowCollLit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

/-! ## The rounds -/

namespace OMsg
variable {E : Type} (o : OMsg E)

/-- the word as sent, read natively -/
abbrev nat : ExtSpec := ⟨o.Str, o.C.NP, Σ p, o.Sy p, fun f p => ⟨p, f p⟩⟩

/-- Round 1: a word in the format of o as an oracle; a seed. -/
@[reducible] def sendRound : Round where
  Orc := o.Str
  Pos := o.C.NP
  Sym := o.Sy
  rd := fun f p => f p
  Plain := Unit
  Chal := o.Z.D
  dOrc := o.sy0
  dPlain := ()

def sendPoint : o.sendRound.IsPoint where
  finPos := o.C.finNP
  decPos := o.C.decNP
  ofSyms := fun f => f
  rd_ofSyms := fun _ _ => rfl
  ofSyms_rd := fun _ => rfl
  zero := o.sy0

variable [Zero E]

/-- the two rounds -/
abbrev sh : Shape := [o.sendRound, plainRound (o.Z.S → E) Unit fun _ => 0]

def pt : o.sh.IsPoint := (o.sendPoint, plainPoint _ _ _, ())

end OMsg

section
variable {E : Type} [Field E] (o : OMsg E)

open Classical in
/-- The sending. -/
def ldSend (X : Type) (E₀ : ExtSpec) : IOR X E₀ (X × o.Smp) (E₀.prod o.ext) where
  shape := o.sh
  blinded _ := true
  extReads _ := ∅
  reads _ := ∅
  out x _ τ := some (x, (τ.2.1, τ.2.2.1.2))
  imp y τ := (y, τ.1.1)
  srcE _ q := match q with
    | .inl p => {p}
    | .inr _ => ∅
  srcO _ q := match q with
    | .inl _ => ∅
    | .inr x => (o.C.src x).image Sum.inl
  tie _ _ := ∅

/-- A set of positions of the prover's oracles, as a set of native positions of the word. -/
def ldSendSet (T : Finset (OPos o.sh)) : Finset o.C.NP :=
  Finset.toLeft (α := o.C.NP) (β := Empty ⊕ Empty) T

/-- The honest sender: the data. -/
structure OMsg.Sender (W W' : Type) where
  /-- the encoding in the format of o, and how its messages and randomness are read over E -/
  N   : Enc o.nat
  upM : N.Msg → o.Msg
  upR : N.Rnd → o.Rnd
  /-- the coins that go into the message -/
  Mk  : Type
  [finMk : Fintype Mk]
  [neMk  : Nonempty Mk]
  /-- the message; what remains a further witness; a fixed witness -/
  put  : W → Mk → N.Msg
  rest : W → W'
  w0   : W

attribute [instance] OMsg.Sender.finMk OMsg.Sender.neMk

variable {o} {W W' : Type}

/-- The laws of a sender. -/
structure OMsg.Sender.Laws (D : o.Sender W W') (back : o.Msg → W' → W) : Prop where
  enc  : ∀ m r, o.upW (D.N.enc m r) = o.C.enc (D.upM m) (D.upR r)
  back : ∀ w k, back (D.upM (D.put w k)) (D.rest w) = w

/-- the answers of the honest sender -/
def OMsg.Sender.ans (D : o.Sender W W') (ρ : o.Z.D) (w : W) (k : D.Mk) : o.Z.S → E :=
  o.Z.val ρ (D.upM (D.put w k))

open Classical in
/-- At every seed the law of the answers does not depend on the witness. -/
def OMsg.Sender.Blind (D : o.Sender W W') : Prop :=
  ∀ ρ w w', (unif D.Mk).map (D.ans ρ w) = (unif D.Mk).map (D.ans ρ w')

open Classical in
/-- At every seed the answers are uniform. -/
def OMsg.Sender.Uniform [Fintype E] (D : o.Sender W W') : Prop :=
  ∀ ρ w, (unif D.Mk).map (D.ans ρ w) = unif (o.Z.S → E)

variable (X : Type) (E₀ : ExtSpec)

/-- The honest side. Coins: those that go into the message, and the encoding randomness. Nothing is
withheld. -/
def ldSendHon (D : o.Sender W W') : (ldSend o X E₀).Honest W (o.Wit × W') where
  Coin := D.Mk × D.N.Rnd
  strat w x c := ((D.N.enc (D.put w c.1) c.2, ()), fun ρ => (((), D.ans ρ w c.1), fun _ =>
    ((x, (ρ, D.ans ρ w c.1)), ((D.upM (D.put w c.1), D.upR c.2), D.rest w))))
  Bad := ∅
  Hid _ _ := ∅

open Classical in
/-- The simulator: the honest prover on the fixed witness. -/
def ldSendSim (D : o.Sender W W') : IOR.Honest.Sim (ldSend o X E₀) := fun x ρ T _ =>
  (unif (D.Mk × D.N.Rnd)).map fun c =>
    some ((ldSend o X E₀).view T (((ldSendHon X E₀ D).strat D.w0 x c).run ρ).1)

variable (o)

/-- The bad values: the seeds with a collision for the word sent. -/
def ldSendBad : BadFam o.sh :=
  (fun m => {ρ | o.Clash m.1 ρ}, fun _ _ => (fun _ => ∅, fun _ _ => ()))

/-- The numbers. -/
def ldSendNums (Kc : Type) (L t : ℕ) : IOR.Nums Kc (ldSend o X E₀) :=
  ⟨(L.choose 2 * o.Z.err, (0, ())), 0, 0, fun _ T => o.C.budT t (ldSendSet o T), fun _ => ∅⟩

variable {X E₀} {Kc : Type}

open Classical in
/-- The knowledge state function. -/
def ldSendState (A : IOR.Rels Kc X E₀ W) (back : o.Msg → W' → W) (a : X × E₀.Str) :
    PTr o.sh → W ⊕ (o.Wit × W') → Bool
  | .atP (.inl _), s => decide (onLeft A.relR a s)
  | .atV (.inl _), s => decide (onLeft A.relR a s)
  | .atP (.inr (m, ρ, _)), s => decide (onLeft A.relR a s ∨ o.Clash m.1 ρ)
  | .atV (.inr (m, ρ, _)), s => decide (onLeft A.relR a s ∨ o.Clash m.1 ρ)
  | .full τ, s => decide (∃ b, (ldSend o X E₀).red.out a τ = some b ∧ onRight (o.sent A back).cf.relR b s)

end

namespace Spec
open IOR

section
variable (E : Type) [Field E]

open Classical in
/-- The data of the sending. -/
def ldSend_data : Prop :=
  ∀ (o : OMsg E) (X : Type) (E₀ : ExtSpec),
    (ldSend o X E₀).shape.length = 2 ∧
    (∀ ρ ρ' : Rho o.sh, ρ.1 = ρ'.1 → ρ = ρ') ∧
    (∀ ρ, (ldSend o X E₀).extReads ρ = ∅) ∧
    (∀ ρ, (ldSend o X E₀).reads ρ = ∅) ∧
    (∀ ρ p, (ldSend o X E₀).tie ρ p = ∅) ∧
    (∀ x y τ, ((ldSend o X E₀).out x y τ).isSome) ∧
    (∀ ρ p, (ldSend o X E₀).srcE ρ (.inl p) = {p} ∧ (ldSend o X E₀).srcO ρ (.inl p) = ∅) ∧
    (∀ ρ q,
      (ldSend o X E₀).srcE ρ (.inr q) = ∅ ∧
      ∀ p, p ∈ (ldSend o X E₀).srcO ρ (.inr q) ↔ ∃ n ∈ o.C.src q, (Sum.inl n : OPos o.sh) = p) ∧
    ∀ (W W' : Type) (D : o.Sender W W'),
      (ldSendHon X E₀ D).Bad = ∅ ∧ ∀ w x, (ldSendHon X E₀ D).Hid w x = ∅

/-- Perfect completeness. -/
def ldSend_acc : Prop :=
  ∀ (o : OMsg E) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
      (back : o.Msg → W' → W) (D : o.Sender W W'),
    D.Laws back → (ldSendHon X E₀ D).Acc A.rel (o.sent A back).rel

/-- Under `o.ListLE L` and `o.Evades`: the bad seeds are within the error. -/
def ldSend_within : Prop :=
  ∀ (o : OMsg E) (L : ℕ),
    o.ListLE L → o.Evades → (ldSendBad o).Within (L.choose 2 * o.Z.err, (0, ()))

/-- At the other seeds the output statement meets the condition, if the input statement meets A's
(`A.on a`). -/
def ldSend_out_on : Prop :=
  ∀ (o : OMsg E) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
      (back : o.Msg → W' → W) a (τ : Tr o.sh) b,
    A.on a → (ldSendBad o).Clean τ → (ldSend o X E₀).red.out a τ = some b → (o.sent A back).on b

/-- The backward step holds on every transcript. -/
def ldSend_back : Prop :=
  ∀ (o : OMsg E) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
      (back : o.Msg → W' → W) a (τ : Tr o.sh) b w,
    (ldSend o X E₀).red.out a τ = some b → (o.sent A back).relR b w → A.relR a (back w.1.1 w.2)

/-- Round-by-round knowledge soundness, on the statements of A, into collision-free statements. -/
def ldSend_into : Prop :=
  ∀ (o : OMsg E) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
      (back : o.Msg → W' → W) (L : ℕ),
    o.ListLE L → o.Evades →
    (ldSend o X E₀).red.KnowInto A.on (o.sent A back).on A.relR (o.sent A back).relR
      (fun _ _ w => back w.1.1 w.2) (L.choose 2 * o.Z.err, (0, ()))

/-- The literature's form, with the state function "the state before, or a collision"; the round
extractors: the identity, then "back". -/
def ldSend_literal : Prop :=
  ∀ (o : OMsg E) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
      (back : o.Msg → W' → W) (L : ℕ),
    o.ListLE L → o.Evades →
    (ldSend o X E₀).red.HasRbrKnowledgeWith A.on (onLeft A.relR)
      (onRight (o.sent A back).cf.relR) (ldSendState o A back)
      (fun _ => RExt.ofFull o.sh fun _ w => back w.1.1 w.2) (L.choose 2 * o.Z.err, (0, ()))

/-- Uniform answers do not depend on the witness. -/
def ldSend_blind_of_uniform [Fintype E] : Prop :=
  ∀ (o : OMsg E) (W W' : Type) (D : o.Sender W W'), D.Uniform → D.Blind

/-- Uniform answers from privacy of the sample map. The entries of the message are named J₀ ⊕ Pd
(entries proper, pad) by ν; the coins are (other coins, pad entries in F), and "put" lays the pad
entries on the pad and reads them nowhere else. -/
def ldSend_uniform_of_private [Fintype E] : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [Algebra F E] (o : OMsg E) (W W' : Type) (D : o.Sender W W')
      (J₀ Pd Mk₀ : Type) [Fintype J₀] [Fintype Pd] [Fintype Mk₀] [Nonempty Mk₀]
      (ν : o.C.J ≃ J₀ ⊕ Pd) (κ : D.Mk ≃ Mk₀ × (Pd → F)) (body : W → Mk₀ → J₀ → E),
    (∀ w k n, D.upM (D.put w k) (ν.symm n) = withPad (F := F) (body w (κ k).1) (κ k).2 n) →
    ((o.Z.comap ν.symm).Private F fun _ => True) → D.Uniform

/-- Exact honest-verifier zero knowledge, with the simulator named, for every input relation.
(not all hypotheses are named here: see the statement below) -/
def ldSend_exactWith : Prop :=
  ∀ (o : OMsg E) (X W W' : Type) (E₀ : ExtSpec) (D : o.Sender W W')
      (t : ℕ) (Ri : X → E₀.Str → W → Prop),
    D.Blind → D.N.Hides (o.C.budT t) →
    (ldSendHon X E₀ D).ExactWith Ri (fun _ T => o.C.budT t (ldSendSet o T)) (ldSendSim X E₀ D)

/-- Under the hypotheses below, the sending leads from A into "one more oracle message",
collision-free. -/
def ldSend_goodT : Prop :=
  ∀ (o : OMsg E) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W) (back : o.Msg → W' → W)
      (D : o.Sender W W') (L t : ℕ),
    o.C.Laws → o.ListLE L → o.Evades → D.Laws back → D.Blind → D.N.Hides (o.C.budT t) →
    GoodT (ldSend o X E₀) (ldSendHon X E₀ D) A (o.sent A back).cf
      (fun _ _ w => back w.1.1 w.2) (ldSendNums o X E₀ Kc L t)

/-- The same, as `IOR.Good`. -/
def ldSend_good : Prop :=
  ∀ (o : OMsg E) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W) (back : o.Msg → W' → W)
      (D : o.Sender W W') (L t : ℕ),
    o.C.Laws → o.ListLE L → o.Evades → D.Laws back → D.Blind → D.N.Hides (o.C.budT t) →
    Good (ldSend o X E₀) (ldSendHon X E₀ D) A (o.sent A back).cf
      (fun _ _ w => back w.1.1 w.2) (ldSendNums o X E₀ Kc L t)

/-- As it enters a chain: from `A.cf`. -/
def ldSend_chain : Prop :=
  ∀ (o : OMsg E) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W) (back : o.Msg → W' → W)
      (D : o.Sender W W') (L t : ℕ),
    o.C.Laws → o.ListLE L → o.Evades → D.Laws back → D.Blind → D.N.Hides (o.C.budT t) →
    GoodT (ldSend o X E₀) (ldSendHon X E₀ D) A.cf (o.sent A back).cf
      (fun _ _ w => back w.1.1 w.2) (ldSendNums o X E₀ Kc L t)

end
end Spec
end Cb
