-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendFam.lean: the sending of several oracle messages in one prover message, each with its
own sample, as an interactive oracle reduction.

The file has a two-round reduction in which the prover sends several words as one oracle, one
verifier message gives every word its seed, and the honest prover answers, for each word, with
linear functionals of the message that it encodes.

Definitions and statements (Cb.Spec.ldSendFam_*); the proofs are in Cb/Ld/LdSendFamProofs.lean. The
joints are those of Cb/Ld/LdSig.lean; the block for one oracle message is Cb/Ld/LdSend.lean.

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
only copied. (A may hold a relation that is relaxed existentially, open inside a test, beside one
that is relaxed by decoding; the two relaxations: the head of Cb/Ld/LdSig.lean.)
To `N.over (N.pull A back)`: N a signature, the family that is sent; statement ((x, samples of N),
(y, words of N)), witness ((message, randomness) for each member, w'): A is claimed of
`back messages w'` (the function `back`, applied to the messages and to w').
Two rounds, none merged; one of them has a verifier message that is not empty.
  Round 1: the prover sends the words of all members of N, as one oracle (a position is (name,
  native position)). The verifier sends one joint seed.
  Round 2: the prover sends, in the clear, the answers of all members. The verifier sends nothing.
How the seeds of the members are drawn is a parameter (`Sig.Seeds`): a finite, non-empty set D of
joint seeds, for each member a map from D to its own seeds, and a number mult a. `Seeds.Fair`: a
seed of the member a comes from at most mult a joint seeds.
  A union bound needs no more than `Fair`.
The errors, counts of values of one verifier message: round 1: the sum over the members a of
mult a · (L a choose 2) · (Z a).err; round 2: 0. If mult a · (number of seeds of a) = |D| (exact
marginals), this is, as a probability, the sum of the members' own errors.
Knowledge soundness is "on the statements of A, into collision-free statements", as for one member;
the extractor is `back messages w'` and reads the output witness alone; the backward step holds on
every transcript.
The honest side (`Sig.Sender`): one encoding `Nn` of the whole family in the members' formats, coins
`Mk` that go into the messages, `put`, `rest`, `w0`, as in Cb/Ld/LdSend.lean. Honest-verifier zero
knowledge in our exact form (`Honest.ExactWith`, Ior/Honest.lean) from: `D.Blind` (at every
joint seed the joint law of all answers does not depend on A's witness) and `Nn.Hides (N.budT t)`:
`t a` long positions of each member a.
The state function (`ldSendFamState`) is for round-by-round knowledge soundness in the literature's
form, with a state function (`HasRbrKnowledgeWith`, Ior/KnowCollLit.lean). It says:
  before the seed: the witness is in A's relaxed relation (`A.relR`);
  after the seed and after the answers: the state before, or a collision of some member;
  at the end: the output statement is outside the condition, or the witness is in its relaxed
  relation.

Main names, each under the hypotheses of its statement: `Spec.ldSendFam_data` (two rounds, the
second verifier message has one value; the verifier reads nothing and never rejects; which positions
a query to the output's oracles reads), `Spec.ldSendFam_acc`, `Spec.ldSendFam_within` (the bad
values are within the errors), `Spec.ldSendFam_out_on` (at the other joint seeds the output meets
the condition), `Spec.ldSendFam_into`, `Spec.ldSendFam_literal`, `Spec.ldSendFam_exactWith`,
`Spec.ldSendFam_goodT`, `Spec.ldSendFam_good` (as `Spec.ldSendFam_goodT`, for the bundle `Good`),
`Spec.ldSendFam_chain`.

What `Laws`, `Fair`, `ListLE`, `Evades`, `Blind` and `Hides` ask: the head of Cb/Ld/LdRng.lean
("What the sending's hypotheses ask").

Notation: `L`, `t`: a number for each member of N (`N.O → ℕ`); `Kc`: the type of the cores of
witnesses (`Rels.core`, Ior/Chain.lean); `A.cf`: the joint A with the condition (`A.on`) moved into
the relaxed relation (`Rels.cf`, Ior/KnowCollGood.lean).

Limits: how `Blind` and `Hides` of a family follow from those of its members under independent coins
is not here. Unsampled oracles that go in the same prover message are not here. A sum of errors at
or above |D| says nothing.
That several oracle messages may go in one prover message, with one answer each and errors that add,
is this protocol's technical report (lean/CREDITS.md). Its case is `Seeds.parts`: one joint seed for
the oracle messages of one prover message, of which each member reads a part, and one answer each.
`Seeds.indep` (a seed for
each member) is a wider case; the parameter covers both.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSend
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

namespace Sig
variable {E : Type} (N : Sig E)

/-- How the seeds of the members are drawn: the data. -/
structure Seeds where
  D : Type
  [fin : Fintype D]
  [ne : Nonempty D]
  /-- the seed of a member -/
  sd : ∀ a, D → (N.om a).Z.D
  /-- from how many joint seeds a seed of a member may come -/
  mult : N.O → ℕ

attribute [instance] Seeds.fin Seeds.ne

variable {N} in
def Seeds.Fair (Sd : N.Seeds) : Prop :=
  ∀ a (ρ : (N.om a).Z.D), cnt (fun s : Sd.D => Sd.sd a s = ρ) ≤ Sd.mult a

/-- Independent seeds. -/
@[reducible] def Seeds.indep : N.Seeds :=
  { D := ∀ a, (N.om a).Z.D, sd := fun a s => s a,
    mult := fun a => ∏ b ∈ Finset.univ.erase a, Fintype.card (N.om b).Z.D }

/-- One seed for all, of which each member reads a part: for each member the joint seeds are the
pairs (its own seed, a rest). -/
@[reducible] def Seeds.parts (D : Type) [Fintype D] [Nonempty D] (Rst : N.O → Type)
    [∀ a, Fintype (Rst a)] (e : ∀ a, D ≃ (N.om a).Z.D × Rst a) : N.Seeds :=
  { D := D, sd := fun a s => (e a s).1, mult := fun a => Fintype.card (Rst a) }

/-- the words as sent, read natively: a position is (name, native position) -/
abbrev nat : ExtSpec :=
  ⟨N.ext.Str, Σ a, (N.om a).C.NP,
    Σ p : (Σ a, (N.om a).C.NP), (N.om p.1).Sy p.2, fun f p => ⟨p, f p.1 p.2⟩⟩

/-- The joint A, a part of whose witness is made from the messages of N. -/
def pull {Kc X W W' : Type} {E₀ : ExtSpec} (A : IOR.Rels Kc X E₀ W) (back : N.Msg → W' → W) :
    IOR.Rels Kc X E₀ (N.Msg × W') where
  rel  := fun x y w => A.rel x y (back w.1 w.2)
  relR := fun a w => A.relR a (back w.1 w.2)
  on   := A.on
  core := fun w => A.core (back w.1 w.2)

/-- Round 1: all words as one oracle; a joint seed. -/
@[reducible] def sendRound (Sd : N.Seeds) : Round where
  Orc := N.ext.Str
  Pos := Σ a, (N.om a).C.NP
  Sym := fun p => (N.om p.1).Sy p.2
  rd := fun f p => f p.1 p.2
  Plain := Unit
  Chal := Sd.D
  dOrc := fun a => (N.om a).sy0
  dPlain := ()

def sendPoint (Sd : N.Seeds) : (N.sendRound Sd).IsPoint where
  finPos := inferInstance
  decPos := inferInstance
  ofSyms := fun g a p => g ⟨a, p⟩
  rd_ofSyms := fun _ _ => rfl
  ofSyms_rd := fun _ => rfl
  zero := fun p => (N.om p.1).sy0 p.2

/-- the answers of all members -/
abbrev Answ : Type := ∀ a, (N.om a).Z.S → E

/-- the two rounds -/
abbrev sh [Zero E] (Sd : N.Seeds) : Shape := [N.sendRound Sd, plainRound N.Answ Unit fun _ _ => 0]

def pt [Zero E] (Sd : N.Seeds) : (N.sh Sd).IsPoint := (N.sendPoint Sd, plainPoint _ _ _, ())

/-- The budget of the family: for each member a, native positions that are read for at most t a of
its long positions. -/
def budT (t : N.O → ℕ) : Finset (Σ a, (N.om a).C.NP) → Prop := fun U =>
  ∀ a, ∃ Xs : Finset (N.om a).P,
    Xs.card ≤ t a ∧ ∀ p, (⟨a, p⟩ : Σ a, (N.om a).C.NP) ∈ U → p ∈ Xs.biUnion (N.om a).C.src

end Sig

section
variable {E : Type} [Field E] (N : Sig E) (Sd : N.Seeds)

open Classical in
/-- The sending of a family. -/
def ldSendFam (X : Type) (E₀ : ExtSpec) : IOR X E₀ (X × N.Smp) (E₀.prod N.ext) where
  shape := N.sh Sd
  blinded _ := true
  extReads _ := ∅
  reads _ := ∅
  out x _ τ := some (x, fun a => (Sd.sd a τ.2.1, τ.2.2.1.2 a))
  imp y τ := (y, τ.1.1)
  srcE _ q := match q with
    | .inl p => {p}
    | .inr _ => ∅
  srcO _ q := match q with
    | .inl _ => ∅
    | .inr x => ((N.om x.1).C.src x.2).image fun p => Sum.inl ⟨x.1, p⟩
  tie _ _ := ∅

/-- A set of positions of the prover's oracles, as a set of native positions of the words. -/
def ldSendFamSet (T : Finset (OPos (N.sh Sd))) : Finset (Σ a, (N.om a).C.NP) :=
  Finset.toLeft (α := Σ a, (N.om a).C.NP) (β := Empty ⊕ Empty) T

/-- The honest sender of a family: the data. -/
structure Sig.Sender (W W' : Type) where
  Nn  : Hiop.Enc N.nat
  upM : Nn.Msg → N.Msg
  upR : Nn.Rnd → ∀ a, (N.om a).Rnd
  Mk  : Type
  [finMk : Fintype Mk]
  [neMk  : Nonempty Mk]
  put  : W → Mk → Nn.Msg
  rest : W → W'
  w0   : W

attribute [instance] Sig.Sender.finMk Sig.Sender.neMk

variable {N} {W W' : Type}

structure Sig.Sender.Laws (D : N.Sender W W') (back : N.Msg → W' → W) : Prop where
  enc  : ∀ m r a, (N.om a).upW (D.Nn.enc m r a) = (N.om a).C.enc (D.upM m a) (D.upR r a)
  back : ∀ w k, back (D.upM (D.put w k)) (D.rest w) = w

/-- the answers of the honest sender at a joint seed -/
def Sig.Sender.ans (D : N.Sender W W') (Sd : N.Seeds) (s : Sd.D) (w : W) (k : D.Mk) : N.Answ :=
  fun a => (N.om a).Z.val (Sd.sd a s) (D.upM (D.put w k) a)

open Classical in
/-- At every joint seed the joint law of all answers does not depend on the witness. -/
def Sig.Sender.Blind (D : N.Sender W W') (Sd : N.Seeds) : Prop :=
  ∀ s w w', (unif D.Mk).map (D.ans Sd s w) = (unif D.Mk).map (D.ans Sd s w')

variable (X : Type) (E₀ : ExtSpec)

/-- The honest side. Nothing is withheld. -/
def ldSendFamHon (D : N.Sender W W') :
    (ldSendFam N Sd X E₀).Honest W (N.Wit × W') where
  Coin := D.Mk × D.Nn.Rnd
  strat w x c := ((D.Nn.enc (D.put w c.1) c.2, ()),
    fun s =>
      (((), D.ans Sd s w c.1),
        fun _ =>
          ((x, fun a => (Sd.sd a s, D.ans Sd s w c.1 a)),
            (fun a => (D.upM (D.put w c.1) a, D.upR c.2 a), D.rest w))))
  Bad := ∅
  Hid _ _ := ∅

open Classical in
/-- The simulator: the honest prover on the fixed witness. -/
def ldSendFamSim (D : N.Sender W W') :
    IOR.Honest.Sim (ldSendFam N Sd X E₀) := fun x ρ T _ =>
  (unif (D.Mk × D.Nn.Rnd)).map fun c =>
    some ((ldSendFam N Sd X E₀).view T (((ldSendFamHon Sd X E₀ D).strat D.w0 x c).run ρ).1)

variable (N)

/-- The bad values: the joint seeds at which some member has a collision for its word. -/
def ldSendFamBad : BadFam (N.sh Sd) :=
  (fun m => {s | ∃ a, (N.om a).Clash (m.1 a) (Sd.sd a s)}, fun _ _ => (fun _ => ∅, fun _ _ => ()))

variable {X E₀} {Kc : Type} in
open Classical in
/-- The knowledge state function. -/
def ldSendFamState (A : IOR.Rels Kc X E₀ W) (back : N.Msg → W' → W) (a : X × E₀.Str) :
    PTr (N.sh Sd) → W ⊕ (N.Wit × W') → Bool
  | .atP (.inl _), s => decide (onLeft A.relR a s)
  | .atV (.inl _), s => decide (onLeft A.relR a s)
  | .atP (.inr (m, ρ, _)), s => decide (onLeft A.relR a s ∨ ∃ i, (N.om i).Clash (m.1 i) (Sd.sd i ρ))
  | .atV (.inr (m, ρ, _)), s => decide (onLeft A.relR a s ∨ ∃ i, (N.om i).Clash (m.1 i) (Sd.sd i ρ))
  | .full τ, s =>
    decide (∃ b,
        (ldSendFam N Sd X E₀).red.out a τ = some b ∧ onRight (N.over (N.pull A back)).cf.relR b s)

/-- the error of round 1 -/
def ldSendFamErr (L : N.O → ℕ) : ℕ := ∑ a, Sd.mult a * ((L a).choose 2 * (N.om a).Z.err)

/-- The numbers. -/
def ldSendFamNums (Kc : Type) (L t : N.O → ℕ) : IOR.Nums Kc (ldSendFam N Sd X E₀) :=
  ⟨(ldSendFamErr N Sd L, (0, ())), 0, 0, fun _ T => N.budT t (ldSendFamSet N Sd T), fun _ => ∅⟩

end

namespace Spec
open IOR

section
variable (E : Type) [Field E]

/-- The count: the words are fixed before the joint seed is drawn. -/
def ldSendFam_cnt : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (L : N.O → ℕ), Sd.Fair →
    (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    ∀ f : N.ext.Str,
      cnt (fun s : Sd.D => ∃ a, (N.om a).Clash (f a) (Sd.sd a s)) ≤ ldSendFamErr N Sd L

/-- Independent seeds are fair, and their marginals are exact. -/
def ldSendFam_fair_indep : Prop :=
  ∀ N : Sig E,
    (Sig.Seeds.indep N).Fair ∧
    ∀ a, (Sig.Seeds.indep N).mult a * Fintype.card (N.om a).Z.D = Fintype.card (Sig.Seeds.indep N).D

/-- One seed of which each member reads a part: fair, with exact marginals. -/
def ldSendFam_fair_parts : Prop :=
  ∀ (N : Sig E) (D : Type) [Fintype D] [Nonempty D] (Rst : N.O → Type)
      [∀ a, Fintype (Rst a)] (e : ∀ a, D ≃ (N.om a).Z.D × Rst a),
    (Sig.Seeds.parts N D Rst e).Fair ∧
    ∀ a, (Sig.Seeds.parts N D Rst e).mult a * Fintype.card (N.om a).Z.D = Fintype.card D

def ldSendFam_data : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (X : Type) (E₀ : ExtSpec),
    (ldSendFam N Sd X E₀).shape.length = 2 ∧
    (∀ ρ ρ' : Rho (N.sh Sd), ρ.1 = ρ'.1 → ρ = ρ') ∧
    (∀ ρ, (ldSendFam N Sd X E₀).extReads ρ = ∅) ∧
    (∀ ρ, (ldSendFam N Sd X E₀).reads ρ = ∅) ∧
    (∀ ρ p, (ldSendFam N Sd X E₀).tie ρ p = ∅) ∧
    (∀ x y τ, ((ldSendFam N Sd X E₀).out x y τ).isSome) ∧
    (∀ ρ p,
      (ldSendFam N Sd X E₀).srcE ρ (.inl p) = {p} ∧ (ldSendFam N Sd X E₀).srcO ρ (.inl p) = ∅) ∧
    (∀ ρ q,
      (ldSendFam N Sd X E₀).srcE ρ (.inr q) = ∅ ∧
      ∀ p,
        p ∈ (ldSendFam N Sd X E₀).srcO ρ (.inr q) ↔
        ∃ n ∈ (N.om q.1).C.src q.2, (Sum.inl ⟨q.1, n⟩ : OPos (N.sh Sd)) = p) ∧
    ∀ (W W' : Type) (D : N.Sender W W'),
      (ldSendFamHon Sd X E₀ D).Bad = ∅ ∧ ∀ w x, (ldSendFamHon Sd X E₀ D).Hid w x = ∅

/-- Perfect completeness. -/
def ldSendFam_acc : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
      (back : N.Msg → W' → W) (D : N.Sender W W'),
    D.Laws back → (ldSendFamHon Sd X E₀ D).Acc A.rel (N.over (N.pull A back)).rel

def ldSendFam_within : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (L : N.O → ℕ), Sd.Fair → (∀ a, (N.om a).ListLE (L a)) →
    (∀ a, (N.om a).Evades) → (ldSendFamBad N Sd).Within (ldSendFamErr N Sd L, (0, ()))

def ldSendFam_out_on : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
      (back : N.Msg → W' → W) a (τ : Tr (N.sh Sd)) b,
    A.on a → (ldSendFamBad N Sd).Clean τ →
    (ldSendFam N Sd X E₀).red.out a τ = some b → (N.over (N.pull A back)).on b

/-- The backward step holds on every transcript. -/
def ldSendFam_back : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
      (back : N.Msg → W' → W) a (τ : Tr (N.sh Sd)) b w,
    (ldSendFam N Sd X E₀).red.out a τ = some b →
    (N.over (N.pull A back)).relR b w → A.relR a (back (N.msgs w.1) w.2)

/-- Round-by-round knowledge soundness, on the statements of A, into collision-free statements. -/
def ldSendFam_into : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
      (back : N.Msg → W' → W) (L : N.O → ℕ),
    Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    (ldSendFam N Sd X E₀).red.KnowInto A.on (N.over (N.pull A back)).on
      A.relR (N.over (N.pull A back)).relR
      (fun _ _ w => back (N.msgs w.1) w.2) (ldSendFamErr N Sd L, (0, ()))

/-- The literature's form, with the state function "the state before, or a collision of some
member"; the round extractors: the identity, then "back". -/
def ldSendFam_literal : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
      (back : N.Msg → W' → W) (L : N.O → ℕ),
    Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    (ldSendFam N Sd X E₀).red.HasRbrKnowledgeWith A.on (onLeft A.relR)
      (onRight (N.over (N.pull A back)).cf.relR) (ldSendFamState N Sd A back)
      (fun _ => RExt.ofFull (N.sh Sd) fun _ w => back (N.msgs w.1) w.2)
      (ldSendFamErr N Sd L, (0, ()))

/-- Exact honest-verifier zero knowledge, with the simulator named, for every input relation.
(not all hypotheses are named here: see the statement below) -/
def ldSendFam_exactWith : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (X W W' : Type) (E₀ : ExtSpec) (D : N.Sender W W')
      (t : N.O → ℕ) (Ri : X → E₀.Str → W → Prop),
    D.Blind Sd → D.Nn.Hides (N.budT t) →
    (ldSendFamHon Sd X E₀ D).ExactWith
      Ri (fun _ T => N.budT t (ldSendFamSet N Sd T)) (ldSendFamSim Sd X E₀ D)

/-- Under the hypotheses below, the sending of a family leads from A into the joint over the family,
collision-free. -/
def ldSendFam_goodT : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
      (back : N.Msg → W' → W) (D : N.Sender W W') (L t : N.O → ℕ),
    (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    D.Laws back → D.Blind Sd → D.Nn.Hides (N.budT t) →
    GoodT (ldSendFam N Sd X E₀) (ldSendFamHon Sd X E₀ D) A (N.over (N.pull A back)).cf
      (fun _ _ w => back (N.msgs w.1) w.2) (ldSendFamNums N Sd X E₀ Kc L t)

def ldSendFam_good : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
      (back : N.Msg → W' → W) (D : N.Sender W W') (L t : N.O → ℕ),
    (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    D.Laws back → D.Blind Sd → D.Nn.Hides (N.budT t) →
    Good (ldSendFam N Sd X E₀) (ldSendFamHon Sd X E₀ D) A (N.over (N.pull A back)).cf
      (fun _ _ w => back (N.msgs w.1) w.2) (ldSendFamNums N Sd X E₀ Kc L t)

/-- As it enters a chain: from A.cf. -/
def ldSendFam_chain : Prop :=
  ∀ (N : Sig E) (Sd : N.Seeds) (Kc X W W' : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ W)
      (back : N.Msg → W' → W) (D : N.Sender W W') (L t : N.O → ℕ),
    (∀ a, (N.om a).C.Laws) → Sd.Fair → (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    D.Laws back → D.Blind Sd → D.Nn.Hides (N.budT t) →
    GoodT (ldSendFam N Sd X E₀) (ldSendFamHon Sd X E₀ D) A.cf (N.over (N.pull A back)).cf
      (fun _ _ w => back (N.msgs w.1) w.2) (ldSendFamNums N Sd X E₀ Kc L t)

end
end Spec
end Cb
