-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/Gen.lean: the primitive of ZKCP/Defs.lean, in its stronger form, more general in three ways.

Not part of the definitions of ZKCP/Defs.lean. Defs.lean has the literal definition. The library of
proofs is built against the definitions of this file. They come back to Defs.lean at one oracle
{0,1}* → {0,1}^λ and R_yes = R_no, as follows. For a scheme of the form toGen A, whose prover proves
a batch slot by slot, ZKCP/Special.lean proves at batches of one that completeness and binding here
are equivalent to those of Defs.lean for A, and that privacy here implies privacy there. For every
scheme G that meets the definitions of this file for batches of at most B, B ≥ 1,
ZKCP/SpecialAny.lean proves that G, used with one request in each call (oneOf G), meets the literal
definition with the same three bounds (isZKCPArg_one); the bounds stay those of B slots, and nothing
but the three clauses is carried.

Limits of the way back. Privacy is an implication only: at B = 1 this file asks more than
Defs.lean (the environment may name an empty batch, or one slot that is not the adversary's), and no
converse is claimed. The equivalence for refined completeness (`ZKCP.HasRefinedCompletenessError`)
is not written. ZKCP/Special.lean is about schemes of the form toGen A only; a scheme with real
batches is not of that form.

A reader of a top theorem that is stated in the words of Defs.lean need not open this file; for the
theorems with batches this file is the statement. Defs.lean has no batches, so for the batch form
there is no literal definition to come back to. A definition is not proved: that this file is the
right batch form is a reading, not a theorem.

What is more general than the stronger form at the end of Defs.lean, and nothing else:

  (G1) oracles. A family S of independent uniformly random functions, each with its own domain and
       its own finite range (Rom.OSpec), in place of the one f. An algorithm with budget t asks the
       family at most t times in all. Why: the construction names its oracles by role (leaves,
       nodes, one Fiat-Shamir oracle for each protocol). Way back to one f: Rom.family
       (Rom/ExitPriv.lean; statement: `Rom.Spec.family`, Rom/Family.lean) proves that a scheme over
       S becomes a scheme over one f : {0,1}* → {0,1}^λ with the same three bounds, for every B,
       under three conditions: the answers of S are tuples of hash blocks of λ bits
       (`Rom.OracleCoding.rng`), the encoding (oracle, query, number of the hash block) ↦ string is a
       bijection, and the extractor reads only entries at oracles whose answer is one hash block.
       That this fails without the last condition is argued, not proved (the example in
       Rom/Family.lean).
  (G2) two relations. R_yes ⊆ R_no: completeness and the environment of the privacy experiment speak
       of R_yes, binding of R_no.
  (G3) batches. P proves a list of at most B pairs (x, w) at once, one proof for each slot; V checks
       one slot. In the privacy experiment the environment marks the slots that are the adversary's
       own; the adversary receives the (x, π) of these, in order and without their positions; for a
       batch the simulator is given only their instances, and neither the other slots nor their
       number.

As in the stronger form at the end of Defs.lean: the environment is given the adversary's whole view
so far and may decline (then the experiment ends); the extractor and the simulator can be named.

Where this file repeats a definition of Defs.lean, what the comments there say on how it is read
applies here as well. For two of these points that is argued and not proved, because the theorems
behind them are stated for Defs.lean only: that environments with coins are covered by deterministic
ones (ZKCP/Basic.lean, privacy_randomised_env), and that the strong form of privacy implies the
literal one.

What the definitions do not have. Draws, the symbol for "no answer", the notice and the abort are
not symbols of the definition: they are values of the proof type (a notice is a proof that V
rejects), or they are outside R_yes. Running time is not modelled.

The step of reading the leaves of a Merkle tree off the list of an algorithm's random-oracle
queries, without rewinding, is public: Paul Valiant,
"Incrementally Verifiable Computation or Proofs of Knowledge Imply Time/Space Efficiency", TCC
2008 (LNCS 4948, pages 1-18); Eli Ben-Sasson, Alessandro Chiesa and Nicholas Spooner, "Interactive
Oracle Proofs", ePrint 2016/116, state it as a procedure ("Valiant's extractor"). This library
assumes no result of these papers: it proves its own form of the step.

Notation: ZKCP: see `IsZKCPArg`, ZKCP/Defs.lean; ivk : IVK, isk : ISK: the two outputs of C
(`Arg.C`); ε, ζ : ℕ → ℕ → ℝ≥0∞, written ε tC tP, ζ tV N: the arguments bound the numbers of queries
of the adversary's committer, prover and verifier, and the number of batches
(`HasIndexBindingWith`, `PrivacyFor`).
-/
import ZKCP.Defs
import Prob.Tv
import Rom.Measure
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)
open Prob (pr sd)

/-! ## Relations (G2) -/

/-- Two indexed relations R_yes ⊆ R_no with the public parameters pp(i). Completeness and the
environment of the privacy experiment speak of R_yes, binding of R_no. Why: with approximate
arithmetic the honest prover serves a smaller relation than the one that an accepted proof
guarantees. The form of ZKCP/Defs.lean is R_yes = R_no. It matters which relation binding speaks of
(ZKCP/GenSanity.lean, quiet_not_binding_yy). -/
structure RelPair (I X W PP : Type) where
  yes : I → X → W → Prop
  no : I → X → W → Prop
  sub : ∀ i x w, yes i x w → no i x w
  pp : I → PP

/-- (i*, x, w) ∈ R_no for i* an index or ⊥; no triple with ⊥ is in it. -/
def RelPair.no' {I X W PP : Type} (R : RelPair I X W PP) : Option I → X → W → Prop
  | some i, x, w => R.no i x w
  | none, _, _ => False

/-- L_no(i) := {x : ∃ w, (i, x, w) ∈ R_no} and L_no(⊥) := ∅. -/
def RelPair.L {I X W PP : Type} (R : RelPair I X W PP) : Option I → Set X
  | some i => {x | ∃ w, R.no i x w}
  | none => ∅

/-! ## Syntax (G1, G3) -/

/-- One entry for each slot of the batch b: a list of the same length. -/
abbrev Slots (Pf : Type) {β : Type} (b : List β) : Type := {l : List Pf // l.length = b.length}

/-- ARG = (C, P, V) over the family S. P takes a batch and returns one proof for each slot: a list
of the same length, by type (Slots).
It is stateless, as in ZKCP/Defs.lean. V checks one pair (x, π) and knows nothing of batches. The
bound B on the length of a batch is a parameter of the properties and not of the scheme, so P must
be total on longer lists, and nothing is asked of it there. -/
structure Arg (S : OSpec) (I X W IVK ISK Pf : Type) where
  C : I → Rom.OComp S (IVK × ISK)
  P : ISK → (b : List (X × W)) → Rom.OComp S (Slots Pf b)
  V : IVK → X → Pf → Rom.OComp S Bool

section Properties
variable {S : OSpec} {I X W PP IVK ISK Pf : Type}
variable (R : RelPair I X W PP) (A : Arg S I X W IVK ISK Pf)

/-! ## Completeness -/

/-- Run V on every pair; the result is true if V accepts all of them. -/
def verifyAll (ivk : IVK) : List (X × Pf) → Rom.OComp S Bool
  | [] => pure true
  | (x, π) :: rest => do
      let c ← A.V ivk x π
      let cs ← verifyAll ivk rest
      pure (c && cs)

/-- One honest batch on a given key: the proofs of all slots, then V on each slot. -/
def sessionExp (ivk : IVK) (isk : ISK) (b : List (X × W)) : Rom.OComp S Bool := do
  let πs ← A.P isk b
  verifyAll A ivk ((b.map Prod.fst).zip πs.val)

def completenessExp (i : I) (b : List (X × W)) : Rom.OComp S Bool := do
  let (ivk, isk) ← A.C i
  sessionExp A ivk isk b

/-- A batch of at most B pairs, all in R_yes for the index i. -/
def ValidBatch (B : ℕ) (i : I) (b : List (X × W)) : Prop :=
  b.length ≤ B ∧ ∀ xw ∈ b, R.yes i xw.1 xw.2

/-- `ZKCP.HasCompletenessError`, for batches: for every valid batch, fixed before the oracles are
drawn, the probability that V rejects some slot is at most α. The empty batch is allowed, and its
error is 0. -/
def HasCompletenessError (B : ℕ) (α : ℝ≥0∞) : Prop :=
  ∀ i b, ValidBatch R B i b → Rom.Pr (completenessExp A i b) (fun _ => {c | c = false}) ≤ α

/-- The bad keys of `ZKCP.HasRefinedCompletenessError`, for a fixed family f. -/
def badKeys (B : ℕ) (αP : ℝ≥0∞) (i : I) (f : Fam S) : Set (IVK × ISK) :=
  {key | ∃ b, ValidBatch R B i b ∧ Rom.PrCoins f (sessionExp A key.1 key.2 b) {c | c = false} > αP}

/-- `ZKCP.HasRefinedCompletenessError`, for batches, rendered in the same way as completeness
above. -/
def HasRefinedCompletenessError (B : ℕ) (αC αP : ℝ≥0∞) : Prop :=
  ∀ i, Rom.Pr (A.C i) (fun f => badKeys R A B αP i f) ≤ αC

/-! ## Index binding (about V alone, so batches do not enter)

`ZKCP.HasIndexBinding`, word for word, over the family S and for R_no. -/

structure Extractor (S : OSpec) (I X W IVK Pf : Type) where
  Ei : IVK → Rom.Trace S → Option I
  Ew : IVK → Rom.Trace S → X → Pf → Rom.Trace S → W

/-- What the experiment of `ZKCP.HasIndexBinding` produces: the same record as in
Defs.lean. -/
abbrev BindingOutcome (I X W : Type) : Type := ZKCP.BindingOutcome I X W

/-- The experiment of `ZKCP.HasIndexBinding`, line by line. -/
def bindingExp {St : Type} (E : Extractor S I X W IVK Pf) (Ct : Rom.OComp S (IVK × St))
    (Pt : St → Rom.OComp S (X × Pf)) : Rom.OComp S (BindingOutcome I X W) := do
  let ((ivk, st), trC) ← Ct.withTrace
  let iStar := E.Ei ivk trC
  let ((x, π), trP) ← (Pt st).withTrace
  let w := E.Ew ivk trC x π trP
  let c ← A.V ivk x π
  pure ⟨c, iStar, x, w⟩

/-- The event of `ZKCP.HasIndexBinding`, for R_no. -/
def bindingBad : Set (BindingOutcome I X W) :=
  {o | o.accept = true ∧ (o.x ∉ R.L o.iStar ∨ ¬ R.no' o.iStar o.x o.w)}

def HasIndexBindingWith (E : Extractor S I X W IVK Pf) (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (tC tP : ℕ) (St : Type) (Ct : Rom.OComp S (IVK × St)) (Pt : St → Rom.OComp S (X × Pf)),
    Ct.QueryBound tC → (∀ st, (Pt st).QueryBound tP) →
      Rom.Pr (bindingExp A E Ct Pt) (fun _ => bindingBad R) ≤ ε tC tP

def HasIndexBinding (ε : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∃ E : Extractor S I X W IVK Pf, HasIndexBindingWith R A E ε

/-! ## Index privacy -/

/-- The adversarial verifier. A request is answered with the list of the (x, π) of its own slots of
the next batch. When a batch takes place is the adversary's choice (its request), and what is in it
is the environment's. A coalition is one adversary that owns several slots. -/
inductive AdvVerifier (S : OSpec) (X Pf : Type) : Type
  | halt : AdvVerifier S X Pf
  | query (o : S.ι) (q : S.Dom o) (k : S.Rng o → AdvVerifier S X Pf) : AdvVerifier S X Pf
  | sample (n : ℕ) (k : Fin (n + 1) → AdvVerifier S X Pf) : AdvVerifier S X Pf
  | request (k : List (X × Pf) → AdvVerifier S X Pf) : AdvVerifier S X Pf

def AdvVerifier.QueryBound : AdvVerifier S X Pf → ℕ → Prop
  | halt, _ => True
  | query _ _ _, 0 => False
  | query _ _ k, t + 1 => ∀ r, (k r).QueryBound t
  | sample _ k, t => ∀ r, (k r).QueryBound t
  | request k, t => ∀ l, (k l).QueryBound t

/-- The view: ivk, what each batch released, the query-answer trace, the values drawn. -/
structure View (S : OSpec) (IVK X Pf : Type) where
  ivk : IVK
  sessions : List (List (X × Pf))
  trace : Rom.Trace S
  coins : List ℕ

/-- A batch as the environment names it: for each slot the instance, the witness, and whether the
slot is the adversary's own.
Which slots are the adversary's own is fixed when the batch is named. A client that joins the
adversary after its batch was served is not covered. -/
abbrev Batch (X W : Type) : Type := List (X × W × Bool)

/-- What P is given. -/
def Batch.pairs (b : Batch X W) : List (X × W) := b.map fun s => (s.1, s.2.1)

/-- The instances of the adversary's own slots, in order. -/
def Batch.ownX (b : Batch X W) : List X := (b.filter fun s => s.2.2).map fun s => s.1

/-- The (x, π) of the adversary's own slots, in order and without their positions. Slot numbers are
seen by the adversary only if the scheme puts them into π. -/
def Batch.released (b : Batch X W) (πs : List Pf) : List (X × Pf) :=
  ((b.zip πs).filter fun s => s.1.2.2).map fun s => (s.1.1, s.2)

/-- The environment: a function of the adversary's whole view so far; none = it declines, and the
experiment ends. It is chosen after i, so it knows i. This is the stronger form at the end of
ZKCP/Defs.lean, and the only form in this file. It is valid (ViewEnv.IsValid) if every slot that it
names, own or not, is in R_yes for the index, and a batch has at most B slots. -/
abbrev ViewEnv (S : OSpec) (IVK X W Pf : Type) : Type := View S IVK X Pf → Option (Batch X W)

def ViewEnv.IsValid (B : ℕ) (Z : ViewEnv S IVK X W Pf) (i : I) : Prop :=
  ∀ v b, Z v = some b → ValidBatch R B i b.pairs

/-- Steps 3 and 4 of the real experiment (numbered as in ZKCP/Defs.lean, realLoop); n is the number
of batches still allowed. -/
def realLoop (Z : ViewEnv S IVK X W Pf) (isk : ISK) :
    AdvVerifier S X Pf → ℕ → View S IVK X Pf → Rom.OComp S (View S IVK X Pf)
  | .halt, _, v => pure v
  | .query o q k, n, v => .query o q fun r => realLoop Z isk (k r) n { v with trace := v.trace ++ [⟨o, q, r⟩] }
  | .sample m k, n, v => .sample m fun r => realLoop Z isk (k r) n { v with coins := v.coins ++ [r.val] }
  | .request _, 0, v => pure v
  | .request k, n + 1, v =>
      match Z v with
      | none => pure v
      | some b =>
        (A.P isk b.pairs).bind fun πs =>
          realLoop Z isk (k (b.released πs.val)) n
            { v with sessions := v.sessions ++ [b.released πs.val] }

def realExp (Vt : IVK → AdvVerifier S X Pf) (Z : ViewEnv S IVK X W Pf) (i : I) (N : ℕ) :
    Rom.OComp S (View S IVK X Pf) := do
  let (ivk, isk) ← A.C i
  realLoop A Z isk (Vt ivk) N ⟨ivk, [], [], []⟩

/-- The simulator: given pp(i) and N it outputs ivk; it answers every oracle query; for a batch it
is given the instances of the adversary's own slots and returns one proof for each. It is given
neither the other slots nor their number: this is a fact about its type (prove : St → (xs : List X)
→ ..). A batch without an own slot and an empty batch look alike to it. -/
structure Simulator (S : OSpec) (PP IVK X Pf : Type) where
  St : Type
  init : PP → ℕ → PMF (IVK × St)
  answer : St → (o : S.ι) → S.Dom o → PMF (S.Rng o × St)
  prove : St → (xs : List X) → PMF (Slots Pf xs × St)

/-- Steps 3 and 4 of the ideal experiment (numbered as in ZKCP/Defs.lean, idealLoop). -/
def idealLoop (Sim : Simulator S PP IVK X Pf) (Z : ViewEnv S IVK X W Pf) :
    AdvVerifier S X Pf → ℕ → View S IVK X Pf → Sim.St → PMF (View S IVK X Pf)
  | .halt, _, v, _ => PMF.pure v
  | .query o q k, n, v, s =>
      (Sim.answer s o q).bind fun out =>
        idealLoop Sim Z (k out.1) n { v with trace := v.trace ++ [⟨o, q, out.1⟩] } out.2
  | .sample m k, n, v, s =>
      (PMF.uniformOfFintype (Fin (m + 1))).bind fun r =>
        idealLoop Sim Z (k r) n { v with coins := v.coins ++ [r.val] } s
  | .request _, 0, v, _ => PMF.pure v
  | .request k, n + 1, v, s =>
      match Z v with
      | none => PMF.pure v
      | some b =>
        (Sim.prove s b.ownX).bind fun out =>
          idealLoop Sim Z (k (b.ownX.zip out.1.val)) n
            { v with sessions := v.sessions ++ [b.ownX.zip out.1.val] } out.2

def idealExp (Sim : Simulator S PP IVK X Pf) (Vt : IVK → AdvVerifier S X Pf)
    (Z : ViewEnv S IVK X W Pf) (i : I) (N : ℕ) : PMF (View S IVK X Pf) :=
  (Sim.init (R.pp i) N).bind fun out => idealLoop Sim Z (Vt out.1) N ⟨out.1, [], [], []⟩ out.2

/-- A query that is asked twice gets one answer, for each oracle of the family. -/
def TraceConsistent (tr : Rom.Trace S) : Prop :=
  ∀ (o : S.ι) (q : S.Dom o) (r r' : S.Rng o),
    (⟨o, q, r⟩ : Rom.QA S) ∈ tr → (⟨o, q, r'⟩ : Rom.QA S) ∈ tr → r = r'

/-- The requirement of `ZKCP.HasIndexPrivacy`, for one index and one environment; N counts
batches. The second clause is as there:
the trace of the ideal view is consistent with probability 1. A proof of an own slot that shows a
neighbour's instance is excluded (ZKCP/GenSanity.lean, nosy_not_private: one scheme, at B = 2: ζ(0,
1) ≥ 1/2).





-/
def PrivacyFor (Sim : Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞)
    (i : I) (Z : ViewEnv S IVK X W Pf) : Prop :=
  ∀ (tV : ℕ) (Vt : IVK → AdvVerifier S X Pf) (N : ℕ), (∀ ivk, (Vt ivk).QueryBound tV) →
    sd (fun T => Rom.Pr (realExp A Vt Z i N) (fun _ => T))
        (fun T => pr (idealExp R Sim Vt Z i N) T) ≤ ζ tV N ∧
    pr (idealExp R Sim Vt Z i N) {v | ¬ TraceConsistent v.trace} = 0

def HasIndexPrivacyWith (B : ℕ) (Sim : Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (i : I) (Z : ViewEnv S IVK X W Pf), Z.IsValid R B i → PrivacyFor R A Sim ζ i Z

def HasIndexPrivacy (B : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∃ Sim : Simulator S PP IVK X Pf, HasIndexPrivacyWith R A B Sim ζ

/-! ## The primitive -/

/-- With the extractor and the simulator named. IsZKCPArg below says only that they exist; the first
implies the second (IsZKCPArgWith.toIsZKCPArg). -/
structure IsZKCPArgWith (B : ℕ) (E : Extractor S I X W IVK Pf) (Sim : Simulator S PP IVK X Pf)
    (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) : Prop where
  completeness : HasCompletenessError R A B α
  indexBinding : HasIndexBindingWith R A E ε
  indexPrivacy : HasIndexPrivacyWith R A B Sim ζ

structure IsZKCPArg (B : ℕ) (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) : Prop where
  completeness : HasCompletenessError R A B α
  indexBinding : HasIndexBinding R A ε
  indexPrivacy : HasIndexPrivacy R A B ζ

theorem IsZKCPArgWith.toIsZKCPArg {R : RelPair I X W PP} {A : Arg S I X W IVK ISK Pf} {B : ℕ}
    {E : Extractor S I X W IVK Pf} {Sim : Simulator S PP IVK X Pf} {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞}
    (h : IsZKCPArgWith R A B E Sim α ε ζ) : IsZKCPArg R A B α ε ζ :=
  ⟨h.completeness, ⟨E, h.indexBinding⟩, ⟨Sim, h.indexPrivacy⟩⟩

end Properties

end ZKCP.Gen
