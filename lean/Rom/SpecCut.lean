-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/SpecCut.lean: a random oracle split into two oracles, one for each of two parts of its answer.

The file has definitions and statements; the proofs are in Rom/CutRun.lean, Rom/CutDown.lean,
Rom/CutBind.lean, Rom/CutPriv.lean, Rom/CutState.lean and Rom/CutTop.lean. Oracles are typed: one
for each kind of query, with structured inputs and outputs. An oracle with answers in R ≃ A × B is
replaced by two oracles on the same queries, with answers in A (the first part) and in B (the second
part); this gives the second family of oracles (`cutSpec`), in which an oracle that is not split
also has a second oracle, a trivial one: its only answer is the unit value. An algorithm asks for
the first part, and for the second only where a rule that sees the first part says so; elsewhere a
fixed element of B takes its place (`OComp.cut`, `cutArg`).

`Spec.cutExit`: suppose that each algorithm of a scheme `A` continues with the same program after an
answer and after that answer with the unqueried second part replaced (`NeedOKCut`), and that the
extractor reads only entries at oracles that are not split (`WholeOnly`). Then the primitive
(`IsZKCPArgWith`, ZKCP/Gen.lean), extractor and simulator named, passes to the scheme over the
second family with the same three bounds; the numbers of queries now count queries to that family.
`Spec.cutState` is this step followed by the expansion of long answers from a state
(Rom/StateFirst.lean), under the hypotheses of both, with that step's added error terms.
`Spec.runCut`, `Spec.cutCost`, `Spec.cutAll`: see their statements.

Purpose. The typed Fiat-Shamir oracle of a round with proof-of-work bits returns these bits, the
hash blocks of the challenge and the chaining value (a field of the next query) at once. Take the
hash block that holds the bits as first part, and a rule that does not ask for the second part after
a failed attempt. Then a failed attempt of an honest algorithm is one query. The expansion from a
state (Rom/StateFirst.lean) can leave the oracle of the first parts unchanged, so it makes no state
for such an attempt, which does not count in kC, kP, kV of `Spec.cutState`. An adversary's attempts
count like all its queries. The implementation, by its authors' description, computes two hashes
with different tags on one input: a test value for every nonce, and the next state only for the
nonce that it keeps. This is known at second hand; no text of the implementation was compared.

Notation:
  B, α, ε, ζ: in `IsZKCPArgWith R A B E Sim α ε ζ` (ZKCP/Gen.lean): a natural number B (in the first
      paragraph A and B are the types of the two parts), a number α and two functions ε, ζ of two
      natural numbers; its fields: `HasCompletenessError R A B α`, `HasIndexBindingWith R A E ε`,
      `HasIndexPrivacyWith R A B Sim ζ`
  nC, nP, nV: rules (`NeedCut`): after the first part a of the answer at q, is the second part
      queried?
  kC, kP, kV: natural numbers, in the three hypotheses of `Spec.cutState` with `CostBoundV`
      (Rom/SpecOverOneA.lean): on every path the weights of the queries add up to at most t, where
      the weight of a query may depend on its answer
  `wCut`: what a typed query costs over the second family, if a query there costs u
  From Rom/StateFirst.lean:
  `Link`: how an oracle with answers in R is treated (`plain` or `chain K e`)
  `wCh`: the weight of a query: 1 at a chain oracle, 0 at an unchanged one
  `PlainOnly`: the extractor reads only entries at unchanged oracles
  `HidFree`: the three algorithms do not read the last block of a chain answer
  `collP`: the collision term: n new states, each against at most m older values, at 2 lam uniform
      bits
  `hitP`: the guessing term: t guesses, each against at most h hidden halves of lam bits

Limits: nothing is proved here, and nothing is said about any scheme; which rule each algorithm runs
under is left to the user (in the schemes with proof-of-work bits V always asks for both parts:
Compile/Batch/CutFit.lean). Only the three properties of `IsZKCPArgWith` are carried over. The
bounds stay the same, but a query of an honest algorithm whose second part is asked is now two
queries. The step goes from typed oracles to typed oracles and says nothing about one hash function.
It does not say that the two parts are hashes of one short input: the query is the typed query,
whatever it holds.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Rom.StateFirst
import Rom.SpecOverOneA

set_option autoImplicit false

noncomputable section

namespace Rom
open ZKCP
open scoped ENNReal

/-- How an oracle with answers in R is treated. (The three facts on A and B are fields, not
instances, so that the definitions below can name them.) -/
inductive OCut (R : Type) : Type 1
  | whole : OCut R
  | cut (A B : Type) (fA : Fintype A) (nA : Nonempty A) (fB : Fintype B) (e : R ≃ A × B) (dB : B) :
      OCut R

namespace OCut
variable {R : Type}

/-- what the first oracle answers: the whole answer, or its first part -/
def Front : OCut R → Type
  | .whole => R
  | .cut A _ _ _ _ _ _ => A
/-- what the second oracle answers: nothing, or the second part -/
def Rest : OCut R → Type
  | .whole => Unit
  | .cut _ B _ _ _ _ _ => B

instance finFront [Fintype R] : ∀ c : OCut R, Fintype c.Front
  | .whole => inferInstanceAs (Fintype R)
  | .cut _ _ fA _ _ _ _ => fA
instance neFront [Nonempty R] : ∀ c : OCut R, Nonempty c.Front
  | .whole => inferInstanceAs (Nonempty R)
  | .cut _ _ _ nA _ _ _ => nA
instance finRest : ∀ c : OCut R, Fintype c.Rest
  | .whole => inferInstanceAs (Fintype Unit)
  | .cut _ _ _ _ fB _ _ => fB
instance neRest : ∀ c : OCut R, Nonempty c.Rest
  | .whole => inferInstanceAs (Nonempty Unit)
  | .cut _ _ _ _ _ _ dB => ⟨dB⟩

def isWhole : OCut R → Bool
  | .whole => true
  | .cut _ _ _ _ _ _ _ => false

/-- the two parts of a typed answer -/
def front : (c : OCut R) → R → c.Front
  | .whole, r => r
  | .cut _ _ _ _ _ e _, r => (e r).1
def rest : (c : OCut R) → R → c.Rest
  | .whole, _ => ()
  | .cut _ _ _ _ _ e _, r => (e r).2

/-- the typed answer from its parts -/
def join : (c : OCut R) → c.Front → c.Rest → R
  | .whole, r, _ => r
  | .cut _ _ _ _ _ e _, a, b => e.symm (a, b)

/-- the typed answer from its first part only: the fixed element replaces the second part -/
def alone : (c : OCut R) → c.Front → R
  | .whole, r => r
  | .cut _ _ _ _ _ e dB, a => e.symm (a, dB)

/-- the typed answer, where the oracle is not split -/
def back : (c : OCut R) → c.Front → Option R
  | .whole, r => some r
  | .cut _ _ _ _ _ _ _, _ => none

end OCut

variable (S : OSpec) (C : ∀ o, OCut (S.Rng o))

/-- The second family. -/
def cutSpec : OSpec where
  ι := S.ι ⊕ S.ι
  Dom := fun x => match x with
    | .inl o => S.Dom o
    | .inr o => S.Dom o
  Rng := fun x => match x with
    | .inl o => (C o).Front
    | .inr o => (C o).Rest
  finRng := fun x => match x with
    | .inl o => OCut.finFront (C o)
    | .inr o => OCut.finRest (C o)
  neRng := fun x => match x with
    | .inl o => OCut.neFront (C o)
    | .inr o => OCut.neRest (C o)

variable {S} {α : Type}

/-- A rule: after the first part a of the answer at q, is the second part queried? -/
abbrev NeedCut : Type := (o : S.ι) → S.Dom o → (C o).Front → Bool

/-- the family of the parts of a family -/
def cutFam (F : Fam S) : Fam (cutSpec S C) := fun x => match x with
  | .inl o => fun q => (C o).front (F o q)
  | .inr o => fun q => (C o).rest (F o q)

/-- The same algorithm over the second family. -/
def OComp.cut (need : NeedCut C) : OComp S α → OComp (cutSpec S C) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => (k r).cut need
  | .query o q k => .query (S := cutSpec S C) (.inl o) q fun a =>
      if (C o).isWhole || !need o q a then (k ((C o).alone a)).cut need
      else .query (S := cutSpec S C) (.inr o) q fun b => (k ((C o).join a b)).cut need

variable {I X W PP IVK ISK Pf : Type}

/-- The same scheme over the second family, a rule for each algorithm. -/
def cutArg (nC nP nV : NeedCut C) (A : Gen.Arg S I X W IVK ISK Pf) :
    Gen.Arg (cutSpec S C) I X W IVK ISK Pf where
  C := fun i => (A.C i).cut C nC
  P := fun k b => (A.P k b).cut C nP
  V := fun v x π => (A.V v x π).cut C nV

/-- The answer, with the second part replaced where the rule does not query it. -/
def shownCut (need : NeedCut C) (o : S.ι) (q : S.Dom o) (r : S.Rng o) : S.Rng o :=
  if (C o).isWhole || !need o q ((C o).front r) then (C o).alone ((C o).front r) else r

/-- The condition: after an answer and after `shownCut` of that answer the algorithm continues with
the same program. -/
def OComp.ReadsCut (need : NeedCut C) (c : OComp S α) : Prop :=
  c.FactorsBy fun o q r r' => r' = shownCut C need o q r

structure NeedOKCut (A : Gen.Arg S I X W IVK ISK Pf) (nC nP nV : NeedCut C) : Prop where
  com : ∀ i, (A.C i).ReadsCut C nC
  prv : ∀ k b, (A.P k b).ReadsCut C nP
  ver : ∀ v x π, (A.V v x π).ReadsCut C nV

/-! ## The extractor, the simulator -/

/-- the entries at oracles that are not split, as entries of the first family -/
def wholeTr (tr : Trace (cutSpec S C)) : Trace S :=
  tr.filterMap fun e => match e with
    | ⟨.inl o, q, a⟩ => ((C o).back a).map fun r => (⟨o, q, r⟩ : QA S)
    | ⟨.inr _, _, _⟩ => none

/-- the entries of a trace of the first family at oracles that are not split -/
def wholeOf (tr : Trace S) : Trace S := tr.filter fun e => (C e.1).isWhole

/-- The extractor reads only entries at oracles that are not split. -/
def WholeOnly (E : Gen.Extractor S I X W IVK Pf) : Prop :=
  (∀ v tr, E.Ei v tr = E.Ei v (wholeOf C tr)) ∧
  (∀ v tr x π tr', E.Ew v tr x π tr' = E.Ew v (wholeOf C tr) x π (wholeOf C tr'))

def extCut (E : Gen.Extractor S I X W IVK Pf) : Gen.Extractor (cutSpec S C) I X W IVK Pf where
  Ei v tr := E.Ei v (wholeTr C tr)
  Ew v tr x π tr' := E.Ew v (wholeTr C tr) x π (wholeTr C tr')

/-- The simulator over the second family: it passes the query to Sim and returns the part that is
queried, also at a trivial oracle. -/
def simCut (Sim : Gen.Simulator S PP IVK X Pf) : Gen.Simulator (cutSpec S C) PP IVK X Pf where
  St := Sim.St
  init := Sim.init
  answer := fun st x => match x with
    | .inl o => fun q => (Sim.answer st o q).map fun out => ((C o).front out.1, out.2)
    | .inr o => fun q => (Sim.answer st o q).map fun out => ((C o).rest out.1, out.2)
  prove := Sim.prove

/-- what a typed query costs over the second family, if a query there costs u -/
def wCut (need : NeedCut C) (u : (x : (cutSpec S C).ι) → (cutSpec S C).Dom x → ℕ) (o : S.ι)
    (q : S.Dom o) (r : S.Rng o) : ℕ :=
  u (.inl o) q + if (C o).isWhole || !need o q ((C o).front r) then 0 else u (.inr o) q

/-! ## The statements -/

namespace Spec

/-- If the algorithm meets the condition `ReadsCut`, then for every family F the split algorithm
under the parts of F returns what the algorithm returns under F. -/
def runCut : Prop :=
  ∀ (S : OSpec) (C : ∀ o, OCut (S.Rng o)) (α : Type) (need : NeedCut C) (c : OComp S α),
    c.ReadsCut C need → ∀ F : Fam S, (c.cut C need).runEager (cutFam C F) = c.runEager F

/-- Under `NeedOKCut` and `WholeOnly` the three properties carry over, with the same bounds. -/
def cutExit : Prop :=
  ∀ (S : OSpec) (C : ∀ o, OCut (S.Rng o)) (I X W PP IVK ISK Pf : Type) (R : Gen.RelPair I X W PP)
      (A : Gen.Arg S I X W IVK ISK Pf) (B : ℕ) (E : Gen.Extractor S I X W IVK Pf)
      (Sim : Gen.Simulator S PP IVK X Pf) (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) (nC nP nV : NeedCut C),
    NeedOKCut C A nC nP nV → WholeOnly C E → Gen.IsZKCPArgWith R A B E Sim α ε ζ →
    Gen.IsZKCPArgWith R (cutArg C nC nP nV A) B (extCut C E) (simCut C Sim) α ε ζ

/-- The queries of the split algorithm: a bound on the typed algorithm in the weight `wCut` gives
the same bound in the weight u. -/
def cutCost : Prop :=
  ∀ (S : OSpec) (C : ∀ o, OCut (S.Rng o)) (α : Type) (need : NeedCut C)
      (u : (x : (cutSpec S C).ι) → (cutSpec S C).Dom x → ℕ) (c : OComp S α) (t : ℕ),
    c.CostBoundV (wCut C need u) t → (c.cut C need).CostBoundAt u t

/-- A sanity statement: under the rule that always queries, every algorithm meets the condition. -/
def cutAll : Prop :=
  ∀ (S : OSpec) (C : ∀ o, OCut (S.Rng o)) (α : Type) (c : OComp S α), c.ReadsCut C fun _ _ _ => true

/-- This step followed by the expansion from a state, under the hypotheses of both, with the added
error terms of the second. (The hypotheses: `NeedOKCut`, `WholeOnly`; `CostBoundV` with kC, kP, kV;
`PlainOnly`, `HidFree`; `IsZKCPArgWith` for A. The terms: `collP`, `hitP`. What these names are:
the head.) -/
def cutState : Prop :=
  ∀ (S : OSpec) (C1 : ∀ o, OCut (S.Rng o)) (lam : ℕ) (C2 : ∀ x, Link lam ((cutSpec S C1).Rng x))
      (I X W PP IVK ISK Pf : Type) (R : Gen.RelPair I X W PP) (A : Gen.Arg S I X W IVK ISK Pf)
      (B : ℕ) (E : Gen.Extractor S I X W IVK Pf) (Sim : Gen.Simulator S PP IVK X Pf) (α : ℝ≥0∞)
      (ε ζ : ℕ → ℕ → ℝ≥0∞) (nC nP nV : NeedCut C1) (kC kP kV : ℕ),
    NeedOKCut C1 A nC nP nV → WholeOnly C1 E → (∀ i, (A.C i).CostBoundV (wCut C1 nC (wCh C2)) kC) →
    (∀ k b, b.length ≤ B → (A.P k b).CostBoundV (wCut C1 nP (wCh C2)) kP) →
    (∀ v x π, (A.V v x π).CostBoundV (wCut C1 nV (wCh C2)) kV) → PlainOnly C2 (extCut C1 E) →
    HidFree C2 (cutArg C1 nC nP nV A) → Gen.IsZKCPArgWith R A B E Sim α ε ζ →
    Gen.IsZKCPArgWith R (stateFirstArg C2 (cutArg C1 nC nP nV A)) B (extSt C2 (extCut C1 E))
      (simSt C2 (simCut C1 Sim)) (α + collP lam (kC + kP + B * kV) (kC + kP + B * kV))
      (fun tC tP => ε tC tP + collP lam (tC + tP + kV) (tC + tP + kV)) (fun t N =>
        ζ t N + collP lam (t + (kC + N * kP)) (t + (kC + N * kP)) + hitP lam t (kC + N * kP))

end Spec

end Rom
