-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Dry/Spec.lean: TWO STATEMENTS ON THE CHAIN OF THE COMPILED PROVER OF ONE SLOT (chainO,
proveX, OnBytes/Prover/Defs.lean) UNDER ANSWERS THAT DO NOT LOOK AT ITS QUERIES' POINTS. DEFINITIONS
AND STATEMENTS; the proofs are in OnBytes/Dry/Control.lean and OnBytes/Dry/ChainLaw.lean.

General statements, for any rounds, wire and strategy. This file states no goal of the release.

Why. A simulator of the interactive protocol wants all verifier messages before it speaks; in a
compiled run the verifier messages are read off the answers to queries that hold the prover's
messages. The way out: a first, DRY pass runs the prover's chain at some fixed strategy, draws a
fresh answer at each deferred query and keeps these answers in their order (OComp.record,
Rom/Handle/Defs.lean); the verifier messages are read off that pass; a second pass replays the
recorded answers at the strategy that is wanted (OComp.runReplay). Two things are owed for it.

  Spec.control       CONTROL. Which oracle the chain asks next, which try of a search for a nonce
    passes, whether a search runs out, and what the verifier messages are hangs on the ANSWERS at
    the Fiat-Shamir oracle and at g, in their order, and on nothing that the strategy sends. In the
    letters of Rom/Handle/Defs.lean: the first pass at ANY strategy σ and the chain at ANY strategy
    σ' ask their deferred queries in step (InStep), and the first pass's output is read off the
    chain's. With record_runReplay (Rom/Handle/Laws.lean) it follows that answers recorded at σ,
    replayed at σ', are used up exactly, never fail to fit, and give jointly with the first pass's
    output what one run at σ' with fresh answers gives. The two passes may have different outer
    roots, instances and coins: of all these the chain's control reads one number alone, how many
    sibling digests the coins hold for the request tree.
  Spec.chainLawDry   THE LAW OF THE VERIFIER MESSAGES OF A DRY PASS. The probability that no search
    runs out and the verifier messages lie in a set B is at most the uniform measure of B with the
    test bits set to 0.

Main names.
  markRun    which oracles a compiled run defers: leaves, the Fiat-Shamir oracles, g, the request
             tree. Plain: the inner nodes of trees. A member of the two statements' premises on m
             (markRun_fb, markRun_g, markRun_node).
  Alike      two sets of coins with one first salt, one slot and one list of sibling digests. (Not
             asked here; it is the premise of Spec.sameWork, OnBytes/Dry/SpecView.lean.) Alike.refl,
             Alike.dressed: coins are alike to themselves, and to themselves with other salts of
             leaves and another string behind the slot's value.
  rhoO       the first pass's program: the chain, of whose outcome the verifier messages alone are
             kept (or "no format", or "the search of round i ran out").
  rhoX       the same with the compiled prover proveX in the chain's place.

What the statements do NOT ask: that the numbers which a search tries are written apart; anything of
a table; that plain parts are written into queries injectively. Answers go by their order, never by
a query's point.

Limits. One slot, one chain. "Deferred" goes by the oracle's name. Spec.control says nothing of the
points that are logged, nor of the proof string. B is a letter. Spec.chainLawDry is a bound from
above on the runs that end well; NOTHING HERE SAYS THAT ANY RUN ENDS WELL: its left side may be 0. A
search may run out; and a run that comes to a round whose kind does not fit the chain's phase ends
in "no format" (chainO, OnBytes/Prover/Defs.lean).
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Defs
import Rom.Handle.Defs
import Prob.Count

set_option autoImplicit false

noncomputable section

namespace OnBytes.Dry
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

/-- The names of the typed oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

/-- Which oracles a compiled run defers: leaves, Fiat-Shamir oracles, g, the request tree. -/
def markRun : ON₂ → Bool
  | .leaf => true
  | .rleaf => true
  | .rnode => true
  | .fb _ => true
  | .g _ => true
  | _ => false

theorem markRun_fb (t : Tag) : markRun (.fb t) = true := rfl
theorem markRun_g (t : Tag) : markRun (.g t) = true := rfl
theorem markRun_node : markRun .node = false := rfl

/-- Two sets of coins are alike: one first salt, one slot, one list of sibling digests. Free: the
salts of leaves, the body of a leaf at which no position stands, the string behind the slot value.
-/
structure Alike {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} (co co' : Coins lam L) : Prop where
  salt : co'.salt = co.salt
  slot : co'.slot = co.slot
  path : co'.path = co.path

theorem Alike.refl {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} (co : Coins lam L) : Alike co co :=
  ⟨rfl, rfl, rfl⟩

/-- Other salts of leaves and another string behind the slot value: alike. -/
theorem Alike.dressed {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} (co : Coins lam L)
    (lf : ℕ → Bool → ℕ → ℕ → Bits) (rs : Bits) : Alike co { co with leaf := lf, rsalt := rs } :=
  ⟨rfl, rfl, rfl⟩

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- **The first pass's program**: the prover's chain; of its outcome the verifier messages alone are
kept. -/
def rhoO (t : Tag) (cms : List (Dig lam)) (x : Option X) (co : Coins lam L) (cap : ℕ → ℕ)
    (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
    (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam) (σ : Strat s Unit) :
    TypedOracleComputation lam K L (Res (Rho s)) :=
  (chainO t cms x co cap s A W embS embP i ph σ).bind fun r => .pure (r.map fun z => z.1)

variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
  (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ)

/-- The same with the compiled prover in the chain's place. -/
def rhoX : TypedOracleComputation lam K L (Res (Rho Q.loc.shape)) :=
  (proveX t Q wq embS embP xin cms x y xt σ co cap).bind fun r => .pure (r.map fun z => z.2.rho)

end

/-- **CONTROL.** For every test m on names that defers this chain's Fiat-Shamir oracle and its g;
any outer roots cms, cms', any instances x, x', and any coins co, co' with equally many sibling
digests: the first pass at (cms, x, co, σ) and the chain at (cms', x', co', σ') ask their deferred
queries in step, and the first pass's output is the chain's outcome cut to the verifier messages. -/
def Spec.control : Prop :=
  ∀ {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (m : ON₂ → Bool) (t : Tag),
    m (.fb t) = true → m (.g t) = true →
    ∀ (cms cms' : List (Dig lam)) (x x' : Option X) (co co' : Coins lam L) (cap : ℕ → ℕ),
      co.path.length = co'.path.length →
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
      (σ σ' : Strat s Unit),
      InStep (S := typedOracleFamily lam K L) (fun o _ => m o) (fun a b => a = b.map fun z => z.1)
        (rhoO t cms x co cap s A W embS embP i ph σ)
        (chainO t cms' x' co' cap s A W embS embP i ph σ')

/-- **THE LAW OF THE VERIFIER MESSAGES OF A DRY PASS.** For every test m on names that defers this
chain's Fiat-Shamir oracle, and a wire whose rounds keep the laws (uniform blocks give a uniform
verifier message; a test's structure is a lens): no search runs out and the verifier messages lie in
B with probability at most the uniform measure of B, the test bits set to 0. -/
def Spec.chainLawDry : Prop :=
  ∀ {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (m : ON₂ → Bool) (t : Tag), m (.fb t) = true →
    ∀ (cms : List (Dig lam)) (x : Option X) (co : Coins lam L) (cap : ℕ → ℕ)
      (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam) (σ : Strat s Unit),
      RoundsQueryLayout.OKG s A W → ∀ B : Set (Rho s),
        pr ((chainO t cms x co cap s A W embS embP i ph σ).record
              (S := typedOracleFamily lam K L) fun o _ => m o)
            {z | ∃ w, z.1 = .ok w ∧ w.1 ∈ B} ≤
          pr (unif (Rho s)) {ρ | RoundsQueryLayout.zero s A W ρ ∈ B}

end OnBytes.Dry
