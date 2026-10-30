-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/InteractiveOracleProof.lean: public-coin interactive oracle proofs (IOPs) with external strings.

The file has definitions and one lemma. A `InteractiveOracleProof X E` has a fixed list of rounds (Iop/Shape.lean),
instances in X, and external strings of the kind E: oracles that are fixed before the first message.
The main properties are round-by-round soundness (`InteractiveOracleProof.Sound`), exact honest-verifier zero
knowledge (`Honest.HVZK`; not all hypotheses are named here: see its statement), and completeness,
for valid private inputs, at every value of the verifier's randomness outside the honest prover's
abort set (`Honest.Acc`; the abort set is `Honest.withheld`).

Also: `oneExternalString`, `twoExternalStrings`, one string or two as external oracles; `Err.Below`:
every error of a list, as a probability, is at most c; `LH.Nums`, all the numbers of an interface.
-/
import Iop.Rbr
import Prob.Tv
noncomputable section -- Lean tags what it cannot compile

namespace Iop
open Prob
open scoped ENNReal

/-- External strings: oracles that are fixed before the first message. -/
structure ExtSpec where
  Str : Type
  Pos : Type
  Sym : Type
  rd  : Str → Pos → Sym

/-- A public-coin IOP with a fixed list of rounds, instances in X and external strings of kind E.
All queries follow the interaction. The positions read in the external strings are a function of x
and ρ; those read in the prover's oracles may also depend on the plain parts (the parts of the
prover's messages that are sent in the clear, not as oracles). The decision is a function of the
whole transcript that is meant to depend on the oracles only at the positions read (`InteractiveOracleProof.IsLocal`
below), so a verifier with only the answers can compute it. -/
structure InteractiveOracleProof (X : Type) (E : ExtSpec) where
  shape    : Shape
  /-- is the oracle at this position blinded (hashed with a salt, never shown in full) (by type any
  map `OPos shape → Bool`; it enters `InteractiveOracleProof.dview`) -/
  blinded  : OPos shape → Bool
  extReads : X → Rho shape → Finset E.Pos
  reads    : X → Rho shape → Plains shape → Finset (OPos shape)
  accept   : X → E.Str → Tr shape → Bool

variable {X : Type} {E : ExtSpec}

/-- The decision depends on the oracles only at the positions read. (A property, not a field: the
structures hold data only (and that a type is not empty: `neCoin`), so that the terms of the
construction can be written down before anything is proved.) -/
def InteractiveOracleProof.IsLocal (Q : InteractiveOracleProof X E) : Prop :=
  ∀ x y y' (τ τ' : Tr Q.shape), τ.rho = τ'.rho → τ.plains = τ'.plains →
      (∀ p ∈ Q.extReads x τ.rho, E.rd y p = E.rd y' p) →
      (∀ p ∈ Q.reads x τ.rho τ.plains, τ.read p = τ'.read p) → Q.accept x y τ = Q.accept x y' τ'

/-- Round-by-round soundness for a language of pairs (x, y), y a value of the external strings: for
every pair outside it the empty transcript is doomed to rejection, with the errors ε. -/
def InteractiveOracleProof.Sound (Q : InteractiveOracleProof X E) (L : X → E.Str → Prop) (ε : Err Q.shape) : Prop :=
  ∀ x y, ¬ L x y → Doomed Q.shape ε (fun τ => Q.accept x y τ = false)

/-- The honest prover. Wt is its private input (index, encoding randomness). -/
structure Honest (Q : InteractiveOracleProof X E) (Wt : Type) where
  Coin  : Type
  [finCoin : Fintype Coin]
  [neCoin  : Nonempty Coin]
  /-- the external strings that belong to the private input -/
  ext   : Wt → E.Str
  /-- its strategy; where it has no honest message it is meant to send fixed substitutes -/
  strat : Wt → X → Coin → Strat Q.shape Unit
  /-- the public part of the abort set: it depends on ρ only -/
  Bad   : Set (Rho Q.shape)
  /-- the rest of the abort set, which may depend on the private input -/
  Hid   : Wt → X → Set (Rho Q.shape)

attribute [instance] Honest.finCoin Honest.neCoin

/-- The disclosed view: the plain parts, the answers at the positions read, and every unblinded
oracle in full. -/
structure DView (Q : InteractiveOracleProof X E) where
  plains : Plains Q.shape
  ext    : E.Pos → Option E.Sym
  orc    : (p : OPos Q.shape) → Option (OSym Q.shape p)

open Classical in
/-- The symbols of the external strings where the verifier reads them, and nothing else. -/
def InteractiveOracleProof.extAns (Q : InteractiveOracleProof X E) (x : X) (ρ : Rho Q.shape) (y : E.Str) :
    E.Pos → Option E.Sym :=
  fun p => if p ∈ Q.extReads x ρ then some (E.rd y p) else none

open Classical in
def InteractiveOracleProof.dview (Q : InteractiveOracleProof X E) (x : X) (y : E.Str) (τ : Tr Q.shape) : DView Q where
  plains := τ.plains
  ext := Q.extAns x τ.rho y
  orc := fun p =>
    if p ∈ Q.reads x τ.rho τ.plains ∨ Q.blinded p = false then some (τ.read p) else none

variable {Q : InteractiveOracleProof X E} {Wt : Type}

/-- The abort set. -/
def Honest.withheld (H : Honest Q Wt) (w : Wt) (x : X) : Set (Rho Q.shape) := H.Bad ∪ H.Hid w x

open Classical in
/-- The output at ρ: the disclosed view, or `none` if ρ is in the abort set. A random variable over
the prover's coins. -/
def Honest.output (H : Honest Q Wt) (w : Wt) (x : X) (ρ : Rho Q.shape) :
    PMF (Option (DView Q)) :=
  if ρ ∈ H.withheld w x then PMF.pure none
  else (unif H.Coin).map fun c => some (Q.dview x (H.ext w) ((H.strat w x c).run ρ).1)

/-- The probability of a set of values of the verifier's randomness. Sets of values of the whole ρ
are measured by probabilities, single rounds by counts. -/
def prRho {s : Shape} (S : Set (Rho s)) : ℝ≥0∞ := pr (unif (Rho s)) S

/-- Honest-verifier zero knowledge, in the exact form. One simulator for all private inputs. It is
given x and ρ, and of the external strings it is given the answers at the verifier's positions and
nothing else (this is a fact about its type; `InteractiveOracleProof.extAns`). For every valid private input, which
contains the encoding randomness, its output has exactly the distribution of the honest output, at
every ρ outside a set of probability at most z. (The exceptional set holds the secret-dependent part
of the abort set, which the simulator cannot recognise, and the ρ at which an honest claim is false
for some coins.) The simulator's running time is not modelled. -/
def Honest.HVZK (H : Honest Q Wt) (valid : Wt → X → Prop) (z : ℝ≥0∞) : Prop :=
  ∃ Sim : X → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q)),
    ∀ w x, valid w x → prRho {ρ | H.output w x ρ ≠ Sim x ρ (Q.extAns x ρ (H.ext w))} ≤ z

/-- How HVZK is proved: exactness outside a set S of ρ, and a bound on S. -/
theorem Honest.HVZK.of_exact (H : Honest Q Wt) (valid : Wt → X → Prop) (z : ℝ≥0∞)
    (Sim : X → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q)))
    (S : Wt → X → Set (Rho Q.shape))
    (hex : ∀ w x, valid w x → ∀ ρ, ρ ∉ S w x → H.output w x ρ = Sim x ρ (Q.extAns x ρ (H.ext w)))
    (hS : ∀ w x, valid w x → prRho (S w x) ≤ z) : H.HVZK valid z :=
  ⟨Sim, fun w x hv => le_trans ((unif (Rho Q.shape)).toOuterMeasure.mono
    (fun ρ hρ => by by_contra hn; exact hρ (hex w x hv ρ hn))) (hS w x hv)⟩

/-- Completeness, (Acc): for every valid private input, the verifier accepts the honest prover at
every single ρ outside the abort set, for all coins. -/
def Honest.Acc (H : Honest Q Wt) (valid : Wt → X → Prop) : Prop :=
  ∀ w x c ρ, valid w x → ρ ∉ H.withheld w x → Q.accept x (H.ext w) ((H.strat w x c).run ρ).1 = true

/-- One string of n symbols as external oracle. -/
abbrev oneExternalString (n : ℕ) (Sg : Type) : ExtSpec := ⟨Fin n → Sg, Fin n, Sg, fun y p => y p⟩

/-- Two such strings, for Link: parent (left) and child (right). -/
abbrev twoExternalStrings (n : ℕ) (Sg : Type) : ExtSpec :=
  ⟨(Fin n → Sg) × (Fin n → Sg), Fin n ⊕ Fin n, Sg, fun y p => Sum.elim y.1 y.2 p⟩

/-- Every error of the list, as a probability, is at most c. -/
def Err.Below : {s : Shape} → Err s → ℝ≥0∞ → Prop
  | [], _, _ => True
  | r :: _, (e, ε), c => (e : ℝ≥0∞) ≤ c * (Fintype.card r.Chal : ℝ≥0∞) ∧ Err.Below ε c

/-- All numbers of the interface (`BatchProtocol`, Iop/Batch.lean). -/
structure LH.Nums where
  (b qT qpar qch qon : ℕ)
  (εs zT zL zO pT pL pO : ℝ≥0∞)

end Iop
