-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/SpecForm.lean: simulators that run a prover strategy of their own, and a
sufficient condition for such a simulator to be exact. Definitions and one statement.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has. All of it is for an arbitrary interactive protocol Q.
  A simulator of this form (simOfStrat) is given the instance x, all verifier messages ρ at once,
  and the symbols ans of the input oracles at the positions that the verifier reads. It samples a
  coin uniformly from its own finite type Ks. From (x, ρ, ans, coin) it builds a strategy of the
  prover's type, which may look at all of ρ from its first message on. It runs that strategy
  against ρ and outputs the disclosed view of the run, with input oracles rebuilt from ans by a
  function bld. On the verifier messages of a given set Sil it outputs none, that is, no view.
  Spec.exactOfShift states the following. Suppose that bld returns every symbol it is given.
  Suppose also that at every valid (w, x), and every ρ outside a set U and outside the honest
  prover's abort set, there is a bijection from the honest prover's coins onto Ks under which the
  honest run and the simulator's run disclose the same (ShiftTo). Then the simulator of this form
  with Sil the honest prover's Bad set satisfies ExactOff outside U. (ExactOff also excuses Hid;
  see Johnson/LinkSim/Spec.lean.) It is proved as exactOfShift in Johnson/LinkSim/Bridge.lean.
  Why a bijection suffices: both sides run a strategy of the same type and pass the run through the
  map Q.dview from a run to its disclosed view. What is left to compare is what the two runs
  disclose: the plain parts, the input oracles' symbols at the positions read, and the oracle
  messages' symbols at the positions read or not blinded.

How it fits. simOfStrat is the form of the simulator in homeExact's statement
(Johnson/LinkSim/AtHome/Home.lean). There the explicit simulator homeSim Z
(Johnson/LinkSim/AtHome/SpecHome.lean) is simLink at the library's full-size parameter set (dsFull).
simLink (Johnson/LinkSim/AtText/SpecExact.lean) is simOfStrat at the link's protocol, with coin type
Kc, its own rebuilding function, and Sil empty. ShiftTo, Shows and Spec.exactOfShift are used in
homeExact's proof: Johnson/LinkSim/AtText/Exact.lean uses the theorem exactOfShift (Bridge.lean)
with U empty (exactOfText). The tests of this form are in Johnson/LinkSim/SpecFormTests.lean and
Johnson/LinkSim/SpecStopTests.lean.

Other names (namespace OnBytes.LinkSim).
  Shows      two transcripts disclose the same at x: the same plain parts, and the same symbols at
             every position that the verifier reads, and at every position that is not blinded
             (see blinded in Johnson/LinkSim/Spec.lean's terms).
  ShiftTo    at (w, x, ρ): a bijection from the honest prover's coins onto the simulator's coins Ks
             under which the two runs disclose the same, coin by coin.

The private input. A strategy is a tree of messages and could hold anything, so its type does not
keep the private input out. What does is where the private input is bound: inside ExactOff, at one
fixed σ, Ks, bld and U. Whoever gives a simulator of this form must give it as a closed term. None
of its parameters may be, or be applied to, an index, a table's randomness or the prover's data.

Limits. Spec.exactOfShift is an implication, no honest prover is given here, and simOfStrat builds a
simulator only from a family σ that its user supplies. The form is one among others. Nothing says
that a simulator must have it. That a strategy of the simulator looks at later verifier messages is
allowed by honest-verifier zero knowledge and by nothing stronger.

Sources. A statement here is covered by the note on sources in the head of Spec.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.Spec

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim
open Prob
open _root_.Compile.Lifetime (SimOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} {E : ExtSpec}

open Classical in
/-- The simulator made of a family of strategies σ. At ρ in Sil it outputs none. Elsewhere it
samples c uniformly from Ks, runs σ x ρ ans c against ρ, and outputs the disclosed view, with the
input oracles (external strings) bld ans. -/
def simOfStrat (Q : InteractiveOracleProof X E) (Ks : Type) [Fintype Ks] [Nonempty Ks]
    (bld : (E.Pos → Option E.Sym) → E.Str) (Sil : Set (Rho Q.shape))
    (σ : X → Rho Q.shape → (E.Pos → Option E.Sym) → Ks → Strat Q.shape Unit) : SimOf Q :=
  fun x ρ ans =>
    if ρ ∈ Sil then PMF.pure none
    else (unif Ks).map fun c => some (Q.dview x (bld ans) ((σ x ρ ans c).run ρ).1)

/-- τ and τ' have the same plain parts, and the same symbols at every position that the verifier
reads in τ or that is not blinded. -/
def Shows (Q : InteractiveOracleProof X E) (x : X) (τ τ' : Tr Q.shape) : Prop :=
  τ.plains = τ'.plains ∧
    ∀ p, p ∈ Q.reads x τ.rho τ.plains ∨ Q.blinded p = false → τ.read p = τ'.read p

/-- There is a bijection φ from the honest prover's coins onto Ks such that, for every coin c, the
honest run at c and the run of σ at φ c disclose the same (Shows). -/
def ShiftTo {Q : InteractiveOracleProof X E} {Wt : Type} (H : Honest Q Wt) (Ks : Type)
    (σ : X → Rho Q.shape → (E.Pos → Option E.Sym) → Ks → Strat Q.shape Unit) (w : Wt) (x : X)
    (ρ : Rho Q.shape) : Prop :=
  ∃ φ : H.Coin → Ks, Function.Bijective φ ∧
    ∀ c, Shows Q x ((H.strat w x c).run ρ).1
      ((σ x ρ (Q.extAns x ρ (H.ext w)) (φ c)).run ρ).1

/-- If bld returns the symbols it is given and ShiftTo holds at every valid (w, x) and every ρ
outside U and the abort set, then simOfStrat, which outputs none exactly on H.Bad, satisfies
ExactOff outside U. Statement only; proved as exactOfShift in Johnson/LinkSim/Bridge.lean. -/
def Spec.exactOfShift : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : InteractiveOracleProof X E) (Wt : Type) (H : Honest Q Wt)
    (valid : Wt → X → Prop) (Ks : Type) [Fintype Ks] [Nonempty Ks]
    (bld : (E.Pos → Option E.Sym) → E.Str)
    (σ : X → Rho Q.shape → (E.Pos → Option E.Sym) → Ks → Strat Q.shape Unit)
    (U : Set (Rho Q.shape)),
    (∀ f p v, f p = some v → E.rd (bld f) p = v) →
    (∀ w x, valid w x → ∀ ρ, ρ ∉ U → ρ ∉ H.withheld w x → ShiftTo H Ks σ w x ρ) →
    ExactOff H valid (simOfStrat Q Ks bld H.Bad σ) U

end OnBytes.LinkSim
