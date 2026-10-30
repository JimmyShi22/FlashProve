-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Dry/SpecView.lean: TWO STATEMENTS ON TWO REPLAYS OF ONE LIST OF RECORDED ANSWERS, AGAINST
ONE TABLE, OF THE CHAIN OF THE COMPILED PROVER OF ONE SLOT (chainO, OnBytes/Prover/Defs.lean) AT TWO
STRATEGIES. DEFINITIONS AND STATEMENTS; the proofs are in OnBytes/Dry/View.lean.

General statements, for any protocol, wire and strategies. This file states no goal of the release.

Why. The reduction of Johnson/WholeKey/Wrap.lean replays recorded answers at a strategy that it
makes from a disclosed view; the honest prover plays its own strategy. The view holds the plain
parts and the symbols at the positions that the verifier reads, so the two strategies differ at the
positions that are not read. What a run hands out (handOut, Johnson/WholeKey/Sim.lean) is the proof
string and a table, into which of the run's deferred queries these are written: all that are no
leaves, and the leaves at the positions that are read.

  Spec.sameWork   THE SAME HASH WORK. ANY two strategies, at coins that are alike (Alike,
      OnBytes/Dry/Spec.lean): the two replays have the same law of (the outcome cut to the verifier
      messages; the table after the run; what is left of the recorded answers; whether they failed
      to fit). So a run whose string is withheld can be played at any strategy.
  Spec.ofView     A FUNCTION OF THE VIEW. Two strategies whose runs at the verifier messages ρ₀ have
      the same plain parts and the same symbols at the positions that the verifier reads there, at
      ONE set of coins, for a protocol whose verifier reads the same positions whatever the nonces
      are: over the runs whose verifier messages are ρ₀, the two replays have the same law of what
      is handed out. The two sides may also hold different external strings y, y' and different
      kept trees xt, xt' over them, as long as these have, at the external positions that the
      verifier reads at ρ₀, the same symbol and the same leaf's input, in trees with the same levels
      of digests.

Main names.
  RunMarks m t   the test m on names defers leaves, the leaves of the request tree, this chain's
                 Fiat-Shamir oracle and its g. (The inner nodes of either kind of tree are free.)
                 runMarks_markRun, runMarks_lateRun: two members.
  work           what Spec.sameWork compares.
  atRho ρ₀ H     H of a run's end, if the run has come to its end with the verifier messages ρ₀;
                 else "none".
  ofView_member  the premises of Spec.ofView on strategies and external strings hold of one strategy
                 and one external string beside themselves: an idle member, at which the statement
                 says nothing. (That they hold of the honest strategy against the strategy made
                 from its view is proved in OnBytes/Dry/ViewAt.lean and
                 Johnson/LateWorld/Session.lean, at letters.)

Limits. One slot, one chain. Spec.ofView speaks of the runs with the verifier messages ρ₀ alone; all
others are lumped into "none". That a replay of recorded answers has the verifier messages of the
pass that recorded them is Spec.control's (OnBytes/Dry/Spec.lean). No member that bites is typed in
this folder: no protocol with a wire at which two different strategies have one view. Nothing here
says that any run ends well.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Sim
import OnBytes.Prover.Inv
import OnBytes.Dry.Spec

set_option autoImplicit false

noncomputable section

namespace OnBytes.Dry
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The names of the typed oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

/-- The test m on names defers leaves, the request tree's leaves, this chain's Fiat-Shamir oracle
and its g. -/
structure RunMarks (m : ON₂ → Bool) (t : Tag) : Prop where
  leaf : m .leaf = true
  rleaf : m .rleaf = true
  fb : m (.fb t) = true
  g : m (.g t) = true

theorem runMarks_markRun (t : Tag) : RunMarks markRun t := ⟨rfl, rfl, rfl, rfl⟩
theorem runMarks_lateRun (t : Tag) : RunMarks lateRun t := ⟨rfl, rfl, rfl, rfl⟩

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- What Spec.sameWork compares: the outcome cut to the verifier messages, the table, what is left
of the recorded answers, the flag. -/
def work {s : Shape}
    (o : Res (OutP lam L s) × RSt (typedOracleFamily lam K L) (Table (typedOracleFamily lam K L))) :
    Res (Rho s) × Table (typedOracleFamily lam K L) × Record (typedOracleFamily lam K L) × Bool :=
  (o.1.map fun z => z.1, o.2.base, o.2.left, o.2.miss)

open Classical in
/-- H of a run's end, if the run has come to its end with the verifier messages ρ₀; else none. -/
def atRho {s : Shape} {St γ : Type} (ρ₀ : Rho s) (H : Res (OutP lam L s) × St → γ)
    (o : Res (OutP lam L s) × St) : Option γ :=
  match o.1 with
  | .ok z => if z.1 = ρ₀ then some (H o) else none
  | _ => none

end

/-- **THE SAME HASH WORK.** -/
def Spec.sameWork : Prop :=
  ∀ {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (m : ON₂ → Bool) (t : Tag), RunMarks m t →
    ∀ (cms : List (Dig lam)) (x : Option X) (co co' : Coins lam L) (cap : ℕ → ℕ), Alike co co' →
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
      (σ σ' : Strat s Unit) (T : Table (typedOracleFamily lam K L)) (lg lg' : Trace (typedOracleFamily lam K L))
      (Rc : Record (typedOracleFamily lam K L)),
      ((chainO t cms x co cap s A W embS embP i ph σ).runReplay (fun o _ => m o) T lg Rc).map work =
        ((chainO t cms x co' cap s A W embS embP i ph σ').runReplay (fun o _ => m o) T lg' Rc).map
          work

/-- **A FUNCTION OF THE VIEW.** -/
def Spec.ofView : Prop :=
  ∀ {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (y y' : E.Str) (xt xt' : ℕ → TreeK lam L) (cap : ℕ → ℕ)
    (σ σ' : Strat Q.loc.shape Unit) (co : Coins lam L) (ρ₀ : Rho Q.loc.shape),
    (∀ τ τ' : Tr Q.loc.shape, Puts Q.loc.shape Q.ann wq.sh τ τ' →
      Q.loc.reads x τ.rho τ'.plains = Q.loc.reads x τ.rho τ.plains) →
    (σ.run ρ₀).1.plains = (σ'.run ρ₀).1.plains →
    (∀ p ∈ Q.loc.reads x ρ₀ (σ.run ρ₀).1.plains, (σ.run ρ₀).1.read p = (σ'.run ρ₀).1.read p) →
    (∀ p ∈ Q.loc.extReads x ρ₀, E.rd y p = E.rd y' p ∧
      (xt (wq.ext.which p)).inp (wq.ext.leaf p) = (xt' (wq.ext.which p)).inp (wq.ext.leaf p) ∧
      (xt (wq.ext.which p)).lv = (xt' (wq.ext.which p)).lv) →
    ∀ (T : Table (typedOracleFamily lam K L)) (lg : Trace (typedOracleFamily lam K L)) (Rc : Record (typedOracleFamily lam K L)),
      ((chainX t Q wq embS embP xin cms x cap σ co).runReplay mkRun T lg Rc).map
          (atRho ρ₀ (handOut Q wq x y xt true co)) =
        ((chainX t Q wq embS embP xin cms x cap σ' co).runReplay mkRun T lg Rc).map
          (atRho ρ₀ (handOut Q wq x y' xt' true co))

/-- The two premises of Spec.ofView on the strategies can be met: a strategy beside itself. -/
theorem ofView_member {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (x : Y)
    (σ : Strat Q.loc.shape Unit) (ρ₀ : Rho Q.loc.shape) :
    (σ.run ρ₀).1.plains = (σ.run ρ₀).1.plains ∧
      ∀ p ∈ Q.loc.reads x ρ₀ (σ.run ρ₀).1.plains, (σ.run ρ₀).1.read p = (σ.run ρ₀).1.read p :=
  ⟨rfl, fun _ _ => rfl⟩

end OnBytes.Dry

#print axioms OnBytes.Dry.ofView_member
