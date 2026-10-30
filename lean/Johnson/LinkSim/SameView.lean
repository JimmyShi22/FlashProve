-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/SameView.lean: two transcripts that disclose the same have the same disclosed view.
General lemmas on the disclosed view of an interactive protocol (InteractiveOracleProof.dview, Iop/InteractiveOracleProof.lean).
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has.
  dview_eq_of_shows   Let two transcripts have the same verifier messages and disclose the same
                    (Shows, Johnson/LinkSim/SpecForm.lean), and let the two input oracles agree at
                    the positions read. Then the two disclosed views are equal.
  dview_run_eq      the same for the runs of two strategies against the same verifier messages.
  extAns_congr      the input-oracle symbols that the verifier reads are the same for two input
                    oracles that agree at the positions read.
  extAns_build      input oracles rebuilt from the symbols read give these symbols back.

How it fits. Used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean).
Johnson/LinkSim/Bridge.lean uses dview_run_eq to prove exactOfShift. Under Johnson/LinkSim/ no file
calls extAns_build.

Limits. Nothing says when two runs disclose the same: that is a hypothesis of each lemma.

Sources. extAns_congr repeats the library's lemma of the same name (Iop/ViewKit.lean), statement and
proof, but that the two input oracles are explicit arguments here. That file is not named among this
file's imports but is imported through them, so the library's lemma could be called in its place.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.SpecForm

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} {E : ExtSpec}

/-- Two input oracles that agree at every position that the verifier reads give the same symbols
read. -/
theorem extAns_congr (Q : InteractiveOracleProof X E) (x : X) (ρ : Rho Q.shape) (y y' : E.Str)
    (h : ∀ p ∈ Q.extReads x ρ, E.rd y p = E.rd y' p) : Q.extAns x ρ y = Q.extAns x ρ y' := by
  funext p
  unfold InteractiveOracleProof.extAns
  by_cases hp : p ∈ Q.extReads x ρ
  · rw [if_pos hp, if_pos hp, h p hp]
  · rw [if_neg hp, if_neg hp]

/-- Input oracles (external strings) that are rebuilt from the symbols read give these symbols
back. -/
theorem extAns_build (Q : InteractiveOracleProof X E) (x : X) (ρ : Rho Q.shape) (y : E.Str)
    (bld : (E.Pos → Option E.Sym) → E.Str) (hb : ∀ f p a, f p = some a → E.rd (bld f) p = a) :
    Q.extAns x ρ (bld (Q.extAns x ρ y)) = Q.extAns x ρ y :=
  extAns_congr Q x ρ _ _ fun p hp => hb _ p _ (by unfold InteractiveOracleProof.extAns; rw [if_pos hp])

/-- Two transcripts with the same verifier messages that disclose the same (Shows), with input
oracles that agree at the positions read, have the same disclosed view. -/
theorem dview_eq_of_shows (Q : InteractiveOracleProof X E) (x : X) (y y' : E.Str) (τ τ' : Tr Q.shape)
    (hρ : τ.rho = τ'.rho) (hS : Shows Q x τ τ')
    (hy : ∀ p ∈ Q.extReads x τ.rho, E.rd y p = E.rd y' p) : Q.dview x y τ = Q.dview x y' τ' := by
  have h1 : τ.plains = τ'.plains := hS.1
  unfold InteractiveOracleProof.dview
  refine congr (congr (congrArg DView.mk h1) ?_) ?_
  · rw [← hρ]
    exact extAns_congr Q x τ.rho y y' hy
  · funext p
    rw [← hρ, ← h1]
    by_cases hp : p ∈ Q.reads x τ.rho τ.plains ∨ Q.blinded p = false
    · rw [if_pos hp, if_pos hp, hS.2 p hp]
    · rw [if_neg hp, if_neg hp]

/-- The same for the runs of two strategies against the same verifier messages. -/
theorem dview_run_eq (Q : InteractiveOracleProof X E) (x : X) (y y' : E.Str) (σ σ' : Strat Q.shape Unit)
    (ρ : Rho Q.shape) (hS : Shows Q x (σ.run ρ).1 (σ'.run ρ).1)
    (hy : ∀ p ∈ Q.extReads x ρ, E.rd y p = E.rd y' p) :
    Q.dview x y (σ.run ρ).1 = Q.dview x y' (σ'.run ρ).1 :=
  dview_eq_of_shows Q x y y' _ _ ((Strat.rho_run σ ρ).trans (Strat.rho_run σ' ρ).symm) hS
    (by rw [Strat.rho_run]; exact hy)

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.dview_eq_of_shows
#print axioms OnBytes.LinkSim.dview_run_eq
#print axioms OnBytes.LinkSim.extAns_build
