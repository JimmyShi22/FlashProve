-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/AtHome.lean: the two link clauses of the zero-knowledge statement (ZeroKnowledgeOnServedRequests) at
the explicit honest link prover explicitLinkProver. This prover part meets ExactOutsideStops with no
error and StopsAtMost at 0, at every map on the messages and every range.

  home_exactOutsideStops   the clause exact, by homeExactAll
  home_stopsAtMost         the clause on stops at 0, by home_withheld: the whole abort set is empty
  home_valid               the clauses speak of something: every private input in range has its
                           honest instance, which is valid

Which protocol: by the head of HomeExactAll.lean the instance of explicitLinkProver is the two tables'
out-of-domain samples.



What is not claimed. That a value of HonestProvers holds explicitLinkProver beside offline and online
provers: this file speaks of the link's part alone. That the index is hidden: the simulator is given
the two tables' samples and symbols.
-/
import VerifiableInference.Final.ZeroKnowledgeBeforeHashing
import Johnson.LinkSim.AtHome.HomeExactAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LinkSim.AtHome
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open OnBytes.LinkSim (validLk)
open _root_.Iop (Rho InteractiveOracleProof Honest)
open VerifiableInference.Compilation (ExactOutsideStops PrivateStopsAtMost)

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- **The exact clause at the link's honest prover**, with no message excepted. -/
theorem home_exactOutsideStops (inRange : (homeR b Z).Index → Prop)
    (clear : Rho (HomeQ Z).shape → Rho (HomeQ Z).shape) :
    ExactOutsideStops (explicitLinkProver b Z) (fun w y => inRange w.1 ∧ (homeR b Z).protocol.validL w y) clear
      (homeSim Z) := by
  intro w y hv ρ _
  exact homeExactAll b Z w y ⟨trivial, trivial, trivial, hv.2⟩ (clear ρ)

/-- **The clause on stops at the link's honest prover**: at 0. -/
theorem home_stopsAtMost (inRange : (homeR b Z).Index → Prop)
    (work : _root_.Iop.WorkBits (HomeQ Z).shape) :
    PrivateStopsAtMost (explicitLinkProver b Z) (fun w y => inRange w.1 ∧ (homeR b Z).protocol.validL w y) work 0 := by
  intro w y _
  have e : {ρ | work.cleared ρ ∈ (explicitLinkProver b Z).Hid w y} = ∅ := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have h2 : work.cleared ρ ∈ (explicitLinkProver b Z).withheld w y := Or.inr h
    rw [home_withheld] at h2
    exact h2
  show _root_.Iop.prRho {ρ | work.cleared ρ ∈ (explicitLinkProver b Z).Hid w y} ≤ 0
  rw [e]
  exact le_of_eq (Prob.pr_empty _)

/-- **The two clauses are not empty**: each private input in range has a valid instance. -/
theorem home_valid (inRange : (homeR b Z).Index → Prop) (w : HomeWt b Z) (hr : inRange w.1) :
    ∃ y, inRange w.1 ∧ (homeR b Z).protocol.validL w y :=
  ⟨homeInst b Z w, hr, ((valid_iff_homeInst b Z w _).2 rfl).2.2.2⟩

/-- **The two clauses in RunByRun's own slots**: at any value of the provers and simulators of the
protocol homeR b Z whose link parts are these two, and any work bits. -/
theorem home_runByRun_link (inRange : (homeR b Z).Index → Prop)
    (provers : VerifiableInference.Compilation.HonestProvers (homeR b Z).protocol)
    (simulators : VerifiableInference.Compilation.RunSimulators (homeR b Z).protocol)
    (work : _root_.Iop.PartsWork (homeR b Z).protocol)
    (hp : provers.linkProver = explicitLinkProver b Z) (hs : simulators.link = homeSim Z) :
    ExactOutsideStops provers.linkProver (fun w y => inRange w.1 ∧ (homeR b Z).protocol.validL w y)
        work.link.cleared simulators.link ∧
      PrivateStopsAtMost provers.linkProver (fun w y => inRange w.1 ∧ (homeR b Z).protocol.validL w y)
        work.link 0 := by
  rw [hp, hs]
  exact ⟨home_exactOutsideStops b Z inRange work.link.cleared,
    home_stopsAtMost b Z inRange work.link⟩

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.home_runByRun_link
#print axioms OnBytes.LinkSim.AtHome.home_exactOutsideStops
#print axioms OnBytes.LinkSim.AtHome.home_stopsAtMost
#print axioms OnBytes.LinkSim.AtHome.home_valid
