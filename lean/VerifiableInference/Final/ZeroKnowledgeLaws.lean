-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/ZeroKnowledgeLaws.lean: small laws of the refusal in ZeroKnowledgeBeforeHashing.lean.

1.  At a request that is not served a value that meets the run-by-run line shows nothing.
2.  HonestProvers.refuseUnserved refuses, at any provers, and at a served request nothing turns.
3.  So whatever meets the other fields of the run-by-run line meets all of them once it refuses.
Nothing here is about one protocol.
-/
import VerifiableInference.Final.ZeroKnowledgeBeforeHashing

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob Hiop.Seeded

variable {I X : Type} {L : HolographicProtocol I X}

/-- At a request that is not served the value shows nothing, at every message. -/
theorem refused_output {work : PartsWork L} {provers : HonestProvers L}
    {simulators : RunSimulators L} {inRange : I → Prop} {Served : I → X → Prop} {N : Budget}
    (h : RunByRun work provers simulators inRange Served N) (n : ℕ) (w : I × L.EncodingRandomness × L.OutOfDomainSeed)
    (y : X × L.Rec) (hi : inRange w.1) (hy : y.2 = L.recOf w.1 w.2.1 w.2.2) (hs : ¬ Served w.1 y.1)
    (ρ : Rho L.onlineBatch.loc.shape) : (provers.onlineAtCopy n).output w y ρ = PMF.pure none := by
  unfold Honest.output
  rw [if_pos]
  rw [h.refuses n w y hi hy hs]
  exact Set.mem_univ _

/-- It refuses: the field refuses holds of it by construction, at any provers. -/
theorem refuseUnserved_withheld (provers : HonestProvers L) (Served : I → X → Prop) (n : ℕ)
    (w : I × L.EncodingRandomness × L.OutOfDomainSeed) (y : X × L.Rec) (h : ¬ Served w.1 y.1) :
    ((provers.refuseUnserved Served).onlineAtCopy n).withheld w y = Set.univ :=
  Set.eq_univ_of_forall fun _ => Or.inr (Or.inl h)

/-- At a served request nothing turns: the private stops. -/
theorem refuseUnserved_hid_served (provers : HonestProvers L) (Served : I → X → Prop) (n : ℕ)
    (w : I × L.EncodingRandomness × L.OutOfDomainSeed) (y : X × L.Rec) (h : Served w.1 y.1) :
    ((provers.refuseUnserved Served).onlineAtCopy n).Hid w y = (provers.onlineAtCopy n).Hid w y := by
  ext ρ
  exact ⟨fun hρ => hρ.elim (fun hn => absurd h hn) id, Or.inr⟩

/-- At a served request nothing turns: the whole abort set. -/
theorem refuseUnserved_withheld_eq (provers : HonestProvers L) (Served : I → X → Prop) (n : ℕ)
    (w : I × L.EncodingRandomness × L.OutOfDomainSeed) (y : X × L.Rec) (h : Served w.1 y.1) :
    ((provers.refuseUnserved Served).onlineAtCopy n).withheld w y =
      (provers.onlineAtCopy n).withheld w y := by
  show (provers.onlineAtCopy n).Bad ∪ ((provers.refuseUnserved Served).onlineAtCopy n).Hid w y = _
  rw [refuseUnserved_hid_served provers Served n w y h]
  rfl

/-- At a served request nothing turns: the output. -/
theorem refuseUnserved_output (provers : HonestProvers L) (Served : I → X → Prop) (n : ℕ)
    (w : I × L.EncodingRandomness × L.OutOfDomainSeed) (y : X × L.Rec) (h : Served w.1 y.1) (ρ : Rho L.onlineBatch.loc.shape) :
    ((provers.refuseUnserved Served).onlineAtCopy n).output w y ρ =
      (provers.onlineAtCopy n).output w y ρ := by
  have e := refuseUnserved_withheld_eq provers Served n w y h
  unfold Honest.output
  by_cases hm : ρ ∈ (provers.onlineAtCopy n).withheld w y
  · rw [if_pos hm, if_pos (e ▸ hm)]
  · rw [if_neg hm, if_neg (fun h' => hm (e ▸ h'))]
    rfl

/-- **THE MEMBER.** Whatever meets the other fields of the run-by-run line meets all of them once it refuses. -/
theorem refuseUnserved_runByRun (work : PartsWork L) (provers : HonestProvers L) (simulators : RunSimulators L)
    (inRange : I → Prop) (Served : I → X → Prop) (N : Budget)
    (hT : provers.SpeakOfTheirTables)
    (hOff : ExactOutsideStops provers.offlineProver (fun w y => inRange w.1 ∧ L.validT w y) work.offline.cleared
      simulators.offline)
    (hLink : ExactOutsideStops provers.linkProver (fun w y => inRange w.1 ∧ L.validL w y) work.link.cleared
      simulators.link)
    (hOn : ∀ n, ExactOutsideStops (provers.onlineAtCopy n)
      (fun w y => inRange w.1 ∧ L.validB Served w y) work.online.cleared (simulators.online n))
    (hOffS : PrivateStopsAtMost provers.offlineProver (fun w y => inRange w.1 ∧ L.validT w y) work.offline
      N.offlineStops)
    (hLinkS : PrivateStopsAtMost provers.linkProver (fun w y => inRange w.1 ∧ L.validL w y) work.link N.linkStops)
    (hOnS : ∀ n, PrivateStopsAtMost (provers.onlineAtCopy n)
      (fun w y => inRange w.1 ∧ L.validB Served w y) work.online N.onlineStops) :
    RunByRun work (provers.refuseUnserved Served) simulators inRange Served N where
  tables := ⟨hT.offline, hT.link, hT.online⟩
  offline := hOff
  link := hLink
  online := fun n w y hv ρ hρ =>
    (refuseUnserved_output provers Served n w y hv.2.2 _).trans
      (hOn n w y hv ρ fun h' => hρ (by
        rw [refuseUnserved_hid_served provers Served n w y hv.2.2]
        exact h'))
  offlineStops := hOffS
  linkStops := hLinkS
  onlineStops := fun n w y hv => by
    show pr (unif (Rho L.onlineBatch.loc.shape))
      {ρ | work.online.cleared ρ ∈ ((provers.refuseUnserved Served).onlineAtCopy n).Hid w y} ≤ N.onlineStops
    rw [refuseUnserved_hid_served provers Served n w y hv.2.2]
    exact hOnS n w y hv
  refuses := fun n w y _ _ hs => refuseUnserved_withheld provers Served n w y hs

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.refused_output
#print axioms VerifiableInference.Compilation.refuseUnserved_withheld
#print axioms VerifiableInference.Compilation.refuseUnserved_hid_served
#print axioms VerifiableInference.Compilation.refuseUnserved_withheld_eq
#print axioms VerifiableInference.Compilation.refuseUnserved_output
#print axioms VerifiableInference.Compilation.refuseUnserved_runByRun
