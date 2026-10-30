-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/HereAtBatch.lean: AT THE TWELVE ATTENTION SEGMENTS, AT EVERY STATE THAT THE FIRST
CHAIN's OWN BLOCKS REACH IN FRONT OF THE BATCHING: THE LEDGER HAS THE PLAN's ARRAY OF THE READS, AT
THE PLANNED WIDTH, OF ONE ROW (Att.P.U3At, Johnson/Desc/First/Att/K05EntsOf.lean). UNDER THE SCOPE,
THE FILES READ AND IM.Open. Lemmas; none of the library's goals. A joining. No prover stands in
them; nothing on completeness, soundness or hiding.

  `u3At_planned`   at every attention plan in what Verify.publicOf returns, at the planned ledger:
      K5Law.public_ofPlan, ofPlan_u3_tree (Johnson/Desc/First/Att/Claims/OfPlan.lean),
      Att.P.plannedK_of_plan (K05PlannedK.lean)
  **`u3At_at_batch`**   at the ledger of a reached state: it has the planned ledger's looks:
      `looks_at_batch` (Johnson/P1K8R/StaticAtBatch.lean), IM.ground_tails (Johnson/IMR/K8Seat.lean)
  **`here_at_batch`**   where the segment's own rounds have been heard (s.heard5? = some hd) the
      state's own part is an attention's, and its ledger has `U3At`
Limits. That the segment's own rounds have been heard is a premise of `here_at_batch`, that a ledger
is open one of `u3At_at_batch`. Nothing on whether any state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P1K8R.StaticAtBatch
import Johnson.Desc.First.Att.K05PlannedK
import Johnson.Desc.First.Att.K05EntsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

/-- At the planned ledger of an attention plan of the public parameters. -/
theorem u3At_planned {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) {g : ℕ} {a : Attention.Plan}
    (hg : X.A[g]? = some a) :
    ∃ T : HTree, a.seam.Fp.trees[a.iU3]? = some T ∧ T.K = Att.P.plannedK a ∧ a.nW ≤ T.K ∧
      T.R = 1 := by
  have hp := K5Law.public_ofPlan h g a hg
  obtain ⟨-, T, hT, hR1, hK, -⟩ := K5Law.ofPlan_u3_tree hp
  exact ⟨T, hT, hK.trans (Att.P.plannedK_of_plan hp).symm, Nat.le_of_eq hK.symm, hR1⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT THE LEDGER OF EVERY STATE REACHED IN FRONT OF AN ATTENTION SEGMENT's BATCHING.** -/
theorem u3At_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Ap : Attention.Plan} (hA : Bs.G₀.W.A[g]? = some Ap) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s)) {G : Fork}
    (hG : s.fork? = some G) : Att.P.U3At Ap (Att.P.plannedK Ap) G := by
  obtain ⟨tails, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨hp, a, x, x', ehp, ea, ex, etl, -, -, -, -, ex', etl', eFp, -⟩ := tails g hg
  obtain rfl : a = Ap := Option.some.inj (ea.symm.trans hA)
  have hlk := looks_at_batch hS hR O (l := 2 * g + 1) (by omega) ex'
    (by rw [if_neg (by omega)]; exact h) hG
  rw [eFp] at hlk
  obtain ⟨T, hT, hK, hW, hR1⟩ := u3At_planned O.public ea
  have e := congrArg (fun L => L[a.iU3]?) hlk
  simp only [List.getElem?_map, Array.getElem?_toList] at e
  rw [hT] at e
  obtain ⟨T', hT', eL⟩ := Option.map_eq_some_iff.1 e
  have eR : T'.R = T.R := congrArg (·.2.1) eL
  have eK : T'.K = T.K := congrArg (·.2.2.1) eL
  exact ⟨T', hT', eK.trans hK, by rw [eK]; exact hW, eR.trans hR1⟩

/-- **Where the segment's own rounds have been heard the own part is an attention's, with that
ledger.** -/
theorem here_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Ap : Attention.Plan} (hA : Bs.G₀.W.A[g]? = some Ap) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s)) {hd : Att.P.Heard}
    (h5 : s.heard5? = some hd) :
    ∃ a, s.here = .att a ∧ Att.P.U3At Ap (Att.P.plannedK Ap) a.F := by
  unfold S.heard5? at h5
  cases hh : s.here with
  | att a => exact ⟨a, rfl, u3At_at_batch hS hR O hg hA h (by simp [S.fork?, hh])⟩
  | between => rw [hh] at h5; exact absurd h5 (by simp)
  | lay a => rw [hh] at h5; exact absurd h5 (by simp)
  | head a => rw [hh] at h5; exact absurd h5 (by simp)
  | fin a => rw [hh] at h5; exact absurd h5 (by simp)
  | mem a => rw [hh] at h5; exact absurd h5 (by simp)

end

end P1K8

#print axioms P1K8.u3At_planned
#print axioms P1K8.u3At_at_batch
#print axioms P1K8.here_at_batch
