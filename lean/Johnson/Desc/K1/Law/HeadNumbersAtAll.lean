-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HeadNumbersAtAll.lean: FOUR PREMISES OF THE LAW ON THE SUB-PROTOCOL K1 (hsub,
hWn, hU, hKw of k01_kind_paidThree, Johnson/Desc/AtSeats/K01KindPaidThree.lean), AT THE
CLOSED CONSTANT (`hA.𝔇`, Johnson/P5J/MgAtAll.lean), each in the premise's own type. Definitions (two
tests with code) and statements with their proofs; nothing is evaluated.

  `hsub_any`, `hsub_atAll`   **hsub**: BY THE MAKE, at every table's numbers: a segment's group is
      its three moments' tenants, the first moment's among them. Proved (general); no example is
      wanted
  `hWn_atAll`   **hWn**: under the head alone: the head's field `pubOne` says that the constant's
      public parameters are what the reader of the public files returns; at every such return each
      attention plan is the planner's own (`planIs_public`,
      Johnson/Desc/First/Att/GuardPublic.lean), and there the planned number of columns of the array
      of the reads IS the plan's nW (`plannedK_of_planIs`, Johnson/Desc/First/Att/K05PlannedK.lean)
  `reads_zero`   under the head alone the number of the output head's array of the reads is 0
      (`public_third`, Johnson/Desc/Kinds/Law/ReadsNamed.lean)
  `readsArrB`, `hU_atAll`   **hU** (there is such a cU) FROM ONE TEST WITH CODE on the planner's
      list of segments and the public parameters: segment 24's list of arrays has an entry at that
      number
  `readsWideB`, `hKw_atAll`   **hKw** FROM ONE TEST WITH CODE on the same two: segment 24's planned
      ledger has an array at that number, with at least as many columns as the head's plan asks
  `readsArr_rejects`, `readsWide_rejects`   negative tests, WEAK: at an empty list of segments both
      reject, at every public parameters. No written value of the planner's list is in reach here

What is not claimed. That the two tests accept at any files: they read the public files' planner's
list alone and are to be evaluated there. No member of the head hA. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.TestsAtAll
import Johnson.Desc.First.Att.K05PlannedK
import Johnson.Desc.First.Att.GuardPublic
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.Desc.First.SentTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.Att.P (plannedK planIs_public plannedK_of_planIs)
open VerifiableInference.Desc.Kinds.Head.Law (readsOf)
open ProofFile (Cl)

/-- **hsub, at every table's numbers.** -/
theorem hsub_any (N : Numbers) (m : ℕ) : ∀ x ∈ N.sent m 0, x ∈ N.group m :=
  fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx)

/-- A test: segment 24's list of arrays has an entry at the number of the head's array of the
reads. -/
def readsArrB (built : Array Stages.LinkH) (X : Verify.Public) : Bool :=
  (((built.map (·.arrayOf)).getD 24 #[])[readsOf X]?).isSome

/-- A test: segment 24's planned ledger has an array at that number, with at least as many columns
as the head's plan asks. -/
def readsWideB (built : Array Stages.LinkH) (X : Verify.Public) : Bool :=
  ((First.FillSent.treesAt built 24)[readsOf X]?).any fun t => decide (X.H.nU.getD 2 0 ≤ t.2.1)

/-- The negative test, weak: at an empty list of segments. -/
theorem readsArr_rejects (X : Verify.Public) : readsArrB #[] X = false := by
  unfold readsArrB
  simp

/-- The negative test, weak: at an empty list of segments. -/
theorem readsWide_rejects (X : Verify.Public) : readsWideB #[] X = false := by
  unfold readsWideB First.FillSent.treesAt
  simp

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
include hA

theorem hsub_atAll : ∀ x ∈ hA.𝔇.N.sent 24 0, x ∈ hA.𝔇.N.group 24 := hsub_any _ 24

/-- **hWn.** -/
theorem hWn_atAll : ∀ (g : ℕ) Ap, (P5J.At.X Zp).A[g]? = some Ap → Ap.nW ≤ plannedK Ap :=
  fun _ _ h => Nat.le_of_eq (plannedK_of_planIs (planIs_public hA.pubOne) h).symm

/-- The number of the head's array of the reads is 0. -/
theorem reads_zero : readsOf (P5J.At.X Zp) = 0 := by
  have h : (P5J.At.X Zp).H.tl.ix.U.getD 2 none = some 0 :=
    Kinds.Head.Law.ReadsNamed.public_third hA.pubOne
  unfold readsOf
  rw [h]
  rfl

/-- **hU**: there is such a cU. -/
theorem hU_atAll (h : readsArrB Zp.made.p.built.links (P5J.At.X Zp) = true) :
    ∃ cU, (hA.𝔇.pubD.d3.arrayOf.getD 24 #[])[readsOf (P5J.At.X Zp)]? = some cU :=
  Option.isSome_iff_exists.1 h

/-- **hKw.** -/
theorem hKw_atAll (h : readsWideB Zp.made.p.built.links (P5J.At.X Zp) = true) :
    ∀ t, (hA.𝔇.pubD.dS.trees 24)[readsOf (P5J.At.X Zp)]? = some t →
      (P5J.At.X Zp).H.nU.getD 2 0 ≤ t.2.1 := by
  intro t ht
  have ht' : (First.FillSent.treesAt Zp.made.p.built.links 24)[readsOf (P5J.At.X Zp)]? = some t :=
    ht
  unfold readsWideB at h
  rw [ht'] at h
  exact of_decide_eq_true h

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hsub_any
#print axioms VerifiableInference.Desc.K1.readsArr_rejects
#print axioms VerifiableInference.Desc.K1.readsWide_rejects
#print axioms VerifiableInference.Desc.K1.hsub_atAll
#print axioms VerifiableInference.Desc.K1.hWn_atAll
#print axioms VerifiableInference.Desc.K1.reads_zero
#print axioms VerifiableInference.Desc.K1.hU_atAll
#print axioms VerifiableInference.Desc.K1.hKw_atAll
