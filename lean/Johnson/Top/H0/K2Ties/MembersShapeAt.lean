-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/MembersShapeAt.lean: the code switch's law at the closed constant's
letters (P5J.At, P5J/LettersAt.lean): THE NAMED TEST membersPlanB (K2Caller/MembersAtPlan.lean: the
table's members at a switch's kept and new tenants are the typed row's entries, by place): ITS HALF
ON SHAPES AND TENANTS IS A THEOREM AT THE CONSTANT's OWN TERMS, AT ALL 25 SWITCHES; THE WHOLE TEST
FOLLOWS FROM THE RADII ALONE.
  shapeAtB     the test with every radius struck on both sides (MembersSplit.lean's (A)), at the
               written values: proofSends0's number of sendings · a list of seats · N0Full's keptOf
               and sent · the written table's row with its radii struck
  membersShape_written  IT ACCEPTS AT ALL 25 SWITCHES at psFull: by decide +kernel
  bent · membersShape_rejects  a negative test, by the kernel: with the tenants of link 1's first
               sending bent in the plan's seats it rejects at the first switch
  sends_at     in scope, laid, under the pin: the first chain's sendings are proofSends0
               (sends_in_scope, Johnson/Goal/Numbers/MadeInScope.lean)
  membersShape_at  (A) at Zp, At.N Zp cF, the written row: under WrittenAt.lean's AtWritten and hs
  membersPlan_at  SO membersPlanB Zp rad (At.N Zp cF) (m + 1) r = true AT r := tableFullLit[m], FROM
               hB ALONE: at each seat p of psFull with a sample, at (sending k, place j), that sits
               at a tenant of N0Full.keptOf m | N0Full.sent (m + 1) 0: rad k j is the radius of the
               written row's entry at that tenant's place
hB IS A PREMISE OF A LEMMA, NO NEW NAMED TEST. It is not paid: at the constant rad is read off a
second reading of the three public files (P5T.radOf of sendRowsOf's rows), which no pin holds.
LIMITS. The full size alone. No soundness is claimed.
-/
import Johnson.Top.H0.K2Ties.MembersSplit
import Johnson.Top.H0.K2Ties.WrittenAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.PlanWritten.Joined (sends_in_scope)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit membersK2B membersPlanB
  keptEntries)
open P5T (PSeat psFull N0Full mineAt memberListsR)
open Johnson.G (proofSends0)
open P5J (LaidAt TS)

/-- The test with every radius struck, at the written values, at the switch into group m + 1. -/
def shapeAtB (ps : List PSeat) (m : ℕ) : Bool :=
  (tableFullLit[m]?).any fun r =>
    membersK2B (memberListsR proofSends0.sends.length (fun _ _ => 0) ps) (N0Full.keptOf m)
      (N0Full.sent (m + 1) 0) (SwRow.struck r)

set_option maxRecDepth 1000000 in
/-- **(A) ACCEPTS AT ALL 25 SWITCHES, AT THE WRITTEN VALUES.** -/
theorem membersShape_written : ((List.range 25).all fun m => shapeAtB psFull m) = true := by
  decide +kernel

/-- The plan's seats with the tenants of link 1's first sending bent. -/
def bent (ps : List PSeat) : List PSeat :=
  ps.map fun p => if p.seg == some (1, 0) then { p with t := p.t + 1000 } else p

set_option maxRecDepth 1000000 in
/-- **A negative test**: with these tenants bent in the plan's seats it rejects at the first
switch. -/
theorem membersShape_rejects : shapeAtB (bent psFull) 0 = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- In scope, under the pin, the first chain's sendings are the written ones. -/
theorem sends_at (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r₀ Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    Zp.made.proof.1 = proofSends0 := by
  rw [sends_in_scope hZ L.pub hy]
  rfl

/-- **(A) AT THE CONSTANT's OWN TERMS.** -/
theorem membersShape_at (A : AtWritten Zp cF) (hs : Zp.made.proof.1 = proofSends0) {m : ℕ}
    (hm : m < 25) {r : SwRow} (hr : tableFullLit[m]? = some r) :
    membersPlanB Zp (fun _ _ => 0) (P5J.At.N Zp cF) (m + 1) (SwRow.struck r) = true := by
  have hp : P5T.planSeats Zp Zp.D.1 = psFull := A.pseats
  have h := List.all_eq_true.1 membersShape_written m (List.mem_range.2 hm)
  unfold shapeAtB at h
  rw [hr] at h
  unfold membersPlanB
  rw [hs, hp, A.keptOf, A.sent]
  exact h

/-- **THE NAMED TEST membersPlanB AT THE CONSTANT's OWN TERMS, FROM THE RADII ALONE.** -/
theorem membersPlan_at (A : AtWritten Zp cF) (hs : Zp.made.proof.1 = proofSends0) {m : ℕ}
    (hm : m < 25) {r : SwRow} (hr : tableFullLit[m]? = some r) (rad : ℕ → ℕ → ℕ)
    (hB : ∀ k j p, k < proofSends0.sends.length → (mineAt psFull k)[j]? = some p →
      ∀ qe ∈ (N0Full.keptOf m).zip (keptEntries r) ++ (N0Full.sent (m + 1) 0).zip r.l,
        p.seat = qe.1 → rad k j = qe.2.2) :
    membersPlanB Zp rad (P5J.At.N Zp cF) (m + 1) r = true := by
  have hp : P5T.planSeats Zp Zp.D.1 = psFull := A.pseats
  refine membersPlan_split (membersShape_at A hs hm hr) ?_
  rw [hs, hp, A.keptOf, A.sent]
  exact hB

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.membersShape_written
#print axioms VerifiableInference.Desc.First.K2Ties.membersShape_rejects
#print axioms VerifiableInference.Desc.First.K2Ties.sends_at
#print axioms VerifiableInference.Desc.First.K2Ties.membersShape_at
#print axioms VerifiableInference.Desc.First.K2Ties.membersPlan_at
