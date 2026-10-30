-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/SentPlaceAt.lean: the code switch's law at the closed constant
(P5J.mgAtAll): THE NAMED TEST sentPlaceB (Johnson/Top/H0/Tw/K2C/SentByPlace.lean: the
tenants that the table's numbers list for a switch's sending are, PLACE BY PLACE, the place's count
of trees plus the sending's own lay: sentFitB's text with «==» for «the same members») IS A THEOREM
AT THE CONSTANT's OWN NUMBERS, AT ALL 25 SWITCHES, at the written lists of notices. The pattern of
SentFitAt.lean.
  sentPlaceB_same  the test reads of the numbers treesAt and sent alone
  sentPlace_written  IT ACCEPTS AT ALL 25 SWITCHES AT THE WRITTEN VALUES (SentFitAt.lean's NW · the
                written list of places · csW · sentW g): by decide +kernel
  NWrev · sentPlace_rejects_reversed  a negative test, by the kernel: with each list of tenants
                turned round the test by place REJECTS at the first switch, WHERE THE TEST ON
                MEMBERS STILL ACCEPTS: so this test says more
  sentPlace_rejects_place  a second: the first switch's list one place further on
  sentPlace_at  SO IT ACCEPTS AT At.N Zp cF, At.ps, the public part's codes: under AtWritten and
                AtTold
  sentPlace_link · sentPlace_head · sentPlace_fin  the same in the letters of the premise hPl of
                three_together (Johnson/Top/H0/Tw/K2C/ThreeTogether.lean): sentPlaceB N (m + 1)
                ps[k]? codes sent, at codes := the public part's, sent := the written list
UNDER WHAT. AtWritten: in scope, the value laid, the pin madePinnedAt. AtTold: the first chain has
the written cut (hcut). NOT HERE. The test at the plan's own numbers n.codes | n.sent
(sentPlaceAll).
LIMITS. The full size alone. No soundness is claimed.
-/
import Johnson.Top.H0.K2Ties.SentFitAt
import Johnson.Top.H0.Tw.K2C.SentByPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First.K2 (switchSpots)
open VerifiableInference.Desc.First.K2Caller (sentPlaceB)
open VerifiableInference.Desc.First.K2Hands (csW sentW)
open P5T (N0Full)
open P5J (TS)

/-- The test reads of the numbers treesAt and sent alone. -/
theorem sentPlaceB_same {N N' : Numbers} (h1 : N.treesAt = N'.treesAt) (h2 : N.sent = N'.sent)
    (m : ℕ) (pIn : Option Place) (codes : Codes) (sent : Array OracleNotice) :
    sentPlaceB N m pIn codes sent = sentPlaceB N' m pIn codes sent := by
  unfold sentPlaceB
  rw [h1, h2]

set_option maxRecDepth 1000000 in
/-- **THE TEST BY PLACE ACCEPTS AT ALL 25 SWITCHES, AT THE WRITTEN VALUES.** -/
theorem sentPlace_written :
    (switchSpots.all fun t =>
      sentPlaceB NW t.1 P5J.At.ps[t.2.2]? csW (sentW t.1).toArray) = true := by
  decide +kernel

/-- The written numbers with each list of tenants turned round. -/
def NWrev : Numbers := { NW with sent := fun m t => (NW.sent m t).reverse }

set_option maxRecDepth 1000000 in
/-- **A negative test**: with the lists of tenants turned round the test by place rejects at the
first switch, where the test on members still accepts. -/
theorem sentPlace_rejects_reversed :
    sentPlaceB NWrev 1 P5J.At.ps[16]? csW (sentW 1).toArray = false ∧
      K2.sentFitB NWrev 1 P5J.At.ps[16]? csW (sentW 1).toArray = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A second**: the first switch's list one place further on, behind its own sending. -/
theorem sentPlace_rejects_place :
    sentPlaceB NW 1 P5J.At.ps[17]? csW (sentW 1).toArray = false := by decide +kernel

/-- **THE TEST BY PLACE ACCEPTS AT THE CONSTANT's OWN NUMBERS.** -/
theorem sentPlace_at {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF)
    (T : AtTold Zp cF) : ∀ t ∈ switchSpots,
      sentPlaceB (P5J.At.N Zp cF) t.1 P5J.At.ps[t.2.2]? Zp.first.codes (sentW t.1).toArray =
        true := by
  intro t ht
  have hc : Zp.first.codes = csW := A.cs
  rw [hc, sentPlaceB_same (N' := NW) T.treesAt A.sent]
  exact List.all_eq_true.1 sentPlace_written t ht

/-- At the switch into group m + 1, m < 23: in the letters of three_together's hPl. -/
theorem sentPlace_link {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF)
    (T : AtTold Zp cF) {m : ℕ} (h23 : m < 23) :
    sentPlaceB (P5J.At.N Zp cF) (m + 1) P5J.At.ps[14 * (m + 1) + 2]? Zp.first.codes
      (sentW (m + 1)).toArray = true :=
  sentPlace_at A T (m + 1, some (m + 1), 14 * (m + 1) + 2)
    (List.mem_append_left _ (List.mem_map.2 ⟨m, List.mem_range.2 h23, rfl⟩))

/-- At the head's switch. -/
theorem sentPlace_head {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF)
    (T : AtTold Zp cF) :
    sentPlaceB (P5J.At.N Zp cF) (23 + 1) P5J.At.ps[339]? Zp.first.codes (sentW 24).toArray =
      true :=
  sentPlace_at A T (24, some 24, 339) (List.mem_append_right _ (by simp))

/-- At the finish's switch. -/
theorem sentPlace_fin {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF)
    (T : AtTold Zp cF) :
    sentPlaceB (P5J.At.N Zp cF) (24 + 1) P5J.At.ps[353]? Zp.first.codes (sentW 25).toArray =
      true :=
  sentPlace_at A T (25, none, 353) (List.mem_append_right _ (by simp))

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.sentPlace_written
#print axioms VerifiableInference.Desc.First.K2Ties.sentPlace_rejects_reversed
#print axioms VerifiableInference.Desc.First.K2Ties.sentPlace_rejects_place
#print axioms VerifiableInference.Desc.First.K2Ties.sentPlace_at
#print axioms VerifiableInference.Desc.First.K2Ties.sentPlace_link
#print axioms VerifiableInference.Desc.First.K2Ties.sentPlace_head
#print axioms VerifiableInference.Desc.First.K2Ties.sentPlace_fin
