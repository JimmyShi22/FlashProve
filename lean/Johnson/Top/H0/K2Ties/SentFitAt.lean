-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/SentFitAt.lean: the code switch's law at the closed constant's letters
(P5J/LettersAt.lean): THE NAMED TEST sentFitB (Tw/K2C/SentFit.lean: the tenants that the table's
numbers list for a switch's sending are the place's count of trees plus the sending's own lay) IS A
THEOREM AT THE CONSTANT's OWN NUMBERS, AT ALL 25 SWITCHES, at the written lists of notices.
  NW           the table's numbers at the written values, as far as the test reads them: N0Full with
               treesAt off toldFull
  sentFitB_same  the test reads of the numbers treesAt and sent alone
  sentFit_written  IT ACCEPTS AT ALL 25 SWITCHES AT THE WRITTEN VALUES (NW · the written list of
               places · csW · the lists sentW g, K2Hands/FrontsFullTied.lean): by decide +kernel
  sentFit_rejects_list · sentFit_rejects_place  two negative tests, by the kernel: the first
               switch's place with the second's list; the first switch's list one place further on
  sentFit_at   SO IT ACCEPTS AT At.N Zp cF, At.ps, the public part's codes: under WrittenAt.lean's
               AtWritten and ToldAt.lean's AtTold
  sentFit_link · sentFit_head · sentFit_fin  the same in the letters of the premise hT of
               hnew_link | hnew_head | hnew_fin (Johnson/P1K2R/TieTwoPays.lean)
UNDER WHAT. AtWritten: in scope, the value laid, the pin madePinnedAt. AtTold: the first chain has
the written cut (hcut). NOT HERE. The test at the plan's own numbers n.codes | n.sent of a switch
(sentFitAll): that wants «the plan's notices are the written list». TieTwoPays.lean's hsent
is another sentence (the piece's base and the rounds' data of its stretch).
LIMITS. The full size alone. No soundness is claimed.
-/
import Johnson.Top.H0.K2Ties.ToldAt
import Johnson.Top.H0.Tw.K2C.SentFit
import Johnson.Top.H0.K2Hands.FrontsFullTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First.K2 (sentFitB switchSpots)
open VerifiableInference.Desc.First.K2Hands (csW sentW)
open P5T (N0Full)
open P5J (TS)

/-- The table's numbers at the written values, as far as the test reads them. -/
def NW : Numbers :=
  { N0Full with treesAt := fun p => treesTold toldFull (borderOf P5J.At.ps p) }

/-- The test reads of the numbers treesAt and sent alone. -/
theorem sentFitB_same {N N' : Numbers} (h1 : N.treesAt = N'.treesAt) (h2 : N.sent = N'.sent)
    (m : ℕ) (pIn : Option Place) (codes : Codes) (sent : Array OracleNotice) :
    sentFitB N m pIn codes sent = sentFitB N' m pIn codes sent := by
  unfold sentFitB
  rw [h1, h2]

set_option maxRecDepth 1000000 in
/-- **THE TEST ACCEPTS AT ALL 25 SWITCHES, AT THE WRITTEN VALUES.** -/
theorem sentFit_written :
    (switchSpots.all fun t =>
      sentFitB NW t.1 P5J.At.ps[t.2.2]? csW (sentW t.1).toArray) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: the first switch's place with the second's list of notices. -/
theorem sentFit_rejects_list : sentFitB NW 1 P5J.At.ps[16]? csW (sentW 2).toArray = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A second**: the first switch's list at the place one sub-protocol further on, behind its own
sending. -/
theorem sentFit_rejects_place : sentFitB NW 1 P5J.At.ps[17]? csW (sentW 1).toArray = false := by
  decide +kernel

/-- **THE TEST ACCEPTS AT THE CONSTANT's OWN NUMBERS.** -/
theorem sentFit_at {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF) (T : AtTold Zp cF) :
    ∀ t ∈ switchSpots,
      sentFitB (P5J.At.N Zp cF) t.1 P5J.At.ps[t.2.2]? Zp.first.codes (sentW t.1).toArray =
        true := by
  intro t ht
  have hc : Zp.first.codes = csW := A.cs
  rw [hc, sentFitB_same (N' := NW) T.treesAt A.sent]
  exact List.all_eq_true.1 sentFit_written t ht

/-- The same at the switch into group m + 1, m < 23: in the letters of hnew_link (hT). -/
theorem sentFit_link {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF) (T : AtTold Zp cF)
    {m : ℕ} (h23 : m < 23) :
    sentFitB (P5J.At.N Zp cF) (m + 1) P5J.At.ps[14 * (m + 1) + 2]? Zp.first.codes
      (sentW (m + 1)).toArray = true :=
  sentFit_at A T (m + 1, some (m + 1), 14 * (m + 1) + 2)
    (List.mem_append_left _ (List.mem_map.2 ⟨m, List.mem_range.2 h23, rfl⟩))

/-- At the head's switch (hnew_head's hT). -/
theorem sentFit_head {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF)
    (T : AtTold Zp cF) :
    sentFitB (P5J.At.N Zp cF) 24 P5J.At.ps[339]? Zp.first.codes (sentW 24).toArray = true :=
  sentFit_at A T (24, some 24, 339) (List.mem_append_right _ (by simp))

/-- At the finish's switch (hnew_fin's hT). -/
theorem sentFit_fin {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (A : AtWritten Zp cF)
    (T : AtTold Zp cF) :
    sentFitB (P5J.At.N Zp cF) 25 P5J.At.ps[353]? Zp.first.codes (sentW 25).toArray = true :=
  sentFit_at A T (25, none, 353) (List.mem_append_right _ (by simp))

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.sentFit_link
#print axioms VerifiableInference.Desc.First.K2Ties.sentFit_head
#print axioms VerifiableInference.Desc.First.K2Ties.sentFit_fin

#print axioms VerifiableInference.Desc.First.K2Ties.sentFit_written
#print axioms VerifiableInference.Desc.First.K2Ties.sentFit_rejects_list
#print axioms VerifiableInference.Desc.First.K2Ties.sentFit_rejects_place
#print axioms VerifiableInference.Desc.First.K2Ties.sentFit_at
