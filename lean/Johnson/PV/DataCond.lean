-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/DataCond.lean: **THE FOUR CONDITIONS ON DATA UNDER WHICH THE CODING THAT IS LAID IS THE
  WRITING SIDE OF A ONE-TO-ONE CODING** (mSOne | mFOne's four premises: Johnson/PV/MSmallOne.lean [not in this library] |
  MFullOne.lean), AS FOUR ROWS WITH CODE, GENERAL IN THE DATA: at whatever DK | DP, K and c a caller
  lays
(the dry run's, the plan's, a description's own): each CAN say no.
  condRows a DK DP K c : List (String × Bool) · condOk := all four · **condOk_gives**: where all
    four say yes the four premises hold, in the very shapes that mSOne | mFOne take.
WHAT kindsAndWorkBelow256 ASKS (OnBytes/Maker/Page/FitAt.lean:56): every written round's kind's number
  and bits of work are below 256: they are written into one byte each.


-/
import OnBytes.Maker.Page.FitAt
import Johnson.EntryRec.OkcFiles

set_option autoImplicit false

namespace PV.DataCond
open OnBytes.Maker OnBytes.Maker.Page

/-- The four rows. a: the stored table's depth at the size (srS.P.T.a | frS.P.T.a). -/
def condRows (a : ℕ) (DK DP : WholeD) (K : ℕ) (c : ByteArray) : List (String × Bool) :=
  [("coding.1: the key file's data: every round's kind and work fit a byte (smallD)", kindsAndWorkBelow256 (DK.at
                    a)),
    ("coding.2: the proof file's data: the same", kindsAndWorkBelow256 (DP.at a)),
    ("coding.3: K + 2 is below 2 ^ 49", decide (K + 1 + 1 < 2 ^ 49)),
    ("coding.4: the configuration's digest has 32 bytes", decide (c.size = 32))]

/-- All four. -/
def condOk (a : ℕ) (DK DP : WholeD) (K : ℕ) (c : ByteArray) : Bool := (condRows a DK DP K c).all
    (·.2)

/-- **Where all four say yes, the four premises hold.** -/
theorem condOk_gives {a : ℕ} {DK DP : WholeD} {K : ℕ} {c : ByteArray} (h : condOk a DK DP K c =
    true) :
    kindsAndWorkBelow256 (DK.at a) = true ∧ kindsAndWorkBelow256 (DP.at a) = true ∧ K + 1 + 1 < 2 ^ 49 ∧ c.size = 32 := by
  simp only [condOk, condRows, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end PV.DataCond

#print axioms PV.DataCond.condOk_gives
-- two of the four seen to say no (DUE [true, true, false, false]): empty data; K := 2 ^ 49; no byte
-- of c
#eval (PV.DataCond.condRows 3 ⟨0, [], [], [], fun _ => 0, fun _ => 0, fun _ => 0⟩ ⟨0, [], [], [],
    fun _ => 0, fun _ => 0, fun _ => 0⟩ (2 ^ 49) ByteArray.empty).map (·.2)
