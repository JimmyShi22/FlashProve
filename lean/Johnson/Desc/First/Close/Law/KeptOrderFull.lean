-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/KeptOrderFull.lean (kind K10): EACH KEPT MEMBER OF A WRITTEN LIST
STANDS, AMONG THE LIST's KEPT MEMBERS, WHERE ITS NUMBER STANDS IN THE SWITCH's ROW's LIST OF KEPT
NUMBERS: at the 25 written lists of the full size and at link 0's five-list. A test with code, its
meaning, evaluations by the kernel.

Why. `keptOrder_of_shapes` (Johnson/Desc/First/Link/Law/KeptPlaces.lean) has
`KeptOrder` from `ShapesAre` and ONE SENTENCE on lo, kb and kl alone: for every i with a main row
and the flag: `(keptNosOf lo kb)[kl.idxOf i.val]? = some (posOf lo i)`. That file stands over its
whole cone. Here the sentence is stated WITH `keptNosOf`'s OWN TEXT WRITTEN OUT (`(List.range
(membersOf lo).length).filter fun w => ((membersOf lo).map kb).getD w false`), so that this file
needs none of that cone. THAT THE TEXT HERE IS THAT DEFINITION's IS HELD BY NOTHING IN THIS FILE:
a file that imports both lays the one for the other by one call (`AtMgA.hord_paid`, HCarPaid.lean).
  `keptOrdB lo kb kl`: the test. `keptOrd_of_B`: what it means.
  `keptOrd_fullB`: at every l below 25: row l of the switch's written table (`tableFullLit`) is
    there, and the test says yes at the l-th written list, the written shape's flags and that row's
    kept numbers: by the kernel. `keptOrd_fiveB`: the same at `loFive`, `kbFive` and row 0's kept
    numbers.
  NEGATIVE LINES, by the kernel: `keptOrd_turned`: at `loFive`, with row 0's kept numbers turned
    about: no. `keptOrd_next`: at `loFive`, with row 1's kept numbers: no. `keptOrd_two`: row 0
    keeps two numbers: so the first bend is a bend.
  `keptOrd_full`, `keptOrd_five`: the sentence itself, at a row that the table holds.
Limits. Closed facts on written values. That the switch's row at a file's plan is the written
table's is not this file's. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LinkZeroFive
import Johnson.Top.H0.K2Caller.TableWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G
open VerifiableInference.Desc.ReqLit
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)

/-- The test. -/
def keptOrdB (lo : List (OracleShape × ℕ)) (kb : Fin lo.length → Bool) (kl : List ℕ) : Bool :=
  (List.finRange lo.length).all fun i =>
    !(decide (memMain lo i) && kb i) ||
      decide (((List.range (membersOf lo).length).filter fun w =>
        ((membersOf lo).map kb).getD w false)[kl.idxOf i.val]? = some (posOf lo i))

/-- **What the test means.** -/
theorem keptOrd_of_B {lo : List (OracleShape × ℕ)} {kb : Fin lo.length → Bool} {kl : List ℕ}
    (h : keptOrdB lo kb kl = true) (i : Fin lo.length) (hi : memMain lo i) (hk : kb i = true) :
    ((List.range (membersOf lo).length).filter fun w =>
      ((membersOf lo).map kb).getD w false)[kl.idxOf i.val]? = some (posOf lo i) := by
  have h1 := List.all_eq_true.1 h i (List.mem_finRange i)
  rw [hk, decide_eq_true hi] at h1
  exact of_decide_eq_true h1

theorem keptOrd_fullB :
    (List.range 25).all (fun l => (tableFullLit[l]?).any fun r =>
      keptOrdB (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])) r.kept) =
      true := by decide +kernel

theorem keptOrd_fiveB : (tableFullLit[0]?).any (fun r => keptOrdB loFive kbFive r.kept) = true := by
  decide +kernel

/-- A negative line: row 0's kept numbers turned about. -/
theorem keptOrd_turned :
    (tableFullLit[0]?).any (fun r => keptOrdB loFive kbFive r.kept.reverse) = false := by
  decide +kernel

/-- A negative line: the next row's kept numbers. -/
theorem keptOrd_next : (tableFullLit[1]?).any (fun r => keptOrdB loFive kbFive r.kept) = false := by
  decide +kernel

/-- Row 0 keeps two numbers. -/
theorem keptOrd_two : (tableFullLit[0]?).any (fun r => r.kept.length == 2) = true := by
  decide +kernel

/-- **The sentence at the written lists.** -/
theorem keptOrd_full (l : ℕ) (hl : l < 25) (r : SwRow) (hr : tableFullLit[l]? = some r)
    (i : Fin (linksFullLit.getD l []).length) (hi : memMain (linksFullLit.getD l []) i)
    (hk : kbAt shapeFull l (linksFullLit.getD l []) i = true) :
    ((List.range (membersOf (linksFullLit.getD l [])).length).filter fun w =>
      ((membersOf (linksFullLit.getD l [])).map
        (kbAt shapeFull l (linksFullLit.getD l []))).getD w false)[r.kept.idxOf i.val]? =
      some (posOf (linksFullLit.getD l []) i) := by
  have h := List.all_eq_true.1 keptOrd_fullB l (List.mem_range.2 hl)
  rw [hr] at h
  exact keptOrd_of_B h i hi hk

/-- **The sentence at link 0's five-list.** -/
theorem keptOrd_five (r : SwRow) (hr : tableFullLit[0]? = some r) (i : Fin loFive.length)
    (hi : memMain loFive i) (hk : kbFive i = true) :
    ((List.range (membersOf loFive).length).filter fun w =>
      ((membersOf loFive).map kbFive).getD w false)[r.kept.idxOf i.val]? =
      some (posOf loFive i) := by
  have h := keptOrd_fiveB
  rw [hr] at h
  exact keptOrd_of_B h i hi hk

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.keptOrd_of_B
#print axioms VerifiableInference.Desc.First.Close.keptOrd_fullB
#print axioms VerifiableInference.Desc.First.Close.keptOrd_fiveB
#print axioms VerifiableInference.Desc.First.Close.keptOrd_turned
#print axioms VerifiableInference.Desc.First.Close.keptOrd_next
#print axioms VerifiableInference.Desc.First.Close.keptOrd_two
#print axioms VerifiableInference.Desc.First.Close.keptOrd_full
#print axioms VerifiableInference.Desc.First.Close.keptOrd_five
