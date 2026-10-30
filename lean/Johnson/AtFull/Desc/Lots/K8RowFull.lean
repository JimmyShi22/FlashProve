-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K8RowFull.lean: AN ADDITION TO Johnson/AtFull/Desc/Lots/K8Row.lean: THE ROW
OF THE SMALLNESS TEST's LOT IN THE FORM THAT ProofFile.Sk.back_of_written ASKS
(Johnson/Desc/ProofFile/Law/Skel/SkelWritten.lean): its right side is the written constant
ProofFile.Sk.Full.lot6. NO SUB-PROTOCOL IMPORTS THIS FILE.
  k8RowsW_full      BY THE KERNEL: k8RowsW, of which K8Row.lean cuts five fields from the written
                    table of the first chain's sub-protocols and writes four itself (the name,
                    planOk := true, claims, after), IS ProofFile.Sk.Full.lot6Blocks, which a program made
                    off the evaluator's print of the lots' own blocks at the full size: A TEST THAT
                    COULD HAVE FAILED: two lists of 25 skeletons, made on two roads
  k8RowsW_full_bent   A FACT, NO TEST: with the second number of every entry of the first row's
                    «before» raised by one the comparison says no. ONCE k8RowsW_full HOLDS THIS
                    BEND COULD NEVER BE ACCEPTED: it shows that the first row's «before» is not
                    empty, and no more
  k8_lotW_at        THE ROW: under K8Row.lean's four hypotheses, at every list of asked places and
                    every list of segments' numbers: lotW as ls (lotSk G (ProofFile.P1K8.lot Z)) = lot6
The second import is the file of the written data (Johnson/Desc/ProofFile/Law/Skel/Full/Data.lean).
LIMITS. NEITHER LIST IS AN INDEPENDENT WITNESS: both come off the very code that they describe (the
one off a print of the flat list's rows, the other off a print of the lots' blocks). That the two
agree shows no hypothesis of the row met. THE FOUR HYPOTHESES STAY OWED. On hn see K8Row.lean's
head: at attention a link without a family passes k8AsksB, so that half of hn holds idly there. hk
asks the built links' kinds whole, where k8RowOn reads of a kind only whether it is 2 (ProofFile.k8Asks,
inside hn, reads also whether it is 1). Evaluated data, synthetic weights. No soundness is claimed.

-/
import Johnson.AtFull.Desc.Lots.K8Row
import Johnson.Desc.ProofFile.Law.Skel.Full.Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8L
open VerifiableInference.Desc (Place)
open Johnson.AtFull.K4Sent (esWritten)
open Johnson.AtFull.Cut (cutWritten)
open ProofFile.Sk (Skel lotSk lotW)

set_option maxRecDepth 1000000 in
/-- **The two written lists are one.** -/
theorem k8RowsW_full : k8RowsW = ProofFile.Sk.Full.lot6Blocks := by decide +kernel

set_option maxRecDepth 1000000 in
/-- With the second number of every entry of the first row's «before» raised by one: no. A fact, no
test: given `k8RowsW_full` it says only that the first row's «before» is not empty. -/
theorem k8RowsW_full_bent :
    decide (k8RowsW = ProofFile.Sk.Full.lot6Blocks.zipIdx.map fun x =>
      if x.2 == 0 then { x.1 with before := x.1.before.map fun y => (y.1, y.2 + 1) } else x.1) =
      false := by
  decide +kernel

variable {Z : ProofFile.Pub} {G : ProofFile.Ground}

/-- **THE ROW, in the form that back_of_written asks.** -/
theorem k8_lotW_at (hc : Z.cuts = cutWritten) (he : Z.D.1.map (·.entry) = esWritten)
    (hk : G.built.toList.map (fun X => (X.kind, X.name)) = k8KindsW) (hn : k8GroundB G = true)
    (as : List Place) (ls : List Nat) :
    lotW as ls (lotSk G (ProofFile.P1K8.lot Z)) = ProofFile.Sk.Full.lot6 := by
  rw [k8_lotSk_at hc he hk hn, k8RowsW_full]
  simp [lotW, ProofFile.Sk.Full.lot6, ProofFile.Sk.Full.lot6Batch]

end P1K8L

#print axioms P1K8L.k8RowsW_full
#print axioms P1K8L.k8RowsW_full_bent
#print axioms P1K8L.k8_lotW_at
