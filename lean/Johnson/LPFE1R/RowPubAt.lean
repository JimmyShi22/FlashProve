-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/RowPubAt.lean: THE FIVE PUBLIC EQUATIONS ON THE TYPED ROW OF THE
CODE SWITCH THAT CLOSES "carry m" (`ProofFile.rowAtK2`, Johnson/Desc/ProofFile/CarryAt.lean), WHICH THE
CLOSING KIND K10's PREMISE ON THE CARRIED CLAIM TAKES (hr): the row's codes are the written ones ·
its list is link m's written list · its group in front is a named member of the written groups · the
flags "kept" of the written request are just the row's kept places · its radius is at most the
written one. A test with code, its law, the test at the written table by Lean's kernel, and the
premise's own text from another file's named test. A law file; no running text imports it.
  `loAt m`, `kbW m`, `gsAt m`   THE TERMS: link m's written list (Johnson.G.linksFullLit) · the
                    written request's flags at it (kbAt shapeFull m,
                    Johnson/Desc/First/Close/Law/ReqKept.lean) · the group in front that the written
                    table's row m bears.
  `rowPubB r m`       THE TEST, on a row. `rowPub_of_B`: its yes gives the five.
  `lit_pub`           BY THE KERNEL: the test says yes at row m of the written table
                    (tableFullLit), at all 25.
  `gsAt_front`        BY THE KERNEL: gsAt m is one of the written groups in front, and its k is the
                    layout's k at the list and the flags: so it can stand where a group was had
                    under "there is".
  `lo_lengths`        BY THE KERNEL: the written lists' lengths: 6 at m = 0 (the index masks'
                    message is among them).
  `rowPubB_kept`, `rowPubB_rad`, `rowPubB_lo`, `rowPubB_g`   THE TEST CAN SAY NO: by the kernel.
  `hr_of_row`         rowAtK2 pol lay KL m = tableFullLit[m]? ⊢ the premise's text.
  `hr_of_test`        the code switch's files' named test accepts (tableWrittenB,
                    Johnson/Top/H0/K2Caller/TableWritten.lean) ⊢ the premise's text, at every m.

Limits. tableWrittenB IS A NAMED TEST THAT THE VERIFIER DOES NOT RUN; it is evaluated at no files
here. The full size alone. Nothing on soundness or on hiding.
-/
import Johnson.Top.H0.K2Caller.TableWritten
import Johnson.Desc.First.Close.Law.ReqKept
import Johnson.G.BatAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params Johnson.G
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.First.Close (kbAt kLay)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit tableWrittenB tableWritten_says)

/-- Link m's written list. -/
def loAt (m : ℕ) : List (OracleShape × ℕ) := linksFullLit.getD m []

/-- The written request's flags at it. -/
def kbW (m : ℕ) : Fin (loAt m).length → Bool := kbAt shapeFull m (loAt m)

/-- The group in front that the written table's row m bears. -/
def gsAt (m : ℕ) : GroupSize := ((tableFullLit[m]?).map (·.g)).getD default

/-- **THE TEST.** -/
def rowPubB (r : SwRow) (m : ℕ) : Bool :=
  decide (r.cs = codesFull2) && decide (r.lo = loAt m) && decide (r.g = gsAt m) &&
    (List.finRange (loAt m).length).all (fun i => kbW m i == decide (i.val ∈ r.kept)) &&
    decide (r.rad ≤ radFull)

/-- **Its yes gives the five.** -/
theorem rowPub_of_B {r : SwRow} {m : ℕ} (h : rowPubB r m = true) :
    r.cs = codesFull2 ∧ r.lo = loAt m ∧ r.g = gsAt m ∧
      (∀ i : Fin (loAt m).length, kbW m i = true ↔ i.val ∈ r.kept) ∧ r.rad ≤ radFull := by
  unfold rowPubB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  refine ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, fun i => ?_, h.2⟩
  rw [h.1.2 i (List.mem_finRange i), decide_eq_true_eq]

set_option maxRecDepth 1000000 in
/-- **At the written table, at all 25.** -/
theorem lit_pub : (List.range 25).all (fun m => (tableFullLit[m]?).any fun r => rowPubB r m) =
    true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The named group is one of the written groups in front, with the layout's k. -/
theorem gsAt_front : (List.range 25).all (fun m => decide (gsAt m ∈ frontFull) &&
    decide ((gsAt m).k = kLay (loAt m) (kbW m))) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- How many messages each written list has. AT m = 0 SIX: the index masks' message is among them.
-/
theorem lo_lengths : (List.range 25).map (fun m => (loAt m).length) =
    6 :: (List.replicate 11 [6, 7]).flatten ++ [6, 5] := by decide +kernel

/-! ## The test can say no: each control turns ONE field of the written table's row 2 -/

set_option maxRecDepth 1000000 in
theorem rowPubB_kept : (tableFullLit[2]?).any (fun r => rowPubB { r with kept := [3] } 2) =
    false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rowPubB_rad : (tableFullLit[2]?).any (fun r => rowPubB { r with rad := radFull + 1 } 2) =
    false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rowPubB_lo : (tableFullLit[2]?).any (fun r => rowPubB { r with lo := loAt 1 } 2) =
    false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rowPubB_g : (tableFullLit[2]?).any (fun r => rowPubB { r with g := gsAt 1 } 2) = false := by
  decide +kernel

/-! ## The premise's own text -/

/-- From "the row is the written table's". -/
theorem hr_of_row {pol lay KL : ByteArray} {m : ℕ}
    (h : ProofFile.rowAtK2 pol lay KL m = tableFullLit[m]?) :
    ∀ r, ProofFile.rowAtK2 pol lay KL m = some r → r.cs = codesFull2 ∧ r.lo = loAt m ∧ r.g = gsAt m ∧
      (∀ i : Fin (loAt m).length, kbW m i = true ↔ i.val ∈ r.kept) ∧ r.rad ≤ radFull := by
  intro r hr
  rw [h] at hr
  have hm : m < 25 := by
    have := (List.getElem?_eq_some_iff.1 hr).1
    simpa [tableFullLit] using this
  have hB := List.all_eq_true.1 lit_pub m (List.mem_range.2 hm)
  rw [hr] at hB
  exact rowPub_of_B hB

/-- **From the code switch's files' named test.** -/
theorem hr_of_test {pol lay KL : ByteArray} (h : tableWrittenB pol lay KL = true) (m : ℕ) :
    ∀ r, ProofFile.rowAtK2 pol lay KL m = some r → r.cs = codesFull2 ∧ r.lo = loAt m ∧ r.g = gsAt m ∧
      (∀ i : Fin (loAt m).length, kbW m i = true ↔ i.val ∈ r.kept) ∧ r.rad ≤ radFull :=
  hr_of_row (tableWritten_says h m)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rowPub_of_B
#print axioms VerifiableInference.Desc.LinkJoin.lit_pub
#print axioms VerifiableInference.Desc.LinkJoin.gsAt_front
#print axioms VerifiableInference.Desc.LinkJoin.lo_lengths
#print axioms VerifiableInference.Desc.LinkJoin.rowPubB_kept
#print axioms VerifiableInference.Desc.LinkJoin.rowPubB_rad
#print axioms VerifiableInference.Desc.LinkJoin.rowPubB_lo
#print axioms VerifiableInference.Desc.LinkJoin.rowPubB_g
#print axioms VerifiableInference.Desc.LinkJoin.hr_of_row
#print axioms VerifiableInference.Desc.LinkJoin.hr_of_test
