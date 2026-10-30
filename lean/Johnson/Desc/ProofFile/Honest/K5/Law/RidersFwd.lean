-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RidersFwd.lean: which items ride past an attention segment's
own rounds, said of the first chain's table READ FORWARD (fwdOpen,
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean; rows,
Johnson/Desc/ProofFile/Honest/Thread/FirstRows.lean), at the full size's written lists and at each
of the twelve borders in front of these rounds. Statements with their proofs on written lists: no
prover and no verifier is in this file.

Main names:
  tableRow, row_full   the forward row at the border is made of the table's row at the
                  kind's place: it
                  shuts what that row closes, and owes what that row opens and what it reads
  riders_fwd      **an item that is open at the border, and that the forward row neither shuts nor
                  owes, is "no mark" or one of the five sorts of riders** (riderB,
                  Johnson/Desc/First/Att/K05Riders.lean)
  noDigitsB, noDigits_closed, noDigits_bite   a test with code on the written lists: at none of the
                  twelve borders the part "every digit lies in the digits' table" of any segment is
                  open; it says yes; a control on the inner test: over all borders of the chain it
                  says no
  riders_no_digits   **no item that is open at the border is that part**
  riders_thrAt, no_digits_thrAt   the two at the first chain's `Thread` at the library's own letters

How. riders_fwd makes no new decision: it is the library's own decided test on the table's open set
(riders_full, Johnson/Desc/First/Att/Door/Law/K5ListsFull.lean) behind the equation of the forward
open set with the table's (opened_full, Johnson/Desc/ProofFile/Honest/K5/Law/Opened.lean).
noDigits_closed is one closed decision by the kernel.
All are CONDITIONAL on: the group's number is below 12. DECIDED AT THE TABLE'S TEXT AS IT STANDS: at
another text the file compiles again or it does not.
Limits. Lists alone: nothing on what an item says. Nothing at another list of segments.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Opened

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Place Strs Chain)
open VerifiableInference.Desc.First (ModelPart Item BlockRow start openSets)
open VerifiableInference.Desc.First.Att.P (riderB ridersB)
open VerifiableInference.Desc.Sound (insL rowQ)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

/-- The table's row at the kind's place. The full name: the frame has a function of its own under
the short one. -/
def tableRow (g : Nat) : BlockRow :=
  VerifiableInference.Desc.First.rowOf P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩

/-- **The forward row at the border is made of the table's row at the kind's place.** -/
theorem row_full {g : Nat} (hg : g < 12) :
    FirstRows.rows P5J.At.links P5J.At.ps (borderOf g) =
      FwdRow.of (tableRow g).ins (tableRow g).outs (tableRow g).ctx := by
  have hpl : P5J.At.ps[borderOf g]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ := H2K5.Door.place_full hg
  unfold FirstRows.rows
  rw [hpl]
  rfl

/-- **Which items ride.** -/
theorem riders_fwd {g : Nat} (hg : g < 12) (i : Item)
    (ho : i ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) (borderOf g))
    (hs : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (borderOf g)).shuts)
    (hw : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (borderOf g)).owes) :
    i = .unmarked ∨ riderB (2 * g + 1) i = true := by
  rw [opened_full hg] at ho
  rw [row_full hg] at hs hw
  have hpl : P5J.At.ps[borderOf g]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ := H2K5.Door.place_full hg
  have hq : rowQ P5J.At.links P5J.At.ps (borderOf g) = tableRow g := by
    unfold rowQ
    rw [hpl]
    rfl
  have hr : ridersB P5J.At.links P5J.At.ps (borderOf g) (2 * g + 1) = true :=
    H2K5.Door.riders_full hg
  unfold ridersB at hr
  have h1 := List.all_eq_true.1 hr i ho
  rcases Bool.or_eq_true _ _ ▸ h1 with h1 | h1
  · have h2 : i ∈ insL P5J.At.links P5J.At.ps (borderOf g) := List.contains_iff_mem.1 h1
    unfold insL at h2
    rw [hq, List.mem_append, List.mem_append, List.mem_singleton] at h2
    rcases h2 with (h2 | h2) | h2
    · exact absurd h2 hs
    · exact absurd (List.mem_append_right _ h2) hw
    · exact .inl h2
  · exact .inr h1

/-- The part "every digit lies in the digits' table" of some segment. -/
def isDigits : Item → Bool
  | .constr _ .lookDigits => true
  | _ => false

/-- A test with code on the written lists: at none of the twelve borders that part is open. -/
def noDigitsB : Bool :=
  (List.range 12).all fun g =>
    (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?).getD []).all fun i =>
      !isDigits i

set_option maxRecDepth 1000000 in
/-- **The test says yes.** No premise: a closed fact, by the kernel. -/
theorem noDigits_closed : noDigitsB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: some border of the chain has that part open: there the same test on one open set says
no. No premise: a closed fact, by the kernel. -/
theorem noDigits_bite :
    ((openSets P5J.At.links P5J.At.ps (start P5J.At.links)).all fun O => O.all fun i =>
      !isDigits i) = false := by
  decide +kernel

/-- **No item that is open at the border is the digits' part.** -/
theorem riders_no_digits {g : Nat} (hg : g < 12) (i : Item)
    (ho : i ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) (borderOf g))
    (n : Nat) : i ≠ .constr n .lookDigits := by
  rw [opened_full hg] at ho
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 noDigits_closed g (List.mem_range.2 hg)) i ho
  rintro rfl
  exact nomatch h1

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **Which items ride, at the first chain's `Thread` at the library's own letters.** -/
theorem riders_thrAt {g : Nat} (hg : g < 12) (i : Item)
    (ho : i ∈ (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).opened
      (borderOf g))
    (h1 : i ∉ ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).row
      (borderOf g)).shuts)
    (h2 : i ∉ ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).row
      (borderOf g)).owes) :
    i = .unmarked ∨ riderB (2 * g + 1) i = true :=
  riders_fwd hg i ho h1 h2

/-- **No item that is open there is the digits' part.** -/
theorem no_digits_thrAt {g : Nat} (hg : g < 12) (i : Item)
    (ho : i ∈ (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).opened
      (borderOf g)) (n : Nat) : i ≠ .constr n .lookDigits :=
  riders_no_digits hg i ho n

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.row_full
#print axioms ProofFile.Honest.K5.riders_fwd
#print axioms ProofFile.Honest.K5.noDigits_closed
#print axioms ProofFile.Honest.K5.noDigits_bite
#print axioms ProofFile.Honest.K5.riders_no_digits
#print axioms ProofFile.Honest.K5.riders_thrAt
#print axioms ProofFile.Honest.K5.no_digits_thrAt
