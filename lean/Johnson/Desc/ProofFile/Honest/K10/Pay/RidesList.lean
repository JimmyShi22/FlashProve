-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/RidesList.lean: which items ride past the closing of a segment: the items that are open in front of it and that its
row of the first chain's table, read forward, neither shuts nor owes. A test on the written lists, by Lean's kernel.

  `riderK`            the six sorts: "no mark" · the weights' pin · the index masks' pin · the pile · "what the own rounds
                     leave for the row on the weights" · a part of a segment's relation that is not the digits' part
  `ridersK10B`, `ridersK10_closed`   the test at the 25 borders 14 l + `IM.nAt l` + 5, and that it says yes
  `ridersK10_bite`    a control: without the fifth sort the test says no
  `placeK10B`, `placeK10_closed`, `place_at_closing`   the place at each of these borders is of the kind K10
  `riders_at_closing`   so: every rider is of one of the six sorts

Limits. Lists alone: nothing on what an item says. Decided at the table's text as it stands, at the full size's list of
segments.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Opened
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First (Item start)
open ProofFile.Honest.FirstRows (rows opens)

/-- The six sorts of item that ride past a closing. -/
def riderK : Item → Bool
  | .unmarked | .pinW | .pinI | .pile | .wo _ => true
  | .constr _ p => !(p == .lookDigits)
  | _ => false

/-- The test at one list of sorts: at each of the 25 borders in front of a closing, every open item
is shut by the closing's row, or owed by it, or of one of the sorts. -/
def ridersBy (f : Item → Bool) : Bool :=
  (List.range 25).all fun l =>
    (((opens P5J.At.links P5J.At.ps (start P5J.At.links))[14 * l + IM.nAt l + 5]?).getD []).all
      fun i =>
        (rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 5)).shuts.contains i ||
          (rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 5)).owes.contains i || f i

def ridersK10B : Bool := ridersBy riderK

set_option maxRecDepth 1000000 in
/-- **The test says yes.** A closed fact, by the kernel. -/
theorem ridersK10_closed : ridersK10B = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: without the sort "what the own rounds leave for the row on the weights" it says no. -/
theorem ridersK10_bite :
    ridersBy (fun i => riderK i && match i with | .wo _ => false | _ => true) = false := by
  decide +kernel

/-- The place at each of the 25 borders is of the kind K10. -/
def placeK10B : Bool :=
  (List.range 25).all fun l =>
    (P5J.At.ps[14 * l + IM.nAt l + 5]?).any fun p => p.kind == KindName.K10

set_option maxRecDepth 1000000 in
theorem placeK10_closed : placeK10B = true := by decide +kernel

theorem place_at_closing {l : Nat} (hl : l < 25) :
    ∃ p, P5J.At.ps[14 * l + IM.nAt l + 5]? = some p ∧ p.kind = KindName.K10 := by
  have t := List.all_eq_true.1 placeK10_closed l (List.mem_range.2 hl)
  cases hp : P5J.At.ps[14 * l + IM.nAt l + 5]? with
  | none =>
    rw [hp] at t
    simp at t
  | some p =>
    rw [hp] at t
    simp only [Option.any_some, beq_iff_eq] at t
    exact ⟨p, rfl, t⟩

/-- **Every rider is of one of the six sorts.** -/
theorem riders_at_closing {l : Nat} (hl : l < 25) (i : Item)
    (ho : i ∈ fwdOpen (start P5J.At.links) (rows P5J.At.links P5J.At.ps) (14 * l + IM.nAt l + 5))
    (hs : i ∉ (rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 5)).shuts)
    (hw : i ∉ (rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 5)).owes) : riderK i = true := by
  obtain ⟨p, hp, -⟩ := place_at_closing hl
  have hle : 14 * l + IM.nAt l + 5 ≤ P5J.At.ps.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hp).1
  have t := List.all_eq_true.1 ridersK10_closed l (List.mem_range.2 hl)
  rw [ProofFile.Honest.K5.opens_get _ _ _ _ hle] at t
  have t1 := List.all_eq_true.1 t i ho
  rcases Eq.mp (Bool.or_eq_true _ _) t1 with t2 | t2
  · rcases Eq.mp (Bool.or_eq_true _ _) t2 with t3 | t3
    · exact absurd (List.contains_iff_mem.1 t3) hs
    · exact absurd (List.contains_iff_mem.1 t3) hw
  · exact t2

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.ridersK10_closed
#print axioms ProofFile.Honest.K10.ridersK10_bite
#print axioms ProofFile.Honest.K10.placeK10_closed
#print axioms ProofFile.Honest.K10.place_at_closing
#print axioms ProofFile.Honest.K10.riders_at_closing
