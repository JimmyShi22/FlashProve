-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6CallsView.lean: THE TWO TESTS callsSeatedC AND maskMeetsC
(Law/K6CallsTest.lean) AS FUNCTIONS OF PLAIN VALUES. Definitions with code, and two equations, for
all parameters.

Why. The two tests read
  of the public parameters Wp: the number of the head's matrices, NHf, each label's owner and name;
  of the table's numbers N: one list (N.group 24);
  of the radii rad: NOTHING (of the caller's list they read the shapes alone);
  of the table's members msR: for each member its shape and its seat, in the list's order;
  of what the caller reads (D): the codes and the shape; and, of its lists of arrays, for each
      matrix ONE TRUTH VALUE: does the segment's list name the matrix's array at the plan's own
      number?
Written so, the tests can be evaluated at written values by Lean's kernel.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold).
  shapesCalls D i      the shapes of the caller's list.
  plainOf msR          of each member: its shape and its seat.
  sitsV, callV         the tests' parts, at plain values.
  **callsSeatedV**, **maskMeetsV**          the two tests at plain values.
  **callsSeatedC_view**, **maskMeetsC_view**   each test is its test at plain values: for all
      parameters.

No existential quantifier in these statements.
What it does not say. That either test accepts anywhere. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6CallsTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes OnBytes.Params
open Johnson.Pack (pMask)
open VerifiableInference.Desc renaming arrayOf → arrayOfD
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigList sigListCalls keptAt bornAt messagesAt)
open VerifiableInference.Desc.Sound (Mem namedOnce seatOf)
open VerifiableInference.Desc.Kinds.Head.Law.OffPad (insideB)

/-- The shapes of the caller's list. -/
def shapesCalls (D : Sent) (i : Nat) : List OracleShape := (sigListCalls D (fun _ => 0) i).map (·.1)

/-- They do not hang on the radii. -/
theorem shapes_of_calls (D : Sent) (rad : OracleShape → Nat) (i : Nat) :
    (sigListCalls D rad i).map (·.1) = shapesCalls D i := by
  unfold shapesCalls sigListCalls sigList
  simp only [List.map_append, List.map_map]
  rfl

/-- Of each member: its shape and its seat. -/
def plainOf (msR : List Mem) : List (OracleShape × (Nat × Nat)) :=
  msR.map fun y => ((y.1.l.get y.2).1, seatOf y)

section
variable (arr : Nat → Nat → Nat) (group : List (Nat × Nat)) (shs : List OracleShape)
  (seatN : Nat → Nat × Nat) (mems : List (OracleShape × (Nat × Nat)))

/-- Member k is there, ok accepts its shape, and it sits as the table has it, with the number n. -/
def sitsV (k n : Nat) (ok : OracleShape → Bool) : Bool :=
  (shs[k]?).any fun sh =>
    ok sh && group.contains (seatN k) && Decidable.decide (arr (seatN k).1 (seatN k).2 = n) &&
      (mems.find? fun y => Decidable.decide (y.2 = seatN k)).any fun y =>
        Decidable.decide (sh = y.1)

end

theorem sitsC_view (arr : Nat → Nat → Nat) (msR : List Mem) (N : Numbers) (D : Sent)
    (rad : OracleShape → Nat) (i : Nat) (seatN : Nat → Nat × Nat) (k n : Nat)
    (ok : OracleShape → Bool) :
    sitsC arr msR N D rad i seatN k n ok =
      sitsV arr (N.group 24) (shapesCalls D i) seatN (plainOf msR) k n ok := by
  unfold sitsC sitsV plainOf
  rw [← shapes_of_calls D rad i, List.getElem?_map, List.find?_map]
  cases (sigListCalls D rad i)[k]? with
  | none => rfl
  | some e =>
    cases hf : (msR.find? fun y => Decidable.decide (seatOf y = seatN k)) with
    | none =>
      simp only [Option.map_some, Option.any_some, Function.comp_def, hf, Option.map_none,
        Option.any_none]
    | some y =>
      simp only [Option.map_some, Option.any_some, Function.comp_def, hf]

section
variable (arr : Nat → Nat → Nat) (group : List (Nat × Nat)) (lay : ReqLayout)
  (num : Nat → Nat → Nat) (D : Sent) (i : Nat) (seatN : Nat → Nat × Nat)
  (mems : List (OracleShape × (Nat × Nat)))

/-- The test at a matrix whose label has the owner and name ow. nm: does the segment's list of
arrays name that array at the plan's own number? -/
def callV (ow : Nat × String) (nm : Bool) : Bool :=
  match arrayOfD lay ow.1 ow.2 with
  | none => true
  | some A =>
    nm && (memberOf D i ow.1 A.message).any fun k =>
      sitsV arr group (shapesCalls D i) seatN mems k (num ow.1 A.message) fun s =>
        insideB D.codes s A

/-- **The first test at plain values.** -/
def callsSeatedV (NM NHf : Nat) (ows : Nat → Nat × String) (nms : Nat → Bool) : Bool :=
  (List.range NM).all fun a =>
    Decidable.decide (NHf + 3 < a) || callV arr group lay num D i seatN mems (ows a) (nms a)

/-- **The second test at plain values.** -/
def maskMeetsV (n ns : Nat) : Bool :=
  ((messagesAt D i).findIdx? fun z => z.shape.maskRows != 0).any fun m0 =>
    ((group.filter fun x => arr x.1 x.2 == n).length == 1) &&
      sitsV arr group (shapesCalls D i) seatN mems ((keptAt D i).length + m0) n fun s =>
        Decidable.decide (0 < s.maskRows) &&
          (ns == 0 || Decidable.decide (ns - 1 < (pMask D.codes s).ell))

end

/-- **The first test is its test at plain values.** -/
theorem callsSeatedC_view (arr : Nat → Nat → Nat) (msR : List Mem) (N : Numbers)
    (Wp : OnBytes.Model.Verify.Public) (lay : ReqLayout) (num : Nat → Nat → Nat) (D : Sent)
    (rad : OracleShape → Nat) (i : Nat) (seatN : Nat → Nat × Nat) :
    callsSeatedC arr msR N Wp lay num D rad i seatN =
      callsSeatedV arr (N.group 24) lay num D i seatN (plainOf msR) (Meaning.sizesOf Wp 24).NM
        Wp.hS.NHf
        (fun a => (Meaning.ownerK (Meaning.labAt Wp 24 a),
          Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 a))))
        (fun a => (D.arrayOf.getD i #[])[(Meaning.tlAt Wp 24).gtTree.getD a 0]? ==
          some (Meaning.ownerK (Meaning.labAt Wp 24 a),
            Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 a)))) := by
  unfold callsSeatedC callsSeatedV callC callV
  simp only [sitsC_view]
  rfl

/-- **The second test is its test at plain values.** -/
theorem maskMeetsC_view (arr : Nat → Nat → Nat) (msR : List Mem) (N : Numbers) (D : Sent)
    (rad : OracleShape → Nat) (i : Nat) (seatN : Nat → Nat × Nat) (n ns : Nat) :
    maskMeetsC arr msR N D rad i seatN n ns =
      maskMeetsV arr (N.group 24) D i seatN (plainOf msR) n ns := by
  unfold maskMeetsC maskMeetsV namedOnce
  simp only [sitsC_view]

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.callsSeatedC_view
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.maskMeetsC_view
