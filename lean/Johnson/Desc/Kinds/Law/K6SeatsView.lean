-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6SeatsView.lean: THE TEST seatsK6C (Law/K6SeatsTest.lean) AS A FUNCTION OF
PLAIN VALUES: numbers, lists, the layout, the shape and the codes: no public parameters Wp, no
table's numbers N, no structure of the plan's side dS. One definition with code, and one equation,
for all parameters.

Why. seatsK6C reads of Wp four things alone (the number of the head's matrices, NHf, each label's
owner and name, the number of the array of the reads); of N one list (N.sent 24 0); of dS, where it
is FillSent.sentDataOf shape base trees, what the shape and ONE NUMBER (base 24) give; of the list
of arrays one entry. Written so, the test can be evaluated at written values by Lean's kernel.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold).
  matSeatV, maskSeatV   the two parts, at plain values. d: a structure of the plan's side, kept as a
      parameter of these two alone.
  **seatsK6V**          the test at plain values.
  **seatsK6C_view**     seatsK6C ... = seatsK6V ..., for all parameters: by unfolding.

No existential quantifier in these statements.
What it does not say. That the test accepts anywhere. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6SeatsTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes OnBytes.Params
open VerifiableInference.Desc renaming arrayOf → arrayOfD
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.FillSent (SentData sentDataOf whereIsP maskP TreeLook)

section
variable (arr : Nat → Nat → Nat) (sent0 : List (Nat × Nat)) (lay6 : ReqLayout)
  (num : Nat → Nat → Nat) (cs : OnBytes.Codes) (d : SentData) (places : List (Nat × Nat))
  (M : List OracleShape) (n0 : Nat)

/-- The test at a matrix whose label has the owner and name ow. -/
def matSeatV (ow : Nat × String) : Bool :=
  match arrayOfD lay6 ow.1 ow.2 with
  | none => true
  | some A =>
    (whereIsP d 24 ow.1 A.message).any fun o =>
      (M[o]?).any fun sh =>
        laidMatrixOk A (K9.rowBitsOf sh .main) (K9.placeBitsOf cs sh .main) &&
          seatC arr sent0 places n0 o (num ow.1 A.message)

/-- The test at the segment's mask row. -/
def maskSeatV (n rb : Nat) (shape : ReqShape) : Bool :=
  (maskP shape d 24).any fun o =>
    (M[o]?).any fun sh => K9.rowBitsOf sh .mask == rb && seatC arr sent0 places n0 o n

end

/-- **The test at plain values.** base: how many oracle messages are sent in front of segment 24's
first sending. a0: the entry of the segment's list of arrays at the number of the reads' array. -/
def seatsK6V (cs : OnBytes.Codes) (lay6 : ReqLayout) (shape : ReqShape) (NM NHf : Nat)
    (ows : Nat → Nat × String) (arr num : Nat → Nat → Nat) (sent0 places : List (Nat × Nat))
    (M : List OracleShape) (base n0 n rb : Nat) (a0 : Option (Nat × String)) : Bool :=
  ((List.range NM).all fun a =>
      Decidable.decide (NHf + 3 < a) ||
        matSeatV arr sent0 lay6 num cs (sentDataOf shape (fun _ => base) fun _ => []) places M n0
          (ows a)) &&
    maskSeatV arr sent0 (sentDataOf shape (fun _ => base) fun _ => []) places M n0 n rb shape &&
    a0.any (secondC lay6 shape)

/-- The plan's term for "where is" reads of the structure three fields at the segment. -/
theorem whereIsP_same {d d' : SentData} {m : Nat} (h1 : d'.born m = d.born m)
    (h2 : d'.own m = d.own m) (h3 : d'.kept m = d.kept m) (b k : Nat) :
    whereIsP d' m b k = whereIsP d m b k := by
  unfold whereIsP
  rw [h1, h2, h3]

/-- **The test is the test at plain values.** -/
theorem seatsK6C_view (arr : Nat → Nat → Nat) (N : Numbers) (Wp : OnBytes.Model.Verify.Public)
    (lay6 : ReqLayout) (num : Nat → Nat → Nat) (n rb : Nat) (cs : OnBytes.Codes) (shape : ReqShape)
    (base : Nat → Nat) (trees : Nat → List TreeLook) (Lp : K12.Door.Laid) (M : List OracleShape)
    (arrs : Array (Nat × String)) (n0 : Nat) :
    seatsK6C arr N Wp lay6 num n rb cs shape (sentDataOf shape base trees) Lp M arrs n0 =
      seatsK6V cs lay6 shape (Meaning.sizesOf Wp 24).NM Wp.hS.NHf
        (fun a => (Meaning.ownerK (Meaning.labAt Wp 24 a),
          Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 a))))
        arr num (N.sent 24 0) Lp.places M (base 24) n0 n rb arrs[readsOf Wp]? := by
  have hw : ∀ b k, whereIsP (sentDataOf shape (fun _ => base 24) fun _ => []) 24 b k =
      whereIsP (sentDataOf shape base trees) 24 b k :=
    fun b k => whereIsP_same rfl rfl rfl b k
  unfold seatsK6C seatsK6V readsC maskSeatC maskSeatV matSeatC matSeatV maskP
  simp only [hw]
  rfl

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.seatsK6C_view
