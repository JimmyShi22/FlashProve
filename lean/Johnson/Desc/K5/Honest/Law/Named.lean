-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Named.lean: the row of parts into which the honest side of an attention
segment's own rounds is cut (`shapes`, Johnson/Desc/K5/Honest/Faces.lean), WRITTEN OUT: the list
itself, each part by its number and name, and the cut by number: at every set of the planner's
numbers. Definitions with code, and statements with their proofs. No premise but where one is named.

  `productsShape`, `unitsShapes`, `keyVars`, `tailShapes`, `leadBehind`   the written list's terms
  `shapesOf_scalars`, `shapesOf_units`, `shapesOf_tail`, `shapes_eq`   **the row is the
      softmax-table units' parts and eleven more**, each with its call as data: how many scalars
      ride in front, each variable's way of summing and its number of coefficients, the ends
  `shape_unit`, `shape_tail`, `shape_iSE` .. `shape_iHB`, `shapes_length`   each part by its number:
      the names `iSE` .. `iHB` of Faces.lean stand at the parts that they name
  `leadBehind_zero`   the corner, see below
  `cut_of_shape`, `productsShape_rounds`, `cut_unit`, `cut_iSE` .. `cut_iSD`   a part's number of
      rounds; the numbers of variables as the summands' files read them off the cut

The corner. Where the planner's numbers have no softmax-table unit, the remainder units' values
wait on, and ride in front of the part for the denominator times the output: `leadBehind`. The
verifier's test on the plan refuses such numbers (`planOk`, Johnson/Desc/First/Att/K5AttentionKind.lean, its
first clause). The list is stated at all numbers, with that term; `leadBehind_zero` strikes it.

Limits. Public numbers alone: no run, no coin and no value is in these facts.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Faces
import Johnson.Desc.First.Att.K5Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open VerifiableInference.Desc.Part.MaskedSum (Var Call)
open VerifiableInference.Desc.First.Att.P (Stage products script keyStage tailStages script_eq)

/-! ## 1 The row, written out -/

/-- A sumcheck of products of two maps, as a part: lead scalars in front, n variables, m pairs. -/
def productsShape (lead n m : Nat) : PartShape :=
  .sum ⟨lead, List.replicate n (.plain 4), some ⟨2, 2 * m⟩⟩

/-- The softmax-table units' parts. lead: the scalars that wait in front of the first. -/
def unitsShapes : Nat → List (Nat × Nat) → List PartShape
  | _, [] => []
  | lead, u :: us => productsShape (lead + 7) u.1 u.2 :: unitsShapes 0 us

/-- The variables of the sumcheck for the key at the index. -/
def keyVars (x : OnBytes.Params.AttentionRounds) : List Var :=
  (List.replicate x.lt 3 ++ List.replicate x.lgk (x.lt + 3) ++ List.replicate x.lt (x.lt + 2)).map
    .plain

/-- The eleven parts behind the units. lead: the scalars that wait in front of the first. -/
def tailShapes (x : OnBytes.Params.AttentionRounds) (lead : Nat) : List PartShape :=
  [productsShape (lead + 5 + x.lt + 2) x.e x.pairs, .one 0, productsShape 2 x.valueM x.pairs,
    productsShape 0 x.valueD x.pairs, .one 0, .one x.pairs, productsShape 0 x.attained x.pairs,
    .one 0, .sum ⟨0, keyVars x, some ⟨x.lt + 1, x.Lam + x.pairs * x.lt⟩⟩, .one 0,
    productsShape 0 x.bits x.pairs]

/-- The scalars that wait in front of the part for the denominator times the output, beside its
own: none where there is a softmax-table unit; else the remainder units' values. -/
def leadBehind (x : OnBytes.Params.AttentionRounds) : Nat :=
  if x.score.isEmpty then x.planeMessages * 3 else 0

theorem shapesOf_scalars (n : Nat) (rest : List Stage) : ∀ (k lead : Nat),
    shapesOf lead (List.replicate k (.scalars n) ++ rest) = shapesOf (lead + k * n) rest
  | 0, lead => by
    rw [Nat.zero_mul]
    rfl
  | k + 1, lead => by
    show shapesOf (lead + n) (List.replicate k (.scalars n) ++ rest) = _
    rw [shapesOf_scalars n rest k (lead + n), Nat.succ_mul, Nat.add_assoc, Nat.add_comm n]

theorem shapesOf_units (rest : List Stage) : ∀ (us : List (Nat × Nat)) (lead : Nat),
    shapesOf lead ((us.flatMap fun u => [.scalars 7, products u.1 u.2]) ++ rest) =
      unitsShapes lead us ++ shapesOf (if us.isEmpty then lead else 0) rest
  | [], _ => rfl
  | u :: us, lead => by
    show productsShape (lead + 7) u.1 u.2 ::
      shapesOf 0 ((us.flatMap fun u => [.scalars 7, products u.1 u.2]) ++ rest) = _
    rw [shapesOf_units rest us 0, ite_self]
    rfl

theorem shapesOf_tail (x : OnBytes.Params.AttentionRounds) (lead : Nat) :
    shapesOf lead (tailStages x) = tailShapes x lead := by
  show [_, _, _, _, _, PartShape.one (0 + x.pairs), _, _, _, _, _] = _
  rw [Nat.zero_add x.pairs]
  rfl

/-- **THE ROW, WRITTEN OUT**, at every set of the planner's numbers. No premise. -/
theorem shapes_eq (x : OnBytes.Params.AttentionRounds) :
    shapes x = unitsShapes (x.planeMessages * 3) x.score ++ tailShapes x (leadBehind x) := by
  unfold shapes
  rw [script_eq, shapesOf_scalars, shapesOf_units, Nat.zero_add, shapesOf_tail]
  rfl

theorem unitsShapes_length : ∀ (us : List (Nat × Nat)) (lead : Nat),
    (unitsShapes lead us).length = us.length
  | [], _ => rfl
  | _ :: us, _ => congrArg (· + 1) (unitsShapes_length us 0)

theorem unitsShapes_get : ∀ (us : List (Nat × Nat)) (lead i : Nat) (u : Nat × Nat),
    us[i]? = some u →
    (unitsShapes lead us)[i]? = some (productsShape ((if i = 0 then lead else 0) + 7) u.1 u.2)
  | [], _, _, _, h => by cases h
  | _ :: _, _, 0, _, h => by
    cases h
    rfl
  | _ :: us, _, i + 1, u, h => by
    show (unitsShapes 0 us)[i]? = _
    rw [unitsShapes_get us 0 i u h, ite_self, if_neg (Nat.succ_ne_zero i)]

/-! ## 2 Each part by its number -/

/-- The part of the softmax-table unit number i. In front of the first ride the remainder units'
values. -/
theorem shape_unit (x : OnBytes.Params.AttentionRounds) (i : Nat) (u : Nat × Nat)
    (h : x.score[i]? = some u) :
    (shapes x)[i]? =
      some (productsShape ((if i = 0 then x.planeMessages * 3 else 0) + 7) u.1 u.2) := by
  have hi : i < (unitsShapes (x.planeMessages * 3) x.score).length := by
    rw [unitsShapes_length]
    exact (List.getElem?_eq_some_iff.1 h).1
  rw [shapes_eq, List.getElem?_append_left hi]
  exact unitsShapes_get _ _ i u h

/-- The part number j behind the units. -/
theorem shape_tail (x : OnBytes.Params.AttentionRounds) (j : Nat) :
    (shapes x)[x.score.length + j]? = (tailShapes x (leadBehind x))[j]? := by
  rw [shapes_eq,
    List.getElem?_append_right (by rw [unitsShapes_length]; exact Nat.le_add_right _ _),
    unitsShapes_length, Nat.add_sub_cancel_left]

theorem shape_iSE (x : OnBytes.Params.AttentionRounds) :
    (shapes x)[iSE x]? = some (productsShape (leadBehind x + 5 + x.lt + 2) x.e x.pairs) :=
  shape_tail x 0
theorem shape_iGam (x : OnBytes.Params.AttentionRounds) : (shapes x)[iGam x]? = some (.one 0) :=
  shape_tail x 1
theorem shape_iVM (x : OnBytes.Params.AttentionRounds) :
    (shapes x)[iVM x]? = some (productsShape 2 x.valueM x.pairs) := shape_tail x 2
theorem shape_iVD (x : OnBytes.Params.AttentionRounds) :
    (shapes x)[iVD x]? = some (productsShape 0 x.valueD x.pairs) := shape_tail x 3
theorem shape_iZero (x : OnBytes.Params.AttentionRounds) : (shapes x)[iZero x]? = some (.one 0) :=
  shape_tail x 4
theorem shape_iM6 (x : OnBytes.Params.AttentionRounds) :
    (shapes x)[iM6 x]? = some (.one x.pairs) := shape_tail x 5
theorem shape_iSF (x : OnBytes.Params.AttentionRounds) :
    (shapes x)[iSF x]? = some (productsShape 0 x.attained x.pairs) := shape_tail x 6
theorem shape_iOm4 (x : OnBytes.Params.AttentionRounds) : (shapes x)[iOm4 x]? = some (.one 0) :=
  shape_tail x 7
theorem shape_iSD (x : OnBytes.Params.AttentionRounds) :
    (shapes x)[iSD x]? =
      some (.sum ⟨0, keyVars x, some ⟨x.lt + 1, x.Lam + x.pairs * x.lt⟩⟩) := shape_tail x 8
theorem shape_iOm5 (x : OnBytes.Params.AttentionRounds) : (shapes x)[iOm5 x]? = some (.one 0) :=
  shape_tail x 9
theorem shape_iHB (x : OnBytes.Params.AttentionRounds) :
    (shapes x)[iHB x]? = some (productsShape 0 x.bits x.pairs) := shape_tail x 10

/-- The row has the units' parts and eleven more. -/
theorem shapes_length (x : OnBytes.Params.AttentionRounds) :
    (shapes x).length = x.score.length + 11 := by
  rw [shapes_eq, List.length_append, unitsShapes_length]
  rfl

/-- Where there is a softmax-table unit, nothing but its own scalars rides in front of the part for
the denominator times the output. The verifier's test on the plan asks that there is one. -/
theorem leadBehind_zero (x : OnBytes.Params.AttentionRounds) (h : x.score.isEmpty = false) :
    leadBehind x = 0 := by
  unfold leadBehind
  rw [h]
  rfl

/-! ## 3 The cut by number -/

/-- A part's number of rounds in the cut. -/
theorem cut_of_shape (x : OnBytes.Params.AttentionRounds) (q d : Nat) (s : PartShape)
    (h : (shapes x)[q]? = some s) : (cut x).getD q d = s.rounds := by
  unfold cut
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  rfl

theorem productsShape_rounds (lead n m : Nat) : (productsShape lead n m).rounds = n + 3 := by
  show (List.replicate n (Var.plain 4)).length + 3 = _
  rw [List.length_replicate]

/-- The numbers of variables, as the summands' files read them off the cut. -/
theorem cut_unit (x : OnBytes.Params.AttentionRounds) (i : Nat) (u : Nat × Nat)
    (h : x.score[i]? = some u) : (cut x).getD i 3 - 3 = u.1 := by
  rw [cut_of_shape x i 3 _ (shape_unit x i u h), productsShape_rounds, Nat.add_sub_cancel]
theorem cut_iSE (x : OnBytes.Params.AttentionRounds) : (cut x).getD (iSE x) 3 - 3 = x.e := by
  rw [cut_of_shape x _ 3 _ (shape_iSE x), productsShape_rounds, Nat.add_sub_cancel]
theorem cut_iVM (x : OnBytes.Params.AttentionRounds) : (cut x).getD (iVM x) 3 - 3 = x.valueM := by
  rw [cut_of_shape x _ 3 _ (shape_iVM x), productsShape_rounds, Nat.add_sub_cancel]
theorem cut_iVD (x : OnBytes.Params.AttentionRounds) : (cut x).getD (iVD x) 3 - 3 = x.valueD := by
  rw [cut_of_shape x _ 3 _ (shape_iVD x), productsShape_rounds, Nat.add_sub_cancel]
theorem cut_iSF (x : OnBytes.Params.AttentionRounds) :
    (cut x).getD (iSF x) 3 - 3 = x.attained := by
  rw [cut_of_shape x _ 3 _ (shape_iSF x), productsShape_rounds, Nat.add_sub_cancel]
theorem cut_iHB (x : OnBytes.Params.AttentionRounds) : (cut x).getD (iHB x) 3 - 3 = x.bits := by
  rw [cut_of_shape x _ 3 _ (shape_iHB x), productsShape_rounds, Nat.add_sub_cancel]
theorem cut_iSD (x : OnBytes.Params.AttentionRounds) :
    (cut x).getD (iSD x) 3 - 3 = x.lt + x.lgk + x.lt := by
  rw [cut_of_shape x _ 3 _ (shape_iSD x)]
  show (keyVars x).length + 3 - 3 = _
  unfold keyVars
  rw [Nat.add_sub_cancel, List.length_map, List.length_append, List.length_append,
    List.length_replicate, List.length_replicate, List.length_replicate]

end H2K5.Honest

#print axioms H2K5.Honest.shapesOf_scalars
#print axioms H2K5.Honest.shapesOf_units
#print axioms H2K5.Honest.shapesOf_tail
#print axioms H2K5.Honest.shapes_eq
#print axioms H2K5.Honest.unitsShapes_length
#print axioms H2K5.Honest.unitsShapes_get
#print axioms H2K5.Honest.shape_unit
#print axioms H2K5.Honest.shape_tail
#print axioms H2K5.Honest.shape_iSE
#print axioms H2K5.Honest.shape_iGam
#print axioms H2K5.Honest.shape_iVM
#print axioms H2K5.Honest.shape_iVD
#print axioms H2K5.Honest.shape_iZero
#print axioms H2K5.Honest.shape_iM6
#print axioms H2K5.Honest.shape_iSF
#print axioms H2K5.Honest.shape_iOm4
#print axioms H2K5.Honest.shape_iSD
#print axioms H2K5.Honest.shape_iOm5
#print axioms H2K5.Honest.shape_iHB
#print axioms H2K5.Honest.shapes_length
#print axioms H2K5.Honest.leadBehind_zero
#print axioms H2K5.Honest.cut_of_shape
#print axioms H2K5.Honest.productsShape_rounds
#print axioms H2K5.Honest.cut_unit
#print axioms H2K5.Honest.cut_iSE
#print axioms H2K5.Honest.cut_iVM
#print axioms H2K5.Honest.cut_iVD
#print axioms H2K5.Honest.cut_iSF
#print axioms H2K5.Honest.cut_iHB
#print axioms H2K5.Honest.cut_iSD
