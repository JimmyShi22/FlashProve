-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/AttLaw.lean: the seven tests on public data at the attention segments
(`K5Asks.rowW`, Johnson/Desc/First/Att/GuardO.lean) read little of the public part: at profile 4 and
twelve groups, its scan of the parameter file and its twelve attention plans. Two definitions with
code and two laws, general in the public part. No goal is stated.
Why. The closed facts at the full size are Bools that Lean's kernel evaluates at what the public
part's makers return (`atMakers`, Johnson/AtFull/Public/AtWitnesses.lean): a test there takes the
layers' record, the layers' plans and the attention's plans, not a public part. So the row is
brought to that form here. No test is typed anew: `K5Asks.testAt` stands on both sides.
  `placeA i a`: the place of the lookup on the calls at attention link i, off the group's plan a:
    the entry of `lookAt` (Johnson/Desc/First/Look/LookAt.lean) for an attention link, by itself.
  `lookAt_odd`: at profile 4, `lookAt X (2 * g + 1) false` is `placeA (2 * g + 1)` of the plan of
    group g, and none where there is no such plan.
  `rowA k P A`: test number k at the twelve groups, off the scan P and the plans A.
  **`rowW_eq`**: at profile 4 and twelve groups `K5Asks.rowW k X = rowA k X.P X.A`.
Limits. NO VALUE IS GIVEN HERE, and no test is shown to say yes. Twelve groups alone. Nothing on
soundness, on a binding of the commitment (the opening form, `BindsWith`), on correctness of
extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Att.GuardO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Entry
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.First.Look (Place lookAt)

/-- The place of the lookup on the calls at attention link i, off the group's plan. -/
def placeA (i : Nat) (a : Attention.Plan) : Place :=
  let kind : String := "attention"
  { name := s!"LINK {i} ({kind}) calls", link := i, calls := a.S.calls.map (·.call),
    pub := a.fs.pub, lid := a.lid, base := a.seam.Fp.fillL, F := a.seam.Fp.fillL.slots a.ns,
    fs := a.fs, ns := a.ns, lm := a.S.cf.lmb }

/-- At profile 4 the place at an odd link is the attention plan's. -/
theorem lookAt_odd {X : Verify.Public} (h4 : X.p4 = true) (g : Nat) :
    lookAt X (2 * g + 1) false = (X.A[g]?).map (placeA (2 * g + 1)) := by
  have e1 : (2 * g + 1 == 2 * X.NGr) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e2 : ((2 * g + 1) % 2 == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e3 : (2 * g + 1) / 2 = g := by omega
  unfold lookAt
  simp only [h4, if_true, e1, e2, e3, Bool.false_eq_true, if_false]
  cases X.A[g]? <;> rfl

/-- Test number k at the twelve groups, off the scan of the parameter file and the plans. -/
def rowA (k : Nat) (P : PolScan) (A : Array Attention.Plan) : Bool :=
  (List.range 12).all fun g =>
    match A[g]? with
    | some a => K5Asks.testAt k a (placeA (2 * g + 1) a)
        { link := 2 * g + 1, piece := 3, work := (Params.settingOf P.frame).workOf .field .request,
          own := a.own, before := [] }
    | none => false

/-- **The row reads the scan and the twelve plans alone.** -/
theorem rowW_eq {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) (k : Nat) :
    K5Asks.rowW k X = rowA k X.P X.A := by
  unfold K5Asks.rowW attLinksN rowA
  rw [h4, hN, if_pos rfl, List.all_map]
  refine congrArg (List.all (List.range 12)) (funext fun g => ?_)
  show (match X.A[g]?, lookAt X (2 * g + 1) false with
    | some a, some x => K5Asks.testAt k a x (parN X (2 * g + 1) a)
    | _, _ => false) = _
  rw [lookAt_odd h4]
  cases X.A[g]? <;> rfl

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.lookAt_odd
#print axioms Johnson.AtFull.Entry.rowW_eq
