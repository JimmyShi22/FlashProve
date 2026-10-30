-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysStart.lean: the start form of the batched sumcheck, taken apart.

The verifier starts the batched sumcheck of a layer sub-proof from a form (joinStart,
OnBytes/Model/Layer.lean): the sum over the lookup's calls of the call's weight times the call's
factor in the lookup's join (joinPart), plus a public number for the padding trees, less the hidden
sum that the second token sumcheck claims, less the form that the lookup's end leaves, plus om[1]
times what the second token sumcheck leaves.

This file writes the form's last, pure part as a function of the calls' factors (startOf), shows
that joinStart returns it (joinStart_eq), and says what it is worth in a world (startOf_value). With
what each call's factor is worth on the library's key vector (joinPart_keyVec',
Johnson/Road/FormsKeysShape.lean) the worth falls into four parts (start_parts): the lookup's own
part; the sums of the keys' products of two cells, less the hidden sum; the keys' matrix products;
and om[1] times what the second token sumcheck leaves.

What is compared with what: the verifier with itself. startOf is a copy of the last lines of
joinStart, tied to it by joinStart_eq.

Main definitions: startOf, padOf. Main theorems: joinStart_eq, startOf_value, start_parts.

What is not claimed. Nothing is said on what makes any of the four parts vanish, or equal to the sum
that the batched sumcheck runs on: these are other statements and random steps. start_parts takes
the worth of each call's factor as a hypothesis, in the form in which joinPart_keyVec' concludes it.
The program does not import this file.
-/
import Johnson.Road.FormsKeysShape

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff eqTab Forest.paddingLaid Forest.noPub)
open OnBytes.Model.Layer (Env Heard aff0 joinStart form)

/-- The public number that the start form has for the padding trees of the lookup: for each tree
past the last one in use, its equality weight times alpha less the padding key of call 0. -/
def padOf (H : Heard) : E :=
  (List.range (2 ^ H.fo.shape.rK - H.fo.shape.NT)).foldl
    (fun a t => addE a (mulE ((eqTab H.fo.zy).getD (H.fo.shape.NT + t) zeroE)
      (subE H.fo.alpha (H.fo.padKey 0)))) zeroE

/-- The start form as a function of the calls' factors: the last lines of joinStart. -/
def startOf (H : Heard) (om : Array E) (parts : List Aff) : Aff :=
  let c0 := parts.zipIdx.foldl (fun (a : Aff) x => a.addMul x.1 (H.fo.e.getD x.2 zeroE)) aff0
  let c1 := c0 + Aff.ofConst (padOf H)
  let c2 := match H.tT with
    | some tT => c1 - Aff.slot tT.sCl
    | none => c1
  let c3 := c2 - H.fo.cEnd
  if H.tT.isSome then c3.addMul H.KT (om.getD 1 zeroE) else c3

/-- joinStart makes the marks and the calls' factors, runs its two tests, and returns startOf of the
factors. -/
theorem joinStart_eq (v : Env) (H : Heard) (om : Array E) :
    joinStart v H om = (do
      let weighed ← form (v.y.calls.mapM v.weighedOf)
      let parts ← form ((v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
        v.joinPart H.fo.alpha H.fo.theta x.2 x.1.1 x.1.2)
      Model.mustAs "internal-forest-join"
        (parts.length == H.fo.shape.calls.size && H.fo.e.size == H.fo.shape.calls.size)
      Forest.paddingLaid H.fo
        (← form (weighed.toList.zipIdx.foldlM (fun laid x => v.laidOf x.2 x.1 laid)
          (Forest.noPub H.fo.shape)))
      pure (startOf H om parts)) := rfl

section Value

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-- The fold that weighs the calls' factors, from any form and any first number. -/
theorem foldParts_value (e : Array E) : ∀ (parts : List Aff) (a : Aff) (n : ℕ),
    ((parts.zipIdx n).foldl (fun (a : Aff) x => a.addMul x.1 (e.getD x.2 zeroE)) a).value ρ W =
      a.value ρ W + ((parts.zipIdx n).map fun x => ρ.val (e.getD x.2 zeroE) * x.1.value ρ W).sum
  | [], a, n => by simp
  | p :: parts, a, n => by
    rw [List.zipIdx_cons, List.foldl_cons, foldParts_value e parts, Aff.value_addMul,
      List.map_cons, List.sum_cons]
    ring

/-- What the start form is worth, where the second token sumcheck is run: the weighted sum of the
calls' factors, plus the padding trees' number, less the hidden sum under the slot sCl, less the
worth of the form that the lookup's end leaves, plus om[1] times the worth of what the second token
sumcheck leaves. -/
theorem startOf_value (H : Heard) (om : Array E) (parts : List Aff) {tT : Model.Tsc}
    (hT : H.tT = some tT) :
    (startOf H om parts).value ρ W =
      (parts.zipIdx.map fun x => ρ.val (H.fo.e.getD x.2 zeroE) * x.1.value ρ W).sum +
        ρ.val (padOf H) - W.slot tT.sCl - H.fo.cEnd.value ρ W +
        ρ.val (om.getD 1 zeroE) * H.KT.value ρ W := by
  unfold startOf
  simp only [hT, Option.isSome_some, if_true]
  rw [Aff.value_addMul, Aff.value_sub, Aff.value_sub, Aff.value_add, Aff.value_ofConst,
    Aff.value_slot, foldParts_value ρ W H.fo.e parts aff0 0, aff0_value, zero_add]

/-- The four parts. If the factor of call number q is worth base q - kv q + ts q + acc q (as
joinPart_keyVec' says: alpha - q theta; the extension of the library's key vector; the sums of the
products of two cells; the matrix products), the start form is worth: the lookup's own part; the
weighted sums of products less the hidden sum; the weighted matrix products; and om[1] times what
the second token sumcheck leaves. -/
theorem start_parts (H : Heard) (om : Array E) (parts : List Aff) {tT : Model.Tsc}
    (hT : H.tT = some tT) (base kv ts acc : ℕ → K)
    (hp : ∀ x ∈ parts.zipIdx, x.1.value ρ W = base x.2 - kv x.2 + ts x.2 + acc x.2) :
    (startOf H om parts).value ρ W =
      ((∑ q ∈ range parts.length, ρ.val (H.fo.e.getD q zeroE) * (base q - kv q)) +
        ρ.val (padOf H) - H.fo.cEnd.value ρ W) +
      ((∑ q ∈ range parts.length, ρ.val (H.fo.e.getD q zeroE) * ts q) - W.slot tT.sCl) +
      (∑ q ∈ range parts.length, ρ.val (H.fo.e.getD q zeroE) * acc q) +
      ρ.val (om.getD 1 zeroE) * H.KT.value ρ W := by
  have e1 : (parts.zipIdx.map fun x => ρ.val (H.fo.e.getD x.2 zeroE) * x.1.value ρ W).sum =
      ∑ q ∈ range parts.length,
        ρ.val (H.fo.e.getD q zeroE) * (base q - kv q + ts q + acc q) := by
    have e2 : (parts.zipIdx.map fun x => ρ.val (H.fo.e.getD x.2 zeroE) * x.1.value ρ W) =
        parts.zipIdx.map fun x =>
          ρ.val (H.fo.e.getD x.2 zeroE) * (base x.2 - kv x.2 + ts x.2 + acc x.2) :=
      List.map_congr_left fun x hx => by rw [hp x hx]
    have e3 : (parts.zipIdx.map fun x =>
        ρ.val (H.fo.e.getD x.2 zeroE) * (base x.2 - kv x.2 + ts x.2 + acc x.2)) =
        (List.range parts.length).map fun q =>
          ρ.val (H.fo.e.getD q zeroE) * (base q - kv q + ts q + acc q) := by
      have e4 : parts.zipIdx.map (·.2) = List.range parts.length := by
        rw [List.zipIdx_map_snd, List.range_eq_range']
      rw [← e4, List.map_map]
      rfl
    rw [e2, e3, list_range_sum]
  rw [startOf_value ρ W H om parts hT, e1]
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  ring

end Value

#print axioms joinStart_eq
#print axioms startOf_value
#print axioms start_parts

end OnBytes.Road
