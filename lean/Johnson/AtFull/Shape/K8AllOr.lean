-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/K8AllOr.lean: THE SMALLNESS TEST's RUN "K8.equations" ON SHAPES, WITH THE
PAYER's FORM OF ITS ONE Bool ASKED FIRST. Three definitions and four general laws, without a
premise: nothing is evaluated.

  all_or          allN … || allB … = allB …, at all arguments: by allB_of_N
                  (Johnson/Desc/K8/Honest/EqAllLight.lean): a yes of allN is a yes of allB.
  allBO           that "or", as a function.
  **allB_eqO**    allB = allBO, at all arguments.
  eqGO, eqRunGO   the text of eqG (Johnson/Desc/K8/Honest/EqAllChain.lean) with allBO for allB, and
                  the text of eqRunG (Johnson/Desc/K8/Honest/EqAllRun.lean) with eqGO for eqG. eqGO
                  is the third text of that step: EqAllLight.lean has eqGL.
  **eqG_eqO**, **eqRunG_eqO**   eqG = eqGO and eqRunG = eqRunGO, at all arguments.

Why. allB's last clause (tailReadyB) lays a mark for each entry of the vectors' parts that hold
tables, one by one, and sorts the tables; the library's lighter test (tailLightB) lays no mark and
still sorts. allN lays no mark, does not sort (it asks that the tables' stretches lie sorted), and
reads a table's number of weights as a number. allN goes one way: its no does not deny allB's yes.
With "or" both stand in the text, so the two texts are equal; and Bool's "or" does not open its
right side where the left is true.

Limits. What either text costs Lean's kernel is not measured here. Where allN says no, allBO is as
dear as allB, and dearer by allN. The update and the claims' shapes are eqG's and eqRunG's own. That
any of these returns at a shape which the chain reaches is not shown. Nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.K8.Honest.EqAllRun
import Johnson.Desc.K8.Honest.EqAllLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Shape

/-- The payer's form or allB is allB. -/
theorem all_or (front : Nat) (t : TailSh) (fs : List FunSh) (L : LedSh) (n : Nat) :
    (allN front t fs L n || allB front t fs L n) = allB front t fs L n := by
  cases h : allN front t fs L n with
  | true => rw [allB_of_N h]; rfl
  | false => rfl

/-- **The whole list's Bool, the payer's form asked first.** -/
def allBO (front : Nat) (t : TailSh) (fs : List FunSh) (L : LedSh) (n : Nat) : Bool :=
  allN front t fs L n || allB front t fs L n

/-- **allB is allBO**, at all arguments. -/
theorem allB_eqO (front : Nat) (t : TailSh) (fs : List FunSh) (L : LedSh) (n : Nat) :
    allB front t fs L n = allBO front t fs L n :=
  (all_or front t fs L n).symm

/-- eqG's text with allBO for allB. -/
def eqGO (front : Nat) (a : ChainSh) : Except String ChainSh :=
  match a.tl, a.led, a.tables with
  | some t, some L, some fs =>
    match t.heard with
    | some g =>
      if allBO (L.claims + front) t fs L 0 then
        .ok ((a.setTl (allRecU (L.claims + front) 0 t fs L)).setLed (allLedU g L))
      else .error "K8.equations: the shape does not pass"
    | none => .error "K8.equations: no record is heard"
  | _, _, _ => .error "K8.equations: no link is open, or no list of tables is laid"

/-- **eqG is eqGO**, at all arguments. -/
theorem eqG_eqO (front : Nat) (a : ChainSh) : eqG front a = eqGO front a := by
  unfold eqG eqGO
  simp only [allB_eqO]
  rfl

/-- eqRunG's text with eqGO for eqG. -/
def eqRunGO (n : Nat) (a : ChainSh) : Except String (List ClaimSh × ChainSh) :=
  (eqGO n a).bind fun t =>
    match eqClaimsG a t with
    | some cs => .ok (cs, t)
    | none => .error "K8.equations: the claims' shapes cannot be said"

/-- **eqRunG is eqRunGO**, at all arguments. -/
theorem eqRunG_eqO (n : Nat) (a : ChainSh) : eqRunG n a = eqRunGO n a := by
  unfold eqRunG eqRunGO
  rw [eqG_eqO]
  rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.all_or
#print axioms VerifiableInference.Desc.First.K8.Honest.allB_eqO
#print axioms VerifiableInference.Desc.First.K8.Honest.eqG_eqO
#print axioms VerifiableInference.Desc.First.K8.Honest.eqRunG_eqO
#print axioms VerifiableInference.Desc.First.K8.Honest.allBO
#print axioms VerifiableInference.Desc.First.K8.Honest.eqGO
#print axioms VerifiableInference.Desc.First.K8.Honest.eqRunGO
