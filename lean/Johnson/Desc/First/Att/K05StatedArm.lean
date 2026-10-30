-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05StatedArm.lean: kind K5: THE ATTENTION SEGMENTS' ARM OF THE ONE STATED
FUNCTION, AND THE PREMISE hSt OF THE KIND's TOPS PAID BY THE MAKE.

The table of joints' filling has one letter St: how the array of the second sending is read as a
stated function of the data of the first sending. Its owner lays St := Stated.of (uBySort uL uA uH)
(Johnson/Desc/Sound/StatedAll.lean): one function with three arms, chosen by
the sort of the segment that is open in the verifier's state, each arm handed the open link's number
off that state (linkNo).

IS IT EMPTY HERE? hSt_of_arm has one premise: the public parameters have a plan for the link.

Main names:
  `uArm W`: the arm: at link number l: uAtt A (funsAt A)
    (Johnson/Desc/First/Att/K05WorldTieAt.lean), A the attention plan number l / 2 of the public
    parameters W; 0 where there is none.
  `linkNo_att`: at a state whose open segment is an attention segment a₀, linkNo is
    a₀.L.check.frame.link.
  `hSt_of_arm`: **hSt**: W.A[x.link / 2]? = some A gives, at every uL and uH: at every state s with
    s.here = .att a₀ and a₀.L.check.frame.link = x.link: StatedAtt (Stated.of (uBySort uL (uArm W)
    uH)) A (funsAt A) s.
  `apart_funsAt`: no two tables of funsAt A s name one position, AT EVERY STATE s (apart_tablesP,
    Johnson/Desc/First/Att/Claims/ReadsApart.lean, at the tables that the seat's reading holds; the
    empty list elsewhere).
  `uAtt_is_sum`: **the arm IS the stated sum**: at a table Fn of funsAt A s, a column c and a run sg
    with tabAt Fn c sg = some pos: uAtt A (funsAt A) s Dt _ (pos / plannedK A) (pos % plannedK A) =
    Σ j < Fn.len, φ j · ‹the unpacked symbol at (Fn.mat, sg · Fn.len + j, c)›: the library's
    holds_entryOf (Johnson/Desc/First/Att/Claims/TabsByChoice.lean), its premise Apart paid.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05WorldTieAt
import Johnson.Desc.First.Att.Claims.FunsAt
import Johnson.Desc.Sound.StatedAll
import Johnson.Desc.First.Att.Claims.ReadsApart

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Sound (Stated UFn uBySort linkNo stated_att)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ)
open K5Law (funsAt Apart apart_tablesP holds_entryOf)

/-- The attention segments' arm of the one stated function. -/
noncomputable def uArm (W : Verify.Public) : ℕ → UFn := fun l =>
  match W.A[l / 2]? with
  | some A => uAtt A (funsAt A)
  | none => fun _ _ _ _ _ => 0

/-- The open link's number at a state whose open segment is an attention segment. -/
theorem linkNo_att {s : First.S} {a₀ : First.AttOwn} (h : s.here = .att a₀) :
    linkNo s = a₀.L.check.frame.link := by
  unfold linkNo First.S.link?
  rw [h]
  rfl

/-- **hSt, by the make.** -/
theorem hSt_of_arm {W : Verify.Public} {x : VerifiableInference.Desc.First.Look.Place}
    {A : Attention.Plan} (hA : W.A[x.link / 2]? = some A) (uL uH : ℕ → UFn) (s : First.S)
    (a₀ : First.AttOwn) (h : s.here = .att a₀) (hl : a₀.L.check.frame.link = x.link) :
    StatedAtt (Stated.of (uBySort uL (uArm W) uH)) A (funsAt A) s := by
  have S := stated_att uL (uArm W) uH s a₀ h
  have e : uArm W (linkNo s) = uAtt A (funsAt A) := by
    unfold uArm
    rw [linkNo_att h, hl, hA]
  rw [e] at S
  exact ⟨S.mask, S.cell⟩

/-- What the claims' seat's reading answers holds tables that tablesP has returned. -/
theorem tables_of_inOf {St : Type} {seat : SeatC St} {c : ParC} {s : St} {z : Runs.In × ℕ}
    (h : inOf seat c s = some z) : ∃ lk, tablesP c.geo c.mats c.nW lk z.1.p = some z.1.t := by
  unfold inOf at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨p, _, lk, _, t, ht, zk, _, K, _, e⟩ := h
  obtain rfl := Option.some.inj e
  exact ⟨lk, ht⟩

/-- **No two tables of funsAt's list name one position**: at every state. -/
theorem apart_funsAt (A : Attention.Plan) (s : First.S) : Apart A.seam.tl (funsAt A s) := by
  unfold funsAt
  cases h : inOf (seatCO (parCOf A)) (parCOf A) s with
  | none =>
    intro Fn hFn
    cases hFn
  | some z =>
    obtain ⟨lk, ht⟩ := tables_of_inOf h
    have := apart_tablesP (tl := A.seam.tl) ht
    show Apart A.seam.tl (z.1.t.funs.map K5Law.funBack).toList
    rw [Array.toList_map]
    exact this

/-- **The arm is the stated sum at the place that tabAt gives**: the form in which the tie on the
array of the second sending speaks. -/
theorem uAtt_is_sum (A : Attention.Plan) (s : First.S) (Dt : Bound GQ) (cN : ℕ × String) {Fn : HFun}
    (hFn : Fn ∈ funsAt A s) {c sg pos : ℕ} (hpos : A.seam.tl.tabAt Fn c sg = some pos) :
    uAtt A (funsAt A) s Dt cN (pos / plannedK A) (pos % plannedK A) =
      ∑ j ∈ Finset.range Fn.len, Reading.gl.val (Fn.phi.getD j zeroE) *
        matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[]) Dt Fn.mat (sg * Fn.len + j) c :=
  holds_entryOf Reading.gl A.seam.tl 0 (plannedK A) _ (funsAt A s) (apart_funsAt A s) {} (fun _ => 0) Fn
    hFn c sg pos hpos

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.apart_funsAt
#print axioms VerifiableInference.Desc.First.Att.P.uAtt_is_sum
#print axioms VerifiableInference.Desc.First.Att.P.linkNo_att
#print axioms VerifiableInference.Desc.First.Att.P.hSt_of_arm
