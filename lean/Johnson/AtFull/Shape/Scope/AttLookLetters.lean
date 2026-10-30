-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/AttLookLetters.lean: THE LOOKUPS' LETTER AT TWO RECORDS THAT MEET SameRead: the
place of a lookup and its shape, equal but for the calls' tables; at the digits equal whole. The steps
on shapes under RelX stand in Scope/AttLookSteps.lean.

Limits. Implications under SameRead. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.Rel
import Johnson.AtFull.Shape.Scope.Sim
import Johnson.AtFull.Shape.LettersAtX

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (Place lookAt placeAt bitsFor places)
open VerifiableInference.Desc.First.Shape (ChainSh HeardAll)
open ProofFile.Honest.K3.Shape (lookHeardSh lookUpd)
open ProofFile.Honest.K3.Law.AtThr (callsG callsB callsU digitsG digitsB digitsU)

variable {X X₀ : Verify.Public}

/-- Where neither record has the plan, or both have. -/
theorem plans_alike (S : SameRead X X₀) (g : Nat) :
    (X.A[g]? = none ∧ X₀.A[g]? = none) ∨
      ∃ p q, X.A[g]? = some p ∧ X₀.A[g]? = some q ∧ stripPlan p = stripPlan q := by
  have e := S.atA g
  cases h1 : X.A[g]? with
  | none =>
    cases h2 : X₀.A[g]? with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some q =>
      rw [h1, h2] at e
      cases e
  | some p =>
    cases h2 : X₀.A[g]? with
    | none =>
      rw [h1, h2] at e
      cases e
    | some q =>
      rw [h1, h2] at e
      exact Or.inr ⟨p, q, rfl, rfl, Option.some.inj e⟩

/-- The readers of the record that the place of a lookup reads, at two records. -/
theorem same_p4 (S : SameRead X X₀) : X.p4 = X₀.p4 := by
  have e := congrArg (fun y : Layer.Lay => y.h.p4) S.lay
  exact e

theorem same_NGr (S : SameRead X X₀) : X.NGr = X₀.NGr := by
  have e := congrArg (fun y : Layer.Lay => y.NGr) S.lay
  exact e

theorem same_cl (S : SameRead X X₀) : X.y.cl = X₀.y.cl := by
  have e := congrArg (fun y : Layer.Lay => y.cl) S.lay
  exact e

theorem same_fo (S : SameRead X X₀) : X.y.fo = X₀.y.fo := by
  have e := congrArg (fun y : Layer.Lay => y.fo) S.lay
  exact e

theorem same_lidb (S : SameRead X X₀) : X.y.h.lidb = X₀.y.h.lidb := by
  have e := congrArg (fun y : Layer.Lay => y.h.lidb) S.lay
  exact e

theorem same_lmb (S : SameRead X X₀) : X.y.h.lmb = X₀.y.h.lmb := by
  have e := congrArg (fun y : Layer.Lay => y.h.lmb) S.lay
  exact e

theorem same_LIDB (S : SameRead X X₀) : X.hS.LIDB = X₀.hS.LIDB := by
  have e := congrArg Head.Shape.LIDB S.hS
  exact e

theorem same_lmbH (S : SameRead X X₀) : X.hS.lmbH = X₀.hS.lmbH := by
  have e := congrArg Head.Shape.lmbH S.hS
  exact e

/-- A place with no table in its calls. -/
def stripPl (x : Place) : Place :=
  { x with calls := x.calls.map stripCall, fs := stripF x.fs }

/-- **The place of a lookup at two records: equal but for the calls' tables.** -/
theorem lookAt_rel (S : SameRead X X₀) (i : Nat) (d : Bool) :
    (lookAt X i d).map stripPl = (lookAt X₀ i d).map stripPl := by
  unfold lookAt
  dsimp only
  rw [same_p4 S, same_NGr S, S.HLy, S.H, S.wsLay, same_LIDB S, same_lmbH S, S.G, same_cl S,
    same_fo S, same_lidb S, same_lmb S]
  generalize (if X₀.p4 = true then 2 else 1) = st
  by_cases c1 : (i == st * X₀.NGr) = true
  · simp only [if_pos c1]
  · by_cases c2 : (i % st == 0) = true
    · simp only [if_neg c1, if_pos c2]
    · simp only [if_neg c1, if_neg c2]
      rcases plans_alike S (i / st) with ⟨h1, h2⟩ | ⟨p, q, h1, h2, e⟩
      · rw [h1, h2]
      · rw [h1, h2]
        have e1 := congrArg Attention.Plan.seam e
        have e2 := congrArg Attention.Plan.ns e
        have e3 := congrArg Attention.Plan.fs e
        have e4 := congrArg (fun a : Attention.Plan => a.S.calls.map (·.call)) e
        have e5 := congrArg (fun a : Attention.Plan => a.S.cf.lmb) e
        have e6 := congrArg Attention.Plan.lid e
        have es : p.seam = q.seam := e1
        have en : p.ns = q.ns := e2
        have ef : stripF p.fs = stripF q.fs := e3
        have ec : (p.S.calls.map (·.call)).map stripCall =
            (q.S.calls.map (·.call)).map stripCall := by
          have e4' : (p.S.calls.map stripA).map (·.call) = (q.S.calls.map stripA).map (·.call) := e4
          simpa [Array.map_map, Function.comp_def, stripA] using e4'
        have el : p.S.cf.lmb = q.S.cf.lmb := e5
        have ei : p.lid = q.lid := e6
        have ep : p.fs.pub = q.fs.pub := by
          have k := congrArg Forest.Shape.pub ef
          exact k
        cases d with
        | true =>
          simp only [Option.bind_some, if_true]
          rw [es, en]
        | false =>
          simp only [Option.bind_some, Bool.false_eq_true, if_false, Option.map_some]
          unfold stripPl
          rw [ec, ef, ep, el, ei, es, en]

/-- **At the digits the place is the same, whole.** -/
theorem lookAt_digits (S : SameRead X X₀) (i : Nat) : lookAt X i true = lookAt X₀ i true := by
  unfold lookAt
  dsimp only
  rw [same_p4 S, same_NGr S, S.HLy, S.H, S.wsLay, same_LIDB S, same_lmbH S, S.G, same_cl S,
    same_fo S, same_lidb S, same_lmb S]
  generalize (if X₀.p4 = true then 2 else 1) = st
  by_cases c1 : (i == st * X₀.NGr) = true
  · simp only [if_pos c1]
  · by_cases c2 : (i % st == 0) = true
    · simp only [if_neg c1, if_pos c2]
    · simp only [if_neg c1, if_neg c2]
      rcases plans_alike S (i / st) with ⟨h1, h2⟩ | ⟨p, q, h1, h2, e⟩
      · rw [h1, h2]
      · rw [h1, h2]
        have e1 := congrArg Attention.Plan.seam e
        have e2 := congrArg Attention.Plan.ns e
        have es : p.seam = q.seam := e1
        have en : p.ns = q.ns := e2
        simp only [Option.bind_some, if_true]
        rw [es, en]

theorem same_frame_set (S : SameRead X X₀) :
    Params.settingOf X.P.frame = Params.settingOf X₀.P.frame := by rw [S.frame]

/-- The lookups' letter at the digits: the same. -/
theorem lookOf_digits (S : SameRead X X₀) (l : Nat) : lookOf X l true = lookOf X₀ l true := by
  unfold lookOf placeAt
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
  rw [lookAt_digits S, same_frame_set S]

/-- shapeFree does not read the tables. -/
theorem shapeFree_strip (cs : Array Call) (lid : Nat) :
    (shapeFree cs lid).map stripF = shapeFree (cs.map stripCall) lid := by
  have e1 : (cs.map stripCall).size = cs.size := Array.size_map ..
  have e2 : (cs.map stripCall).foldl (fun m c => min m c.n) lid =
      cs.foldl (fun m c => min m c.n) lid := by
    rw [Array.foldl_map]
    rfl
  have e3 : (cs.map stripCall).foldl (fun m c => max m c.k) 0 =
      cs.foldl (fun m c => max m c.k) 0 := by
    rw [Array.foldl_map]
    rfl
  have e4 : ∀ d, (cs.map stripCall).map (fun c => c.n - d) = cs.map (fun c => c.n - d) := by
    intro d
    rw [Array.map_map]
    rfl
  unfold shapeFree
  dsimp only
  rw [e2, e3, e4, e1]
  split
  · rw [Option.map_map]
    rfl
  · rfl

/-- A letter of a lookup with no table in its shape. -/
def stripLk (s : Forest.Shape × Nat) : Forest.Shape × Nat := (stripF s.1, s.2)

theorem stripLk_map (o : Option Forest.Shape) (p : Array Nat) (n : Nat) :
    (o.map fun h0 => (({ h0 with pub := p } : Forest.Shape), n)).map stripLk =
      (o.map stripF).map fun h0 => (({ h0 with pub := p } : Forest.Shape), n) := by
  cases o <;> rfl

/-- **The lookups' letter on the calls at an attention link, at two records: equal but for the calls'
tables.** -/
theorem lookOf_rel_odd (S : SameRead X X₀) {l : Nat} (ho : l % 2 = 1) :
    (lookOf X l false).map stripLk = (lookOf X₀ l false).map stripLk := by
  have e := lookAt_rel S l false
  unfold lookOf placeAt
  rw [if_neg (by simp [ho]), if_neg (by simp [ho]), same_frame_set S]
  cases h1 : lookAt X l false with
  | none =>
    cases h2 : lookAt X₀ l false with
    | none => rfl
    | some y =>
      rw [h1, h2] at e
      cases e
  | some x =>
    cases h2 : lookAt X₀ l false with
    | none =>
      rw [h1, h2] at e
      cases e
    | some y =>
      rw [h1, h2] at e
      have ex : stripPl x = stripPl y := Option.some.inj e
      have ec : x.calls.map stripCall = y.calls.map stripCall := by
        have k := congrArg Place.calls ex
        exact k
      have ep : x.pub = y.pub := by
        have k := congrArg Place.pub ex
        exact k
      have ei : x.lid = y.lid := by
        have k := congrArg Place.lid ex
        exact k
      have en : x.F.next = y.F.next := by
        have k := congrArg (fun z : Place => z.F.next) ex
        exact k
      show ((shapeFree x.calls x.lid).map fun h0 =>
          (({ h0 with pub := x.pub } : Forest.Shape), x.F.next)).map stripLk =
        ((shapeFree y.calls y.lid).map fun h0 =>
          (({ h0 with pub := y.pub } : Forest.Shape), y.F.next)).map stripLk
      rw [stripLk_map, stripLk_map, shapeFree_strip, shapeFree_strip, ec, ei, ep, en]

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.lookAt_rel
#print axioms Johnson.AtFull.Shape.Scope.lookAt_digits
#print axioms Johnson.AtFull.Shape.Scope.lookOf_digits
#print axioms Johnson.AtFull.Shape.Scope.shapeFree_strip
#print axioms Johnson.AtFull.Shape.Scope.lookOf_rel_odd
