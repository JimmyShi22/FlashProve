-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/AttRowsB.lean: THE ROWS "first", "keys", "join", "second" OF AN ATTENTION LINK AT TWO
PLANS EQUAL BUT FOR WHAT MOVES, AT TWO SHAPES EQUAL BUT FOR THE CALLS' TABLES: both return, with one list of
claims' shapes and such shapes behind, or both refuse.

Limits. "keys" and "join" under padKeyOk at both plans (hpad_of_public pays it at what publicOfO returns).
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.AttRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo parCOf ParC Heard)
open VerifiableInference.Desc.First.Att.P.Runs (In JoinsP PadIn)
open VerifiableInference.Desc.First.Shape (ChainSh HeardAll Heard5Sh LedSh ClaimSh affSh)
open H2K5.Honest (partsOf inBlank keysBlank tabsGC tabsG heard5Blank ledBlank ShIn JSh k5FirstG
  k5SecondG k5KeysG k5JoinG bareSh formsSh)
open K5Law (OptRel)

/-- Two values of a run: one list of claims' shapes; two shapes equal but for the tables. -/
abbrev YCs (y y' : List ClaimSh × ChainSh) : Prop := y.1 = y'.1 ∧ stripC y.2 = stripC y'.2

theorem partsOf_strip (c : ChainSh) :
    partsOf (stripC c) = (partsOf c).map fun x => (x.1, stripH x.2.1, x.2.2) := by
  have e1 : (stripC c).att = c.att := rfl
  have e2 : (stripC c).look = c.look.map stripH := rfl
  have e3 : (stripC c).led = c.led := rfl
  unfold partsOf
  rw [e1, e2, e3]
  generalize c.att.bind (·.heard5) = x
  generalize c.look = y
  generalize c.led = z
  cases x <;> cases y <;> cases z <;> rfl

theorem tabsGC_strip (A : Attention.Plan) (c : ChainSh) :
    tabsGC (stripPlan A) (stripC c) = tabsGC A c := by
  have e1 : (stripC c).att = c.att := rfl
  have e2 : (stripC c).look = c.look.map stripH := rfl
  have e3 : (stripC c).led = c.led := rfl
  unfold tabsGC
  rw [e1, e2, e3]
  generalize c.att.bind (·.heard5) = x
  generalize c.look = y
  generalize c.led = z
  cases x <;> cases y <;> cases z <;> first | rfl | exact tabsG_strip _ _ _ _

theorem tabsGC_same {A B : Attention.Plan} (e : stripPlan A = stripPlan B) {c c' : ChainSh}
    (hc : stripC c = stripC c') : tabsGC A c = tabsGC B c' := by
  rw [← tabsGC_strip A, e, hc, tabsGC_strip]

theorem lookOfO_strip (lmb : Nat) (K : HeardAll) :
    P.lookOfO lmb (stripH K).blank = P.lookOfO lmb K.blank := rfl

theorem inAt_blank (c : ParC) (K : HeardAll) (h : Heard) (U : Fork) :
    K5Law.inAt c (stripH K).blank h U = K5Law.inAt c K.blank h U := by
  unfold K5Law.inAt
  rw [lookOfO_strip]
  rfl

/-- What a flat input keeps. -/
abbrev flatX (x : In × Nat) : In × Nat := (flatIn x.1, x.2)

theorem inBlank_flat (A : Attention.Plan) (c : ChainSh) :
    inBlank (stripPlan A) (stripC c) = (inBlank A c).map flatX := by
  unfold inBlank
  rw [partsOf_strip]
  cases partsOf c with
  | none => rfl
  | some q =>
    show K5Law.inAt (parCOf (stripPlan A)) (stripH q.2.1).blank (heard5Blank q.1) (ledBlank q.2.2) = _
    rw [inAt_blank, parCOf_strip, inAt_flat]
    rfl

theorem inBlank_same {A B : Attention.Plan} (e : stripPlan A = stripPlan B) {c c' : ChainSh}
    (hc : stripC c = stripC c') : (inBlank A c).map flatX = (inBlank B c').map flatX := by
  rw [← inBlank_flat, ← inBlank_flat, e, hc]

theorem inAt_self {c : ParC} {gl : Forest.Heard} {h : Heard} {U : Fork} {x : In × Nat}
    (e : K5Law.inAt c gl h U = some x) : ShIn x.1 x.1 ∧ x.1.g = c.geo := by
  unfold K5Law.inAt at e
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at e
  obtain ⟨p, hp, t, ht, k, -, rfl⟩ := e
  exact ⟨H2K5.Honest.shIn_of c rfl rfl hp hp ht ht, rfl⟩

theorem inBlank_self {A : Attention.Plan} {c : ChainSh} {x : In × Nat}
    (e : inBlank A c = some x) : ShIn x.1 x.1 ∧ x.1.g = (parCOf A).geo := by
  unfold inBlank at e
  obtain ⟨q, -, hq⟩ := Option.bind_eq_some_iff.1 e
  exact inAt_self hq

/-- "first" at two inputs that are flat alike. -/
theorem first_between {x y : In × Nat} (Hx : ShIn x.1 x.1) (Hy : ShIn y.1 y.1)
    (e : flatX x = flatX y) :
    OptRel (fun z z' => z.1.map affSh = z'.1.map affSh ∧ JSh z.2 z'.2)
      (P.Runs.firstRun x.1 x.2) (P.Runs.firstRun y.1 y.2) := by
  have ef : flatIn x.1 = flatIn y.1 := congrArg Prod.fst e
  have e2 : x.2 = y.2 := by
    have t := congrArg Prod.snd e
    exact t
  have r1 := first_flat Hx x.2
  have r2 := first_flat Hy y.2
  rw [ef, e2] at r1
  rw [e2]
  cases h1 : P.Runs.firstRun x.1 y.2 <;> cases h2 : P.Runs.firstRun y.1 y.2 <;>
    cases h3 : P.Runs.firstRun (flatIn y.1) y.2 <;> rw [h1, h3] at r1 <;> rw [h2, h3] at r2 <;>
    first
      | trivial
      | exact r1.elim
      | exact r2.elim
      | exact ⟨r1.1.trans r2.1.symm, r1.2.1.trans r2.2.1.symm, r1.2.2.trans r2.2.2.symm⟩

/-- **The row "first".** -/
theorem first_row {A B : Attention.Plan} (e : stripPlan A = stripPlan B) (n : Nat) {c c' : ChainSh}
    (hc : stripC c = stripC c') : Alike YCs (k5FirstG A n c) (k5FirstG B n c') := by
  have eT := tabsGC_same e hc
  have eI := inBlank_same e hc
  unfold k5FirstG
  rw [eT]
  split
  · cases hx : inBlank A c with
    | none =>
      cases hy : inBlank B c' with
      | none =>
        simp only [Option.bind_none]
        exact Or.inr ⟨rfl, rfl⟩
      | some y =>
        rw [hx, hy] at eI
        cases eI
    | some x =>
      cases hy : inBlank B c' with
      | none =>
        rw [hx, hy] at eI
        cases eI
      | some y =>
        rw [hx, hy] at eI
        have r := first_between (inBlank_self hx).1 (inBlank_self hy).1 (Option.some.inj eI)
        simp only [Option.bind_some]
        cases h1 : P.Runs.firstRun x.1 x.2 with
        | none =>
          cases h2 : P.Runs.firstRun y.1 y.2 with
          | none => exact Or.inr ⟨rfl, rfl⟩
          | some v =>
            rw [h1, h2] at r
            exact r.elim
        | some u =>
          cases h2 : P.Runs.firstRun y.1 y.2 with
          | none =>
            rw [h1, h2] at r
            exact r.elim
          | some v =>
            rw [h1, h2] at r
            have em : u.1.map (fun f => bareSh (affSh f)) = v.1.map fun f => bareSh (affSh f) := by
              have := congrArg (List.map bareSh) r.1
              simpa [List.map_map, Function.comp_def] using this
            exact Or.inl ⟨_, _, rfl, rfl, em, hc⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- **The row "second".** -/
theorem second_row {A B : Attention.Plan} (e : stripPlan A = stripPlan B) (n : Nat) {c c' : ChainSh}
    (hc : stripC c = stripC c') : Alike YCs (k5SecondG A n c) (k5SecondG B n c') := by
  have eT := tabsGC_same e hc
  have eI := inBlank_same e hc
  have eS : (inBlank A c).bind (fun x => P.Runs.secondRun x.1 x.2) =
      (inBlank B c').bind fun x => P.Runs.secondRun x.1 x.2 := by
    have t : ∀ o : Option (In × Nat), o.bind (fun x => P.Runs.secondRun x.1 x.2) =
        (o.map flatX).bind fun x => P.Runs.secondRun x.1 x.2 := by
      intro o
      cases o <;> rfl
    rw [t (inBlank A c), t (inBlank B c'), eI]
  unfold k5SecondG
  rw [eT, eS]
  split
  · split
    · exact Or.inl ⟨_, _, rfl, rfl, rfl, hc⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-! ## "keys" and "join" -/

theorem weighedUnits_strip (g : Geo) : P.Runs.weighedUnits (stripG g) = P.Runs.weighedUnits g := by
  unfold P.Runs.weighedUnits
  dsimp only
  simp only [units_strip, lastHolding_strip, List.map_map]
  rfl

theorem laidPadding_strip (g : Geo) (k3 : PadIn) :
    P.Runs.laidPadding (stripG g) k3 = P.Runs.laidPadding g k3 := by
  unfold P.Runs.laidPadding
  dsimp only
  rw [weighedUnits_strip]
  show ((g.calls.map stripCG).toList.zipIdx.foldlM _ k3.noPub) = _
  simp only [Array.toList_map, List.zipIdx_map, List.foldlM_map]
  rfl

theorem padOfO_strip (h : Forest.Shape) : P.padOfO (stripF h) = P.padOfO h := rfl

theorem keys_between {i i' : In} (k3 : PadIn) {j j' : JoinsP} (hx : P.padKeyOk i.g = true)
    (hy : P.padKeyOk i'.g = true) (es : stripG i.g = stripG i'.g) (hj : JSh j j') :
    OptRel (fun z z' => formsSh z = formsSh z') (P.Runs.keysRun i k3 j)
      (P.Runs.keysRun i' k3 j') := by
  rw [P.Runs.keysRun_Q k3 j hx, P.Runs.keysRun_Q k3 j' hy]
  unfold P.Runs.keysRunQ
  have e1 : P.Runs.allJoined j = P.Runs.allJoined j' := by
    unfold P.Runs.allJoined
    rw [hj.1]
  have e2 : P.Runs.paddingLaidQ i.g k3 = P.Runs.paddingLaidQ i'.g k3 := by
    unfold P.Runs.paddingLaidQ
    rw [← laidPadding_strip i.g, es, laidPadding_strip]
  rw [e1, e2]
  cases P.Runs.gather 0 (P.Runs.allJoined j' >>= fun _ => P.Runs.paddingLaidQ i'.g k3) with
  | none => trivial
  | some u => exact hj.2

theorem geo_same {A B : Attention.Plan} (e : stripPlan A = stripPlan B) :
    stripG (parCOf A).geo = stripG (parCOf B).geo := by
  have e1 : (parCOf (stripPlan A)).geo = stripG (parCOf A).geo := geo_strip A.S
  have e2 : (parCOf (stripPlan B)).geo = stripG (parCOf B).geo := geo_strip B.S
  rw [← e1, ← e2, e]

/-- **keysBlank at two plans and two shapes.** -/
theorem keysBlank_rel {A B : Attention.Plan} (e : stripPlan A = stripPlan B)
    (hA : P.padKeyOk (parCOf A).geo = true) (hB : P.padKeyOk (parCOf B).geo = true)
    {c c' : ChainSh} (hc : stripC c = stripC c') :
    OptRel (fun z z' => formsSh z = formsSh z') (keysBlank A c) (keysBlank B c') := by
  have eP : (partsOf c).map (fun x => (x.1, stripH x.2.1, x.2.2)) =
      (partsOf c').map fun x => (x.1, stripH x.2.1, x.2.2) := by
    rw [← partsOf_strip, ← partsOf_strip, hc]
  have eI := inBlank_same e hc
  unfold keysBlank
  cases h1 : partsOf c with
  | none =>
    cases h2 : partsOf c' with
    | none => trivial
    | some q' =>
      rw [h1, h2] at eP
      cases eP
  | some q =>
    cases h2 : partsOf c' with
    | none =>
      rw [h1, h2] at eP
      cases eP
    | some q' =>
      rw [h1, h2] at eP
      have eq := Option.some.inj eP
      have eK : stripH q.2.1 = stripH q'.2.1 := congrArg (fun z => z.2.1) eq
      have e3 : P.padOfO q.2.1.shape = P.padOfO q'.2.1.shape := by
        rw [← padOfO_strip q.2.1.shape, ← padOfO_strip q'.2.1.shape]
        have t := congrArg (fun K : HeardAll => P.padOfO K.shape) eK
        exact t
      simp only [Option.bind_some]
      rw [e3]
      cases hx : inBlank A c with
      | none =>
        cases hy : inBlank B c' with
        | none => trivial
        | some y =>
          rw [hx, hy] at eI
          cases eI
      | some x =>
        cases hy : inBlank B c' with
        | none =>
          rw [hx, hy] at eI
          cases eI
        | some y =>
          rw [hx, hy] at eI
          have X := inBlank_self hx
          have Y := inBlank_self hy
          have r := first_between X.1 Y.1 (Option.some.inj eI)
          simp only [Option.bind_some]
          cases f1 : P.Runs.firstRun x.1 x.2 with
          | none =>
            cases f2 : P.Runs.firstRun y.1 y.2 with
            | none => trivial
            | some v =>
              rw [f1, f2] at r
              exact r.elim
          | some u =>
            cases f2 : P.Runs.firstRun y.1 y.2 with
            | none =>
              rw [f1, f2] at r
              exact r.elim
            | some v =>
              rw [f1, f2] at r
              simp only [Option.bind_some]
              refine keys_between _ ?_ ?_ ?_ r.2
              · rw [X.2]
                exact hA
              · rw [Y.2]
                exact hB
              · rw [X.2, Y.2]
                exact geo_same e

/-- **The row "keys".** -/
theorem keys_row {A B : Attention.Plan} (e : stripPlan A = stripPlan B)
    (hA : P.padKeyOk (parCOf A).geo = true) (hB : P.padKeyOk (parCOf B).geo = true)
    (n : Nat) {c c' : ChainSh} (hc : stripC c = stripC c') :
    Alike YCs (k5KeysG A n c) (k5KeysG B n c') := by
  have eT := tabsGC_same e hc
  have r := keysBlank_rel e hA hB hc
  unfold k5KeysG
  rw [eT]
  split
  · cases h1 : keysBlank A c with
    | none =>
      cases h2 : keysBlank B c' with
      | none => exact Or.inr ⟨rfl, rfl⟩
      | some v =>
        rw [h1, h2] at r
        exact r.elim
    | some u =>
      cases h2 : keysBlank B c' with
      | none =>
        rw [h1, h2] at r
        exact r.elim
      | some v => exact Or.inl ⟨_, _, rfl, rfl, rfl, hc⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- **The row "join".** -/
theorem join_row {A B : Attention.Plan} (e : stripPlan A = stripPlan B)
    (hA : P.padKeyOk (parCOf A).geo = true) (hB : P.padKeyOk (parCOf B).geo = true)
    (n : Nat) {c c' : ChainSh} (hc : stripC c = stripC c') :
    Alike YCs (H2K5.Honest.k5JoinG A n c) (H2K5.Honest.k5JoinG B n c') := by
  have eT := tabsGC_same e hc
  have r := keysBlank_rel e hA hB hc
  have eL : c.led = c'.led := by
    have t := congrArg ChainSh.led hc
    exact t
  have eH : c.lookHeard.map stripH = c'.lookHeard.map stripH := by
    have t := congrArg ChainSh.lookHeard hc
    exact t
  unfold H2K5.Honest.k5JoinG
  rw [eT, ← eL]
  split
  · cases h1 : keysBlank A c with
    | none =>
      cases h2 : keysBlank B c' with
      | none =>
        cases c.led <;> cases c.lookHeard <;> cases c'.lookHeard <;> exact Or.inr ⟨rfl, rfl⟩
      | some v =>
        rw [h1, h2] at r
        exact r.elim
    | some u =>
      cases h2 : keysBlank B c' with
      | none =>
        rw [h1, h2] at r
        exact r.elim
      | some v =>
        rw [h1, h2] at r
        have ef : formsSh u = formsSh v := r
        have es : u.size = v.size := by
          have := congrArg List.length ef
          simpa [formsSh] using this
        cases hl : c.lookHeard with
        | none =>
          cases hl' : c'.lookHeard with
          | none =>
            cases c.led <;> exact Or.inr ⟨rfl, rfl⟩
          | some K' =>
            rw [hl, hl'] at eH
            cases eH
        | some K =>
          cases hl' : c'.lookHeard with
          | none =>
            rw [hl, hl'] at eH
            cases eH
          | some K' =>
            rw [hl, hl'] at eH
            have eK : stripH K = stripH K' := Option.some.inj eH
            have e1 : K.owedJoin = K'.owedJoin := by
              have t := congrArg HeardAll.owedJoin eK
              exact t
            have e2 : K.e = K'.e := by
              have t := congrArg HeardAll.e eK
              exact t
            have e3 : K.shape.calls.size = K'.shape.calls.size := by
              have := congrArg (fun z : HeardAll => z.shape.calls.size) eK
              simpa [stripH, stripF] using this
            have e4 : K.cEnd = K'.cEnd := by
              have t := congrArg HeardAll.cEnd eK
              exact t
            cases hd : c.led with
            | none => exact Or.inr ⟨rfl, rfl⟩
            | some L =>
              simp only []
              rw [e1, e2, e3, es]
              split
              · refine Or.inl ⟨_, _, rfl, rfl, ?_, ?_⟩
                · show [bareSh (H2K5.Honest.joinFormSh K (formsSh u))] =
                    [bareSh (H2K5.Honest.joinFormSh K' (formsSh v))]
                  unfold H2K5.Honest.joinFormSh
                  rw [ef, e4]
                · show stripC (c.setLed _) = stripC (c'.setLed _)
                  rw [← sC_setLed, ← sC_setLed, hc]
              · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.first_row
#print axioms Johnson.AtFull.Shape.Scope.second_row
#print axioms Johnson.AtFull.Shape.Scope.keys_row
#print axioms Johnson.AtFull.Shape.Scope.join_row
