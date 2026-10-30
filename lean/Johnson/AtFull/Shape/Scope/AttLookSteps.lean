-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/AttLookSteps.lean: THE LOOKUPS' TWO STEPS ON SHAPES UNDER THE RELATION RelX (Scope/Rel.lean),
AND THE TWO CELLS AT AN ATTENTION LINK. The lookup on the calls copies its record, with the calls' tables, into the
shape: at two records that are equal but for these tables the two steps go alike under RelX: `callsG_alike`. The
lookup on the digits has one record at both: `digitsG_alike`. So at an odd link l < 24 the cells at the places 2
and 7 go alike: `lookCalls_cell`, `lookDigits_cell`, in the form that Scope/Join.lean's steps_rel takes.

Limits. Implications under SameRead. Nothing says that a step returns. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.Scope.AttLookLetters
import Johnson.AtFull.Shape.Scope.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape (ChainSh HeardAll)
open VerifiableInference.Desc.K3 (faceOf)
open ProofFile.Honest.K3.Shape (lookHeardSh lookUpd)
open ProofFile.Honest.K3.Law.AtThr (callsG callsB callsU digitsG digitsB digitsU)

variable {X X₀ : Verify.Public}

/-! ## 1 What the steps read of a lookup's record -/

open VerifiableInference.Desc.K3 (Face keyOrders leafVars)
open VerifiableInference.Desc.First.Shape (PscSh LedSh)
open ProofFile.Honest.K3.Shape (lookOps keysOps keysSh heardVSh joinSh HeardVSh noSh)

/-- A reader that does not see the calls' tables answers alike at two records that are equal but for
these. -/
theorem fld {β : Type} {h h₀ : Forest.Shape} (e : stripF h = stripF h₀) (π : Forest.Shape → β)
    (hπ : ∀ z, π (stripF z) = π z) : π h = π h₀ := by
  rw [← hπ h, ← hπ h₀, e]

theorem size_of_strip {h h₀ : Forest.Shape} (e : stripF h = stripF h₀) :
    h.calls.size = h₀.calls.size := by
  have k := congrArg (fun z : Forest.Shape => z.calls.size) e
  simpa [stripF] using k

theorem elems_rel {h h₀ : Forest.Shape} (e : stripF h = stripF h₀) :
    Forest.elems h = Forest.elems h₀ := fld e Forest.elems fun _ => rfl

theorem keyOrders_rel {h h₀ : Forest.Shape} (e : stripF h = stripF h₀) :
    keyOrders h = keyOrders h₀ := fld e keyOrders fun _ => rfl

theorem keysOps_congr {f f' : Face} (ho : f.orders = f'.orders) :
    ∀ l : List (Nat × Nat), keysOps f l = keysOps f' l
  | [] => rfl
  | x :: xs => by
    simp only [keysOps, ho, keysOps_congr ho xs]

theorem keysSh_congr {f f' : Face} (ho : f.orders = f'.orders) (l : List (Nat × Nat)) :
    ∀ Cs rows n, keysSh f l Cs rows n = keysSh f' l Cs rows n := by
  induction l with
  | nil =>
    intro Cs rows n
    simp only [keysSh]
  | cons x xs ih =>
    intro Cs rows n
    cases Cs with
    | nil => simp only [keysSh]
    | cons C Cs => simp only [keysSh, ho, ih]

theorem lookOps_congr {f f' : Face} (h1 : f.planes = f'.planes) (h2 : f.parts = f'.parts)
    (h3 : f.mu = f'.mu) (h4 : f.d = f'.d) (ho : f.orders = f'.orders) :
    lookOps f = lookOps f' := by
  unfold lookOps leafVars
  rw [h1, h2, h3, h4, keysOps_congr ho]

theorem heardVSh_congr {f f' : Face} (h1 : f.planes = f'.planes) (h2 : f.parts = f'.parts)
    (h3 : f.mu = f'.mu) (h4 : f.d = f'.d) (ho : f.orders = f'.orders) (n : Nat) :
    heardVSh f n = heardVSh f' n := by
  unfold heardVSh joinSh leafVars
  simp only [h1, h2, h3, h4, keysSh_congr ho]

section
variable {h h₀ : Forest.Shape} (e : stripF h = stripF h₀)
include e

theorem face_parts : (faceOf h).parts = (faceOf h₀).parts :=
  congrArg (fun v => [v]) (fld e (·.v) fun _ => rfl)

theorem face_d : (faceOf h).d = (faceOf h₀).d := fld e (·.d) fun _ => rfl

theorem face_orders : (faceOf h).orders = (faceOf h₀).orders :=
  congrArg (fun k => fun _ : Nat => k) (keyOrders_rel e)

theorem lookUpd_rel (L : LedSh) : lookUpd (faceOf h) L = lookUpd (faceOf h₀) L := by
  unfold lookUpd
  rw [lookOps_congr (f := faceOf h) (f' := faceOf h₀) rfl (face_parts e) rfl (face_d e)
    (face_orders e)]

theorem heardVSh_rel (n : Nat) : heardVSh (faceOf h) n = heardVSh (faceOf h₀) n :=
  heardVSh_congr (f := faceOf h) (f' := faceOf h₀) rfl (face_parts e) rfl (face_d e)
    (face_orders e) n

end

/-- lookHeardSh's text, with what it reads of the record as letters. -/
def mkHeard (sh : Forest.Shape) (g : HeardVSh) (dT d NC rK : Nat) (iota : Array Nat) (sz o : Nat) :
    HeardAll :=
  let key := g.keys.headD (0, noSh)
  let zx := min dT key.1 - 0
  let zy := min key.1 key.1 - dT
  { shape := sh, rows := g.rows
    leaves := PscSh.mk false true ((List.range (5 + d)).map fun j => if j < d then 3 else 2)
      (5 + d) g.leavesFirst g.leavesStart false
    sBit := g.sBit, zx := zx, zy := zy, e := NC, cEnd := key.2, zb0 := 5 + d
    zb1 := 5 + d, tT := sz
    zk := (List.range NC).map fun c => (min zy zy - (rK - iota.getD c 0)) + zx
    owedObjects := o, owedPlanes := o + 1, owedJoin := o + 2 }

theorem lookHeardSh_mk (h : Forest.Shape) (n o : Nat) :
    lookHeardSh h n o =
      mkHeard h (heardVSh (faceOf h) n) h.dT h.d h.NC h.rK h.iota h.calls.size o := rfl

theorem stripH_mk (sh : Forest.Shape) (g : HeardVSh) (dT d NC rK : Nat) (iota : Array Nat)
    (sz o : Nat) :
    stripH (mkHeard sh g dT d NC rK iota sz o) = mkHeard (stripF sh) g dT d NC rK iota sz o := rfl

theorem heard_rel {h h₀ : Forest.Shape} (e : stripF h = stripF h₀) (n o : Nat) :
    stripH (lookHeardSh h n o) = stripH (lookHeardSh h₀ n o) := by
  rw [lookHeardSh_mk, lookHeardSh_mk, stripH_mk, stripH_mk, e, heardVSh_rel e,
    fld e (·.dT) fun _ => rfl, fld e (·.d) fun _ => rfl, fld e (·.NC) fun _ => rfl,
    fld e (·.rK) fun _ => rfl, fld e (·.iota) fun _ => rfl, size_of_strip e]

/-! ## 2 The lookup on the calls -/

theorem callsB_rel {h h₀ : Forest.Shape} (e : stripF h = stripF h₀) (f : Nat) {a a' : ShA}
    (r : RelX X X₀ a a') : callsB h f a.1 = callsB h₀ f a'.1 := by
  have hl : a.1.lookHeard.isNone = a'.1.lookHeard.isNone := by
    have k := congrArg Option.isNone r.lookHeard
    simpa using k
  unfold callsB
  rw [r.marked, r.rowsOwed, r.led, hl, elems_rel e]

theorem callsU_rel {h h₀ : Forest.Shape} (e : stripF h = stripF h₀) {a a' : ShA}
    (r : RelX X X₀ a a') : RelX X X₀ (callsU h a.1, a.2) (callsU h₀ a'.1, a'.2) := by
  have hl := r.led
  cases ha : a.1.led with
  | none =>
    have ha' : a'.1.led = none := by rw [← hl]; exact ha
    have e1 : callsU h a.1 = a.1 := by unfold callsU; rw [ha]
    have e2 : callsU h₀ a'.1 = a'.1 := by unfold callsU; rw [ha']
    rw [e1, e2]
    exact r
  | some Ld =>
    have ha' : a'.1.led = some Ld := by rw [← hl]; exact ha
    have e1 : callsU h a.1 = ChainSh.mk a.1.marked a.1.here a.1.tl (some (lookUpd (faceOf h) Ld))
        a.1.tables a.1.rowsOwed a.1.core a.1.reply a.1.indexMasks a.1.pile a.1.atEnd a.1.check
        a.1.link (if a.1.here == 3 then a.1.look else some (lookHeardSh h Ld.next Ld.owed.length))
        (some (lookHeardSh h Ld.next Ld.owed.length)) a.1.own a.1.head a.1.att a.1.fin := by
      unfold callsU; rw [ha]
    have e2 : callsU h₀ a'.1 = ChainSh.mk a'.1.marked a'.1.here a'.1.tl
        (some (lookUpd (faceOf h₀) Ld)) a'.1.tables a'.1.rowsOwed a'.1.core a'.1.reply
        a'.1.indexMasks a'.1.pile a'.1.atEnd a'.1.check a'.1.link
        (if a'.1.here == 3 then a'.1.look else some (lookHeardSh h₀ Ld.next Ld.owed.length))
        (some (lookHeardSh h₀ Ld.next Ld.owed.length)) a'.1.own a'.1.head a'.1.att a'.1.fin := by
      unfold callsU; rw [ha']
    rw [e1, e2]
    refine relX_of r.marked r.here r.tl (congrArg some (lookUpd_rel e Ld)) r.tables r.rowsOwed r.core
      r.reply r.indexMasks r.pile r.atEnd r.check r.link ?_
      (congrArg some (heard_rel e Ld.next Ld.owed.length)) r.own r.head r.att r.fin r.forms
    show (if a.1.here == 3 then a.1.look else some (lookHeardSh h Ld.next Ld.owed.length)).map stripH =
      (if a'.1.here == 3 then a'.1.look
        else some (lookHeardSh h₀ Ld.next Ld.owed.length)).map stripH
    rw [r.here]
    split
    · exact r.look
    · exact congrArg some (heard_rel e Ld.next Ld.owed.length)

/-- **THE LOOKUP ON THE CALLS, AT TWO RECORDS EQUAL BUT FOR THE CALLS' TABLES.** -/
theorem callsG_alike {h h₀ : Forest.Shape} (e : stripF h = stripF h₀) (f : Nat) {a a' : ShA}
    (r : RelX X X₀ a a') :
    Alike (RelX X X₀) (liftQ (callsG h f) a) (liftQ (callsG h₀ f) a') := by
  have hb := callsB_rel e f r
  by_cases hc : callsB h₀ f a'.1 = true
  · refine Or.inl ⟨(callsU h a.1, a.2), (callsU h₀ a'.1, a'.2), ?_, ?_, callsU_rel e r⟩
    · unfold liftQ callsG
      rw [hb, if_pos hc]
      rfl
    · unfold liftQ callsG
      rw [if_pos hc]
      rfl
  · refine Or.inr ⟨?_, ?_⟩
    · unfold liftQ callsG
      rw [hb, if_neg hc]
      rfl
    · unfold liftQ callsG
      rw [if_neg hc]
      rfl

/-! ## 3 The lookup on the digits -/

theorem digitsB_rel (h : Forest.Shape) (f u : Nat) {a a' : ShA} (r : RelX X X₀ a a') :
    digitsB h f u a.1 = digitsB h f u a'.1 := by
  unfold digitsB
  rw [r.marked, r.rowsOwed, r.tl, r.led]

theorem digitsU_rel (h : Forest.Shape) (c : Nat) {a a' : ShA} (r : RelX X X₀ a a') :
    RelX X X₀ (digitsU h c a.1, a.2) (digitsU h c a'.1, a'.2) := by
  have ht := r.tl
  have hl := r.led
  cases hT : a.1.tl with
  | none =>
    have hT' : a'.1.tl = none := by rw [← ht]; exact hT
    have e1 : digitsU h c a.1 = a.1 := by unfold digitsU; rw [hT]
    have e2 : digitsU h c a'.1 = a'.1 := by unfold digitsU; rw [hT']
    rw [e1, e2]
    exact r
  | some T =>
    have hT' : a'.1.tl = some T := by rw [← ht]; exact hT
    cases hL : a.1.led with
    | none =>
      have hL' : a'.1.led = none := by rw [← hl]; exact hL
      have e1 : digitsU h c a.1 = a.1 := by unfold digitsU; rw [hT, hL]
      have e2 : digitsU h c a'.1 = a'.1 := by unfold digitsU; rw [hT', hL']
      rw [e1, e2]
      exact r
    | some Ld =>
      have hL' : a'.1.led = some Ld := by rw [← hl]; exact hL
      rw [ProofFile.Honest.K3.Law.AtThr.digitsU_at hT hL, ProofFile.Honest.K3.Law.AtThr.digitsU_at hT' hL']
      exact relX_of r.marked r.here rfl rfl r.tables r.rowsOwed r.core r.reply r.indexMasks r.pile
        r.atEnd r.check r.link r.look r.lookHeard r.own r.head r.att r.fin r.forms

/-- **THE LOOKUP ON THE DIGITS, AT ONE RECORD.** -/
theorem digitsG_alike (h : Forest.Shape) (f u c : Nat) {a a' : ShA} (r : RelX X X₀ a a') :
    Alike (RelX X X₀) (liftQ (digitsG h f u c) a) (liftQ (digitsG h f u c) a') := by
  have hb := digitsB_rel h f u r
  by_cases hc : digitsB h f u a'.1 = true
  · refine Or.inl ⟨(digitsU h c a.1, a.2), (digitsU h c a'.1, a'.2), ?_, ?_, digitsU_rel h c r⟩
    · unfold liftQ digitsG
      rw [hb, if_pos hc]
      rfl
    · unfold liftQ digitsG
      rw [if_pos hc]
      rfl
  · refine Or.inr ⟨?_, ?_⟩
    · unfold liftQ digitsG
      rw [hb, if_neg hc]
      rfl
    · unfold liftQ digitsG
      rw [if_neg hc]
      rfl

/-! ## 4 The two cells at an attention link -/

theorem oddAt_link {l j : Nat} (hl : l < 24) (hj : j < 14) (ho : l % 2 = 1) :
    oddAt (14 * l + j + 1) = true := by
  have e : (14 * l + j + 1 - 1) / 14 = l := by omega
  unfold oddAt
  rw [e, ho]
  simp
  omega

theorem relAt_odd {n : Nat} (h : oddAt n = true) (a a' : ShA) :
    RelAt X X₀ n a a' = RelX X X₀ a a' := by
  unfold RelAt
  rw [if_pos h]

/-- A step that goes alike under RelX is a cell's first half between two borders inside an attention
link. -/
theorem cellRel_of_alike {l j : Nat} (hl : l < 24) (hj : j + 1 < 14) (ho : l % 2 = 1) {c c' : Cell}
    (h : ∀ a a', RelX X X₀ a a' → Alike (RelX X X₀) (c.1 a) (c'.1 a')) :
    CellRel X X₀ (14 * l + j + 1) c c' := by
  intro a a' r
  rw [relAt_odd (oddAt_link hl (by omega) ho)] at r
  have e : RelAt X X₀ (14 * l + j + 1 + 1) = RelX X X₀ := by
    funext b b'
    exact relAt_odd (oddAt_link (j := j + 1) hl hj ho) b b'
  rw [e]
  exact h a a' r

theorem refuse_alike (w w' : String) (a a' : ShA) :
    Alike (RelX X X₀) ((noCell w).1 a) ((noCell w').1 a') := Or.inr ⟨rfl, rfl⟩

theorem lookUC_same (S : SameRead X X₀) (l : Nat) : lookUC X l = lookUC X₀ l := by
  unfold lookUC
  rw [S.G]
  split
  · rfl
  · have e := congrArg (Option.map fun a : Attention.Plan => (a.nMsg, a.nLin)) (S.atA (l / 2))
    simpa [Option.map_map, Function.comp_def, stripPlan] using e

/-- **THE LOOKUP ON THE CALLS AT AN ATTENTION LINK.** -/
theorem lookCalls_cell (S : SameRead X X₀) {l : Nat} (hl : l < 24) (ho : l % 2 = 1) :
    CellRel X X₀ (14 * l + 2 + 1) ((TabL.linkRow (LW X) l).at 2) ((TabL.linkRow (LW X₀) l).at 2) := by
  refine cellRel_of_alike hl (by omega) ho fun a a' r => ?_
  show Alike (RelX X X₀) ((TabL.lookCalls (LW X) l).1 a) ((TabL.lookCalls (LW X₀) l).1 a')
  have e := lookOf_rel_odd S ho
  unfold TabL.lookCalls
  show Alike (RelX X X₀)
    ((match lookOf X l false with
      | some s => (liftQ (callsG s.1 s.2), noVals)
      | none => noCell "the lookup: no site").1 a)
    ((match lookOf X₀ l false with
      | some s => (liftQ (callsG s.1 s.2), noVals)
      | none => noCell "the lookup: no site").1 a')
  cases h1 : lookOf X l false with
  | none =>
    cases h2 : lookOf X₀ l false with
    | none => exact refuse_alike _ _ a a'
    | some t =>
      rw [h1, h2] at e
      cases e
  | some s =>
    cases h2 : lookOf X₀ l false with
    | none =>
      rw [h1, h2] at e
      cases e
    | some t =>
      rw [h1, h2] at e
      have k : stripLk s = stripLk t := Option.some.inj e
      have k1 : stripF s.1 = stripF t.1 := by
        have q := congrArg Prod.fst k
        exact q
      have k2 : s.2 = t.2 := by
        have q := congrArg Prod.snd k
        exact q
      show Alike (RelX X X₀) (liftQ (callsG s.1 s.2) a) (liftQ (callsG t.1 t.2) a')
      rw [k2]
      exact callsG_alike k1 t.2 r

/-- **THE LOOKUP ON THE DIGITS AT AN ATTENTION LINK.** -/
theorem lookDigits_cell (S : SameRead X X₀) {l : Nat} (hl : l < 24) (ho : l % 2 = 1) :
    CellRel X X₀ (14 * l + 7 + 1) ((TabL.linkRow (LW X) l).at 7) ((TabL.linkRow (LW X₀) l).at 7) := by
  refine cellRel_of_alike hl (by omega) ho fun a a' r => ?_
  show Alike (RelX X X₀) ((TabL.lookDigits (LW X) l).1 a) ((TabL.lookDigits (LW X₀) l).1 a')
  unfold TabL.lookDigits
  show Alike (RelX X X₀)
    ((match lookOf X l true, lookUC X l with
      | some s, some (u, c) => (liftQ (digitsG s.1 s.2 u c), noVals)
      | _, _ => noCell "the lookup on the digits: no site").1 a)
    ((match lookOf X₀ l true, lookUC X₀ l with
      | some s, some (u, c) => (liftQ (digitsG s.1 s.2 u c), noVals)
      | _, _ => noCell "the lookup on the digits: no site").1 a')
  rw [lookOf_digits S l, lookUC_same S l]
  cases lookOf X₀ l true with
  | none => exact refuse_alike _ _ a a'
  | some s =>
    cases lookUC X₀ l with
    | none => exact refuse_alike _ _ a a'
    | some q => exact digitsG_alike s.1 s.2 q.1 q.2 r

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.callsG_alike
#print axioms Johnson.AtFull.Shape.Scope.digitsG_alike
#print axioms Johnson.AtFull.Shape.Scope.lookCalls_cell
#print axioms Johnson.AtFull.Shape.Scope.lookDigits_cell
