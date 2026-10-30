-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/BatchRel.lean: THE BATCHING MEMBER's STEP ON SHAPES GOES ALIKE UNDER RelX
WHERE ITS RUNS DO, AND THE RUNS THAT READ NOTHING OF THE TABLES THAT look AND lookHeard CARRY.

  RC, YC       two chain's shapes equal but for those tables; the same of a run's value, with one
               list of claims' shapes.
  **RowAlike g g'**   two runs on shapes go alike under RC.
  drawG_rel, stepG_rel, gatherFrom_rel, laidG_rel, addsG_rel, batchG_rel, batchGS_rel.
  **cellG_rel**   a batching cell out of two lists of rows, pairwise alike.
  objects_alike, guests_alike, eq_alike   three rows.

Limits. Nothing is evaluated; no step is shown to return. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.Scope.AttChain
import Johnson.AtFull.Shape.BatchCellsAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K9 (SegSort Where)
open VerifiableInference.Desc.K9.Shape
open ProofFile.Honest.K3.Shape (objectsG guestsG heardShAt)

variable {X X₀ : Verify.Public}

/-- Two shapes equal but for the calls' tables in look and lookHeard. -/
def RC (a a' : ChainSh) : Prop := stripC a = stripC a'

/-- Two values of a run: one list of claims' shapes, and RC behind. -/
def YC (y y' : List ClaimSh × ChainSh) : Prop := y.1 = y'.1 ∧ RC y.2 y'.2

/-- **Two runs on shapes go alike.** -/
def RowAlike (g g' : Nat → ChainSh → Except String (List ClaimSh × ChainSh)) : Prop :=
  ∀ n c c', RC c c' → Alike YC (g n c) (g' n c')

namespace RC
variable {a a' : ChainSh}
theorem e (h : RC a a') : stripC a = stripC a' := h
theorem marked (h : RC a a') : a.marked = a'.marked := by
  have t := congrArg ChainSh.marked h.e
  exact t
theorem here (h : RC a a') : a.here = a'.here := by
  have t := congrArg ChainSh.here h.e
  exact t
theorem tl (h : RC a a') : a.tl = a'.tl := by
  have t := congrArg ChainSh.tl h.e
  exact t
theorem led (h : RC a a') : a.led = a'.led := by
  have t := congrArg ChainSh.led h.e
  exact t
theorem tables (h : RC a a') : a.tables = a'.tables := by
  have t := congrArg ChainSh.tables h.e
  exact t
theorem rowsOwed (h : RC a a') : a.rowsOwed = a'.rowsOwed := by
  have t := congrArg ChainSh.rowsOwed h.e
  exact t
theorem link (h : RC a a') : a.link = a'.link := by
  have t := congrArg ChainSh.link h.e
  exact t
theorem head (h : RC a a') : a.head = a'.head := by
  have t := congrArg ChainSh.head h.e
  exact t
theorem lookHeard (h : RC a a') : a.lookHeard.map stripH = a'.lookHeard.map stripH := by
  have t := congrArg ChainSh.lookHeard h.e
  exact t

theorem core (h : RC a a') : a.core = a'.core := by
  have t := congrArg ChainSh.core h.e
  exact t
theorem reply (h : RC a a') : a.reply = a'.reply := by
  have t := congrArg ChainSh.reply h.e
  exact t
theorem indexMasks (h : RC a a') : a.indexMasks = a'.indexMasks := by
  have t := congrArg ChainSh.indexMasks h.e
  exact t
theorem pile (h : RC a a') : a.pile = a'.pile := by
  have t := congrArg ChainSh.pile h.e
  exact t
theorem atEnd (h : RC a a') : a.atEnd = a'.atEnd := by
  have t := congrArg ChainSh.atEnd h.e
  exact t
theorem check (h : RC a a') : a.check = a'.check := by
  have t := congrArg ChainSh.check h.e
  exact t
theorem look (h : RC a a') : a.look.map stripH = a'.look.map stripH := by
  have t := congrArg ChainSh.look h.e
  exact t
theorem own (h : RC a a') : a.own = a'.own := by
  have t := congrArg ChainSh.own h.e
  exact t
theorem att (h : RC a a') : a.att = a'.att := by
  have t := congrArg ChainSh.att h.e
  exact t
theorem fin (h : RC a a') : a.fin = a'.fin := by
  have t := congrArg ChainSh.fin h.e
  exact t

/-- From the components. -/
theorem of (h1 : a.marked = a'.marked) (h2 : a.here = a'.here) (h3 : a.tl = a'.tl)
    (h4 : a.led = a'.led) (h5 : a.tables = a'.tables) (h6 : a.rowsOwed = a'.rowsOwed)
    (h7 : a.core = a'.core) (h8 : a.reply = a'.reply) (h9 : a.indexMasks = a'.indexMasks)
    (h10 : a.pile = a'.pile) (h11 : a.atEnd = a'.atEnd) (h12 : a.check = a'.check)
    (h13 : a.link = a'.link) (h14 : a.look.map stripH = a'.look.map stripH)
    (h15 : a.lookHeard.map stripH = a'.lookHeard.map stripH) (h16 : a.own = a'.own)
    (h17 : a.head = a'.head) (h18 : a.att = a'.att) (h19 : a.fin = a'.fin) : RC a a' := by
  unfold RC stripC
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]

theorem setLed (h : RC a a') (L : LedSh) : RC (a.setLed L) (a'.setLed L) :=
  .of h.marked h.here h.tl (congrArg (Option.map fun _ => L) h.led) h.tables h.rowsOwed h.core
    h.reply h.indexMasks h.pile h.atEnd h.check h.link h.look h.lookHeard h.own h.head h.att h.fin

theorem setLink (h : RC a a') (L : LinkSh) : RC (a.setLink L) (a'.setLink L) :=
  .of h.marked h.here h.tl h.led h.tables h.rowsOwed h.core h.reply h.indexMasks h.pile h.atEnd
    h.check (congrArg (Option.map fun _ => L) h.link) h.look h.lookHeard h.own h.head h.att h.fin

theorem setRowsOwed (h : RC a a') (r : Option Nat) : RC (a.setRowsOwed r) (a'.setRowsOwed r) :=
  .of h.marked h.here h.tl h.led h.tables rfl h.core h.reply h.indexMasks h.pile h.atEnd h.check
    h.link h.look h.lookHeard h.own h.head h.att h.fin

theorem setTl (h : RC a a') (t : TailSh) : RC (a.setTl t) (a'.setTl t) :=
  .of h.marked h.here (congrArg (Option.map fun _ => t) h.tl) h.led h.tables h.rowsOwed h.core
    h.reply h.indexMasks h.pile h.atEnd h.check h.link h.look h.lookHeard h.own h.head h.att h.fin

theorem owedSh (h : RC a a') : owedSh a = owedSh a' := by
  unfold VerifiableInference.Desc.K9.Shape.owedSh
  rw [h.rowsOwed]

theorem usedSh (h : RC a a') : usedSh a = usedSh a' := by
  unfold VerifiableInference.Desc.K9.Shape.usedSh
  rw [h.here, h.tl, h.led, h.head]

theorem thereB (h : RC a a') : thereB a = thereB a' := by
  unfold VerifiableInference.Desc.K9.Shape.thereB
  rw [h.link, h.led, h.tl, h.usedSh]

end RC

/-- Two results: the frame's binding. -/
theorem alike_bind {α β γ δ : Type} {S : α → β → Prop} {R : γ → δ → Prop}
    {x : Except String α} {y : Except String β} {f : α → Except String γ}
    {f' : β → Except String δ} (h : Alike S x y)
    (hf : ∀ b b', S b b' → Alike R (f b) (f' b')) : Alike R (x.bind f) (y.bind f') := by
  rcases h with ⟨b, b', rfl, rfl, hs⟩ | ⟨h1, h2⟩
  · exact hf b b' hs
  · cases x with
    | ok _ => cases h1
    | error e =>
      cases y with
      | ok _ => cases h2
      | error e' => exact Or.inr ⟨rfl, rfl⟩

theorem alike_ok {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Alike R (.ok a) (.ok b) := Or.inl ⟨a, b, rfl, rfl, h⟩

theorem alike_err {α β : Type} {R : α → β → Prop} (e e' : String) :
    Alike R (.error e : Except String α) (.error e' : Except String β) := Or.inr ⟨rfl, rfl⟩

/-! ## The batching's member -/

theorem drawG_rel (rows : Nat) {a a' : ChainSh} (h : RC a a') :
    Alike RC (drawG rows a) (drawG rows a') := by
  unfold drawG
  rw [h.link, h.led, h.tl, h.usedSh, h.owedSh]
  split
  · split
    · exact alike_ok (((h.setLink _).setLed _).setRowsOwed _)
    · exact alike_err _ _
  · exact alike_err _ _

theorem eachS_rel (k : SegSort) (o : Nat × String) (cs : List ClaimSh) {a a' : ChainSh}
    (h : RC a a') : eachS k o cs a = eachS k o cs a' := by
  unfold eachS
  rw [h.tl]

theorem stepG_rel (k : SegSort)
    {g g' : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)}
    (hg : ∀ o, RowAlike (g o) (g' o)) {x x' : List ClaimSh × ChainSh} (hx : YC x x')
    (o : Nat × String) : Alike YC (VerifiableInference.Desc.K9.Shape.stepG k g x o)
      (VerifiableInference.Desc.K9.Shape.stepG k g' x' o) := by
  unfold VerifiableInference.Desc.K9.Shape.stepG
  rw [hx.1]
  refine alike_bind (hg o _ _ _ hx.2) fun y y' hy => ?_
  rw [hy.1, eachS_rel k o y'.1 hy.2]
  split
  · exact alike_ok ⟨rfl, hy.2⟩
  · exact alike_err _ _

theorem gatherFrom_rel (k : SegSort)
    {g g' : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)}
    (hg : ∀ o, RowAlike (g o) (g' o)) : ∀ (os : List (Nat × String))
    {x x' : List ClaimSh × ChainSh}, YC x x' →
      Alike YC (gatherFrom k g os x) (gatherFrom k g' os x')
  | [], _, _, hx => alike_ok hx
  | o :: os, _, _, hx =>
    alike_bind (stepG_rel k hg hx o) fun _ _ hy => gatherFrom_rel k hg os hy

theorem laidG_rel {y y' : List ClaimSh × ChainSh} (hy : YC y y') :
    Alike RC (laidG y) (laidG y') := by
  unfold laidG
  rw [hy.2.thereB, hy.2.led, hy.1, hy.2.owedSh]
  split
  · split
    · exact alike_ok ((hy.2.setLed _).setRowsOwed _)
    · exact alike_err _ _
  · exact alike_err _ _

theorem addsG_rel (k : SegSort)
    {g g' : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)}
    (hg : ∀ o, RowAlike (g o) (g' o)) (order : List (Nat × String)) {a a' : ChainSh}
    (h : RC a a') : Alike RC (addsG k g order a) (addsG k g' order a') := by
  unfold addsG
  rw [h.thereB, h.link]
  split
  · exact alike_bind (gatherFrom_rel k hg order ⟨rfl, h⟩) fun _ _ hy => laidG_rel hy
  · exact alike_err _ _

theorem batchGS_rel (rows : Nat) (k : SegSort)
    {g g' : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)}
    (hg : ∀ o, RowAlike (g o) (g' o)) (order : List (Nat × String)) {a a' : ChainSh}
    (h : RC a a') : Alike RC (batchGS rows k g order a) (batchGS rows k g' order a') := by
  unfold batchGS batchG
  refine alike_bind (alike_bind (drawG_rel rows h) fun _ _ hb => addsG_rel k hg order hb)
    fun u u' hu => ?_
  rw [hu.marked]
  split
  · exact alike_err _ _
  · exact alike_ok hu

/-- Two lists of rows under one list of names, pairwise alike. -/
def RowsAlike (rows rows' : List ((Nat × String) × Row)) : Prop :=
  List.Forall₂ (fun r r' => r.1 = r'.1 ∧ RowAlike r.2.g r'.2.g) rows rows'

theorem tabOf_alike {rows rows' : List ((Nat × String) × Row)} (h : RowsAlike rows rows')
    (o : Nat × String) : RowAlike (tabOf rows o).g (tabOf rows' o).g := by
  unfold tabOf
  induction h with
  | nil => exact fun _ _ _ _ => alike_err _ _
  | @cons x x' xs xs' hx _ ih =>
    obtain ⟨k, r⟩ := x
    obtain ⟨k', r'⟩ := x'
    obtain ⟨e, hr⟩ := hx
    have e' : k = k' := e
    subst e'
    simp only [List.lookup]
    split
    · exact hr
    · exact ih

/-- **THE BATCHING CELL GOES ALIKE.** -/
theorem cellG_rel (p : Where) (k : SegSort) {rows rows' : List ((Nat × String) × Row)}
    (h : RowsAlike rows rows') (order : List (Nat × String)) {x x' : ShA}
    (hx : RelX X X₀ x x') :
    Alike (RelX X X₀) (cellG p k rows order x) (cellG p k rows' order x') := by
  unfold cellG liftQ
  have r := batchGS_rel p.rows k (fun o => tabOf_alike h o) order (relC hx)
  rcases r with ⟨b, b', e1, e2, hb⟩ | ⟨h1, h2⟩
  · rw [e1, e2]
    exact Or.inl ⟨_, _, rfl, rfl, rel_of hb hx.forms⟩
  · cases e1 : batchGS p.rows k (fun o => (tabOf rows o).g) order x.1 with
    | ok _ =>
      rw [e1] at h1
      cases h1
    | error _ =>
      cases e2 : batchGS p.rows k (fun o => (tabOf rows' o).g) order x'.1 with
      | ok _ =>
        rw [e2] at h2
        cases h2
      | error _ => exact Or.inr ⟨rfl, rfl⟩

/-! ## Three rows -/

theorem guests_alike : RowAlike guestsG guestsG := fun _ _ _ h => alike_ok ⟨rfl, h⟩

theorem heardShAt_rel (d : Bool) {a a' : ChainSh} (h : RC a a') :
    (heardShAt d a).map stripH = (heardShAt d a').map stripH := by
  unfold heardShAt
  cases d
  · exact h.lookHeard
  · simp only [if_true]
    rw [h.tl]

theorem objects_alike (d : Bool) : RowAlike (objectsG d) (objectsG d) := by
  intro n c c' h
  have hh := heardShAt_rel d h
  unfold objectsG
  rw [h.led]
  cases e1 : heardShAt d c with
  | none =>
    cases e2 : heardShAt d c' with
    | none => cases c'.led <;> exact alike_err _ _
    | some _ =>
      rw [e1, e2] at hh
      cases hh
  | some g =>
    cases e2 : heardShAt d c' with
    | none =>
      rw [e1, e2] at hh
      cases hh
    | some g' =>
      rw [e1, e2] at hh
      have eg : stripH g = stripH g' := Option.some.inj hh
      have er : g.rows = g'.rows := by
        have t := congrArg HeardAll.rows eg
        exact t
      have eo : g.owedObjects = g'.owedObjects := by
        have t := congrArg HeardAll.owedObjects eg
        exact t
      cases c'.led with
      | none => exact alike_err _ _
      | some L =>
        show Alike YC (.ok (g.rows.map _, c.setLed (L.setOwed (paidB L.owed g.owedObjects))))
          (.ok (g'.rows.map _, c'.setLed (L.setOwed (paidB L.owed g'.owedObjects))))
        rw [er, eo]
        exact alike_ok ⟨rfl, h.setLed _⟩

theorem eqG_rel (n : Nat) {a a' : ChainSh} (h : RC a a') :
    Alike RC (VerifiableInference.Desc.First.K8.Honest.eqG n a)
      (VerifiableInference.Desc.First.K8.Honest.eqG n a') := by
  unfold VerifiableInference.Desc.First.K8.Honest.eqG
  rw [h.tl, h.led, h.tables]
  split
  · split
    · split
      · exact alike_ok ((h.setTl _).setLed _)
      · exact alike_err _ _
    · exact alike_err _ _
  · exact alike_err _ _

theorem eq_alike : RowAlike VerifiableInference.Desc.First.K8.Honest.eqRunG
    VerifiableInference.Desc.First.K8.Honest.eqRunG := by
  intro n c c' h
  unfold VerifiableInference.Desc.First.K8.Honest.eqRunG
  refine alike_bind (eqG_rel n h) fun t t' ht => ?_
  have e : VerifiableInference.Desc.First.K8.Honest.eqClaimsG c t =
      VerifiableInference.Desc.First.K8.Honest.eqClaimsG c' t' := by
    unfold VerifiableInference.Desc.First.K8.Honest.eqClaimsG
    rw [h.tl, h.tables, RC.tl ht, RC.led ht]
  rw [e]
  split
  · exact alike_ok ⟨rfl, ht⟩
  · exact alike_err _ _

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.eq_alike
#print axioms Johnson.AtFull.Shape.Scope.cellG_rel
#print axioms Johnson.AtFull.Shape.Scope.objects_alike
#print axioms Johnson.AtFull.Shape.Scope.guests_alike
