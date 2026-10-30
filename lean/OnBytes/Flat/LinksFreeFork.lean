-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeFork.lean: two states of a sub-proof's check that differ only in two parts of
the one equation.

The check of the head reads the request, and from its first claim that holds a value made of the
request the state of the check (`Fork`, OnBytes/Model/Hide.lean) differs from request to request, in
a dry run too. The claims are added up in the weights L on the virtual rows, the coefficients LS on
the slots and the constant c0. In what was read of the program's text (the head's forms and claims,
OnBytes/Model/HeadForms.lean and Head.lean, and the reads of the smallness test,
OnBytes/Model/Tail.lean) a value made of the request stands in a form's constant or among the
weights of a run on a row, never in a coefficient on a slot. So the relation leaves L and c0 free
and asks that LS is equal; `Fork.settle` refuses by whether a coefficient of LS is 0, so it matters.
This file has the relation and shows that the steps which add a claim keep it.

Main definitions: `eraseRow`, `eraseTree` (an array without the weights L: zeros, as many);
`ForkAlike` (all fields are equal but trees and c0; the arrays agree without their weights);
`AffAlike` (two forms name the same entries and have one part on the slots; the entries'
coefficients and the constant are free); `Run2Alike`; `cmpA`, `cmpLA` (how two routines are compared
from two states that are alike: `Cmp.state`, OnBytes/Flat/DryRel.lean). Main theorems: `push_alike`,
`kap_alike`, `lin_alike`, `pushRuns_alike`: at two states and two forms or lists of runs that are
alike both steps refuse or both go through, and the states left are alike. `change_rel`, `take_rel`,
`ask_rel`: the three doors through which a routine reaches the state. `trees_read`, `trees_size`:
what does not look at the weights is the same in both.

Not claimed: that no routine puts a value made of the request on a slot: whoever compares two
routines has to show `AffAlike` of their forms. Nothing on a step that reads a weight or the
constant back. Nothing on a run on a view. For proofs only; no module of the program imports this
file.


-/
import OnBytes.Flat.LinksFreeLayer

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model

/-! ## The relation -/

/-- A virtual row without the weights that the claims have put on its entries: zeros, as many. -/
def eraseRow (r : HRow) : HRow := { r with L := Array.replicate r.L.size zeroE }

/-- An array without these weights. -/
def eraseTree (X : HTree) : HTree := { X with rows := X.rows.map eraseRow }

/-- **Two states of a sub-proof's check are alike**: they agree in all but two parts of the one
equation: the weights L on the virtual rows, of which there are as many, and the constant c0. The
coefficients LS on the slots are equal. -/
def ForkAlike (F F' : Fork) : Prop :=
  F' = { F with trees := F'.trees, c0 := F'.c0 } ∧ F.trees.map eraseTree = F'.trees.map eraseTree

theorem ForkAlike.refl (F : Fork) : ForkAlike F F := ⟨rfl, rfl⟩

/-- Two forms name the same entries and have the same part on the slots; the entries' coefficients
and the constant are free. -/
def AffAlike (a a' : Aff) : Prop :=
  a.ents.toList.map (fun x => (x.tree, x.row, x.idx)) =
      a'.ents.toList.map (fun x => (x.tree, x.row, x.idx)) ∧
    a.slots = a'.slots

theorem AffAlike.refl (a : Aff) : AffAlike a a := ⟨rfl, rfl⟩

/-! ## Arrays -/

theorem map_modify_of {α β : Type} (g : α → β) (f : α → α) (h : ∀ x, g (f x) = g x)
    (a : Array α) (i : Nat) : (a.modify i f).map g = a.map g := by
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_map, Array.getElem_modify]
    split
    · exact h _
    · rfl

theorem eraseRow_modify (r : HRow) (k : Nat) (h : E → E) :
    eraseRow { r with L := r.L.modify k h } = eraseRow r := by
  unfold eraseRow
  simp only [Array.size_modify]

theorem eraseTree_modify (X : HTree) (row : Nat) (h : E → E) (kk : HRow → Nat) :
    eraseTree { X with rows := X.rows.modify row fun r => { r with L := r.L.modify (kk r) h } } =
      eraseTree X := by
  unfold eraseTree
  simp only [map_modify_of eraseRow _ (fun r => eraseRow_modify r (kk r) h)]

theorem hasEnt_erase (T : Array HTree) (x : Ent) :
    Fork.hasEnt (T.map eraseTree) x = Fork.hasEnt T x := by
  unfold Fork.hasEnt
  simp only [Array.getElem?_map]
  cases T[x.tree]? with
  | none => rfl
  | some X =>
    simp only [Option.map_some, eraseTree, Array.getElem?_map]
    cases X.rows[x.row]? with
    | none => rfl
    | some r => simp only [Option.map_some, eraseRow, Array.size_replicate]

theorem optRel_map' {α β : Type} {R : α → α → Prop} {S : β → β → Prop} {x x' : Option α}
    {f f' : α → β} (hx : OptRel R x x') (hf : ∀ a a', R a a' → S (f a) (f' a')) :
    OptRel S (x.map f) (x'.map f') := by
  cases x <;> cases x'
  · trivial
  · exact hx.elim
  · exact hx.elim
  · exact hf _ _ hx

/-! ## Adding a form to the one equation -/

/-- What a form's entry names. -/
abbrev entKey (x : Ent) : Nat × Nat × Nat := (x.tree, x.row, x.idx)

theorem hasEnt_key (T : Array HTree) {x x' : Ent} (h : entKey x = entKey x') :
    Fork.hasEnt T x = Fork.hasEnt T x' := by
  have h1 : x.tree = x'.tree := congrArg (·.1) h
  have h2 : x.row = x'.row := congrArg (·.2.1) h
  have h3 : x.idx = x'.idx := congrArg (·.2.2) h
  unfold Fork.hasEnt
  rw [h1, h2, h3]

theorem pushEnt_alike (w w' : E) {T T' : Array HTree} (hT : T.map eraseTree = T'.map eraseTree)
    {x x' : Ent} (h : entKey x = entKey x') :
    OptRel (fun U U' => U.map eraseTree = U'.map eraseTree) (Fork.pushEnt w T x)
      (Fork.pushEnt w' T' x') := by
  have e : Fork.hasEnt T x = Fork.hasEnt T' x' := by
    rw [← hasEnt_erase T, hT, hasEnt_erase, hasEnt_key T' h]
  unfold Fork.pushEnt
  rw [e]
  split
  · show Array.map _ _ = Array.map _ _
    rw [map_modify_of eraseTree _ (fun X => eraseTree_modify X _ _ _),
      map_modify_of eraseTree _ (fun X => eraseTree_modify X _ _ _), hT]
  · trivial

theorem foldlM_pushEnt (w w' : E) : ∀ (l l' : List Ent) (T T' : Array HTree),
    l.map entKey = l'.map entKey → T.map eraseTree = T'.map eraseTree →
    OptRel (fun U U' => U.map eraseTree = U'.map eraseTree) (l.foldlM (Fork.pushEnt w) T)
      (l'.foldlM (Fork.pushEnt w') T')
  | [], [], _, _, _, hT => hT
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h
  | x :: l, x' :: l', T, T', h, hT => by
      rw [List.foldlM_cons, List.foldlM_cons]
      simp only [List.map_cons, List.cons.injEq] at h
      exact optRel_bind (pushEnt_alike w w' hT h.1)
        fun U U' hU => foldlM_pushEnt w w' l l' U U' h.2 hU

/-- **`Fork.push` at two states and two forms that are alike, under one weight.** -/
theorem push_alike {F F' : Fork} (hF : ForkAlike F F') (w : E) {a a' : Aff}
    (ha : AffAlike a a') : OptRel ForkAlike (F.push w a) (F'.push w a') := by
  obtain ⟨e, hT⟩ := hF
  generalize F'.trees = T' at e hT
  generalize F'.c0 = c' at e
  subst e
  unfold Fork.push
  dsimp only
  split
  · trivial
  · have h1 := foldlM_pushEnt w w _ _ _ _ ha.1 hT
    rw [← ha.2, ← Array.foldlM_toList (xs := a.ents), ← Array.foldlM_toList (xs := a'.ents)]
    revert h1
    generalize List.foldlM (Fork.pushEnt w) F.trees a.ents.toList = r1
    generalize List.foldlM (Fork.pushEnt w) T' a'.ents.toList = r1'
    generalize Array.foldlM (Fork.pushSlot w F.ns) F.LS a.slots = r2
    intro h1
    cases r1 <;> cases r1' <;> cases r2 <;>
      first
        | trivial
        | exact h1.elim
        | exact ⟨rfl, h1⟩

/-! ## Adding runs of weights -/

theorem eraseTree_newL (X : HTree) (row : Nat) (h : HRow → Array E)
    (hh : ∀ r, (h r).size = r.L.size) :
    eraseTree { X with rows := X.rows.modify row fun r => { r with L := h r } } = eraseTree X := by
  have e : ∀ r : HRow, eraseRow { r with L := h r } = eraseRow r := by
    intro r
    unfold eraseRow
    dsimp only
    rw [hh r]
  unfold eraseTree
  dsimp only
  rw [map_modify_of eraseRow _ e]

theorem size_runLoop (kc : E) (w : Array E) (w0 first : Nat) :
    ∀ (count i : Nat) (L : Array E), (runLoop kc w w0 first count i L).size = L.size
  | 0, _, _ => rfl
  | count + 1, i, L => by
      unfold runLoop
      dsimp only
      rw [size_runLoop kc w w0 first count]
      split
      · rfl
      · exact Array.size_modify

/-- Two runs name the same entries; the factor and the weights are free, the vectors of weights
have one size. -/
def Run2Alike (r r' : Run2) : Prop :=
  r.tree = r'.tree ∧ r.row = r'.row ∧ r.first = r'.first ∧ r.w0 = r'.w0 ∧ r.n = r'.n ∧
    r.w.size = r'.w.size

theorem Run2Alike.refl (r : Run2) : Run2Alike r r := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem runFits_erase (T : Array HTree) (r : Run2) :
    runFits (T.map eraseTree) r = runFits T r := by
  unfold runFits
  simp only [Array.getElem?_map]
  cases T[r.tree]? with
  | none => rfl
  | some X =>
    simp only [Option.map_some, eraseTree, Array.getElem?_map]
    cases X.rows[r.row]? with
    | none => rfl
    | some R => simp only [Option.map_some, eraseRow, Array.size_replicate]

theorem runFits_alike (T : Array HTree) {r r' : Run2} (h : Run2Alike r r') :
    runFits T r = runFits T r' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold runFits
  rw [h1, h2, h3, h4, h5, h6]

theorem pushRun_alike (k k' : E) {T T' : Array HTree} (hT : T.map eraseTree = T'.map eraseTree)
    {r r' : Run2} (h : Run2Alike r r') :
    OptRel (fun U U' => U.map eraseTree = U'.map eraseTree) (pushRun k T r) (pushRun k' T' r') := by
  have e : runFits T r = runFits T' r' := by
    rw [← runFits_erase T, hT, runFits_erase, runFits_alike T' h]
  unfold pushRun
  rw [e]
  split
  · show Array.map _ _ = Array.map _ _
    rw [map_modify_of eraseTree _ (fun X => eraseTree_newL X _ _ fun R => size_runLoop ..),
      map_modify_of eraseTree _ (fun X => eraseTree_newL X _ _ fun R => size_runLoop ..), hT]
  · trivial

theorem foldlM_pushRun (k k' : E) {l l' : List Run2} (h : All2 Run2Alike l l') :
    ∀ (T T' : Array HTree), T.map eraseTree = T'.map eraseTree →
    OptRel (fun U U' => U.map eraseTree = U'.map eraseTree) (l.foldlM (pushRun k) T)
      (l'.foldlM (pushRun k') T') := by
  induction h with
  | nil => exact fun _ _ hT => hT
  | cons h0 _ ih =>
    intro T T' hT
    rw [List.foldlM_cons, List.foldlM_cons]
    exact optRel_bind (pushRun_alike k k' hT h0) fun U U' hU => ih U U' hU

/-- **`Fork.pushRuns` at two states and two lists of runs that are alike, under any two
weights.** -/
theorem pushRuns_alike {F F' : Fork} (hF : ForkAlike F F') (k k' : E) {runs runs' : Array Run2}
    (h : All2 Run2Alike runs.toList runs'.toList) :
    OptRel ForkAlike (F.pushRuns k runs) (F'.pushRuns k' runs') := by
  obtain ⟨e, hT⟩ := hF
  generalize F'.trees = T' at e hT
  generalize F'.c0 = c' at e
  subst e
  unfold Fork.pushRuns
  dsimp only
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  exact optRel_map' (foldlM_pushRun k k' h _ _ hT) fun _ _ hU => ⟨rfl, hU⟩

/-! ## What is read of the arrays -/

/-- What does not look at the weights is the same in the arrays of two states that are alike. -/
theorem trees_read {T T' : Array HTree} (h : T.map eraseTree = T'.map eraseTree) {β : Type}
    (φ : Option HTree → β) (hφ : ∀ o, φ (o.map eraseTree) = φ o) (i : Nat) :
    φ T[i]? = φ T'[i]? := by
  have h0 := congrArg (fun A => A[i]?) h
  simp only [Array.getElem?_map] at h0
  rw [← hφ T[i]?, h0, hφ]

theorem trees_size {T T' : Array HTree} (h : T.map eraseTree = T'.map eraseTree) :
    T.size = T'.size := by
  have h0 := congrArg Array.size h
  simpa only [Array.size_map] using h0

/-! ## The layers above blocks, with states that are alike -/

/-- How two routines of a sub-proof's check are compared: from two states that are alike. -/
abbrev cmpA : Cmp SubM := Cmp.state ForkAlike Cmp.blk

/-- How two routines of a link are compared: from one context of the link and two such states. -/
abbrev cmpLA : Cmp LinkM := Cmp.state Eq cmpA

/-- `SubM.change` at two steps that keep states alike. -/
theorem change_rel {f f' : Fork → Option Fork}
    (h : ∀ F F', ForkAlike F F' → OptRel ForkAlike (f F) (f' F')) :
    cmpA.Rel Eq (SubM.change f) (SubM.change f') := by
  intro F F' hF c _
  have h0 := h F F' hF
  unfold SubM.change
  revert h0
  cases f F <;> cases f' F' <;> intro h0
  · trivial
  · exact h0.elim
  · exact h0.elim
  · exact ⟨⟨rfl, h0⟩, rfl⟩

/-- `SubM.take` likewise, with values in R. -/
theorem take_rel {α : Type} {R : α → α → Prop} {f f' : Fork → Option (α × Fork)}
    (h : ∀ F F', ForkAlike F F' →
      OptRel (fun x x' => R x.1 x'.1 ∧ ForkAlike x.2 x'.2) (f F) (f' F')) :
    cmpA.Rel R (SubM.take f) (SubM.take f') := by
  intro F F' hF c _
  have h0 := h F F' hF
  unfold SubM.take
  revert h0
  cases f F <;> cases f' F' <;> intro h0
  · trivial
  · exact h0.elim
  · exact h0.elim
  · exact ⟨h0, rfl⟩

/-- `SubM.ask` likewise. -/
theorem ask_rel {α : Type} {R : α → α → Prop} {f f' : Fork → Option α}
    (h : ∀ F F', ForkAlike F F' → OptRel R (f F) (f' F')) :
    cmpA.Rel R (SubM.ask f) (SubM.ask f') := by
  intro F F' hF c _
  have h0 := h F F' hF
  unfold SubM.ask
  revert h0
  cases f F <;> cases f' F' <;> intro h0
  · trivial
  · exact h0.elim
  · exact h0.elim
  · exact ⟨⟨h0, hF⟩, rfl⟩

/-! ## The steps on the state that do not read the coefficients -/

theorem kapTake_alike {F F' : Fork} (h : ForkAlike F F') (c : Nat) :
    OptRel (fun x x' => x.1 = x'.1 ∧ ForkAlike x.2 x'.2) (F.kapTake c) (F'.kapTake c) := by
  obtain ⟨e, hT⟩ := h
  generalize F'.trees = T' at e hT
  generalize F'.c0 = c' at e
  subst e
  unfold Fork.kapTake Fork.kapAt
  dsimp only
  repeat' split
  all_goals first
    | trivial
    | exact ⟨rfl, rfl, hT⟩

theorem kap_alike {F F' : Fork} (h : ForkAlike F F') :
    OptRel (fun x x' => x.1 = x'.1 ∧ ForkAlike x.2 x'.2) F.kap F'.kap := by
  have e : F'.nClaim = F.nClaim := by rw [h.1]
  have h0 := kapTake_alike h F.nClaim
  unfold Fork.kap
  rw [e]
  revert h0
  cases F.kapTake F.nClaim <;> cases F'.kapTake F.nClaim <;> intro h0
  · trivial
  · exact h0.elim
  · exact h0.elim
  · rename_i x x'
    obtain ⟨k, G⟩ := x
    obtain ⟨k', G'⟩ := x'
    obtain ⟨h1, h2, h3⟩ := h0
    dsimp only at h1 h2 h3
    generalize G'.trees = T' at h2 h3
    generalize G'.c0 = c' at h2
    subst h2
    exact ⟨h1, rfl, h3⟩

/-- **`Fork.lin` at two states and two forms that are alike.** -/
theorem lin_alike {F F' : Fork} (h : ForkAlike F F') {a a' : Aff} (ha : AffAlike a a') :
    OptRel ForkAlike (F.lin a) (F'.lin a') :=
  optRel_bind (kap_alike h) fun x x' k => by
    rw [← k.1]
    exact push_alike k.2 _ ha

end OnBytes.Flat
