-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeHeadE.lean: the two tests of the smallness test on its own claims
(`HTailF2.selfTestF`, `HTailF2.tileSelfTestF`, OnBytes/Model/Tail.lean) at two requests.

These routines read the weights L back from the state, which differ from request to request. What
they make of them goes two ways. A comparison of values goes to `testAs`, which a dry run skips:
there any two answers serve (`ask_any`, `testAs_any`). A question on shapes goes to `mustAs`, which
a dry run does not skip: there the answer is shown to be the same, because it reads of an array only
what two arrays share that agree without their weights (`tree_fields`: name, kind, numbers of rows
and columns, number of virtual rows, each row's weights on the rows, and the NUMBER of its weights
L), and of a table only its public numbers and the number of its weights.

Main theorems: `tree_at`, `row_at`, `tree_fields`; `ask_any`, `ask_eq`, `testAs_any`;
`piecesTile_eq`, `tieShapeHeld_eq`, `planesShapeHeld_eq`, `funs_all'`, `funs_filter`, `funs_foldl`,
`readShapeHeld_eq`; `selfTestF_rel`, `tileSelfTestF_rel`.

Not claimed: anything on a run on a view, where the skipped comparisons are made. For proofs only;
no module of the program imports this file.


-/
import OnBytes.Flat.LinksFreeHeadD

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Model.Head

/-! ## What two arrays share that agree without their weights -/

theorem getD_map_erase (T : Array HTree) (i : Nat) :
    (T.map eraseTree).getD i {} = eraseTree (T.getD i {}) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases T[i]? with
  | none => simp only [Option.map_none, Option.getD_none, eraseTree, Array.map_empty]
  | some X => rfl

theorem tree_at {T T' : Array HTree} (h : T.map eraseTree = T'.map eraseTree) (i : Nat) :
    eraseTree (T'.getD i {}) = eraseTree (T.getD i {}) := by
  rw [← getD_map_erase, ← getD_map_erase, h]

theorem getD_map_eraseRow (A : Array HRow) (i : Nat) :
    (A.map eraseRow).getD i {} = eraseRow (A.getD i {}) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[i]? with
  | none =>
    simp only [Option.map_none, Option.getD_none, eraseRow, Array.size_empty, Array.replicate_zero]
  | some r => rfl

theorem row_at {X X' : HTree} (h : eraseTree X' = eraseTree X) (r : Nat) :
    eraseRow (X'.rows.getD r {}) = eraseRow (X.rows.getD r {}) := by
  have h0 : X'.rows.map eraseRow = X.rows.map eraseRow := congrArg HTree.rows h
  rw [← getD_map_eraseRow, ← getD_map_eraseRow, h0]

/-- What is read of an array beside the weights. -/
theorem tree_fields {X X' : HTree} (h : eraseTree X' = eraseTree X) :
    X'.name = X.name ∧ X'.kind = X.kind ∧ X'.R = X.R ∧ X'.K = X.K ∧
      X'.rows.size = X.rows.size ∧ (∀ r, (X'.rows.getD r {}).coef = (X.rows.getD r {}).coef) ∧
      ∀ r, (X'.rows.getD r {}).L.size = (X.rows.getD r {}).L.size := by
  have n1 : (eraseTree X').name = (eraseTree X).name := congrArg HTree.name h
  have n2 : (eraseTree X').kind = (eraseTree X).kind := congrArg HTree.kind h
  have n3 : (eraseTree X').R = (eraseTree X).R := congrArg HTree.R h
  have n4 : (eraseTree X').K = (eraseTree X).K := congrArg HTree.K h
  have n5 : ∀ r, (eraseRow (X'.rows.getD r {})).coef = (eraseRow (X.rows.getD r {})).coef :=
    fun r => congrArg HRow.coef (row_at h r)
  refine ⟨n1, n2, n3, n4, ?_, n5, fun r => ?_⟩
  · have h0 := congrArg (fun Y => Y.rows.size) h
    simpa only [eraseTree, Array.size_map] using h0
  · have h0 := congrArg (fun y => y.L.size) (row_at h r)
    simpa only [eraseRow, Array.size_replicate] using h0

/-! ## Questions whose answers go to a test that a dry run skips -/

theorem ask_any {α : Type} (f f' : Fork → α) :
    cmpA.Rel (fun _ _ => True) (SubM.ask fun F => some (f F)) (SubM.ask fun F => some (f' F)) :=
  ask_rel fun _ _ _ => trivial

theorem testAs_any (name : String) (b b' : Bool) :
    cmpA.Rel Eq (liftM (testAs name b) : SubM Unit) (liftM (testAs name b')) :=
  Cmp.blk.lift ForkAlike (by show Over.K (m := Blk) _; keeps) (relB_testAs name b b')

/-! ## The first of the tail's own tests -/

theorem selfTestF_rel (tl : HTailF2) (f' : Array HFun) (nU : Array Nat) :
    cmpA.Rel Eq (tl.selfTestF nU) (HTailF2.selfTestF { tl with funs := f' } nU) := by
  unfold HTailF2.selfTestF
  dsimp only
  refine cmpA.bind' (by keeps) (ask_any _ _) fun ok ok' _ => ?_
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA.bind' (by keeps) (testAs_any _ _ _) fun _ _ _ => ?_
  refine cmpA_same (by resp) fun _ => ?_
  exact testAs_any _ _ _

/-! ## What the second of the tail's tests reads of the state and of the tables -/

theorem piecesTile_eq (tl : HTailF2) (f' : Array HFun) (F : Fork) (T' : Array HTree) (c' : E)
    (W : List HTailF2.Want) (h : F.trees.map eraseTree = T'.map eraseTree) :
    HTailF2.piecesTile { tl with funs := f' } { F with trees := T', c0 := c' } W =
      tl.piecesTile F W := by
  obtain ⟨n1, -, n3, n4, -, n6, n7⟩ := tree_fields (tree_at h tl.ix.ZZ)
  unfold HTailF2.piecesTile
  dsimp only
  simp only [n1, n3, n4, n6, n7] <;> rfl

theorem tieShapeHeld_eq (tl : HTailF2) (f' : Array HFun) (F : Fork) (T' : Array HTree) (c' : E)
    (h : F.trees.map eraseTree = T'.map eraseTree) :
    HTailF2.tieShapeHeld { tl with funs := f' } { F with trees := T', c0 := c' } =
      tl.tieShapeHeld F := by
  funext mu
  obtain ⟨-, n2, n3, n4, n5, n6, n7⟩ := tree_fields (tree_at h (tl.gtTree.getD mu 0))
  unfold HTailF2.tieShapeHeld
  dsimp only
  simp only [n2, n3, n4, n5, n6, n7]

theorem planesShapeHeld_eq (tl : HTailF2) (f' : Array HFun) (F : Fork) (T' : Array HTree) (c' : E)
    (g : Forest.Heard) (h : F.trees.map eraseTree = T'.map eraseTree) :
    HTailF2.planesShapeHeld { tl with funs := f' } { F with trees := T', c0 := c' } g =
      tl.planesShapeHeld F g := by
  obtain ⟨-, -, n3, n4, n5, n6, n7⟩ := tree_fields (tree_at h tl.ix.BZ)
  unfold HTailF2.planesShapeHeld
  dsimp only
  simp only [n3, n4, n5, n6, n7] <;> rfl

theorem funs_all' {f f' : Array HFun} (h : FunsAlike f f') (q : HFun → Bool)
    (hq : ∀ a b, FunAlike a b → q a = q b) : f.all q = f'.all q := by
  rw [← Array.all_toList, ← Array.all_toList]
  exact all_alike hq h

theorem funs_filter {f f' : Array HFun} (h : FunsAlike f f') (p : HFun → Bool)
    (hp : ∀ a b, FunAlike a b → p a = p b) : FunsAlike (f.filter p) (f'.filter p) := by
  unfold FunsAlike at h ⊢
  rw [Array.toList_filter, Array.toList_filter]
  generalize f.toList = l at h
  generalize f'.toList = l' at h
  induction h with
  | nil => exact .nil
  | cons h0 _ ih =>
    simp only [List.filter_cons, hp _ _ h0]
    split
    · exact .cons h0 ih
    · exact ih

theorem funs_foldl {β : Type} {f f' : Array HFun} (h : FunsAlike f f') (g : β → HFun → β)
    (hg : ∀ s a b, FunAlike a b → g s a = g s b) (s : β) : f.foldl g s = f'.foldl g s := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  unfold FunsAlike at h
  generalize f.toList = l at h
  generalize f'.toList = l' at h
  induction h generalizing s with
  | nil => rfl
  | cons h0 _ ih => simp only [List.foldl_cons, hg s _ _ h0, ih]

theorem readShapeHeld_eq (tl : HTailF2) {f' : Array HFun} (hf : FunsAlike tl.funs f')
    {L4 L4' : Array E} (hs : L4.size = L4'.size) :
    HTailF2.readShapeHeld { tl with funs := f' } L4' = tl.readShapeHeld L4 := by
  have hr := funs_filter hf
    (fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2))
    (fun a b hab => by rw [hab.1])
  unfold HTailF2.readShapeHeld
  dsimp only
  rw [← hs, ← funs_all' hr _ (fun a b hab => by
      obtain ⟨e, h1⟩ := hab
      rw [e]
      dsimp only
      rw [h1]),
    ← funs_foldl hr _ (fun s a b hab => by rw [hab.1])]

/-- Two questions to the state with one answer, whatever the weights and the constant. -/
theorem ask_eq {α : Type} {f f' : Fork → Option α}
    (h : ∀ (F : Fork) (T' : Array HTree) (c' : E), F.trees.map eraseTree = T'.map eraseTree →
      f' { F with trees := T', c0 := c' } = f F) : cmpA.Rel Eq (SubM.ask f) (SubM.ask f') := by
  refine ask_rel ?_
  intro F F' hF
  obtain ⟨e, h1⟩ := hF
  generalize F'.trees = T' at e h1
  generalize F'.c0 = c' at e
  subst e
  rw [h F T' c' h1]
  exact OptRel.refl (fun _ => rfl) _

/-! ## The second of the tail's own tests -/

theorem tileSelfTestF_rel (tl : HTailF2) {f' : Array HFun} (hf : FunsAlike tl.funs f') :
    cmpA.Rel Eq tl.tileSelfTestF (HTailF2.tileSelfTestF { tl with funs := f' }) := by
  unfold HTailF2.tileSelfTestF
  dsimp only
  refine cmpA_same (by resp) fun g => ?_
  refine cmpA_same (by resp) fun jo => ?_
  refine cmpA_same (by resp) fun w => ?_
  refine cmpA_same (ask_same _ fun F T' c' h => congrArg some
    (tree_fields (tree_at h tl.ix.ZZ)).2.2.2.2.1) fun rowsZZ => ?_
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA.bind' (S := Eq) (by keeps)
    (ask_eq fun F T' c' h => congrArg some (piecesTile_eq tl f' F T' c' _ h)) fun b b' e => ?_
  subst e
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA.bind' (by keeps) (ask_any _ _) fun _ _ _ => ?_
  refine cmpA.bind' (by keeps) (testAs_any _ _ _) fun _ _ _ => ?_
  refine cmpA.bind' (S := Eq) (by keeps) (ask_eq fun F T' c' h => congrArg some ?_) fun b b' e => ?_
  · obtain ⟨-, -, -, -, -, n6, n7⟩ := tree_fields (tree_at h tl.ix.ZZ)
    dsimp only
    rw [tieShapeHeld_eq tl f' F T' c' h, planesShapeHeld_eq tl f' F T' c' g h]
    simp only [n6, n7]
  subst e
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA.bind' (by keeps) (ask_any _ _) fun _ _ _ => ?_
  refine cmpA.bind' (by keeps) (testAs_any _ _ _) fun _ _ _ => ?_
  refine cmpA.bind' (S := fun (a a' : Array E) => a.size = a'.size) (by keeps)
    (ask_rel (R := fun (a a' : Array E) => a.size = a'.size) fun F F' hF =>
      show Array.size _ = Array.size _ from
        ((tree_fields (tree_at hF.2 tl.ix.ZZ)).2.2.2.2.2.2 _).symm)
    fun L4 L4' hs => ?_
  rw [readShapeHeld_eq tl hf hs]
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA.bind' (by keeps) (ask_any _ _) fun _ _ _ => ?_
  exact testAs_any _ _ _

end OnBytes.Flat
