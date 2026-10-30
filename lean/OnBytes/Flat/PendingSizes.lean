-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/PendingSizes.lean: whether the row that a sub-proof leaves on the table can be made,
and its shape, hang on sizes and on units' numbers alone.

`wsPending` (OnBytes/Model/Pending.lean) makes that row from what the merge of the claims on the
weights returns. It refuses by tests on public numbers and on the sizes of arrays of field elements.
This file follows the sizes through the functions that it calls. Statements on pure functions; no
block occurs.

Main names:
  `size_wsOuter`, `size_eqTab`, `length_wsDigits`: the sizes of three tables.
  `FacSizes`, `RecSizes`: two factors on the rows have the same sizes; what is left of two claims
    names one unit, with factors of the same sizes. They are `RowFacAlike`, `RecAlike` of
    OnBytes/Flat/LinksFree.lean under second names, so that this file needs OnBytes/Flat/DryRel.lean
    alone; OnBytes/Flat/PendingFreeOf.lean bridges them.
  `size_wsGamma`: then the claims' coefficients on the rows are as many.
  `ExSizes`, `wsGammaAdd_sizes`, `foldGamma_sizes`: both are refused, or both are added, to vectors
    of one size.
  `wsSpan_eq`: the stretch of rows is the same.
  `stretchBlocks_skel`, `stretchInTheCube_skel`, `memberWeightsOnRows_skel`: the blocks of a stretch
    have the same pairs and dense variables, whatever the values, if these are as many.
  `PendAlike`, `wsPending_alike`: both are refused, or both rows are made, equal in all but the
    weights, which have the same numbers of variables.

Not claimed: anything on a run. Two refusals may bear two names. For proofs only; no module of the
program imports this file.


-/
import OnBytes.Flat.DryRel
import OnBytes.Model.Pending

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model

/-! ## Three tables -/

theorem size_foldl_push {α β : Type} (f : β → α) (l : List β) (out : Array α) :
    (l.foldl (fun o y => o.push (f y)) out).size = out.size + l.length := by
  induction l generalizing out with
  | nil => rfl
  | cons y l ih =>
    rw [List.foldl_cons, ih, Array.size_push, List.length_cons]
    omega

/-- All products of two arrays: as many as the product of the sizes. -/
theorem size_wsOuter (a b : Array E) : (wsOuter a b).size = a.size * b.size := by
  have h : ∀ (l : List E) (out : Array E),
      (l.foldl (fun out x => b.foldl (fun o y => o.push (mulE x y)) out) out).size =
        out.size + l.length * b.size := by
    intro l
    induction l with
    | nil => intro out; simp
    | cons x l ih =>
      intro out
      rw [List.foldl_cons, ih, ← Array.foldl_toList, size_foldl_push, List.length_cons,
        Array.length_toList, Nat.succ_mul]
      omega
  unfold wsOuter
  rw [← Array.foldl_toList, h]
  simp

/-- One more coordinate doubles the table. -/
theorem size_eqTabStep (t : Array E) (zv : E) : (eqTabStep t zv).size = 2 * t.size := by
  have h : ∀ (l : List E) (out : Array E),
      (l.foldl (fun n a => (n.push (subE a (mulE a zv))).push (mulE a zv)) out).size =
        out.size + 2 * l.length := by
    intro l
    induction l with
    | nil => intro out; rfl
    | cons x l ih =>
      intro out
      rw [List.foldl_cons, ih, Array.size_push, Array.size_push, List.length_cons]
      omega
  unfold eqTabStep
  rw [← Array.foldl_toList]
  have h' := h t.toList (Array.emptyWithCapacity (2 * t.size))
  simpa using h'

/-- The table of the equality polynomial has 2 ^ (the number of coordinates) entries. -/
theorem size_eqTab (z : Array E) : (eqTab z).size = 2 ^ z.size := by
  have h : ∀ (l : List E) (t : Array E), (l.foldl eqTabStep t).size = 2 ^ l.length * t.size := by
    intro l
    induction l with
    | nil => intro t; simp
    | cons x l ih =>
      intro t
      rw [List.foldl_cons, ih, size_eqTabStep, List.length_cons, Nat.pow_succ, Nat.mul_assoc]
  unfold eqTab
  rw [← Array.foldl_toList, h]
  simp

/-- One scalar for each digit. -/
theorem length_wsDigits : ∀ (n : Nat) (s : E), (wsDigits n s).length = n
  | 0, _ => rfl
  | n + 1, s => by
    rw [wsDigits, List.length_cons, length_wsDigits n]

/-! ## A claim's coefficients on the rows -/

/-- Two factors on the rows have the same sizes. -/
def FacSizes (x x' : WsRowFac) : Prop :=
  x.HV.size = x'.HV.size ∧ x.pl.size = x'.pl.size ∧ x.AV.size = x'.AV.size

/-- What is left of two claims: one unit, factors of the same sizes. -/
def RecSizes (c c' : WsRecClaim) : Prop := c.ui = c'.ui ∧ All2 FacSizes c.f c'.f

/-- Two factors of the same sizes are written out as tables of one size. -/
theorem size_table {x x' : WsRowFac} (h : FacSizes x x') (g : WsGrp) :
    (x.table g).size = (x'.table g).size := by
  unfold WsRowFac.table
  split
  · rw [size_wsOuter, size_wsOuter, size_eqTab, size_eqTab, h.1, h.2.1]
  · split
    · rfl
    · exact h.2.2

/-- Two lists that go together member by member, each zipped with one third list. -/
theorem All2.zipRight {α β γ : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : All2 R l l') : ∀ g : List γ,
      All2 (fun (y : α × γ) (y' : β × γ) => R y.1 y'.1 ∧ y.2 = y'.2) (l.zip g) (l'.zip g) := by
  induction h with
  | nil => intro g; exact .nil
  | cons h0 _ ih =>
    intro g
    cases g with
    | nil => exact .nil
    | cons c g => exact .cons ⟨h0, rfl⟩ (ih g)

/-- Two lists that go together member by member, both reversed. -/
theorem All2.reverse {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : All2 R l l') : All2 R l.reverse l'.reverse := by
  induction h with
  | nil => exact .nil
  | cons h0 _ ih =>
    rw [List.reverse_cons, List.reverse_cons]
    exact ih.append (.cons h0 .nil)

/-- The products with the factors' tables, one after the other: the sizes go together. -/
theorem size_foldOuter {l l' : List (WsRowFac × WsGrp)}
    (h : All2 (fun y y' => FacSizes y.1 y'.1 ∧ y.2 = y'.2) l l') :
    ∀ v v' : Array E, v.size = v'.size →
      (l.foldl (fun v y => wsOuter v (y.1.table y.2)) v).size =
        (l'.foldl (fun v y => wsOuter v (y.1.table y.2)) v').size := by
  induction h with
  | nil => intro v v' hv; exact hv
  | cons h0 _ ih =>
    intro v v' hv
    rw [List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_
    rw [size_wsOuter, size_wsOuter, hv, size_table h0.1, h0.2]

/-- **Two claims with factors of the same sizes have as many coefficients on the rows of a
unit.** -/
theorem size_wsGamma (u : WsUnit) {c c' : WsRecClaim} (h : All2 FacSizes c.f c'.f) (w w' : E) :
    (wsGamma u c w).size = (wsGamma u c' w').size := by
  unfold wsGamma
  refine size_foldOuter (h.zipRight u.g).reverse _ _ ?_
  simp [length_wsDigits]

/-! ## Adding them up -/

/-- Two results: both are refusals, or both are vectors of one size. -/
def ExSizes : Except String (Array E) → Except String (Array E) → Prop
  | .ok a, .ok a' => a.size = a'.size
  | .error _, .error _ => True
  | _, _ => False

/-- Two vectors of one size, as results. -/
theorem exSizes_ok {a a' : Array E} (h : a.size = a'.size) :
    ExSizes (pure a) (pure a') := h

/-- Changing entries in place keeps the size. -/
theorem size_foldModify (f : E → E → E) (l : List E) (G : Array E) (n : Nat) :
    (l.foldl (fun (s : Array E × Nat) x => (s.1.modify s.2 fun y => f y x, s.2 + 1))
      (G, n)).1.size = G.size := by
  induction l generalizing G n with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, ih, Array.size_modify]

/-- Adding a claim's coefficients into a vector keeps its size. -/
theorem size_addInto (v G : Array E) (off : Nat) :
    (v.foldl (fun (s : Array E × Nat) x => (s.1.modify s.2 fun y => addE y x, s.2 + 1))
      (G, off)).1.size = G.size := by
  rw [← Array.foldl_toList]
  exact size_foldModify addE _ _ _

/-- **Both claims are refused, or both are added, to vectors of one size.** -/
theorem wsGammaAdd_sizes (lay : WsLay) {G G' : Array E} (hG : G.size = G'.size)
    {c c' : WsRecClaim} (h : RecSizes c c') (w : E) :
    ExSizes (wsGammaAdd G lay c w) (wsGammaAdd G' lay c' w) := by
  unfold wsGammaAdd
  rw [← h.1]
  cases lay.U[c.ui]? with
  | none => trivial
  | some u =>
    simp only []
    have hcond : ((wsGamma u c w).size != u.rows || c.f.length != u.g.length ||
        decide (G.size < u.off + u.rows)) =
        ((wsGamma u c' w).size != u.rows || c'.f.length != u.g.length ||
          decide (G'.size < u.off + u.rows)) := by
      rw [size_wsGamma u h.2 w w, h.2.length, hG]
    rw [hcond]
    split
    · trivial
    · refine exSizes_ok ?_
      rw [size_addInto, size_addInto, hG]

/-- The same for two lists of claims that go together member by member. -/
theorem foldGamma_sizes (lay : WsLay) {l l' : List WsRecClaim} (h : All2 RecSizes l l') :
    ∀ G G' : Array E, G.size = G'.size →
      ExSizes (l.foldlM (fun G c => wsGammaAdd G lay c oneE) G)
        (l'.foldlM (fun G c => wsGammaAdd G lay c oneE) G') := by
  induction h with
  | nil => intro G G' hG; exact hG
  | cons h0 _ ih =>
    intro G G' hG
    rw [List.foldlM_cons, List.foldlM_cons]
    have h1 := wsGammaAdd_sizes lay hG h0 oneE
    revert h1
    cases wsGammaAdd G lay _ oneE <;> cases wsGammaAdd G' lay _ oneE <;> intro h1
    · trivial
    · exact h1.elim
    · exact h1.elim
    · exact ih _ _ h1

/-- **The stretch of rows is the same**: it is read off the units' numbers alone. -/
theorem wsSpan_eq (lay : WsLay) {l l' : List WsRecClaim} (h : All2 RecSizes l l') :
    wsSpan lay l = wsSpan lay l' := by
  unfold wsSpan
  generalize ((2 ^ 64 - 1, 0) : Nat × Nat) = r
  induction h generalizing r with
  | nil => rfl
  | @cons c c' _ _ h0 _ ih =>
    rw [List.foldlM_cons, List.foldlM_cons, ← h0.1]
    cases lay.U[c.ui]? with
    | none => rfl
    | some u => exact ih _

/-! ## The blocks of a stretch -/

/-- what of a tensor does not hang on values: its pairs and its dense variables -/
def skel (t : Tensor) : List (E × E) × List Nat := (t.pairs, t.denseVars)

/-- **The blocks of a stretch have the same pairs and dense variables**, whatever the values, if
these are as many. -/
theorem stretchBlocks_skel (kRow firstRow : Nat) {v v' : Array E} (h : v.size = v'.size) :
    ∀ fuel start, (stretchBlocks kRow firstRow v fuel start).map skel =
      (stretchBlocks kRow firstRow v' fuel start).map skel
  | 0, _ => rfl
  | fuel + 1, start => by
    unfold stretchBlocks
    simp only [h]
    split
    · rfl
    · rw [List.map_cons, List.map_cons, stretchBlocks_skel kRow firstRow h fuel]
      congr 1
      split <;> rfl

/-- Two lists of tensors, or none twice. -/
def OptSkel : Option (List Tensor) → Option (List Tensor) → Prop
  | some g, some g' => g.map skel = g'.map skel
  | none, none => True
  | _, _ => False

/-- So both stretches are refused, or both are cut into blocks with the same pairs and dense
variables. -/
theorem stretchInTheCube_skel (kRow firstRow : Nat) {v v' : Array E} (h : v.size = v'.size) :
    OptSkel (stretchInTheCube kRow firstRow v) (stretchInTheCube kRow firstRow v') := by
  have hs := stretchBlocks_skel kRow firstRow h (2 * kRow + 2) firstRow
  have hd : ((stretchBlocks kRow firstRow v (2 * kRow + 2) firstRow).map
        fun t => 2 ^ t.denseVars.length) =
      ((stretchBlocks kRow firstRow v' (2 * kRow + 2) firstRow).map
        fun t => 2 ^ t.denseVars.length) := by
    have := congrArg (List.map fun s : List (E × E) × List Nat => 2 ^ s.2.length) hs
    simpa [List.map_map, Function.comp_def, skel] using this
  unfold stretchInTheCube
  simp only [h, hd]
  split
  · split
    · exact hs
    · trivial
  · trivial

/-- The same with the test that the stretch lies inside the matrix. -/
theorem memberWeightsOnRows_skel (S : Params.LinShape) (firstRow : Nat) {v v' : Array E}
    (h : v.size = v'.size) :
    OptSkel (memberWeightsOnRows S firstRow v) (memberWeightsOnRows S firstRow v') := by
  unfold memberWeightsOnRows
  rw [h]
  split
  · exact stretchInTheCube_skel _ _ h
  · trivial

/-! ## The row -/

/-- Two results of `wsPending`: both are refusals, or both are rows that are equal in all but the
weights, which have the same numbers of variables. -/
def PendAlike : Except String WsPending → Except String WsPending → Prop
  | .ok p, .ok p' => p.psi = p'.psi ∧ p.beta = p'.beta ∧ p.target = p'.target ∧
      p.g.map Tensor.vars = p'.g.map Tensor.vars
  | .error _, .error _ => True
  | _, _ => False

/-- **At two values of the merge that agree in the merged part, and whose claims name the same units
with factors of the same sizes, `wsPending` refuses both or makes two rows that are alike.** It can
refuse at six places; each is passed by both or by neither. -/
theorem wsPending_alike (lay : WsLay) {o o' : WsForkOut} (hm : o.toWsMerged = o'.toWsMerged)
    (hr : All2 RecSizes o.recs o'.recs) (claims : Nat) (S : Params.LinShape) :
    PendAlike (wsPending lay o claims S) (wsPending lay o' claims S) := by
  have e1 : o.rm = o'.rm := congrArg WsMerged.rm hm
  have e2 : o.beta = o'.beta := congrArg WsMerged.beta hm
  have e3 : o.fvp = o'.fvp := congrArg WsMerged.fvp hm
  have e4 : o.recs.isEmpty = o'.recs.isEmpty := by
    revert hr
    generalize o.recs = l
    generalize o'.recs = l'
    intro hr
    cases hr <;> rfl
  unfold wsPending
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  rw [← e1, ← e2, ← e3, ← e4, ← hr.length, ← wsSpan_eq lay hr]
  split
  · trivial
  · split
    · trivial
    · cases wsSpan lay o.recs with
      | error _ => trivial
      | ok fl =>
        obtain ⟨first, last⟩ := fl
        simp only []
        split
        · trivial
        · have hG := foldGamma_sizes lay hr (Array.replicate last zeroE)
            (Array.replicate last zeroE) rfl
          revert hG
          cases List.foldlM (fun G c => wsGammaAdd G lay c oneE) (Array.replicate last zeroE)
              o.recs <;>
            cases List.foldlM (fun G c => wsGammaAdd G lay c oneE) (Array.replicate last zeroE)
              o'.recs <;> intro hG
          · trivial
          · exact hG.elim
          · exact hG.elim
          · rename_i Gam Gam'
            have hx : (Gam.extract first last).size = (Gam'.extract first last).size := by
              have hG' : Gam.size = Gam'.size := hG
              simp [Array.size_extract, hG']
            have hw := memberWeightsOnRows_skel S first hx
            revert hw
            simp only []
            cases memberWeightsOnRows S first (Gam.extract first last) <;>
              cases memberWeightsOnRows S first (Gam'.extract first last) <;> intro hw
            · trivial
            · exact hw.elim
            · exact hw.elim
            · refine ⟨rfl, rfl, rfl, ?_⟩
              have := congrArg (List.map fun s : List (E × E) × List Nat => s.1.length) hw
              simpa [List.map_map, Function.comp_def, skel, Tensor.vars] using this

end OnBytes.Flat
