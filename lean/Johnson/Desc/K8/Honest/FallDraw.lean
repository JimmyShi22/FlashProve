-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallDraw.lean: A YES OF THE BATCHING BLOCK, CUT, AS FAR AS THE COUNT OF
Johnson/Desc/K8/Honest/FallCount.lean NEEDS IT. Statements and proofs, on the block's own text
(Johnson/Desc/First/Batch/Kind.lean: K9.batch, at the lens K9.atS). No prover.

  `drawnAt_ok`   the draw's yes: one element was drawn; the draw's tests passed; what it writes
  `batch_ok`     the block's yes: the draw's yes; the function of claims returned; the claims were
      added by the block's own adding; what is written
  `addList_count`   the adding's yes: the claims' number stays within the plan's
  `shapeOf`      of each array: its number of columns, and each virtual row's first column;
      `shape_of_frame`, `shape_fill`, `K_of_shape`, `L0_of_shape`
  `drawn_trees`  the arrays behind the draw are those in front with the weights' room laid
  `tlFork_iff`, `tl_set`, `behind_set`   what is read behind the block's writing
Limits: from a yes alone.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallAlg
import Johnson.Desc.First.Batch.Law.AtBlock
import Johnson.Desc.First.Batch.Law.AtSLens
import Johnson.Desc.First.Batch.BlindK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims

/-! ## The block's yes -/

theorem drawnAt_ok (p : K9.Where) (s t : S) (d : Fmt.Drawn) (h : drawnAt p s d = .ok t) :
    ∃ a x o, K9.atS.get? s = some a ∧ d.elems = [x] ∧
      K9.drawnClean p.rows (E.ofTriple x) a.owed a.used a.L a.F = .ok o ∧
      t = K9.atS.set s { a with owed := o.owed, L := o.L, F := o.F } := by
  unfold drawnAt at h
  simp only [K9.drawAlone] at h
  obtain ⟨a, ha, h1⟩ := K9L.ok_bind h
  obtain ⟨chi, hchi, h2⟩ := K9L.ok_bind h1
  obtain ⟨o, ho, h3⟩ := K9L.ok_bind h2
  clear h h1 h2
  have hc : (match d.elems with
      | [x] => some (E.ofTriple x)
      | _ => none) = some chi := K9L.there_ok hchi
  cases hq : d.elems with
  | nil =>
    rw [hq] at hc
    exact absurd hc (by simp)
  | cons x l =>
    cases l with
    | nil =>
      rw [hq] at hc
      have ec : E.ofTriple x = chi := Option.some.inj hc
      subst ec
      exact ⟨a, x, o, K9L.there_ok ha, rfl, ho, (Except.ok.inj h3).symm⟩
    | cons x' l' =>
      rw [hq] at hc
      exact absurd hc (by simp)

theorem batch_ok (p : K9.Where) (g : S → Except String (List Claim × S)) (s t' : S)
    (d : Fmt.Drawn) (h : (K9.batch K9.atS p g).decide s [⟨[], d⟩] [] = .ok t') :
    ∃ (t e : S) (cls : List Claim) (y : K9.Part) (G : Fork), drawnAt p s d = .ok t ∧
      g t = .ok (cls, e) ∧ K9.atS.get? e = some y ∧ K9.addList y.F cls = .ok G ∧
      t' = K9.atS.set e { y with F := G } := by
  simp only [K9.batch] at h
  obtain ⟨t, h1, h2⟩ := K9L.ok_bind h
  simp only [K9.adds] at h2
  obtain ⟨_, _, h2⟩ := K9L.ok_bind h2
  obtain ⟨_, _, h2⟩ := K9L.ok_bind h2
  obtain ⟨z, hz, h2⟩ := K9L.ok_bind h2
  obtain ⟨y, hy, h2⟩ := K9L.ok_bind h2
  obtain ⟨G, hG, h2⟩ := K9L.ok_bind h2
  exact ⟨t, z.2, z.1, y, G, h1, hz, K9L.there_ok hy, hG, (Except.ok.inj h2).symm⟩

/-- The block's own adding hands out a number only below the plan's. -/
theorem addList_count : ∀ (cls : List Claim) (F G : Fork), F.LS.size = F.ns →
    K9.addList F cls = .ok G → F.nClaim ≤ F.planClaimsF → F.nClaim + cls.length ≤ F.planClaimsF
  | [], _, _, _, _, h => by simpa using h
  | cl :: l, F, G, hs, h, _ => by
    unfold K9.addList at h
    rw [List.foldlM_cons] at h
    obtain ⟨F1, h1, h2⟩ := K9L.ans_bind h
    obtain ⟨x, hx⟩ := K9L.weightNext_of_addOne F F1 cl h1
    have hlt := (K9L.weightNext_ok F x hx).2.2.1
    obtain ⟨-, e, hs1, -⟩ :=
      K9L.addClaim_total Reading.gl allZero F F1 cl hs (K9L.addOne_older F F1 cl h1)
    have n1 : F1.nClaim = F.nClaim + 1 := by rw [e]
    have p1 : F1.planClaimsF = F.planClaimsF := by rw [e]
    have h3 := addList_count l F1 G hs1 h2 (by omega)
    simp only [List.length_cons]
    omega

/-! ## What of the arrays the test reads beside the weights -/

/-- Of each array: its number of columns, and the first column of each virtual row's weights. -/
def shapeOf (A : Array HTree) : Array (Nat × Array Nat) :=
  A.map fun X => (X.K, X.rows.map (·.L0))

theorem shape_of_frame (A B : Array HTree) (h : treesFrame A = treesFrame B) :
    shapeOf A = shapeOf B := by
  have e : ∀ X : Array HTree,
      shapeOf X = (treesFrame X).map fun z => (z.1.K, z.2.map (·.1.L0)) := fun X => by
    simp [shapeOf, treesFrame, HTree.frame, HRow.frame, Array.map_map, Function.comp_def]
  rw [e A, e B, h]

theorem shape_fold : ∀ (l : List Nat) (tr : Array HTree),
    shapeOf (l.foldl (fun trees ti => trees.modify ti K9L.fillOne) tr) = shapeOf tr
  | [], _ => rfl
  | ti :: l, tr => by
    rw [List.foldl_cons, shape_fold l]
    refine map_modify_same (fun X : HTree => (X.K, X.rows.map (·.L0))) K9L.fillOne (fun X => ?_) tr ti
    have e : (K9L.fillOne X).rows.map (·.L0) = X.rows.map (·.L0) := by
      simp only [K9L.fillOne, Array.map_map]
      congr 1
      funext r
      simp only [Function.comp]
      split <;> rfl
    show ((K9L.fillOne X).K, (K9L.fillOne X).rows.map (·.L0)) = _
    rw [e]
    rfl

theorem shape_fill (F : Fork) (T : Tail2) : shapeOf (t2FillL F T).trees = shapeOf F.trees :=
  shape_fold _ _

theorem K_of_shape (A : Array HTree) (t : Nat) :
    (A.getD t {}).K = ((shapeOf A).getD t (0, #[])).1 := by
  simp only [shapeOf, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[t]? <;> rfl

theorem L0_of_shape (A : Array HTree) (t r : Nat) :
    ((A.getD t {}).rows.getD r {}).L0 = (((shapeOf A).getD t (0, #[])).2).getD r 0 := by
  simp only [shapeOf, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[t]? with
  | none => simp
  | some X =>
    simp only [Option.map_some, Option.getD_some, Array.getElem?_map]
    cases X.rows[r]? <;> rfl

theorem colsU_eq (F : Fork) (t : Nat) : OnBytes.Tie.Pv.Tail.Port.colsU F t = (F.trees.getD t {}).K := by
  simp only [OnBytes.Tie.Pv.Tail.Port.colsU, Array.getD_eq_getD_getElem?]
  cases F.trees[t]? <;> rfl

theorem drawn_trees (rows : Nat) (chi : E) (owed : Option Nat) (used : Nat) (L : LinkCtx)
    (F : Fork) (o : K9.Drawn) (h : K9.drawnClean rows chi owed used L F = .ok o) :
    o.F.trees = (t2FillL F L.list).trees := by
  unfold K9.drawnClean at h
  obtain ⟨o', ho, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  have e : o' = o := Except.ok.inj h
  subst e
  unfold K9.drawn at ho
  obtain ⟨_, _, ho⟩ := K9L.ok_bind ho
  obtain ⟨_, _, ho⟩ := K9L.ok_bind ho
  obtain ⟨_, _, ho⟩ := K9L.ok_bind ho
  obtain ⟨_, _, ho⟩ := K9L.ok_bind ho
  obtain ⟨_, _, ho⟩ := K9L.ok_bind ho
  have e := Except.ok.inj ho
  rw [← e]

/-! ## What is read behind the block's writing -/

theorem tlFork_iff (s : S) (tl : HTailF2) (F : Fork) :
    tlForkP.get? s = some (tl, F) ↔ s.tl? = some tl ∧ s.fork? = some F := by
  simp only [tlForkP, Part.pair, tlP, forkP]
  cases s.tl? <;> cases s.fork? <;> simp

theorem tl_set (e : S) (q : K9.Part) : (K9.atS.set e q).tl? = e.tl? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  cases here with
  | lay x => rfl
  | att x => rfl
  | head x =>
    by_cases ho : x.opened = true
    · simp [K9.atS, S.putLink, S.putFork, S.tl?, ho]
    · simp [K9.atS, S.putLink, S.putFork, S.tl?, ho]
  | between => rfl
  | fin x => rfl
  | mem x => rfl

theorem behind_set (e : S) (y : K9.Part) (G : Fork) (tlb : HTailF2)
    (hy : K9.atS.get? e = some y) (ht : e.tl? = some tlb) :
    tlForkP.get? (K9.atS.set e { y with F := G }) = some (tlb, G) := by
  obtain ⟨a', ha', hF, -, -⟩ := K9L.atS_reads e { y with F := G } (by rw [hy]; rfl)
  refine (tlFork_iff _ _ _).2 ⟨by rw [tl_set, ht], ?_⟩
  rw [K9.get_fork _ a' ha', hF]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.drawnAt_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.batch_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.addList_count
#print axioms VerifiableInference.Desc.First.K8.Honest.shape_of_frame
#print axioms VerifiableInference.Desc.First.K8.Honest.shape_fill
#print axioms VerifiableInference.Desc.First.K8.Honest.L0_of_shape
#print axioms VerifiableInference.Desc.First.K8.Honest.drawn_trees
#print axioms VerifiableInference.Desc.First.K8.Honest.behind_set
