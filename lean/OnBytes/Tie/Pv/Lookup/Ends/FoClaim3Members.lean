-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoClaim3Members.lean.
The members of claim 3 of the attention sub-proof, written out.

`formsD_claim3` (OnBytes/Tie/Pv/Lookup/Ends/FoFixedDAttForms.lean) holds the value and the list of
the claims that `Attention.claim3` adds, as data. By definition they are those of `fixedD_claim3`
(OnBytes/Tie/Pv/Lookup/Ends/FoFixedDAtt.lean), of which the list `attA`
(OnBytes/Tie/Pv/Lookup/Ends/FoBaseD.lean) begins. Here the value and every member of the list are
written functions of the record, the key forms before, and the number K of columns of the array of
tables.

 * `weightedF n w fv`: the sum over i below n of `w[i]` times the form `fv i`. `planeF h K t x lam a
   z isD`: the form of plane x of the pair (lam, a) at the point z: such a sum of entries of the
   array of tables (`u3Form`). `lessF start pw fv`: the form start minus the sum over the pieces w
   of `w.wp` times `fv w`.
 * `planeMember h K pc x`: member x of a plane claim: the slot `pc.s0 + x` minus the sum over the
   unit's pieces of the piece's weight times plane x at the unit's point.
 * `linPlanesL`, `callKRL`, `claim3L`: the lists: of a plane claim, its `pc.np` members; of a call
   q, those of the plane claims of that call, in their order; of claim 3, those of the calls of kind
   KR, in list order.
 * `u3at_vL`, `weighted_vL`, `plane_vL`, `lessPieces_vL`, `linPlanes_vL`, `callKR_vL`: each
   routine's data have that value and that list.
 * `claim3_vL`: for a good record h and good key forms j (the two instances that `formsD_claim3`
   asks): the value of `formsD_claim3 h j` at k is `joins3 h j`
   (OnBytes/Tie/Pv/Lookup/Ends/FoAttKf.lean) and its list is `claim3L h (k h.iU3)`. `claim3_fixedD`:
   the same of `fixedD_claim3 h j`.
 * `claim3L_length`: the list has `cnt3 h` members (OnBytes/Tie/Pv/Lookup/Ends/FoAddsAtt.lean), at
   every K.
 * `good_joins3`: the key forms behind claim 3 read the array of tables alone.
 * `attA_claim3`: `attA P h k` is `claim3L h (k h.iU3)`, then the lists of claims 4 and 5 at the key
   forms `joins3 h (Joins.empty P.NC)`.

Every routine of claim 3 has a value at all numbers of columns, so these equations hold outright,
with no premise on a run: the test of `u3at` on its index has no part in the data (a run on which it
fails does not return).

Limits: claim 3 alone: the lists of claims 4 to 8 and of the planes are not written out. Those of
OnBytes/Tie/Pv/Lookup/Ends/FoFixedD.lean and OnBytes/Tie/Pv/Lookup/Ends/FoBaseD.lean stand here too.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedDAttForms
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedDUnfold
import OnBytes.Tie.Pv.Lookup.Ends.FoAttKf
import OnBytes.Tie.Pv.Lookup.Ends.FoAddsAtt
import OnBytes.Tie.Pv.Lookup.Ends.FoBaseD

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

/-- The sum over i below n of w[i] times the form fv i. -/
def weightedF (n : ℕ) (w : Array E) (fv : ℕ → Aff) : Aff :=
  (List.range n).foldl (fun s i => Aff.addMul s (fv i) (w.getD i zeroE)) (Aff.ofConst zeroE)

/-- The form start minus the sum over the pieces w of w.wp times the form fv w. -/
def lessF (start : Aff) (pw : Array PW) (fv : PW → Aff) : Aff :=
  pw.toList.foldl (fun s w => Aff.addMul s (fv w) (mulE minusOne w.wp)) start

/-- Plane x of the pair (lam, a) at the point z, in an array of tables of K columns. -/
def planeF (h : Attention.Heard) (K t x lam a : ℕ) (z : Array E) (isD : Bool) : Aff :=
  weightedF (eqTab (z.extract 0 ((if isD = true then h.S.nD else h.S.nM) - h.S.cf.lmS))).size
    (eqTab (z.extract 0 ((if isD = true then h.S.nD else h.S.nM) - h.S.cf.lmS)))
    fun hi => u3Form h.iU3 K (t +
      (((if isD = true then (5 * h.S.Lam * h.S.HA) <<< h.S.nM else 0) +
        ((x * h.S.Lam + lam) * h.S.HA + a) <<< if isD = true then h.S.nD else h.S.nM) >>>
          h.S.cf.lmS + hi))

/-- Member x of a plane claim. -/
def planeMember (h : Attention.Heard) (K : ℕ) (pc : PlaneClaim) (x : ℕ) : Aff :=
  lessF (Aff.slot (pc.s0 + x)) pc.pw fun w => planeF h K h.t.tA x w.lam w.a pc.z pc.isD

/-- The members of a plane claim. -/
def linPlanesL (h : Attention.Heard) (K : ℕ) (pc : PlaneClaim) : List Cl :=
  (List.range pc.np).map fun x => (planeMember h K pc x, #[])

/-- The members of call q. -/
def callKRL (h : Attention.Heard) (K q : ℕ) : List Cl :=
  h.planes.toList.flatMap fun pc => if pc.call == q then linPlanesL h K pc else []

/-- The members of claim 3. -/
def claim3L (h : Attention.Heard) (K : ℕ) : List Cl :=
  h.S.calls.toList.zipIdx.flatMap fun x => if x.1.kind == .kr then callKRL h K x.2 else []

theorem u3at_vL (h : Attention.Heard) (t i : ℕ) (k : ℕ → ℕ) :
    (fixedD_u3at h t i).v k = some (u3Form h.iU3 (k h.iU3) (t + i)) ∧
    (fixedD_u3at h t i).L k = [] := ⟨rfl, rfl⟩

theorem flatMap_none {α β : Type} (l : List α) : l.flatMap (fun _ => ([] : List β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih]; rfl

theorem weighted_vL {t0 : ℕ} (n : ℕ) (w : Array E) (f : ℕ → SubM Aff)
    (hf : ∀ i, FixedD t0 (f i)) (k : ℕ → ℕ) (fv : ℕ → Aff)
    (H : ∀ i, (hf i).v k = some (fv i) ∧ (hf i).L k = []) :
    (fixedD_weighted n w f hf).v k = some (weightedF n w fv) ∧
    (fixedD_weighted n w f hf).L k = [] := by
  have := foldlM_vL (t0 := t0)
    (fun (s : Aff) (a : ℕ) _ _ => (hf a).bind fun a_3 _ =>
      FixedD.pure (s.addMul a_3 (w.getD a zeroE)))
    k (fun s i => Aff.addMul s (fv i) (w.getD i zeroE)) (fun _ => []) (List.range n)
    (Aff.ofConst zeroE) inferInstance inferInstance (fun a _ s gs _ => by
      obtain ⟨h1, h2⟩ := H a
      obtain ⟨b1, b2⟩ := bindD_some (hf a)
        (fun a_3 (_ : Good t0 a_3) => FixedD.pure (t0 := t0) (s.addMul a_3 (w.getD a zeroE))) h1
      exact ⟨b1, by rw [b2, h2]; rfl⟩)
  rw [flatMap_none] at this
  exact this

theorem plane_vL (h : Attention.Heard) (t x lam a : ℕ) (z : Array E) (isD : Bool) (k : ℕ → ℕ) :
    (fixedD_plane h t x lam a z isD).v k = some (planeF h (k h.iU3) t x lam a z isD) ∧
    (fixedD_plane h t x lam a z isD).L k = [] :=
  weighted_vL _ _ _ _ k _ fun _ => u3at_vL h t _ k

theorem lessPieces_vL {t0 : ℕ} (start : Aff) (pw : Array PW) (f : PW → SubM Aff) [Good t0 start]
    (hf : ∀ w, FixedD t0 (f w)) (k : ℕ → ℕ) (fv : PW → Aff)
    (H : ∀ w, (hf w).v k = some (fv w) ∧ (hf w).L k = []) :
    (fixedD_lessPieces start pw f hf).v k = some (lessF start pw fv) ∧
    (fixedD_lessPieces start pw f hf).L k = [] := by
  have := arrayFoldlM_vL (t0 := t0)
    (fun (s : Aff) (a : PW) _ _ => (hf a).bind fun a_3 _ =>
      FixedD.pure (s.addMul a_3 (mulE minusOne a.wp)))
    k (fun s w => Aff.addMul s (fv w) (mulE minusOne w.wp)) (fun _ => []) pw start
    inferInstance inferInstance (fun a _ s gs _ => by
      obtain ⟨h1, h2⟩ := H a
      obtain ⟨b1, b2⟩ := bindD_some (hf a)
        (fun a_3 (_ : Good t0 a_3) => FixedD.pure (t0 := t0) (s.addMul a_3 (mulE minusOne a.wp)))
        h1
      exact ⟨b1, by rw [b2, h2]; rfl⟩)
  rw [flatMap_none] at this
  exact this

theorem linPlanes_vL (h : Attention.Heard) (pc : PlaneClaim) (k : ℕ → ℕ) :
    (fixedD_linPlanes h pc).v k = some () ∧
    (fixedD_linPlanes h pc).L k = linPlanesL h (k h.iU3) pc := by
  have := forM_vL (t0 := h.iU3)
    (fun (a : ℕ) _ =>
      (fixedD_lessPieces (t0 := h.iU3) (Aff.slot (pc.s0 + a)) pc.pw
        (fun w => plane h h.t.tA a w.lam w.a pc.z pc.isD) fun w =>
        fixedD_plane h h.t.tA a w.lam w.a pc.z pc.isD).bind fun a _ => FixedD.lin a)
    k (fun x => [(planeMember h (k h.iU3) pc x, #[])]) (List.range pc.np) inferInstance
    (fun a _ _ => by
      obtain ⟨h1, h2⟩ := lessPieces_vL (t0 := h.iU3) (Aff.slot (pc.s0 + a)) pc.pw
        (fun w => plane h h.t.tA a w.lam w.a pc.z pc.isD)
        (fun w => fixedD_plane h h.t.tA a w.lam w.a pc.z pc.isD) k
        (fun w => planeF h (k h.iU3) h.t.tA a w.lam w.a pc.z pc.isD)
        fun w => plane_vL h h.t.tA a w.lam w.a pc.z pc.isD k
      obtain ⟨b1, b2⟩ := bindD_some _
        (fun a (_ : Good h.iU3 a) => FixedD.lin (t0 := h.iU3) a) h1
      exact ⟨b1, by rw [b2, h2]; rfl⟩)
  refine ⟨this.1, this.2.trans ?_⟩
  unfold linPlanesL
  induction List.range pc.np with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih]; rfl

theorem callKR_vL (h : Attention.Heard) (q : ℕ) (k : ℕ → ℕ) :
    (fixedD_callKR h q).v k = some (kfKR h q) ∧
    (fixedD_callKR h q).L k = callKRL h (k h.iU3) q := by
  unfold kfKR callKRL fixedD_callKR
  refine arrayFoldlM_vL _ k (fun v pc => if pc.call == q then v + keyKR pc else v)
    (fun pc => if pc.call == q then linPlanesL h (k h.iU3) pc else []) _ _ _ _
    fun a _ s gs ga => ?_
  rw [ite_v, ite_L]
  beta_reduce
  by_cases c : (a.call == q) = true
  · rw [if_pos c, if_pos c, if_pos c, if_pos c]
    obtain ⟨h1, h2⟩ := linPlanes_vL h a k
    rw [bind_v, bind_L, bindV_some _ _ h1, bindL_some _ _ h1, h2]
    exact ⟨rfl, List.append_nil _⟩
  · rw [if_neg c, if_neg c, if_neg c, if_neg c]
    exact ⟨rfl, rfl⟩

/-- **The value and the members of claim 3.** -/
theorem claim3_vL (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] (k : ℕ → ℕ) :
    (formsD_claim3 h j).v k = some (joins3 h j) ∧
    (formsD_claim3 h j).L k = claim3L h (k h.iU3) := by
  unfold joins3 claim3L formsD_claim3
  refine foldlM_vL _ k
    (fun (j : Joins) (x : ACall × ℕ) => if x.1.kind == .kr then j.set x.2 (kfKR h x.2) else j)
    (fun x => if x.1.kind == .kr then callKRL h (k h.iU3) x.2 else []) _ _ _ _
    fun a _ s gs ga => ?_
  rw [ite_v, ite_L]
  beta_reduce
  by_cases c : (a.1.kind == Table.kr) = true
  · rw [if_pos c, if_pos c, if_pos c, if_pos c]
    obtain ⟨h1, h2⟩ := callKR_vL h a.2 k
    rw [bind_v, bind_L, bindV_some _ _ h1, bindL_some _ _ h1, h2]
    exact ⟨rfl, List.append_nil _⟩
  · rw [if_neg c, if_neg c, if_neg c, if_neg c]
    exact ⟨rfl, rfl⟩

/-- The same of the data of OnBytes/Tie/Pv/Lookup/Ends/FoFixedDAtt.lean. -/
theorem claim3_fixedD (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j]
    (k : ℕ → ℕ) :
    (fixedD_claim3 h j).v k = some (joins3 h j) ∧
    (fixedD_claim3 h j).L k = claim3L h (k h.iU3) := claim3_vL h j k

theorem length_flatMap_sum {α β : Type} (f : α → List β) (l : List α) :
    (l.flatMap f).length = (l.map fun a => (f a).length).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.length_append, ih, List.map_cons, List.sum_cons]

theorem callKRL_length (h : Attention.Heard) (K q : ℕ) : (callKRL h K q).length = cntKR h q := by
  unfold callKRL cntKR
  rw [length_flatMap_sum]
  congr 1
  refine List.map_congr_left fun pc _ => ?_
  by_cases c : (pc.call == q) = true
  · rw [if_pos c, if_pos c]
    unfold linPlanesL
    rw [List.length_map, List.length_range]
  · rw [if_neg c, if_neg c]
    rfl

/-- The number of members of claim 3, at every number of columns. -/
theorem claim3L_length (h : Attention.Heard) (K : ℕ) : (claim3L h K).length = cnt3 h := by
  unfold claim3L cnt3
  rw [length_flatMap_sum]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  by_cases c : (x.1.kind == Table.kr) = true
  · rw [if_pos c, if_pos c, callKRL_length]
  · rw [if_neg c, if_neg c]
    rfl

/-- The key forms behind claim 3 are good. -/
theorem good_joins3 (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] :
    Good h.iU3 (joins3 h j) :=
  ⟨(formsD_claim3 h j).goodV (fun _ => 0) _ (claim3_vL h j _).1⟩

/-- The list `attA` begins with the members of claim 3; behind them stand the lists of claims 4 and
5, at the key forms behind claim 3. -/
theorem attA_claim3 (P : Plan) (h : Attention.Heard) [Good h.iU3 h] (k : ℕ → ℕ) :
    attA P h k = claim3L h (k h.iU3) ++
      ((@fixedD_claim4 h _ (joins3 h (Joins.empty P.NC)) (good_joins3 h _)).bind
        fun j4 g4 => @fixedD_claim5 h _ j4 g4).L k := by
  obtain ⟨e1, e2⟩ := claim3_fixedD h (Joins.empty P.NC) k
  rw [attA_unfold, bindL_some _ _ e1, e2]

end Fo
