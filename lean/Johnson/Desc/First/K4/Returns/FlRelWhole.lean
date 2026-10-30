-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/FlRelWhole.lean: TWO RUNS OF ONE TEXT (FlRel,
Johnson/Desc/First/K4/Returns/FlRel.lean): THE MERGE OF THE WEIGHT CLAIMS (flatForkEnd,
OnBytes/K/Kc/QuietLink.lean). General laws: nothing is evaluated.

  filterMap_len, onRows_sh, zip_onRows, rowPart_sh   what is left of a weight claim has the sizes
                  that the claim's factors' sizes give.
  zip_slots_rel, wsForkStart_rel, wsForkRounds_rel, MergeAlike, zip_recs, **flatForkEnd_rel**   at
                  two lists of claims with one unit and factors of one size each: one shape of the
                  merge's record (mergeSh, Johnson/Desc/First/Shape/Own.lean).

Limits. The weak form of the frame. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.FlRelHear
import Johnson.Desc.First.K4.Returns.Pub.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Flat (All2 OptRel FacAlike ClaimAlike)
open OnBytes.Desc.First.K4.RtPub (ClaimSkel weightClaims_rel claimE_rel)
open VerifiableInference.Desc.First.Shape

/-! ## What is left of a weight claim -/

theorem filterMap_len {α : Type} (c : Nat → Bool) (a b : Nat → α) : ∀ l : List Nat,
    (l.filterMap fun i => if c i then none else some (a i)).length =
      (l.filterMap fun i => if c i then none else some (b i)).length
  | [] => rfl
  | i :: l => by
    rw [List.filterMap_cons, List.filterMap_cons]
    cases h : c i
    · simp only [Bool.false_eq_true, if_false, List.length_cons, filterMap_len c a b l]
    · simp only [if_true, filterMap_len c a b l]

theorem onRows_sh {x x' : WsFac} (h : FacAlike x x') (g : WsGrp) :
    ((x.onRows g).HV.size, (x.onRows g).pl.size, (x.onRows g).AV.size) =
      ((x'.onRows g).HV.size, (x'.onRows g).pl.size, (x'.onRows g).AV.size) := by
  unfold WsFac.onRows
  split
  · show (x.HV.size, (List.toArray _).size, 0) = (x'.HV.size, (List.toArray _).size, 0)
    have e := filterMap_len (fun i => g.takenBit (g.z - 1 - i)) (fun i => x.pt.getD i zeroE)
      (fun i => x'.pt.getD i zeroE) (List.range g.z)
    simp only [List.size_toArray]
    rw [h.1, e]
  · split
    · rfl
    · show (0, 0, x.AV.size) = (0, 0, x'.AV.size)
      rw [h.2.2]

theorem zip_onRows {l l' : List WsFac} (h : All2 FacAlike l l') : ∀ gs : List WsGrp,
    ((l.zip gs).map fun y => y.1.onRows y.2).map (fun x => (x.HV.size, x.pl.size, x.AV.size)) =
      ((l'.zip gs).map fun y => y.1.onRows y.2).map fun x => (x.HV.size, x.pl.size, x.AV.size) := by
  induction h with
  | nil => exact fun _ => rfl
  | cons h0 _ ih =>
    intro gs
    cases gs with
    | nil => rfl
    | cons g gs =>
      rw [List.zip_cons_cons, List.zip_cons_cons, List.map_cons, List.map_cons, List.map_cons,
        List.map_cons, ih gs, onRows_sh h0 g]

theorem rowPart_sh (lay : WsLay) {c c' : WsClaim} (h : ClaimAlike c c') (k k' : E) :
    recSh (wsRowPart lay c k) = recSh (wsRowPart lay c' k') := by
  unfold wsRowPart
  rw [h.1]
  cases lay.U[c'.ui]? with
  | none => rfl
  | some u =>
    show RecSh.mk c'.ui _ = RecSh.mk c'.ui _
    exact congrArg (RecSh.mk c'.ui) (zip_onRows h.2 u.g)

/-! ## The merge -/

theorem zip_slots_rel : ∀ (l : List Nat) (r r' : List E), r.length = r'.length →
    ∀ a a' : Aff, SameSh a a' →
      SameSh ((l.zip r).foldl (fun s y => Aff.addMul s (Aff.slot y.1) y.2) a)
        ((l.zip r').foldl (fun s y => Aff.addMul s (Aff.slot y.1) y.2) a')
  | [], _, _, _, _, _, h => by simpa using h
  | _ :: _, [], [], _, _, _, h => by simpa using h
  | _ :: _, [], _ :: _, hl, _, _, _ => by cases hl
  | _ :: _, _ :: _, [], hl, _, _, _ => by cases hl
  | j :: l, x :: r, x' :: r', hl, a, a', h => by
    rw [List.zip_cons_cons, List.zip_cons_cons, List.foldl_cons, List.foldl_cons]
    exact zip_slots_rel l r r' (Nat.succ.inj hl) _ _ (SameSh.addMul h (SameSh.refl _) _ _)

theorem wsForkStart_rel (sv : Array Nat) {rho rho' : Array E} (h : SameSize rho rho') :
    SameSh (wsForkStart sv rho) (wsForkStart sv rho') := by
  unfold wsForkStart
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_zip, Array.toList_zip]
  exact zip_slots_rel _ _ _ (by rw [Array.length_toList, Array.length_toList]; exact h) _ _
    (SameSh.refl _)

theorem wsForkRounds_rel : ∀ (n : Nat) (rm rm' : Array E) (p p' : Psc), SameSize rm rm' →
    PscAlike p p' →
      FlRel (fun x x' : Array E × Psc => SameSize x.1 x'.1 ∧ PscAlike x.2 x'.2)
        (Fl.wsForkRounds n rm p) (Fl.wsForkRounds n rm' p')
  | 0, _, _, _, _, hr, hp => by
    unfold Fl.wsForkRounds
    exact FlRel.pure ⟨hr, hp⟩
  | n + 1, rm, rm', p, p', hr, hp => by
    unfold Fl.wsForkRounds
    refine FlRel.bind (FlRel.roundIn .sum2 hp zeroE zeroE 0) fun x x' hx => ?_
    obtain ⟨r, q⟩ := x
    obtain ⟨r', q'⟩ := x'
    exact wsForkRounds_rel n _ _ q q' (by
      show (rm.push r).size = (rm'.push r').size
      rw [Array.size_push, Array.size_push, hr]) hx

/-- Two records of the merge of one shape. -/
def MergeAlike (w w' : WsForkOut) : Prop := mergeSh w = mergeSh w'

theorem zip_recs (lay : WsLay) (f f' : WsClaim → E → E) {l l' : List WsClaim}
    (h : All2 ClaimAlike l l') : ∀ r r' : List E, r.length = r'.length →
      ((l.zip r).map fun y => wsRowPart lay y.1 (f y.1 y.2)).map recSh =
        ((l'.zip r').map fun y => wsRowPart lay y.1 (f' y.1 y.2)).map recSh := by
  induction h with
  | nil => exact fun _ _ _ => rfl
  | cons h0 _ ih =>
    intro r r' hl
    cases r with
    | nil =>
      cases r' with
      | nil => rfl
      | cons _ _ => cases hl
    | cons x r =>
      cases r' with
      | nil => cases hl
      | cons x' r' =>
        rw [List.zip_cons_cons, List.zip_cons_cons, List.map_cons, List.map_cons, List.map_cons,
          List.map_cons, ih r r' (Nat.succ.inj hl), rowPart_sh lay h0]

theorem flatForkEnd_rel (lay : WsLay) {cl cl' : Array WsClaim}
    (h : All2 ClaimAlike cl.toList cl'.toList) (sv : Array Nat) :
    FlRel MergeAlike (flatForkEnd lay cl sv) (flatForkEnd lay cl' sv) := by
  unfold flatForkEnd Fl.wsForkMerge
  simp only [bind_assoc, pure_bind]
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.batch _) fun rho rho' hrho => ?_
  refine FlRel.bind (FlRel.pscBegin (wsForkStart_rel sv hrho)) fun p p' hp => ?_
  refine FlRel.bind (wsForkRounds_rel lay.lk _ _ p p' rfl hp) fun x x' hx => ?_
  obtain ⟨rm, q⟩ := x
  obtain ⟨rm', q'⟩ := x'
  refine FlRel.bind (FlRel.pscEnds hx.2 1 1) fun y y' hy => ?_
  obtain ⟨sFv, q2⟩ := y
  obtain ⟨sFv', q2'⟩ := y'
  obtain ⟨rfl, hq2⟩ : sFv = sFv' ∧ PscAlike q2 q2' := hy
  refine FlRel.bind (FlRel.shown _ _) fun fvp fvp' _ => ?_
  refine FlRel.pure ?_
  show MergeSh.mk rm.size (pscSh q2) sFv (((cl.zip rho).toList.map fun y =>
      wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 rm))).map recSh) =
    MergeSh.mk rm'.size (pscSh q2') sFv (((cl'.zip rho').toList.map fun y =>
      wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 rm'))).map recSh)
  rw [hx.1, hq2, Array.toList_zip, Array.toList_zip,
    zip_recs lay (fun c r => mulE r (wsEpsT lay c rm)) (fun c r => mulE r (wsEpsT lay c rm')) h
      rho.toList rho'.toList (by rw [Array.length_toList, Array.length_toList]; exact hrho)]

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.filterMap_len
#print axioms OnBytes.Desc.First.K4.Rt.onRows_sh
#print axioms OnBytes.Desc.First.K4.Rt.zip_onRows
#print axioms OnBytes.Desc.First.K4.Rt.rowPart_sh
#print axioms OnBytes.Desc.First.K4.Rt.zip_slots_rel
#print axioms OnBytes.Desc.First.K4.Rt.wsForkStart_rel
#print axioms OnBytes.Desc.First.K4.Rt.wsForkRounds_rel
#print axioms OnBytes.Desc.First.K4.Rt.zip_recs
#print axioms OnBytes.Desc.First.K4.Rt.flatForkEnd_rel
#print axioms OnBytes.Desc.First.K4.Rt.MergeAlike
