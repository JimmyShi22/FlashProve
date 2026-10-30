-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/K4Two.lean: K4's WHOLE HEARING AT TWO PUBLIC RECORDS THAT DIFFER IN THE
TABLE OF SCALES AND THE LAYOUT's THREE eps: where both runs return, what they leave has one shape.

  turnY            the layout with its three eps set.
  joinStart_rel, hearStack_rel   the texts of Johnson/Desc/First/K4/Returns/FlRelHear.lean at
                   EnvTurn (JoinTwo.lean), which has no field on the scales.
  **hear_turn**    the text of hear_rel (FlRelTop.lean) at two records. The layout's eps are read
                   nowhere in the hearing: Lean sees that by unfolding.

Limits. The weak form of the frame: where both runs return. Nothing is evaluated.
-/
import Johnson.AtFull.Shape.Scope.JoinTwo
import Johnson.Desc.First.K4.Returns.FlRelTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt.Two
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Flat (All2 OptRel FacAlike ClaimAlike mapM_opt_rel)
open OnBytes.Desc.First.K4.RtPub (ClaimSkel weightClaims_rel claimE_rel)
open VerifiableInference.Desc.First.Shape

/-- The layout with its three eps set. -/
def turnY (y : Lay) (e1 e2 eF : Nat) : Lay :=
  { y with h := { y.h with eps1 := e1, eps2 := e2, epsF := eF } }

theorem rel_of_some {α : Type} {R : α → α → Prop} {a b : Option α} {c d : α} (r : OptRel R a b)
    (h1 : a = some c) (h2 : b = some d) : R c d := by
  subst h1 h2
  exact r

attribute [local irreducible] OnBytes.Flat.OptRel

theorem joinStart_rel {v v' : Env} (S : EnvTurn v v') {H H' : Heard} (h : NormsAlike H H')
    (om om' : Array E) :
    FlRel SameSh (joinStart engFl v H om) (joinStart engFl v' H' om') := by
  unfold joinStart
  dsimp only
  have hw : v.weighedOf = v'.weighedOf := funext fun c => weighedOf_y S.keys.y c
  rw [S.keys.y, hw]
  refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => by
    rw [ha] at hb
    exact Option.some.inj hb) fun weighed weighed' hwe => ?_
  subst hwe
  refine FlRel.bind (FlRel.getRel (mapM_opt_rel (R := SameSh)
    (f := fun x : (CallD × Array Bool) × Nat =>
      v.joinPart H.fo.alpha H.fo.theta x.2 x.1.1 x.1.2)
    (f' := fun x : (CallD × Array Bool) × Nat =>
      v'.joinPart H'.fo.alpha H'.fo.theta x.2 x.1.1 x.1.2)
    (fun x => joinPart_rel S H.fo.alpha H.fo.theta H'.fo.alpha H'.fo.theta x.2 x.1.1 x.1.2 x.1.2)
    _)) fun parts parts' hp => ?_
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.getAny _ _) fun laid laid' _ => ?_
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.getRel h.tT) fun tT tT' ht => ?_
  refine FlRel.pure ?_
  have c1 : tT.sCl = tT'.sCl := congrArg TscSh.sCl ht
  have c2 : SameSh H.fo.cEnd H'.fo.cEnd :=
    congrArg HeardAll.cEnd (congrArg NormsSh.fo h : heardAll H.fo = heardAll H'.fo)
  have c3 : SameSh H.KT H'.KT := congrArg NormsSh.KT h
  rw [c1]
  exact SameSh.addMul (SameSh.sub (SameSh.sub (SameSh.add
    (parts_fold_rel _ _ hp 0 _ _ (SameSh.refl _)) (SameSh.const _ _)) (SameSh.refl _)) c2) c3 _ _


theorem hearStack_rel (P : Pub) {v v' : Env} (S : EnvTurn v v') {H H' : Heard}
    (h : NormsAlike H H') (lamS NCLp : Nat) :
    FlRel StackAlike (hearStack engFl P v H lamS NCLp) (hearStack engFl P v' H' lamS NCLp) := by
  unfold hearStack
  dsimp only
  refine FlRel.bind (FlRel.batch 2) fun om om' _ => ?_
  refine FlRel.bind (FlRel.getRel h.tT) fun tT tT' ht => ?_
  refine FlRel.bind (FlRel.shownAll _ _ _) fun shownT shownT' _ => ?_
  refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => by
    rw [ha] at hb
    exact Option.some.inj hb) fun TS TS' hTS => ?_
  subst hTS
  refine FlRel.bind (FlRel.getRel (panels_shp (W := False)
    (p := { v := v, e := H.fo.e, shownT := shownT, zt := H.ztF, stubO := stubO P.y })
    (p₀ := { v := v', e := H'.fo.e, shownT := shownT', zt := H'.ztF, stubO := stubO P.y })
    S.keys (fun f => f.elim) TS)) fun pans pans' hpans => ?_
  obtain ⟨hbl, hplaces⟩ := placePanels_shp hpans.bl
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (joinStart_rel S h om om') fun C C' hC => ?_
  refine FlRel.bind (FlRel.pscBegin hC) fun p p' hp => ?_
  refine FlRel.bind (plainRounds_rel (st := { lam := lamS, p := p })
    (st' := { lam := lamS, p := p' }) rfl hp) fun st st' hst => ?_
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.pscEnds hst.2 2 _) fun x x' hx => ?_
  obtain ⟨sA0, q⟩ := x
  obtain ⟨sA0', q'⟩ := x'
  obtain ⟨rfl, hq⟩ : sA0 = sA0' ∧ PscAlike q q' := hx
  refine FlRel.bind (FlRel.shownAll _ _ _) fun sh1 sh1' _ => ?_
  refine FlRel.bind (FlRel.shownAll _ _ _) fun sh2 sh2' _ => ?_
  refine FlRel.bind (FlRel.shown _ _) fun a a' _ => ?_
  refine FlRel.bind (FlRel.shown _ _) fun b b' _ => ?_
  refine FlRel.bind (FlRel.getRel (stackEnd_shp (W := False) P.y lamS om sh1 sh2 om' sh1' sh2'
    a b a' b' hbl hst.1)) fun fin fin' hfin => ?_
  refine FlRel.bind (FlRel.pscRow hq _ _ (SameSh.refl {})) fun z z' hz => ?_
  obtain ⟨rowS, q2⟩ := z
  obtain ⟨rowS', q2'⟩ := z'
  refine FlRel.pure ?_
  show StackSh.mk st.rs.size sA0 (sA0 + 1) (sA0 + 1 + (1 + P.y.LamM))
      (sA0 + 1 + (1 + P.y.LamM) + 1) (affSh fin.Alin) (affSh fin.Blin) fin.wD (affSh rowS) =
    StackSh.mk st'.rs.size sA0 (sA0 + 1) (sA0 + 1 + (1 + P.y.LamM))
      (sA0 + 1 + (1 + P.y.LamM) + 1) (affSh fin'.Alin) (affSh fin'.Blin) fin'.wD (affSh rowS')
  rw [hst.1, hfin.1, hfin.2.1, hfin.2.2, hz.1]


set_option maxHeartbeats 4000000 in
/-- **K4's HEARING AT TWO RECORDS**: at ledgers of one shape, tapes of one shape, lookup's records of
one shape, any two lists of tokens, any table of scales and any three eps: where both runs return,
what they leave has one shape, and so have the ledgers behind. -/
theorem hear_turn (P : Pub) (e1 e2 eF : Nat) (s : Layer.Scales) (t t' : Array Nat) (hp : HPlan2) (g : Nat)
    {fo fo' : Forest.Heard} (hfo : heardAll fo = heardAll fo') :
    FlRel HeardAlike (hear engFl { P with y := turnY P.y e1 e2 eF, sc := s, tokv := t } hp g fo)
      (hear engFl { P with tokv := t' } hp g fo') := by
  unfold hear
  dsimp only
  by_cases hg : (g == 0) = true
  · simp only [hg, if_true]
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => Option.some.inj (ha.symm.trans hb)) fun iU3 iU3' hi => ?_
    subst hi
    refine FlRel.bind (hearNorms_rel P g hfo) fun H1 H1' hH1 => ?_
    refine FlRel.bind (hearTerms_rel P hH1) fun H H' hH => ?_
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => Option.some.inj (ha.symm.trans hb)) fun x x' hx => ?_
    subst hx
    obtain ⟨tab, laid, nU3⟩ := x
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    have S : EnvTurn
        { y := P.y, sc := s, g := g, iU3 := iU3,
          K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo.zk }
        { y := P.y, sc := P.sc, g := g, iU3 := iU3,
          K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo'.zk } :=
      ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    refine FlRel.bind (hearStack_rel P S hH _ _) fun K K' hK => ?_
    refine FlRel.bind (hearGated_rel P hH hK) fun z z' hz => ?_
    obtain ⟨hd, hd2⟩ := z
    obtain ⟨hd', hd2'⟩ := z'
    refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => Option.some.inj (ha.symm.trans hb)) fun TS TS' hTS => ?_
    subst hTS
    have CS : ClaimSkel
        { v := { y := P.y, sc := s, g := g, iU3 := iU3,
                 K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo.zk },
          wsLay := P.wsLay, rope := P.rope, rs := K.rs, rt := (H.tT.map (·.r)).getD #[] }
        { v := { y := P.y, sc := P.sc, g := g, iU3 := iU3,
                 K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo'.zk },
          wsLay := P.wsLay, rope := P.rope, rs := K'.rs, rt := (H'.tT.map (·.r)).getD #[] } :=
      ⟨rfl, rfl, rfl, congrArg StackSh.rs hK, zk_sizes hfo⟩
    refine FlRel.bind (FlRel.getRel (weightClaims_rel CS TS)) fun cP cP' hcP => ?_
    refine FlRel.bind (S := All2 ClaimAlike) (FlRel.get fun a b ha hb => ?_) fun cE cE' hcE => ?_
    · obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ha
      obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 hb
      have k1 : (t.size != P.y.T || t.any (· ≥ P.V)) = false := claimE_tok hx
      have k2 : (t'.size != P.y.T || t'.any (· ≥ P.V)) = false := claimE_tok hx'
      rw [Bool.or_eq_false_iff] at k1 k2
      have s1 : t.size = t'.size := by
        have a1 : t.size = P.y.T := by simpa using k1.1
        have a2 : t'.size = P.y.T := by simpa using k2.1
        rw [a1, a2]
      have r := claimE_rel CS (congrArg NormsSh.ZE hH : H.ZE.size = H'.ZE.size)
        (congrArg NormsSh.tkh hH : H.tkh.size = H'.tkh.size) P.V s1 (k1.2.trans k2.2.symm)
      exact .cons (rel_of_some r hx hx') .nil
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (FlRel.claimsIn 1) fun sVE sVE' hs => ?_
    subst hs
    have k1 : K.sV = K'.sV := congrArg StackSh.sV hK
    rw [k1]
    refine FlRel.bind (flatForkEnd_rel P.wsLay (cl := (cP ++ cE).toArray)
      (cl' := (cP' ++ cE').toArray) (hcP.append hcE) _) fun wo wo' hwo => ?_
    refine FlRel.bind (FlRel.getRel (pointsOf_rel P.y hH hz.1 hz.2)) fun pts pts' hpts => ?_
    refine FlRel.bind (FlRel.getRel (funsOf_rel P.y hfo hpts laid)) fun funs funs' hf => ?_
    refine FlRel.pure ⟨?_, hf⟩
    show OwnSh.mk g iU3 _ (tab.map fun x => (x.name, x.first, x.len)) (fo.zk.toList.map (·.size))
        (normsSh H) (stackSh K) (levelSh hd) (some (levelSh hd2)) sVE (mergeSh wo) =
      OwnSh.mk g iU3 _ (tab.map fun x => (x.name, x.first, x.len)) (fo'.zk.toList.map (·.size))
        (normsSh H') (stackSh K') (levelSh hd') (some (levelSh hd2')) sVE (mergeSh wo')
    rw [show fo.zk.toList.map (·.size) = fo'.zk.toList.map (·.size) from
      congrArg HeardAll.zk hfo, show normsSh H = normsSh H' from hH,
      show stackSh K = stackSh K' from hK, show levelSh hd = levelSh hd' from hz.1,
      show levelSh hd2 = levelSh hd2' from hz.2, show mergeSh wo = mergeSh wo' from hwo]
  · simp only [hg, if_false, Bool.false_eq_true, pure_bind]
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => Option.some.inj (ha.symm.trans hb)) fun iU3 iU3' hi => ?_
    subst hi
    refine FlRel.bind (hearNorms_rel P g hfo) fun H1 H1' hH1 => ?_
    refine FlRel.bind (hearTerms_rel P hH1) fun H H' hH => ?_
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => Option.some.inj (ha.symm.trans hb)) fun x x' hx => ?_
    subst hx
    obtain ⟨tab, laid, nU3⟩ := x
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    have S : EnvTurn
        { y := P.y, sc := s, g := g, iU3 := iU3,
          K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo.zk }
        { y := P.y, sc := P.sc, g := g, iU3 := iU3,
          K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo'.zk } :=
      ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    refine FlRel.bind (hearStack_rel P S hH _ _) fun K K' hK => ?_
    refine FlRel.bind (hearGated_rel P hH hK) fun z z' hz => ?_
    obtain ⟨hd, hd2⟩ := z
    obtain ⟨hd', hd2'⟩ := z'
    refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => Option.some.inj (ha.symm.trans hb)) fun TS TS' hTS => ?_
    subst hTS
    have CS : ClaimSkel
        { v := { y := P.y, sc := s, g := g, iU3 := iU3,
                 K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo.zk },
          wsLay := P.wsLay, rope := P.rope, rs := K.rs, rt := (H.tT.map (·.r)).getD #[] }
        { v := { y := P.y, sc := P.sc, g := g, iU3 := iU3,
                 K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo'.zk },
          wsLay := P.wsLay, rope := P.rope, rs := K'.rs, rt := (H'.tT.map (·.r)).getD #[] } :=
      ⟨rfl, rfl, rfl, congrArg StackSh.rs hK, zk_sizes hfo⟩
    refine FlRel.bind (FlRel.getRel (weightClaims_rel CS TS)) fun cP cP' hcP => ?_
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    have k1 : K.sV = K'.sV := congrArg StackSh.sV hK
    rw [k1]
    refine FlRel.bind (flatForkEnd_rel P.wsLay (cl := (cP ++ []).toArray)
      (cl' := (cP' ++ []).toArray) (hcP.append .nil) _) fun wo wo' hwo => ?_
    refine FlRel.bind (FlRel.getRel (pointsOf_rel P.y hH hz.1 hz.2)) fun pts pts' hpts => ?_
    refine FlRel.bind (FlRel.getRel (funsOf_rel P.y hfo hpts laid)) fun funs funs' hf => ?_
    refine FlRel.pure ⟨?_, hf⟩
    show OwnSh.mk g iU3 _ (tab.map fun x => (x.name, x.first, x.len)) (fo.zk.toList.map (·.size))
        (normsSh H) (stackSh K) (levelSh hd) (some (levelSh hd2)) 0 (mergeSh wo) =
      OwnSh.mk g iU3 _ (tab.map fun x => (x.name, x.first, x.len)) (fo'.zk.toList.map (·.size))
        (normsSh H') (stackSh K') (levelSh hd') (some (levelSh hd2')) 0 (mergeSh wo')
    rw [show fo.zk.toList.map (·.size) = fo'.zk.toList.map (·.size) from
      congrArg HeardAll.zk hfo, show normsSh H = normsSh H' from hH,
      show stackSh K = stackSh K' from hK, show levelSh hd = levelSh hd' from hz.1,
      show levelSh hd2 = levelSh hd2' from hz.2, show mergeSh wo = mergeSh wo' from hwo]


end OnBytes.Desc.First.K4.Rt.Two

#print axioms OnBytes.Desc.First.K4.Rt.Two.hear_turn
