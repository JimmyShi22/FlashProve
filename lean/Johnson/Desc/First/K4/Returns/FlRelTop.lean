-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/FlRelTop.lean: TWO RUNS OF ONE TEXT (FlRel,
Johnson/Desc/First/K4/Returns/FlRel.lean): K4's WHOLE HEARING (hear,
OnBytes/Desc/First/K4/Hear.lean, at the engine of plain functions). A general law: nothing is
evaluated.

  zk_sizes, claimE_tok   two small tools: the calls' points' sizes; where the embedding's claim is
                  there, the request's tokens have passed its test.
  HeardAlike      what the hearing leaves, twice: one shape (ownSh,
                  Johnson/Desc/First/Shape/Own.lean); tables of one shape.
  **hear_rel**    at ledgers of one shape, tapes of one shape, lookup's records of one shape AND ANY
                  TWO LISTS OF TOKENS: where both runs return, HeardAlike, and the ledgers behind
                  have one shape.

Limits. The weak form of the frame: that one run returns where the other does is not said. Nothing
on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.FlRelWhole
import Johnson.Desc.First.K4.Returns.FunsRel

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

/-- The calls' points have one size each. -/
theorem zk_sizes {fo fo' : Forest.Heard} (h : heardAll fo = heardAll fo') (q : Nat) :
    (fo.zk.getD q #[]).size = (fo'.zk.getD q #[]).size := by
  have e : fo.zk.toList.map (·.size) = fo'.zk.toList.map (·.size) := congrArg HeardAll.zk h
  have e' := congrArg (fun l => l.getD q 0) e
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList] at e'
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  cases h1 : fo.zk[q]? <;> cases h2 : fo'.zk[q]? <;> rw [h1, h2] at e' <;> simpa using e'

/-- Where the embedding's claim is there, the request's tokens have passed its test. -/
theorem claimE_tok {c : ClaimEnv} {ZE tkh : Array E} {V : Nat} {t : Array Nat} {x : WsClaim}
    (h : c.claimE ZE tkh V t = some x) : (t.size != c.v.y.T || t.any (· ≥ V)) = false := by
  cases hc : (t.size != c.v.y.T || t.any (· ≥ V)) with
  | false => rfl
  | true =>
    exfalso
    unfold ClaimEnv.claimE at h
    dsimp only at h
    rw [if_pos hc] at h
    cases h

/-- What K4's hearing leaves, twice: one shape; tables of one shape. -/
def HeardAlike (o o' : Own) : Prop := ownSh o = ownSh o' ∧ FunsAlike o.funs o'.funs

attribute [local irreducible] OnBytes.Flat.OptRel

/-- **K4's HEARING, TWICE: at ledgers of one shape, tapes of one shape, lookup's records of one
shape, and any two lists of tokens**: where both runs return, what they leave has one shape, and so
have the ledgers behind. -/
theorem hear_rel (P : Pub) (t t' : Array Nat) (hp : HPlan2) (g : Nat) {fo fo' : Forest.Heard}
    (hfo : heardAll fo = heardAll fo') :
    FlRel HeardAlike (hear engFl { P with tokv := t } hp g fo)
      (hear engFl { P with tokv := t' } hp g fo') := by
  have n1 : ∀ (u : Array Nat) (f : Forest.Heard),
      hearNorms engFl { P with tokv := u } g f = hearNorms engFl P g f := fun _ _ => rfl
  have n2 : ∀ (u : Array Nat) (H : Heard),
      hearTerms engFl { P with tokv := u } H = hearTerms engFl P H := fun _ _ => rfl
  have n3 : ∀ (u : Array Nat) (v : Env) (H : Heard) (a b : Nat),
      hearStack engFl { P with tokv := u } v H a b = hearStack engFl P v H a b :=
    fun _ _ _ _ _ => rfl
  have n4 : ∀ (u : Array Nat) (H : Heard) (K : HeardStack),
      hearGated engFl { P with tokv := u } H K = hearGated engFl P H K := fun _ _ _ => rfl
  have n5 : ∀ u : Array Nat, callsTS { P with tokv := u } = callsTS P := fun _ => rfl
  unfold hear
  dsimp only
  simp only [n1, n2, n3, n4, n5]
  by_cases hg : (g == 0) = true
  · simp only [hg, if_true]
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => by
      rw [ha] at hb
      exact Option.some.inj hb) fun iU3 iU3' hi => ?_
    subst hi
    refine FlRel.bind (hearNorms_rel P g hfo) fun H1 H1' hH1 => ?_
    refine FlRel.bind (hearTerms_rel P hH1) fun H H' hH => ?_
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => by
      rw [ha] at hb
      exact Option.some.inj hb) fun x x' hx => ?_
    subst hx
    obtain ⟨tab, laid, nU3⟩ := x
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    have S : EnvSame
        { y := P.y, sc := P.sc, g := g, iU3 := iU3,
          K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo.zk }
        { y := P.y, sc := P.sc, g := g, iU3 := iU3,
          K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo'.zk } :=
      ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
    refine FlRel.bind (hearStack_rel P S hH _ _) fun K K' hK => ?_
    refine FlRel.bind (hearGated_rel P hH hK) fun z z' hz => ?_
    obtain ⟨hd, hd2⟩ := z
    obtain ⟨hd', hd2'⟩ := z'
    refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => by
      rw [ha] at hb
      exact Option.some.inj hb) fun TS TS' hTS => ?_
    subst hTS
    have CS : ClaimSkel
        { v := { y := P.y, sc := P.sc, g := g, iU3 := iU3,
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
      have k1 := claimE_tok hx
      have k2 := claimE_tok hx'
      rw [Bool.or_eq_false_iff] at k1 k2
      have s1 : t.size = t'.size := by
        have a1 : t.size = P.y.T := by simpa using k1.1
        have a2 : t'.size = P.y.T := by simpa using k2.1
        rw [a1, a2]
      have r := claimE_rel CS (congrArg NormsSh.ZE hH : H.ZE.size = H'.ZE.size)
        (congrArg NormsSh.tkh hH : H.tkh.size = H'.tkh.size) P.V s1 (k1.2.trans k2.2.symm)
      rw [hx, hx'] at r
      exact .cons (by
        unfold OnBytes.Flat.OptRel at r
        exact r) .nil
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
    refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => by
      rw [ha] at hb
      exact Option.some.inj hb) fun iU3 iU3' hi => ?_
    subst hi
    refine FlRel.bind (hearNorms_rel P g hfo) fun H1 H1' hH1 => ?_
    refine FlRel.bind (hearTerms_rel P hH1) fun H H' hH => ?_
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => by
      rw [ha] at hb
      exact Option.some.inj hb) fun x x' hx => ?_
    subst hx
    obtain ⟨tab, laid, nU3⟩ := x
    refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
    have S : EnvSame
        { y := P.y, sc := P.sc, g := g, iU3 := iU3,
          K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo.zk }
        { y := P.y, sc := P.sc, g := g, iU3 := iU3,
          K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo'.zk } :=
      ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
    refine FlRel.bind (hearStack_rel P S hH _ _) fun K K' hK => ?_
    refine FlRel.bind (hearGated_rel P hH hK) fun z z' hz => ?_
    obtain ⟨hd, hd2⟩ := z
    obtain ⟨hd', hd2'⟩ := z'
    refine FlRel.bind (S := Eq) (FlRel.get fun a b ha hb => by
      rw [ha] at hb
      exact Option.some.inj hb) fun TS TS' hTS => ?_
    subst hTS
    have CS : ClaimSkel
        { v := { y := P.y, sc := P.sc, g := g, iU3 := iU3,
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

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.zk_sizes
#print axioms OnBytes.Desc.First.K4.Rt.claimE_tok
#print axioms OnBytes.Desc.First.K4.Rt.hear_rel
#print axioms OnBytes.Desc.First.K4.Rt.HeardAlike
