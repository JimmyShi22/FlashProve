-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/OneToAll.lean: WHAT THE LAW ON A PROXIMITY TEST's ACCEPTANCE ASKS
AT ONE LIST OF CHALLENGES IS ENOUGH FOR EVERY LIST THAT THE TEST's DECLARED ROUNDS CAN SAMPLE. The
premises of `accepts_every_list` (ShapeAll.lean in this folder) that name no challenge, `FrontAsks`
and `DataFront`, follow from `ShapeAsks` and `DataAsks` (PlanB.lean) at any one list: the way back
of ShapeAll.lean's two laws. So the two small synthetic places at which all is held at one list by
the kernel's own evaluation are members of `accepts_every_list`. Statements and proofs.

  **`frontAsks_of_shape`**, **`dataFront_of_data`**   the plan's test · `ShapeAsks` (`DataAsks`) and
                 `FormAsks` at one list ⟹ `FrontAsks` (`DataFront`)
  **`accepts_all_of_one`**   the plan's test · `FormPub` · the three structures at one list ⟹ at
                 every list that can be sampled the block's decision accepts all that the term shows
  **`every_one`**, **`every_came`**   so at the places of ToyAll.lean and ToyCame.lean: AT EVERY
                 LIST THAT THE PLACE's DECLARED ROUNDS CAN SAMPLE, at these toys' input, front and
                 coins

Limits. Those of ShapeAll.lean: the fresh table has come earlier; three stages or more; one family
of coins. The two members are small synthetic places, each at one input, front and family of coins;
that lists meet `drawsFit` there: EveryFits.lean in this folder. Nothing on completeness, on
soundness or on what is hidden.


-/
import Johnson.Desc.ProofFile.Honest.K12.ShapeAll
import Johnson.Desc.ProofFile.Honest.K12.SortsMember
import Johnson.Desc.ProofFile.Honest.K12.FormPubAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPub_of runRows_plain
  switchPubB SingleSh door_facts batT_codes rounds_split gpLS_eq)

variable {W X : Type}

/-- **`FrontAsks` from `ShapeAsks` at one list.** -/
theorem frontAsks_of_shape (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (hP : planB J.p K Dp.ts.length = true)
    (S : ShapeAsks J w fr C D K Dp) (F : FormAsks J w fr C D) : FrontAsks J w fr K Dp := by
  unfold planB planL at hP
  split at hP
  · rename_i a next nx' rest' hst
    have hA : stA J.p = a := by
      unfold stA
      rw [hst]
      rfl
    have hN : stN J.p = next := by
      unfold stN
      rw [hst]
      rfl
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hP
    obtain ⟨-, -, -, p4, p5, -⟩ := hP
    obtain ⟨id, hm⟩ := Option.isSome_iff_exists.1 S.came
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, -, s10⟩ := S
    have f1 := F.bat
    have f2 := F.fold
    have s2' := s2
    simp only [hA, hN] at s2' f2
    obtain ⟨G, row, x, H, hr, eB, -⟩ :=
      door_facts s2' hm s4 (fun G hG => runRows_plain s5 hG) s6 p4 f1
    have eR : J.recB w fr (D 0) = batT (J.rec₀ w fr) G row := (recB_eq J w fr (D 0)).trans eB
    rw [eR] at f2
    have FF := foldFront_first H x row hr
    have hfold := fold5_yes FF p5 _ f2
    have e1 := getD_of_ok (d := batT (J.rec₀ w fr) G row) hfold
    obtain ⟨rE, rR, hrs, hR'⟩ := rounds_split (length_of_foldCut p5) f2
    have hk0 : row.kept = #[] := H2K.Pin.combine_noKept0 _ _ _ _ _ hr fun k => H.noKept k
    have eT : tFold J w fr C D = foldT (batT (J.rec₀ w fr) G row) row
        (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
          a.h⟩ ((lettersOf J.p a next).n.code, (lettersOf J.p a next).n.maskCode) id
        (rE :: rR) := by
      show t1At J.p _ 0 (stA J.p) (laidS J.p) 1 (J.recB w fr (D 0)) _ D = _
      rw [hA, eR, ← hrs]
      exact e1
    refine ⟨s1, s2, s3, s4, s5, s6, fun G' hG' => ?_, fun G' id' hG' hm' => ?_⟩
    · obtain rfl : G = G' := Option.some.inj (H.group.symm.trans hG')
      obtain ⟨q1, q2, -, -, q5, q6⟩ := s7 row (layoutOf (J.rec₀ w fr).st G) (by rw [eR]; rfl)
      rw [eR] at q1
      refine ⟨q1, ?_, q5, q6⟩
      rw [← gpLS_eq] at q2 ⊢
      rw [hk0] at q2
      exact q2
    · obtain rfl : G = G' := Option.some.inj (H.group.symm.trans hG')
      obtain rfl : id = id' := Option.some.inj (hm.symm.trans hm')
      have q := (s10 _ _ (by rw [eT]; rfl)).1
      rw [eT] at q
      obtain ⟨y1, y2, y3, y4⟩ := foldOut_says (batT (J.rec₀ w fr) G row) row
        (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
          a.h⟩ id rE rR
      rw [hA] at q
      rw [hA, hN]
      refine (readPubB_congr _ _ _ _ y1 (y4 fun k => H.noKept k) ?_ y3 y2).symm.trans q
      show (rR.map drawnOf).length = a.k
      rw [List.length_map]
      exact hR'
  · simp at hP

/-- **`DataFront` from `DataAsks` at one list.** -/
theorem dataFront_of_data (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : ShapeAsks J w fr C D K Dp)
    (F : FormAsks J w fr C D) (Dt : DataAsks J w fr C D Dp c R) : DataFront J w fr C Dp c R := by
  refine ⟨Dt.cols, Dt.state, Dt.trees, fun G' hG' => ?_⟩
  unfold planB planL at hP
  split at hP
  · rename_i a next nx' rest' hst
    have hA : stA J.p = a := by
      unfold stA
      rw [hst]
      rfl
    have hN : stN J.p = next := by
      unfold stN
      rw [hst]
      rfl
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at hP
    obtain ⟨-, -, -, p4, -⟩ := hP
    obtain ⟨id, hm⟩ := Option.isSome_iff_exists.1 S.came
    have s2 := S.door
    simp only [hA, hN] at s2
    obtain ⟨G, row, x, H, hr, eB, -⟩ :=
      door_facts s2 hm S.tidy (fun G hG => runRows_plain S.plainRows hG) S.claims p4 F.bat
    have eR : J.recB w fr (D 0) = batT (J.rec₀ w fr) G row := (recB_eq J w fr (D 0)).trans eB
    obtain rfl : G = G' := Option.some.inj (H.group.symm.trans hG')
    have q := Dt.allSay row (layoutOf (J.rec₀ w fr).st G) (by rw [eR]; rfl) G hG'
    rw [eR] at q
    exact q
  · simp at hP

/-- **ONE LIST IS ENOUGH FOR ALL.** -/
theorem accepts_all_of_one (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (hF : formPubB J.p = true)
    (S : ShapeAsks J w fr C D K Dp) (F : FormAsks J w fr C D) (Dt : DataAsks J w fr C D Dp c R)
    (ds : List Fmt.Drawn) (hd : drawsFit ((laidOf J.p).map (·.1)) ds = true) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C (byNo ds)).rs.map noDigest) (testAll J w fr C (byNo ds)).gs = .ok t' := by
  cases hs : J.p.nums.stages with
  | nil =>
    unfold formPubB at hF
    rw [hs] at hF
    cases hF
  | cons a l =>
    cases l with
    | nil =>
      unfold formPubB at hF
      rw [hs] at hF
      cases hF
    | cons next rest =>
      exact accepts_every_list J w fr C K Dp c R hP a next rest hs (formPub_of_B _ _ _ _ hs hF)
        (frontAsks_of_shape J w fr C D K Dp hP S F)
        (dataFront_of_data J w fr C D K Dp c R hP S F Dt) ds hd

/-- **At the place of ToyAll.lean: at every list that can be sampled.** -/
theorem every_one (ds : List Fmt.Drawn)
    (hd : drawsFit ((laidOf (ToyGroup.one Toy.list₁).J.p).map (·.1)) ds = true) :
    ∃ t', (proximityTestKind guardedProximityTestParts (ToyGroup.one Toy.list₁).J.p : Block T12 Unit).decide
      ((ToyGroup.one Toy.list₁).J.rec₀ (ToyGroup.one Toy.list₁).w (ToyGroup.one Toy.list₁).fr)
      ((testAll (ToyGroup.one Toy.list₁).J (ToyGroup.one Toy.list₁).w (ToyGroup.one Toy.list₁).fr
        (ToyGroup.one Toy.list₁).C (byNo ds)).rs.map noDigest)
      (testAll (ToyGroup.one Toy.list₁).J (ToyGroup.one Toy.list₁).w (ToyGroup.one Toy.list₁).fr
        (ToyGroup.one Toy.list₁).C (byNo ds)).gs = .ok t' := by
  obtain ⟨Dp, hP, S, F, Dt⟩ := sorts_one
  exact accepts_all_of_one _ _ _ _ _ _ Dp _ _ hP formPubB_toy S F Dt ds hd

/-- **At the place of ToyCame.lean: at every list that can be sampled.** -/
theorem every_came (ds : List Fmt.Drawn)
    (hd : drawsFit ((laidOf (ToyCame.came 0).J.p).map (·.1)) ds = true) :
    ∃ t', (proximityTestKind guardedProximityTestParts (ToyCame.came 0).J.p : Block T12 Unit).decide
      ((ToyCame.came 0).J.rec₀ (ToyCame.came 0).w (ToyCame.came 0).fr)
      ((testAll (ToyCame.came 0).J (ToyCame.came 0).w (ToyCame.came 0).fr (ToyCame.came 0).C
        (byNo ds)).rs.map noDigest)
      (testAll (ToyCame.came 0).J (ToyCame.came 0).w (ToyCame.came 0).fr (ToyCame.came 0).C
        (byNo ds)).gs = .ok t' := by
  obtain ⟨Dp, hP, S, F, Dt⟩ := sorts_came
  exact accepts_all_of_one _ _ _ _ _ _ Dp _ _ hP formPubB_came S F Dt ds hd

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.frontAsks_of_shape
#print axioms ProofFile.Honest.K12.dataFront_of_data
#print axioms ProofFile.Honest.K12.accepts_all_of_one
#print axioms ProofFile.Honest.K12.every_one
#print axioms ProofFile.Honest.K12.every_came
