-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the clauses at the second part's entry from what the first part has heard.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/AsksFromFront.lean: shapeAsksD_of_front and dataAsks_of_frontD
(ShapeAllDense.lean) with, of FormAsks, only the two clauses that their proofs use, bat and fold. At
the second part's entry only the first part's challenges have been heard, and these two clauses
read no others. The proofs are those two, with these two clauses in the place of F.

  shapeAsksD_of_first, dataAsks_of_first   the two
  bat_fold_of_heard   the two clauses at a list that fits the first part's declared rounds

No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.ShapeAllDense
import Johnson.Desc.ProofFile.Honest.K12.FormDraws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open ProofFile.Honest ProofFile.Honest.K12
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open ProofFile.Honest.Sh (door_facts_dense)
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPub_of runRows_plain
  switchPubB SingleSh door_facts batT_codes rounds_split gpLS_eq)
variable {W X : Type}

theorem shapeAsksD_of_first (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (hP : planB J.p K Dp.ts.length = true)
    (S : FrontAsksD J w fr K Dp) (fb : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true)
    (ff : roundsFit (((laidS J.p).take (1 + (stA J.p).k)).map (·.1))
      (rfAt (coinsOf J.p.nums.stages C.hide C.rest) 0 (stA J.p) 1 (J.recB w fr (D 0))
        (J.first w fr C) D) = true) : ShapeAsksD J w fr C D K Dp := by
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
    obtain ⟨-, -, p3, p4, p5, p6, -⟩ := hP
    obtain ⟨id, hm⟩ := Option.isSome_iff_exists.1 S.came
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s9⟩ := S
    have f1 := fb
    have f2 := ff
    have s2' := s2
    simp only [hA, hN] at s2' s7 s9 f2
    have Pl := switchPub_of p3
    rw [← s1] at Pl
    obtain ⟨G, row, x, H, hr, eB, -⟩ :=
      door_facts_dense s2' hm s4 s5 s6 p4 f1
    have eR : J.recB w fr (D 0) = batT (J.rec₀ w fr) G row := (recB_eq J w fr (D 0)).trans eB
    rw [eR] at f2
    have FF := foldFront_first H x row hr
    have hfold := fold5_yes FF p5 _ f2
    have e1 := getD_of_ok (d := batT (J.rec₀ w fr) G row) hfold
    obtain ⟨rE, rR, hrs, hR'⟩ := rounds_split (length_of_foldCut p5) f2
    have hk0 : row.kept = #[] := H2K.Pin.combine_noKept0 _ _ _ _ _ hr fun k => H.noKept k
    have kk : (sgOf a).h + (sgOf a).g = a.k := kk_eq p6
    obtain ⟨q1, q2, q3, q4⟩ := s7 G H.group
    have eT : tFold J w fr C D = foldT (batT (J.rec₀ w fr) G row) row
        (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
          a.h⟩ ((lettersOf J.p a next).n.code, (lettersOf J.p a next).n.maskCode) id
        (rE :: rR) := by
      show t1At J.p _ 0 (stA J.p) (laidS J.p) 1 (J.recB w fr (D 0)) _ D = _
      rw [hA, eR, ← hrs]
      exact e1
    refine ⟨s1, s2, s3, s4, s5, s6, ?_, ?_, ?_⟩
    ·
      intro row' L' h
      rw [eR] at h ⊢
      have h' : Passing.claim row (layoutOf (J.rec₀ w fr).st G) = .claim row' L' := h
      injection h' with h1 h2
      subst h1 h2
      rw [hA]
      refine ⟨q1, ?_, H.layK.trans kk.symm, H.layH, q3, q4⟩
      rw [← gpLS_eq, hk0]
      rw [← gpLS_eq] at q2
      exact q2
    · rw [eT]
      exact (foldT_keeps _ _ _ _ _ _ _).1.trans ((batT_codes _ G row).trans s1)
    ·
      intro rows gp h
      rw [eT] at h ⊢
      have h' : Passing.single (foldOut (batT (J.rec₀ w fr) G row) row
          (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2,
            a.k, a.h⟩ id (rE :: rR)) (batT (J.rec₀ w fr) G row).st.groups.size =
          .single rows gp := h
      injection h' with h1 h2
      subst h1 h2
      rw [hA, hN]
      obtain ⟨y1, y2, y3, y4⟩ := foldOut_says (batT (J.rec₀ w fr) G row) row
        (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
          a.h⟩ id rE rR
      constructor
      · refine (readPubB_congr _ _ _ _ y1 (y4 fun k => H.noKept k) ?_ y3 y2).trans
          (s9 G id H.group hm)
        show (rR.map drawnOf).length = a.k
        rw [List.length_map]
        exact hR'
      · have hcodes : (batT (J.rec₀ w fr) G row).st.codes = (J.rec₀ w fr).st.codes :=
          batT_codes _ G row
        have Pl' : SwitchPub J.p (batT (J.rec₀ w fr) G row).st.codes 0 a next
            (nx' :: rest').isEmpty ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
              a.h⟩ (lettersOf J.p a next).n (lettersOf J.p a next).dS
            (lettersOf J.p a next).dC := by
          rw [hcodes]
          exact Pl
        have hrow : foldRowOk (spent (batT (J.rec₀ w fr) G row).st id)
            (ioppFoldShape ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
              (layoutOf (J.rec₀ w fr).st G)) row = true :=
          (Own.foldRowFits_agrees _ _ _).trans ((foldRowFits_spent _ _ _ _).trans FF.rowFits)
        have hlen : (rR.map drawnOf).length = a.k := by
          rw [List.length_map]
          exact hR'
        rw [(foldT_keeps _ _ _ _ _ _ _).1]
        obtain ⟨g1, g2, g3, g4, g5, -⟩ := foldedFit_pure (batT (J.rec₀ w fr) G row).st.codes
          (sgOf a) (sgOf next) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
          Pl'.codes (lettersOf J.p a next).n.code (lettersOf J.p a next).n.maskCode Pl'.zk
          Pl'.codeN Pl'.zkN Pl'.small (batT (J.rec₀ w fr) G row).st
          (spent (batT (J.rec₀ w fr) G row).st id) row (layoutOf (J.rec₀ w fr).st G) id
          (drawnOf rE) (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target))
          (rR.map drawnOf) rfl rfl hk0 (fun k _ => H.noKept k) (hlen.trans Pl.codes.k)
          ((Own.foldShapeFits_agrees _ _).trans FF.shape) hrow
        exact ⟨g1, g2, g3, g4, g5⟩
  · simp at hP

theorem dataAsks_of_first (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (S : FrontAsksD J w fr K Dp)
    (fb : roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], D 0⟩] = true) (Dt : DataFront J w fr C Dp c R) :
    DataAsks J w fr C D Dp c R := by
  refine ⟨Dt.cols, Dt.state, Dt.trees, fun row' L' h G' hG' => ?_⟩
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
      door_facts_dense s2 hm S.tidy S.denseRows S.claims p4 fb
    have eR : J.recB w fr (D 0) = batT (J.rec₀ w fr) G row := (recB_eq J w fr (D 0)).trans eB
    obtain rfl : G = G' := Option.some.inj (H.group.symm.trans hG')
    rw [eR] at h ⊢
    have h' : Passing.claim row (layoutOf (J.rec₀ w fr).st G) = .claim row' L' := h
    injection h' with h1 h2
    subst h1 h2
    exact Dt.allSay G hG'
  · simp at hP


/-- **The two clauses at a list that fits the first part's declared rounds.** -/
theorem bat_fold_of_heard (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (ds : List Fmt.Drawn) (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = a :: next :: rest) (P : FormPub J.p a next rest)
    (hd : drawsFit (((laidOf J.p).take (2 + a.k)).map (·.1)) ds = true) :
    roundsFit (((laidOf J.p).take 1).map (·.1)) [⟨[], byNo ds 0⟩] = true ∧
    roundsFit (((laidS J.p).take (1 + (stA J.p).k)).map (·.1))
      (rfAt (coinsOf J.p.nums.stages C.hide C.rest) 0 (stA J.p) 1 (J.recB w fr (byNo ds 0))
        (J.first w fr C) (byNo ds)) = true := by
  have hA : stA J.p = a := by
    unfold stA
    rw [hst]
    rfl
  have kk : (sgOf a).h + (sgOf a).g = a.k := kk_eq P.hk
  have F0 := fitFrom_of_draws ((laidOf J.p).take (2 + a.k)) ds hd
  have Fb : FitFrom (byNo ds) ((laidOf J.p).take 1) 0 := by
    have := F0.take 1
    rwa [List.take_take, Nat.min_eq_left (by omega)] at this
  have F1 : FitFrom (byNo ds) ((laidS J.p).take (1 + a.k)) 1 := by
    have := F0.drop 1
    rw [Nat.zero_add] at this
    have e : ((laidOf J.p).take (2 + a.k)).drop 1 = (laidS J.p).take (1 + a.k) := by
      show _ = ((laidOf J.p).drop 1).take (1 + a.k)
      rw [List.drop_take]
      congr 1
      omega
    rwa [e] at this
  have S1 : (laidS J.p).map asked = ([.e] :: List.replicate a.k [.e, .e]) ++
      ([[], [.answer]] ++ bodyItems next rest) := by
    have e := congrArg (List.drop 1) P.sorts
    rw [← List.map_drop] at e
    refine e.trans ?_
    show bodyItems a (next :: rest) = _
    rw [bodyItems, kk, List.append_assoc]
  have hlenF : ([Fmt.Item.e] :: List.replicate a.k [Fmt.Item.e, Fmt.Item.e]).length = 1 + a.k := by
    rw [List.length_cons, List.length_replicate, Nat.add_comm]
  refine ⟨?_, ?_⟩
  · refine roundsFit_sorts ((laidOf J.p).take 1) 0 _ Fb (fun n r h => ?_) ?_
    · match n, h with
      | 0, h =>
        obtain rfl := Option.some.inj h
        rfl
    · rw [List.map_take, P.sorts]
      rfl
  · simp only [hA]
    refine roundsFit_sorts ((laidS J.p).take (1 + a.k)) 1 _ F1
      (fun n r h => drawn_fold _ _ _ _ _ _ _ n r h) ?_
    rw [aFold_sorts, kk, List.map_take, S1, List.take_left' hlenF]

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.shapeAsksD_of_first
#print axioms ProofFile.Honest.K12.Sim2.dataAsks_of_first
#print axioms ProofFile.Honest.K12.Sim2.bat_fold_of_heard
