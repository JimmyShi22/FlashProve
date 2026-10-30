-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/ShapeAsksOwn.lean

`ShapeAsksO` FROM WHAT STANDS IN FRONT OF THE TEST, WHERE THE FIRST FOLD SENDS ITS OWN TABLE: the twin of
`shapeAsks_of_front` (ShapeAll.lean in the folder above). The fold's laws are taken at `enteredT`
(`front_entered`): so its single rows, their public test and `OldOk` are the first case's, at the state that
the entering leaves.

  `FrontAsksO`   the twin of `FrontAsks`: `came` turned to `noMask`; `pub` at the new message's number, at the
                 statement and book that the entering leaves
  `shapeAsks_of_front_own`   the statement

HOW EACH PREMISE WOULD BE PAID AT jobKO. hP: `planOB_KO_full` at Dp.ts.length = 3; `ts_O` says 3 of the shape. S: codes,
door, tidy, plainRows, claims, plain: the closed lines of KeyTenLinesKernel.lean under `shape_doorOmegaF`,
`three_doorOmegaF`; plain by `frontPlain₀_of_B` (FrontAtShape.lean, general in the place) at `plain_O`. noMask by text.
pub: `frontPubOwn_of_B` (FrontPubOwn.lean) at the closed line. F: `formAsks_of_draws`.

Limits. Conditional. The state on entry is compared with nothing here. Nothing on completeness, on soundness or
on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Own.EndOkOwn
import Johnson.Desc.ProofFile.Honest.K12.Own.DataAsksOwn
import Johnson.Desc.K12.Honest.OwnFoldFirst
import Johnson.Desc.K12.Honest.OwnFoldLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TermAsks SwitchPub claimsB testSh readPubB singleSh switchPub_of runRows_plain
  doorB testFrontOwn_of batOwes_of cameB tBat batT_codes rounds_split gpLS_eq length_of_foldCutOwn)

variable {W X : Type}

section Asks
variable (J : TestJob W X) (w : W) (fr : Front X)

/-- **What is asked of the state in front, where the first fold sends its own table.** -/
structure FrontAsksO (K : Codes) (Dp : Plain) : Prop where
  codes : (J.rec₀ w fr).st.codes = K
  door : Sh.doorB J.p (stA J.p) (stN J.p) (((laidOf J.p).take 1).map (·.1))
    (lettersOf J.p (stA J.p) (stN J.p)).i
    ((lettersOf J.p (stA J.p) (stN J.p)).n.code, (lettersOf J.p (stA J.p) (stN J.p)).n.maskCode)
    (testSh (J.rec₀ w fr)) = true
  noMask : (J.rec₀ w fr).mask = none
  tidy : stTidyB (J.rec₀ w fr).st = true
  plainRows : stPlainB (J.rec₀ w fr).st = true
  claims : claimsB (J.rec₀ w fr) = true
  plain : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
    gpOf J.p (batT (J.rec₀ w fr) G {}) (stA J.p) (layoutOf (J.rec₀ w fr).st G) = some Dp ∧
      ok (gpL J.p (stA J.p) {} Dp) = true ∧
      2 ^ (layoutOf (J.rec₀ w fr).st G).logEll = (stA J.p).C.l ∧
      2 ^ (layoutOf (J.rec₀ w fr).st G).logEllZk = (stA J.p).Z.l
  pub : ∀ G, (J.rec₀ w fr).st.groups[(J.rec₀ w fr).g]? = some G →
    readPubB (coreSh ⟨Ground.withGroup (spent (withOwn (begun (J.rec₀ w fr).st (J.rec₀ w fr).g G)
          (ioppFoldShape ⟨(lettersOf J.p (stA J.p) (stN J.p)).i.1,
            (lettersOf J.p (stA J.p) (stN J.p)).i.2, (stA J.p).k, (stA J.p).h⟩
            (layoutOf (J.rec₀ w fr).st G)))
          (begun (J.rec₀ w fr).st (J.rec₀ w fr).g G).oracles.size)
        (lettersOf J.p (stA J.p) (stN J.p)).n.code (lettersOf J.p (stA J.p) (stN J.p)).n.maskCode,
      ownBook J.p.nums.firstTree (begun (J.rec₀ w fr).st (J.rec₀ w fr).g G) (J.rec₀ w fr).book
        (J.rec₀ w fr).roots
        (ioppFoldShape ⟨(lettersOf J.p (stA J.p) (stN J.p)).i.1,
          (lettersOf J.p (stA J.p) (stN J.p)).i.2, (stA J.p).k, (stA J.p).h⟩
          (layoutOf (J.rec₀ w fr).st G)),
      (J.rec₀ w fr).roots + 1⟩)
      (frontSingle (layoutOf (J.rec₀ w fr).st G) (lettersOf J.p (stA J.p) (stN J.p)).i (stA J.p).k
        (stA J.p).h (begun (J.rec₀ w fr).st (J.rec₀ w fr).g G).oracles.size) (stA J.p).C.a = true

end Asks

/-- What `door_facts_own` gives, with the front and the combination. -/
theorem door_front_own {p : P12} {a next : Fmt.M1.Stage} {t₀ : T12} {i nn : ℕ × ℕ} {dB : Fmt.Drawn}
    (h : doorB p a next (((laidOf p).take 1).map (·.1)) i nn (testSh t₀) = true)
    (hm : t₀.mask = none) (ht : stTidyB t₀.st = true)
    (hpl : ∀ G, t₀.st.groups[t₀.g]? = some G → ∀ r ∈ (runRows t₀.st G).toList, PlainRow r)
    (hB : batCut (((laidOf p).take 1).map (·.1)) = true)
    (fB : roundsFit (((laidOf p).take 1).map (·.1)) [⟨[], dB⟩] = true) :
    ∃ G row x, TestFrontOwn p a next t₀ G i nn ∧
      Bat.combine (begun t₀.st t₀.g G) t₀.g ⟨layoutOf t₀.st G, runRows t₀.st G⟩ x = some row ∧
      tBat p t₀ dB = batT t₀ G row := by
  unfold doorB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, -⟩, h4⟩ := h
  have h4' : (match t₀.mask with
    | some id => cameB a (testSh t₀).core t₀.g i id
    | none => (testSh t₀).core.st.oracles.length == (testSh t₀).core.book.place.length) = true := h4
  rw [hm] at h4'
  obtain ⟨G, H⟩ := testFrontOwn_of h1 hm (by simpa using h4') ht hpl
  obtain ⟨row, hr, hb⟩ := bat5_yes_own H _ (batOwes_of h2 H.group) hB [⟨[], dB⟩] fB
  exact ⟨G, row, _, H, hr, getD_of_ok hb⟩

/-- **`ShapeAsksO` at the challenges D, from `FrontAsksO`.** -/
theorem shapeAsks_of_front_own (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (K : Codes) (Dp : Plain) (hP : planOB J.p K Dp.ts.length = true)
    (S : FrontAsksO J w fr K Dp) (F : FormAsks J w fr C D) : ShapeAsksO J w fr C D K Dp := by
  unfold planOB planOL at hP
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
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s9⟩ := S
    have f1 := F.bat
    have f2 := F.fold
    have s2' := s2
    simp only [hA, hN] at s2' s7 s9 f2
    have Pl := switchPub_of p3
    rw [← s1] at Pl
    obtain ⟨G, row, x, H, hr, eB⟩ :=
      door_front_own s2' s3 s4 (fun G hG => runRows_plain s5 hG) p4 f1
    have eR : J.recB w fr (D 0) = batT (J.rec₀ w fr) G row := (recB_eq J w fr (D 0)).trans eB
    rw [eR] at f2
    have FO := foldFrontOwn_first H x row hr
    have FF := front_entered FO
    have hfold := fold5_yes_own FO p5 _ f2
    have e1 := getD_of_ok (d := batT (J.rec₀ w fr) G row) hfold
    obtain ⟨rE, rR, hrs, hR'⟩ := rounds_split (length_of_foldCutOwn p5) f2
    have hk0 : row.kept = #[] := H2K.Pin.combine_noKept0 _ _ _ _ _ hr fun k => H.noKept k
    have kk : (sgOf a).h + (sgOf a).g = a.k := kk_eq p6
    obtain ⟨q1, q2, q3, q4⟩ := s7 G H.group
    have eT : tFold J w fr C D = foldTOwn J.p (batT (J.rec₀ w fr) G row) row
        (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
          a.h⟩ ((lettersOf J.p a next).n.code, (lettersOf J.p a next).n.maskCode) (rE :: rR) := by
      show t1At J.p _ 0 (stA J.p) (laidS J.p) 1 (J.recB w fr (D 0)) _ D = _
      rw [hA, eR, ← hrs]
      exact e1
    refine ⟨s1, s2, s3, s4, s5, s6, ?_, ?_, ?_⟩
    · -- the plain data
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
      exact (foldTOwn_keeps _ _ _ _ _ _ _).1.trans ((batT_codes _ G row).trans s1)
    · -- the single rows
      intro rows gp h
      rw [eT] at h ⊢
      have h' : Passing.single (foldOut (enteredT J.p (batT (J.rec₀ w fr) G row)
            (ioppFoldShape ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
              (layoutOf (J.rec₀ w fr).st G))) row
          (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2,
            a.k, a.h⟩ (batT (J.rec₀ w fr) G row).st.oracles.size (rE :: rR))
          (batT (J.rec₀ w fr) G row).st.groups.size = .single rows gp := h
      injection h' with h1 h2
      subst h1 h2
      rw [hA, hN]
      obtain ⟨y1, y2, y3, y4⟩ := foldOut_says (enteredT J.p (batT (J.rec₀ w fr) G row)
          (ioppFoldShape ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
            (layoutOf (J.rec₀ w fr).st G))) row
        (layoutOf (J.rec₀ w fr).st G) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
          a.h⟩ (batT (J.rec₀ w fr) G row).st.oracles.size rE rR
      constructor
      · refine (readPubB_congr _ _ _ _ y1 (y4 fun k => H.noKept k) ?_ y3 y2).trans
          (s9 G H.group)
        show (rR.map drawnOf).length = a.k
        rw [List.length_map]
        exact hR'
      · have hcodes : (enteredT J.p (batT (J.rec₀ w fr) G row)
            (ioppFoldShape ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
              (layoutOf (J.rec₀ w fr).st G))).st.codes = (J.rec₀ w fr).st.codes :=
          batT_codes _ G row
        have Pl' : SwitchPub J.p (enteredT J.p (batT (J.rec₀ w fr) G row)
            (ioppFoldShape ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
              (layoutOf (J.rec₀ w fr).st G))).st.codes 0 a next
            (nx' :: rest').isEmpty ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k,
              a.h⟩ (lettersOf J.p a next).n (lettersOf J.p a next).dS
            (lettersOf J.p a next).dC := by
          rw [hcodes]
          exact Pl
        have hrow : foldRowOk (spent (enteredT J.p (batT (J.rec₀ w fr) G row)
            (ioppFoldShape ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
              (layoutOf (J.rec₀ w fr).st G))).st (batT (J.rec₀ w fr) G row).st.oracles.size)
            (ioppFoldShape ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
              (layoutOf (J.rec₀ w fr).st G)) row = true :=
          (Own.foldRowFits_agrees _ _ _).trans ((foldRowFits_spent _ _ _ _).trans FF.rowFits)
        have hlen : (rR.map drawnOf).length = a.k := by
          rw [List.length_map]
          exact hR'
        obtain ⟨g1, g2, g3, g4, g5, -⟩ := foldedFit_pure (enteredT J.p (batT (J.rec₀ w fr) G row)
            (ioppFoldShape ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
              (layoutOf (J.rec₀ w fr).st G))).st.codes
          (sgOf a) (sgOf next) ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
          Pl'.codes (lettersOf J.p a next).n.code (lettersOf J.p a next).n.maskCode Pl'.zk
          Pl'.codeN Pl'.zkN Pl'.small (enteredT J.p (batT (J.rec₀ w fr) G row)
            (ioppFoldShape ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
              (layoutOf (J.rec₀ w fr).st G))).st
          (spent (enteredT J.p (batT (J.rec₀ w fr) G row)
            (ioppFoldShape ⟨(lettersOf J.p a next).i.1, (lettersOf J.p a next).i.2, a.k, a.h⟩
              (layoutOf (J.rec₀ w fr).st G))).st (batT (J.rec₀ w fr) G row).st.oracles.size) row
          (layoutOf (J.rec₀ w fr).st G) (batT (J.rec₀ w fr) G row).st.oracles.size
          (drawnOf rE) (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target))
          (rR.map drawnOf) rfl rfl hk0 (fun k _ => H.noKept k) (hlen.trans Pl.codes.k)
          ((Own.foldShapeFits_agrees _ _).trans FF.shape) hrow
        exact ⟨g1, g2, g3, g4, g5⟩
  · simp at hP

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.FrontAsksO
#print axioms ProofFile.Honest.K12.Own.door_front_own
#print axioms ProofFile.Honest.K12.Own.shapeAsks_of_front_own
