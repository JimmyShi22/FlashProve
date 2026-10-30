-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunByLast.lean: proof of `Spec.last_eq` (RunBySpec.lean). At a
last stage (k = 0, h = 0) where `Tab` holds, `stagesBy` (RunBy.lean) with no later stage gives the
rounds, trees and opened columns of `lastAll` (Johnson/Desc/K12/Honest/Stages.lean).

  `lastBy_eq`    the proof

By what. A sum computed on words has words below the prime (`okE_addE`, OnBytes/Slice/SimBase.lean),
so it is the element that it decodes to, encoded (`eq_ofE`, RunByTab.lean). The one main row and the
one mask row come from `col_main0` and `col_mask0` (RunByCols.lean). Both definitions make the claim
by the same calls, and define the trees and the opened columns in the same way.

Limits.
- If `stageAt` or `claimAt` returns no claim, both definitions go on with an empty claim.
- The warnings in `RunOut.no` are not covered.
- Two definitions give the same words. Nothing follows on what a verifier decides.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunByCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open OnBytes.Slice (GE ofE toE lst vec toE_addE toE_mulE toE_dot_of_le okE_addE vec_toArray)
open Johnson.Prover.Link (PS BOut wr μOf formG tauSW shownAll lst_wr length_wr mainOf maskOf
  lastOut rowOf)
open Fmt.M1 (E Code Stage dot)
open Fmt.M1.Own (PSt axL)
open VerifiableInference.Desc.K12 (P12 T12 Laid)
open H2K.Pub (sgOf)

/-! ## 1 The first round's element -/

/-- The inner product on words with an encoded row decodes to the field's form (`formG`,
Johnson/Prover/Link/Base.lean). -/
theorem last_form (n : ℕ) (c : Array E) (f : ℕ → GE) :
    toE (dot .two c (wr n f).toArray) = formG n c f := by
  have hn : (wr n f).toArray.size = n := by rw [List.size_toArray, length_wr]
  rw [toE_dot_of_le c (wr n f).toArray n (by
    rw [hn]
    exact Nat.min_le_right _ _)]
  unfold formG
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [vec_toArray (wr n f) i, lst_wr _ _ _ (Finset.mem_range.1 hi)]

/-- The first round's element is `tauSW`. -/
theorem last_tau (C Z : Code) (c d : Array E) (h0 h1 : ℕ → GE) :
    Fld.two.addE (dot .two c (wr C.l h0).toArray) (dot .two d (wr Z.l h1).toArray) =
      tauSW C Z c d h0 h1 :=
  eq_ofE (okE_addE _ _) (by rw [toE_addE, last_form, last_form])

/-! ## 2 The second round's lists -/

/-- u + lam * v computed entry by entry on two encoded lists of length n is the functions' u + lam *
v, encoded. -/
theorem last_axL (n : ℕ) (lam : E) (u v : ℕ → GE) :
    axL .two (wr n u) lam (wr n v) = wr n fun j => u j + toE lam * v j := by
  unfold axL
  rw [length_wr, length_wr, Nat.max_self]
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < n := List.mem_range.1 hi
  refine eq_ofE (okE_addE _ _) ?_
  rw [toE_addE, toE_mulE]
  show lst (wr n u) i + toE lam * lst (wr n v) i = _
  rw [lst_wr _ _ _ hi', lst_wr _ _ _ hi']

/-- The second round's four lists, appended, are `shownAll`. -/
theorem last_shown (C Z : Code) (lam : E) (m0 r0 m1 r1 h0 s0 h1 s1 : ℕ → GE) :
    axL .two (wr C.l h0) lam (wr C.l m0) ++ axL .two (wr Z.l h1) lam (wr Z.l m1) ++
        axL .two (wr C.r s0) lam (wr C.r r0) ++ axL .two (wr Z.r s1) lam (wr Z.r r1) =
      shownAll C Z lam m0 r0 m1 r1 h0 s0 h1 s1 := by
  rw [last_axL, last_axL, last_axL, last_axL, List.append_assoc, List.append_assoc]
  rfl

/-! ## 3 The stage -/

/-- `stagesBy` with no later stage and `lastOut` give the same two rounds. -/
theorem last_rounds (S : Seams) (p : P12) (K : Sorted) (j : ℕ) (s : Stage) (l : Laid) (o : ℕ)
    (t : T12) (P : PS) (q : PSt) (trees : List Tree) (D : ℕ → Fmt.Drawn) (k0 : s.k = 0)
    (h0 : s.h = 0) (T : Tab s true P q) :
    (stagesBy S p K [] j s l o t q trees D).rs =
      (lastOut p j s o t P (fun _ => []) (rowOf t) D).rs := by
  have hP : q.P = [wr s.C.l P.sM, wr s.Z.l (P.fM 0)] := T.ride
  have hPi : q.Pi = [wr s.C.r P.sT, wr s.Z.r (P.fT 0)] := T.rideT
  have e0 : q.P.getD 0 [] = wr s.C.l P.sM := by rw [hP]; rfl
  have e1 : q.P.getD 1 [] = wr s.Z.l (P.fM 0) := by rw [hP]; rfl
  have e2 : q.Pi.getD 0 [] = wr s.C.r P.sT := by rw [hPi]; rfl
  have e3 : q.Pi.getD 1 [] = wr s.Z.r (P.fT 0) := by rw [hPi]; rfl
  have pk : 0 < 2 ^ s.k := Nat.pos_of_ne_zero (by positivity)
  have ph : 0 < 2 ^ s.h := Nat.pos_of_ne_zero (by positivity)
  have eM : q.M.getD 0 [] = wr s.C.l (mainOf (sgOf s) (μOf (sgOf s) P)) := by
    rw [T.main, getD_range _ _ _ 0 pk]
    refine wr_congr _ _ _ fun c hc => ?_
    rw [col_main0 s P k0 h0 c hc, k0, pow_zero, one_mul, zero_add]
  have eW : q.W.getD 0 [] = wr s.Z.l (maskOf (sgOf s) (μOf (sgOf s) P)) := by
    rw [T.mask, getD_range _ _ _ 0 ph]
    refine wr_congr _ _ _ fun c hc => ?_
    rw [col_mask0 s P h0 c hc, h0, pow_zero, one_mul, zero_add]
  have eR : q.Rh.getD 0 [] = wr s.C.r (P.tM 0) := by rw [T.mainT, getD_range _ _ _ 0 pk]
  have eS : q.Sg.getD 0 [] = wr s.Z.r (P.tZ 0) := by rw [T.maskT, getD_range _ _ _ 0 ph]
  show [(⟨[.e (Fld.two.addE (dot .two _ (q.P.getD 0 []).toArray)
        (dot .two _ (q.P.getD 1 []).toArray))], D o⟩ : Fmt.RoundView),
      ⟨(axL .two (q.P.getD 0 []) (headE (D o)) (q.M.getD 0 []) ++
        axL .two (q.P.getD 1 []) (headE (D o)) (q.W.getD 0 []) ++
        axL .two (q.Pi.getD 0 []) (headE (D o)) (q.Rh.getD 0 []) ++
        axL .two (q.Pi.getD 1 []) (headE (D o)) (q.Sg.getD 0 [])).map .e, D (o + 1)⟩] = _
  rw [e0, e1, e2, e3, eM, eW, eR, eS, last_tau, last_shown, rowAt_eq]
  rfl

theorem lastBy_eq : Spec.last_eq := by
  intro S p K j s l o t P q trees D k0 h0 T
  exact congrArg
    (fun r => BOut.mk r [fun _ => [], fun _ => []] (groupsAt trees (D (o + 1)).poss))
    (last_rounds S p K j s l o t P q trees D k0 h0 T)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.last_form
#print axioms ProofFile.Honest.K12.Light.last_tau
#print axioms ProofFile.Honest.K12.Light.last_axL
#print axioms ProofFile.Honest.K12.Light.last_shown
#print axioms ProofFile.Honest.K12.Light.last_rounds
#print axioms ProofFile.Honest.K12.Light.lastBy_eq
