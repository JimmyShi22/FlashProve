-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PublicAtPlan.lean: CONDITIONAL: the public premises of the files on the
honest prover's side of an attention segment's own rounds, at a plan that the verifier's planner
returns and that passes this library's one test on a plan. A joining of the library's lemmas, with
arithmetic on numbers of variables. Definitions, and statements with their proofs.

TWO PREMISES, both public: hA: `Attention.plan settings inp cf = .ok A` (OnBytes/Model/
AttentionPlan.lean); hok: `planOkAll cf A.S A.fs = true` (Johnson/Desc/First/Att/K05PlanAll.lean).
The place is P := (A.S, A.own); the lookup's numbers are C := `callsOf A.fs`.

THE TABLE: premise; files under Johnson/Desc/K5/Honest/Law/ that spend it, whole or in part (the
list is not whole); what gives it here.
  `Sized P`          all files on readings         `sized_of_hid` at the planner's shape
  `Planned P`        Weights, ReadSE .. ReadHB, ReadVM, ReadSD, Starts
                                                   the planner fills its numbers of these rounds out
                                                   of the shape (`Meaning.plan_own`,
                                                   Johnson/Goal/Meaning/PlanOwn.lean); the row of
                                                   parts written out (Named.lean)
  a token has at most 16 bits   ReadHB, Starts     the first refusal in the planner of shapes
  `CallsFit`, `KeysFit`   Weights, Keys            a clause of the test
  `UnitIs` at the seven units   Weights, UnitPts, Starts, RuleValues
                                                   `units_all`
                                                   (Johnson/Desc/First/Att/K05UnitsOk.lean);
                                                   for a softmax-table unit also at the families
                                                   m1, d1 (`unitIs_m1`, `unitIs_d1`)
  `PairsAre` at the seven units   ReadSE, ReadVD, ReadVM, ReadKM, ReadKD, Starts, RuleValues
                                                   `seven_of_hid`
                                                   (Johnson/Desc/First/Att/Claims/PiecesTie.lean)
                                                   at a key point of zeros, carried to every key
                                                   point
  two softmax-table units, the one below the diagonal first; their numbers of variables and
  of pieces          ReadKM, ReadKD, TilesKit      `units_all`; `counts_place`; Named.lean
  one shift a group; the planner's list of softmax-table units has two members; `GeoFits`
                                                   `UsualCalls`, a clause of the test; the same
                                                   list; `geoFits_of_planOk`

Main names:
  `pieces_lam`, `pieces_a`, `pairs_free`   a piece's layer and head do not hang on the key point
  `pairs_of_all`    `PairsAre` from the library's `PiecesAll`
  `keyPt_zero`      a key point of zeros is the library's at the point 0
  `pairs_of_fam`    `PairsAre` at every key point, for one family
  `lt_le_of_hid`    a token has at most 16 bits
  `PublicAll P fs`  all of the table in one structure
  `public_at_plan`  **`PublicAll (A.S, A.own) A.fs` from hA and hok**

Limits. That a plan passes the test is not shown here. The test asks for one shift in the group and
four calls: a plan with two shifts is not reached. Nothing is said of a premise that names a
challenge or a cell. No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.Starts
import Johnson.Desc.K5.Honest.Law.Named
import Johnson.Desc.First.Att.K05GeoAtPlan
import Johnson.Desc.First.Att.Claims.PtsOf
import Johnson.Goal.Meaning.PlanOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open OnBytes.Road.L5 (dimOf callsOf callAt UsualCalls CallsFit)
open OnBytes.Road.Rows (PiecesAll)
open VerifiableInference.Desc.First.Att.P (Geo W1 UnitG geoOf callOf keysOf piecesOf pcsSorted
  weights remainders UnitIs UnitsAll planOkAll)
open Inst.Model.AttSeg (Calls Pub Fam Step g18)
open K5Law (pwBack FamAt KeyPt)

/-! ## "Piece b is pair b" does not hang on the key point -/

theorem pieces_lam (u : UnitG) (key : Array E) (b : ℕ) :
    ((piecesOf u key).getD b ⟨0, 0, zeroE⟩).lam = (((pcsSorted u)[b]?).map (·.lam)).getD 0 := by
  rw [pieces_eq]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  cases (pcsSorted u)[b]? <;> rfl

theorem pieces_a (u : UnitG) (key : Array E) (b : ℕ) :
    ((piecesOf u key).getD b ⟨0, 0, zeroE⟩).a = (((pcsSorted u)[b]?).map (·.a)).getD 0 := by
  rw [pieces_eq]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  cases (pcsSorted u)[b]? <;> rfl

/-- A piece's layer and head are the same at every key point. -/
theorem pairs_free {g : Geo} {u : UnitG} {key : Array E} (h : PairsAre g (piecesOf u key))
    (key' : Array E) : PairsAre g (piecesOf u key') := fun b hb => by
  rw [pieces_lam, pieces_a, ← pieces_lam u key, ← pieces_a u key]
  exact h b hb

/-- `PairsAre` from the library's statement on the same pieces in its other type. -/
theorem pairs_of_all {S : OnBytes.Attention.Shape} {pw : Array W1}
    (h : PiecesAll S (pwBack pw)) : PairsAre (geoOf S) pw := by
  intro b hb
  have hs : pw.size = S.NP := by
    have := h.1
    unfold pwBack at this
    rwa [Array.size_map] at this
  have hb' : b < pw.size := by
    rw [hs]
    exact hb
  have e : pw[b]? = some pw[b] := Array.getElem?_eq_getElem hb'
  have q := h.2 b hb ⟨pw[b].lam, pw[b].a, pw[b].wp⟩ (by
    unfold pwBack
    rw [Array.getElem?_map, e]
    rfl)
  rw [Array.getD_eq_getD_getElem?, e]
  exact q

/-- The library's challenges, all 0. They serve one call alone: the library's lemma on the pieces
speaks under a key point that reads as the library's; `PairsAre` names no reading, no point and no
challenge, so a true member of that premise is laid (`keyPt_zero`) and the result is carried to
every key point (`pairs_free`). -/
def pubZero : Pub Cb.Gl.E :=
  { z := fun _ => 0, th := 0, tg := fun _ => 0, ti := fun _ => 0, tbi := fun _ => 0
    tbg := fun _ => 0, tk := fun _ => 0, o := fun _ => 0, o' := fun _ => 0, o'' := fun _ => 0
    fi := fun _ => 0, fg := fun _ => 0, fn := fun _ => 0 }

/-- A key point of zeros, of the call's length, is the library's key point at the point 0. -/
theorem keyPt_zero (fs : OnBytes.Model.Forest.Shape) (q : Fin 4) :
    KeyPt Reading.gl fs (Array.replicate ((callsOf fs).a q) zeroE) q pubZero := by
  refine ⟨Array.size_replicate, fun t ht => ?_⟩
  have e : pt Reading.gl (Array.replicate ((callsOf fs).a q) zeroE) t = 0 := by
    unfold pt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, if_pos ht]
    exact Reading.gl.zero
  rw [e]
  unfold Calls.zC
  split <;> rfl

/-- **"Piece b is pair b" at every key point**, for the unit of one family. -/
theorem pairs_of_fam {S : OnBytes.Attention.Shape} {fs : OnBytes.Model.Forest.Shape} {q : Fin 4}
    {s : OnBytes.Attention.Seg} {f : Fam} (F : FamAt Reading.gl S fs pubZero q s f)
    (key : Array E) :
    PairsAre (geoOf S)
      (piecesOf ((geoOf S).unitAt q.val (callOf (callAt S q.val)) (keysOf s)) key) := by
  refine pairs_free (key := Array.replicate ((callsOf fs).a q) zeroE) (pairs_of_all ?_) key
  rw [K5Law.pw_back]
  exact (F _ (keyPt_zero fs q)).1

/-! ## A token's bits -/

/-- **A token has at most 16 bits**: the first refusal in the planner of shapes. -/
theorem lt_le_of_hid {lid : ℕ} {cf : OnBytes.Attention.Cfg} {S : OnBytes.Attention.Shape}
    {fs : OnBytes.Model.Forest.Shape}
    (h : OnBytes.Attention.shapeHid lid cf = Except.ok (S, fs)) : S.cf.lt ≤ 16 := by
  obtain ⟨S0, h0⟩ := OnBytes.Road.L5.shape_of_hid h
  rw [(OnBytes.Road.L5.shaped_of_hid h).cfg]
  unfold OnBytes.Attention.shape at h0
  obtain ⟨e1, _⟩ := OnBytes.Road.L5.refuse_ok h0
  simp only [Bool.or_eq_false_iff] at e1
  exact Nat.not_lt.mp (of_decide_eq_false e1.1.2)

/-! ## All in one -/

/-- **The public premises of the files on the readings, in one structure.** fs: the lookup's
shape. -/
structure PublicAll (P : Pub5) (fs : OnBytes.Model.Forest.Shape) : Prop where
  sized : Sized P
  planned : Planned P
  lt16 : P.D.lT ≤ 2 ^ 4
  fit : CallsFit P.S fs
  keys : KeysFit fs
  /-- spent by no file on the readings: it says why there are just two softmax-table units -/
  oneShift : ∀ l < 2 ^ P.S.cf.ll, P.S.cf.sh.getD l 0 = P.S.cf.sh.getD 0 0
  units : ∃ r1 r2 u1 u2 wl ix wh, UnitsAll P.S fs r1 r2 u1 u2 wl ix wh ∧
    UnitIs P.D (callsOf fs) .m1 1 u1 ∧ UnitIs P.D (callsOf fs) .d1 1 u2 ∧
    u1.pcs.length = P.D.nb ∧ u2.pcs.length = P.D.nb
  /-- follows from `units`; kept in the form in which `divPts_of` and `lonePts_of` take it -/
  wl : ∀ u, P.g.single .wl = some u → ∃ q, UnitIs P.D (callsOf fs) .w3 q u
  pairsScores : ∀ u ∈ P.g.scores, ∀ key, PairsAre P.g (piecesOf u key)
  pairsRem : ∀ u ∈ remainders P.g, ∀ key, PairsAre P.g (piecesOf u key)
  pairsWl : ∀ u, P.g.single .wl = some u → ∀ key, PairsAre P.g (piecesOf u key)
  pairsIx : ∀ u, P.g.single .ix = some u → ∀ key, PairsAre P.g (piecesOf u key)
  pairsWh : ∀ u, P.g.single .wh = some u → ∀ key, PairsAre P.g (piecesOf u key)
  score : P.x.score.isEmpty = false
  score2 : P.x.score.length = 2
  /-- the library's structure on the place's numbers against the planner's -/
  geo : VerifiableInference.Desc.First.Att.P.GeoFits P.g P.x
  vKM : (cut P.x).getD 0 3 - 3 = Step.s6b.g P.D
  vKD : (cut P.x).getD 1 3 - 3 = Step.s6d.g P.D

/-- **All of them, at a plan that the planner returns and that passes the one test.** -/
theorem public_at_plan {settings : OnBytes.Model.Settings} {inp : OnBytes.Attention.In}
    {cf : OnBytes.Attention.Cfg} {A : OnBytes.Attention.Plan}
    (hA : OnBytes.Attention.plan settings inp cf = Except.ok A)
    (hok : planOkAll cf A.S A.fs = true) : PublicAll ⟨A.S, A.own⟩ A.fs := by
  have hid := (OnBytes.Road.L5.plan_shape hA).1
  have PA := VerifiableInference.Desc.First.Att.P.plan_all hid hok
  have O := Meaning.plan_own hA
  have H : Sized ⟨A.S, A.own⟩ := sized_of_hid hid
  have Pl := PA.law.place
  have hl := H.Z.lnT
  have ht := H.tok
  have hl' : 2 ≤ A.S.lnT := hl
  have ht' : A.S.cf.lt = A.S.lnT + A.S.cf.lB := ht
  obtain ⟨r1, r2, u1, u2, wl, ix, wh, U⟩ := PA.units
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := K5Law.seven_of_hid Reading.gl hid PA.law.usual pubZero
  obtain ⟨_, k2⟩ := VerifiableInference.Desc.First.Att.P.counts_place Pl
  have hsc : A.own.score = [(A.S.nvKF .fm, (callAt A.S 1).npOf .fm),
      (A.S.nvKF .fd, (callAt A.S 1).npOf .fd)] := O.score.trans k2
  have nb : (dimOf A.S).nb = A.S.NP := rfl
  refine
    { sized := H
      planned := ⟨O.pairs, O.lt, O.lgk, O.Lam, ?_, ?_, ?_, ?_, ?_, ?_⟩
      lt16 := ?_
      fit := PA.law.fit
      keys := keysFit_of_calls PA.law.fit
      oneShift := ?_
      units := ⟨r1, r2, u1, u2, wl, ix, wh, U,
        VerifiableInference.Desc.First.Att.P.unitIs_m1
          (OnBytes.Road.L5.callsFit_a01 PA.law.fit) U.m2,
        VerifiableInference.Desc.First.Att.P.unitIs_d1
          (OnBytes.Road.L5.callsFit_a01 PA.law.fit) U.d2, ?_, ?_⟩
      wl := fun u hu => ⟨2, ?_⟩
      pairsScores := ?_
      pairsRem := ?_
      pairsWl := ?_
      pairsIx := ?_
      pairsWh := ?_
      score := ?_
      score2 := ?_
      geo := VerifiableInference.Desc.First.Att.P.geoFits_of_planOk hA hok
      vKM := ?_
      vKD := ?_ }
  · rw [cut_iSE]
    show A.own.e = A.S.cf.lgk + (A.S.lnT - 1 + 1 + A.S.cf.lB)
    rw [O.e]
    unfold OnBytes.Attention.Shape.nvE
    omega
  · rw [cut_iVM]
    show A.own.valueM = A.S.cf.lgk + (A.S.lnT - 1) + (A.S.lnT - 1 + 1) + A.S.cf.lB
    rw [O.valueM]
    unfold OnBytes.Attention.Shape.nvVM
    omega
  · rw [cut_iVD]
    show A.own.valueD = A.S.cf.lgk + (A.S.lnT - 1 + 1) + A.S.cf.lB
    rw [O.valueD]
    unfold OnBytes.Attention.Shape.nvVD
    omega
  · rw [cut_iSF]
    show A.own.attained = A.S.lnT - 1 + 1 + A.S.cf.lB + A.S.cf.lgk + A.S.cf.ldh
    rw [O.attained]
    unfold OnBytes.Attention.Shape.nvF
    omega
  · rw [cut_iSD]
    show A.own.lt + A.own.lgk + A.own.lt =
      A.S.lnT - 1 + 1 + A.S.cf.lB + A.S.cf.lgk + (A.S.lnT - 1 + 1 + A.S.cf.lB)
    rw [O.lt, O.lgk]
    omega
  · rw [cut_iHB]
    show A.own.bits = A.S.lnT - 1 + 1 + A.S.cf.lB + A.S.cf.lgk + 4
    rw [O.bits]
    unfold OnBytes.Attention.Shape.nvH
    omega
  · have := lt_le_of_hid hid
    show A.S.lnT - 1 + 1 + A.S.cf.lB ≤ 2 ^ 4
    omega
  · have e := (OnBytes.Road.L5.shaped_of_hid hid).cfg
    show ∀ l < 2 ^ A.S.cf.ll, A.S.cf.sh.getD l 0 = A.S.cf.sh.getD 0 0
    rw [e]
    exact PA.law.usual.one
  · rw [← U.m2.nPw #[], VerifiableInference.Desc.First.Att.P.weights_size]
  · rw [← U.d2.nPw #[], VerifiableInference.Desc.First.Att.P.weights_size]
  · have e : wl = u := Option.some.inj (U.sWl.symm.trans hu)
    rw [← e]
    exact U.w3
  · intro u hu key
    have hu' : u ∈ (geoOf A.S).scores := hu
    rw [K5Law.place_scores Pl] at hu'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu'
    rcases hu' with rfl | rfl
    · exact pairs_of_fam f3 key
    · exact pairs_of_fam f4 key
  · intro u hu key
    have hu' : u ∈ remainders (geoOf A.S) := hu
    unfold remainders at hu'
    rw [K5Law.place_kr Pl] at hu'
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hu'
    rcases hu' with rfl | rfl
    · exact pairs_of_fam f1 key
    · exact pairs_of_fam f2 key
  · intro u hu key
    have e := Option.some.inj ((K5Law.place_wl Pl).1.symm.trans hu)
    rw [← e]
    exact pairs_of_fam f5 key
  · intro u hu key
    have e := Option.some.inj ((K5Law.place_wl Pl).2.symm.trans hu)
    rw [← e]
    exact pairs_of_fam f6 key
  · intro u hu key
    have e := Option.some.inj ((K5Law.place_wh Pl).symm.trans hu)
    rw [← e]
    exact pairs_of_fam f7 key
  · show A.own.score.isEmpty = false
    rw [hsc]
    rfl
  · show A.own.score.length = 2
    rw [hsc]
    rfl
  · rw [cut_unit A.own 0 (A.S.nvKF .fm, (callAt A.S 1).npOf .fm) (by rw [hsc]; rfl)]
    show A.S.nvKF .fm = A.S.cf.lgk + (A.S.lnT - 1) + (A.S.lnT - 1 + 1) + A.S.cf.ldh
    show (if (OnBytes.Attention.Seg.fm == .fm) = true then A.S.cf.lgk + 2 * A.S.lnT - 1 + A.S.cf.ldh
      else A.S.cf.lgk + A.S.lnT + A.S.cf.ldh) = _
    rw [if_pos (by decide)]
    omega
  · rw [cut_unit A.own 1 (A.S.nvKF .fd, (callAt A.S 1).npOf .fd) (by rw [hsc]; rfl)]
    show (if (OnBytes.Attention.Seg.fd == .fm) = true then A.S.cf.lgk + 2 * A.S.lnT - 1 + A.S.cf.ldh
      else A.S.cf.lgk + A.S.lnT + A.S.cf.ldh) = A.S.cf.lgk + (A.S.lnT - 1 + 1) + A.S.cf.ldh
    rw [if_neg (by decide)]
    omega

end H2K5.Honest

#print axioms H2K5.Honest.pieces_lam
#print axioms H2K5.Honest.pieces_a
#print axioms H2K5.Honest.pairs_free
#print axioms H2K5.Honest.pairs_of_all
#print axioms H2K5.Honest.keyPt_zero
#print axioms H2K5.Honest.pairs_of_fam
#print axioms H2K5.Honest.lt_le_of_hid
#print axioms H2K5.Honest.public_at_plan
