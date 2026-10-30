-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyDepthsAt.lean:
DepthsDeclared at threadKey at borders 10, 11, 12, under
the table as placed: tbKey (E2E/KeyTreesKey.lean), its letter tt called with testTbl.

  shapes_U, shapes_O   the sendings' trees' depths at the written value. By the kernel
  tb_low, tb_high      tbKey's arms: own 0 to 2 by the book, from 3 on the letter
  declared_of          DepthsDeclared at a border, from two closed tests, at a letter of the right
                       depths
  ttPlaced, lays_U_at, lays_O_at, depth_tt_U, depth_tt_O   the letter as placed, and its depths
  declared_ten         at 10: no premise on own 7
  declared_eleven, declared_twelve   at 11, 12: under ONE premise: own 7's text has depth 13
  depthsAt_ten, depthsAt_eleven, depthsAt_twelve   so DepthsAt at every k and m

WHAT THE PREMISES ARE. e and hK₀: the written values. hJU, hJO: the two jobs have the numbers, members
and word on the fresh table that lays_U and lays_O were taken at. h7: own 7, which has no text.
Nothing of a run: no k, no m, no Thr.

A YES WOULD NOT SHOW: that the table as placed is laid in a thread that stands · anything at ok but
the constant yes · own 7's text · the table's contents: this speaks of logLength alone · that L2 is
the right letter. Nothing on completeness, soundness or hiding.
-/
import E2E.KeyOpensLaw
import E2E.KeyDepthsKernel
import E2E.KeyTreeOwners
import Johnson.Desc.ProofFile.Honest.K12.DepthsOfText
import Johnson.Desc.ProofFile.Honest.K12.FoldedAtKeyBookKernel
import Johnson.Desc.ProofFile.Honest.K12.OmegaAtKeyBookKernel
import Johnson.Desc.ProofFile.Honest.K12.StepsAtKey
import Johnson.Desc.ProofFile.Honest.Thread.OneState

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

namespace AtPublicFiles.KeyDepthsAt
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source Claim)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey parKey sits_two)
open AtPublicFiles.AtFiles.Full (PF QK)
open AtPublicFiles.KeyBook (KeyPub keyBook atFull fullPub)
open AtPublicFiles.KeyTreesKey (treesOf5)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyOpens (ro keyR opensR depthsR depthOf decls_ro flat_ro takesFit takes_two takes_five
  depths_twelve)
open H2K.Member (piKUFull piKOFull)
open ProofFile.Honest.K12 (TestJob testTbl testTbl_depth sendTable_depth cut_of_due laysB laysB_congr)

/-- The depths of the trees of «send o_u». By the kernel. -/
theorem shapes_U : ((VerifiableInference.Desc.Own.treesMade (jobU ⟨QK, 0⟩).Q.codes
    (jobU ⟨QK, 0⟩).Q.sent).getD {}).shapes.toList.map (·.logN) = [24] := by
  decide +kernel

/-- The depths of the trees of «send o_omega». By the kernel. -/
theorem shapes_O : ((VerifiableInference.Desc.Own.treesMade (jobOmega ⟨QK, 0⟩).Q.codes
    (jobOmega ⟨QK, 0⟩).Q.sent).getD {}).shapes.toList.map (·.logN) = [22, 13] := by
  decide +kernel

theorem trees_U : treesU QK = 1 := by decide +kernel

theorem trees_O : treesOf5 QK = 2 := by decide +kernel

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type} (K₀ : KeyPub) (hK₀ : fullPub = some K₀)
  (weights : W₀ → Weights) (rand : Rc → TableRand)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)

include hK₀ in
/-- The book covers the first sending's cut. -/
theorem fit_two : (sendingPart (jobU ⟨QK, 0⟩)).takes.f ≤
      (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 2, 0⟩).f ∧
    (sendingPart (jobU ⟨QK, 0⟩)).takes.e ≤ (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 2, 0⟩).e := by
  have h := takes_two
  unfold atFull at h
  rw [hK₀] at h
  have h' : takesFit (keyBook K₀) ⟨sendPlace 2, 0⟩ (jobU ⟨QK, 0⟩) = true := h
  simpa only [takesFit, Bool.and_eq_true, decide_eq_true_eq] using h'

include hK₀ in
/-- The book covers the second sending's cut. -/
theorem fit_five : (sendingPart (jobOmega ⟨QK, 0⟩)).takes.f ≤
      (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 5, 0⟩).f ∧
    (sendingPart (jobOmega ⟨QK, 0⟩)).takes.e ≤
      (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 5, 0⟩).e := by
  have h := takes_five
  unfold atFull at h
  rw [hK₀] at h
  have h' : takesFit (keyBook K₀) ⟨sendPlace 5, 0⟩ (jobOmega ⟨QK, 0⟩) = true := h
  simpa only [takesFit, Bool.and_eq_true, decide_eq_true_eq] using h'

include hK₀ in
/-- **Own 0 to 2: the sendings' depths, at all k, w, h.** -/
theorem tb_low (k : Coins (keyBook K₀)) (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn) {j : ℕ}
    (hj : j < 3) :
    (tbKey QK weights rand tk tt (.own j) k w h).2.logLength = depthOf.getD j 0 := by
  have lU : ((VerifiableInference.Desc.Own.treesMade (jobU ⟨QK, 0⟩).Q.codes
      (jobU ⟨QK, 0⟩).Q.sent).getD {}).shapes.toList.length = 1 := by
    have := congrArg List.length shapes_U
    rw [List.length_map] at this
    exact this
  have lO : ((VerifiableInference.Desc.Own.treesMade (jobOmega ⟨QK, 0⟩).Q.codes
      (jobOmega ⟨QK, 0⟩).Q.sent).getD {}).shapes.toList.length = 2 := by
    have := congrArg List.length shapes_O
    rw [List.length_map] at this
    exact this
  have cU := cut_of_due k 1 (by omega) ⟨sendPlace 2, 0⟩ (sendingPart (jobU ⟨QK, 0⟩)).takes
    (fit_two K₀ hK₀)
  have cO := cut_of_due k 1 (by omega) ⟨sendPlace 5, 0⟩ (sendingPart (jobOmega ⟨QK, 0⟩)).takes
    (fit_five K₀ hK₀)
  have hU := trees_U
  have hO := trees_O
  show (tbKey QK weights rand tk tt (.own j) k w h).2.logLength = _
  unfold tbKey
  by_cases c : j < treesU QK
  · simp only [if_pos c]
    have hj0 : j = 0 := by omega
    subst hj0
    rw [sendTable_depth (jobU ⟨QK, 0⟩) (witOf QK weights rand) (sendPlace 2) 1 0 k w h cU (by omega),
      shapes_U]
    rfl
  · have c' : j < treesU QK + treesOf5 QK := by omega
    simp only [if_neg c, if_pos c']
    rw [sendTable_depth (jobOmega ⟨QK, 0⟩) (witOf QK weights rand) (sendPlace 5) 1 (j - treesU QK) k w h
      cO (by omega), shapes_O, hU]
    have : j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl <;> rfl

/-- **From 3 on the arm is the letter.** -/
theorem tb_high (k : Coins (keyBook K₀)) (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn) {j : ℕ}
    (hj : 3 ≤ j) : tbKey QK weights rand tk tt (.own j) k w h = tt j k w h := by
  have hU := trees_U
  have hO := trees_O
  have n1 : ¬ j < treesU QK := by omega
  have n2 : ¬ j < treesU QK + treesOf5 QK := by omega
  unfold tbKey
  simp only [if_neg n1, if_neg n2]

variable (Xs : Source) (Nr : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w₁ : Common W₀ Rc TableKey)

include hK₀ in
/-- **DepthsDeclared at a border**, from the two closed tests, at a letter of the right depths. -/
theorem declared_of (e : parKey Xs PF = QK) (n : ℕ) (hd : depthsR keyR depthOf n = true)
    (ho : opensR keyR n = true)
    (ht : ∀ j, 3 ≤ j → j < ((keyR.take n).map (·.2)).sum →
      ∀ (k : Coins (keyBook K₀)) (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn),
        (tt j k w h).2.logLength = depthOf.getD j 0) :
    DepthsDeclared (threadKey Xs Nr PF K ℓ Nm Mg₀ (tbKey QK weights rand tk tt) rest Kp Vd w₁) n := by
  have hR : (threadKey Xs Nr PF K ℓ Nm Mg₀ (tbKey QK weights rand tk tt) rest Kp Vd w₁).bs.map ro =
      keyR :=
    ((sits_two Xs Nr PF K ℓ Nm Mg₀ (tbKey QK weights rand tk tt) rest Kp Vd w₁).2.2.2.1 ▸
      flat_ro Xs.chains e :)
  intro d hdm o hom k w h
  rw [decls_ro, hR] at hdm
  unfold depthsR at hd
  unfold opensR at ho
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 hd d hdm) o hom
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 ho d hdm) o hom
  obtain ⟨a, src⟩ := o
  cases src with
  | taken c x =>
    cases h1
  | own j =>
    have ha : a.a = depthOf.getD j 0 := beq_iff_eq.1 h1
    obtain ⟨i, hi, hij⟩ := List.mem_map.1 (of_decide_eq_true h2)
    obtain rfl : i = j := Fmt.TreeSource.own.inj hij
    have hj := List.mem_range.1 hi
    show (tbKey QK weights rand tk tt (.own i) k w h).2.logLength = a.a
    rw [ha]
    by_cases c : i < 3
    · exact tb_low K₀ hK₀ weights rand tk tt k w h c
    · rw [tb_high K₀ weights rand tk tt k w h (by omega)]
      exact ht i (by omega) hj k w h

/-- **The letter as placed.** own 3–6 the test on G_u, own 7 a text named t7, own 8–10 the test on
G_omega; n₀ at the written places. -/
def ttPlaced (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (t7 : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table) :
    Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table :=
  fun n => if n < 7 then testTbl 1 JU own₀ 8 (fun _ _ _ => true) (n - 3)
    else if n = 7 then t7
    else testTbl 1 JO own₀ 43 (fun _ _ _ => true) (n - 8)

include hK₀ in
theorem lays_U_at (J : TestJob (Common W₀ Rc TableKey) X₀)
    (hp : J.p = piKUFull) (hm : J.members = AtPublicFiles.KeyTest.jobFolded.members)
    (hf : J.fresh = AtPublicFiles.KeyTest.jobFolded.fresh) : laysB (keyBook K₀) 1 J = true := by
  rw [laysB_congr (keyBook K₀) 1 J ProofFile.Honest.K12.FoldedAtKeyBook.jobKUB hp hm hf]
  have h := ProofFile.Honest.K12.FoldedAtKeyBook.lays_U
  unfold atFull at h
  rw [hK₀] at h
  exact h

include hK₀ in
theorem lays_O_at (J : TestJob (Common W₀ Rc TableKey) X₀)
    (hp : J.p = piKOFull) (hm : J.members = AtPublicFiles.KeyTest.jobOmega.members)
    (hf : J.fresh = AtPublicFiles.KeyTest.jobOmega.fresh) : laysB (keyBook K₀) 1 J = true := by
  rw [laysB_congr (keyBook K₀) 1 J ProofFile.Honest.K12.OmegaAtKeyBook.jobKOB hp hm hf]
  have h := ProofFile.Honest.K12.OmegaAtKeyBook.lays_O
  unfold atFull at h
  rw [hK₀] at h
  exact h

/-- The stages' next depths against depthOf, at the test on G_u. -/
theorem next_U : ∀ τ, τ < 4 →
    (piKUFull.nums.stages.getD (τ + 1) default).C.a = depthOf.getD (3 + τ) 0 := by
  decide +kernel

/-- The same at the test on G_omega. -/
theorem next_O : ∀ τ, τ < 3 →
    (piKOFull.nums.stages.getD (τ + 1) default).C.a = depthOf.getD (8 + τ) 0 := by
  decide +kernel

theorem hk_U : ∀ a ∈ piKUFull.nums.stages, a.h ≤ a.k := by decide +kernel
theorem hk_O : ∀ a ∈ piKOFull.nums.stages, a.h ≤ a.k := by decide +kernel
theorem len_U : piKUFull.nums.stages.length = 5 := by decide +kernel
theorem len_O : piKOFull.nums.stages.length = 4 := by decide +kernel

include hK₀ in
/-- **At own 3 to 6 the letter has the declared depths, at all k, w, h.** -/
theorem depth_tt_U (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (t7 : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (hp : JU.p = piKUFull) (hm : JU.members = AtPublicFiles.KeyTest.jobFolded.members)
    (hf : JU.fresh = AtPublicFiles.KeyTest.jobFolded.fresh) {j : ℕ} (h3 : 3 ≤ j) (h7 : j < 7)
    (k : Coins (keyBook K₀)) (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn) :
    (ttPlaced K₀ JU JO own₀ t7 j k w h).2.logLength = depthOf.getD j 0 := by
  have hk : ∀ a ∈ JU.p.nums.stages, a.h ≤ a.k := by rw [hp]; exact hk_U
  have hτ : j - 3 + 1 < JU.p.nums.stages.length := by rw [hp, len_U]; omega
  have e := testTbl_depth JU hk 1 (Or.inr rfl) (lays_U_at K₀ hK₀ JU hp hm hf) own₀ 8 hτ k w h
  have n := next_U (j - 3) (by omega)
  unfold ttPlaced
  rw [if_pos h7, e, hp, n]
  congr 1
  omega

include hK₀ in
/-- **At own 8 to 10 likewise.** -/
theorem depth_tt_O (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (t7 : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (hp : JO.p = piKOFull) (hm : JO.members = AtPublicFiles.KeyTest.jobOmega.members)
    (hf : JO.fresh = AtPublicFiles.KeyTest.jobOmega.fresh) {j : ℕ} (h8 : 8 ≤ j) (h11 : j < 11)
    (k : Coins (keyBook K₀)) (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn) :
    (ttPlaced K₀ JU JO own₀ t7 j k w h).2.logLength = depthOf.getD j 0 := by
  have hk : ∀ a ∈ JO.p.nums.stages, a.h ≤ a.k := by rw [hp]; exact hk_O
  have hτ : j - 8 + 1 < JO.p.nums.stages.length := by rw [hp, len_O]; omega
  have e := testTbl_depth JO hk 1 (Or.inr rfl) (lays_O_at K₀ hK₀ JO hp hm hf) own₀ 43 hτ k w h
  have n := next_O (j - 8) (by omega)
  unfold ttPlaced
  rw [if_neg (by omega), if_neg (by omega), e, hp, n]
  congr 1
  omega

theorem sum_ten : ((keyR.take 10).map (·.2)).sum = 7 := by decide +kernel
theorem sum_eleven : ((keyR.take 11).map (·.2)).sum = 11 := by decide +kernel
theorem sum_twelve : ((keyR.take 12).map (·.2)).sum = 11 := by decide +kernel
theorem depths_ten : depthsR keyR depthOf 10 = true := by decide +kernel
theorem depths_eleven : depthsR keyR depthOf 11 = true := by decide +kernel
theorem opensR_ten : opensR keyR 10 = true := by decide +kernel
theorem opensR_eleven : opensR keyR 11 = true := by decide +kernel
theorem opensR_twelve : opensR keyR 12 = true := by decide +kernel
theorem seven_is : depthOf.getD 7 0 = 13 := by decide +kernel

include hK₀ in
/-- **AT BORDER 10: no premise on own 7.** -/
theorem declared_ten (e : parKey Xs PF = QK) (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (t7 : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (hp : JU.p = piKUFull) (hm : JU.members = AtPublicFiles.KeyTest.jobFolded.members)
    (hf : JU.fresh = AtPublicFiles.KeyTest.jobFolded.fresh) :
    DepthsDeclared (threadKey Xs Nr PF K ℓ Nm Mg₀
      (tbKey QK weights rand tk (ttPlaced K₀ JU JO own₀ t7)) rest Kp Vd w₁) 10 :=
  declared_of K₀ hK₀ weights rand tk _ Xs Nr K ℓ Nm Mg₀ rest Kp Vd w₁ e 10 depths_ten opensR_ten
    fun j h3 hs k w h => by
      rw [sum_ten] at hs
      exact depth_tt_U K₀ hK₀ JU JO own₀ t7 hp hm hf h3 hs k w h

include hK₀ in
/-- **AT BORDERS 11 AND 12, under one premise: own 7's text has depth 13.** -/
theorem declared_eleven (e : parKey Xs PF = QK) (JU JO : TestJob (Common W₀ Rc TableKey) X₀)
    (own₀ : X₀)
    (t7 : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (hp : JU.p = piKUFull) (hm : JU.members = AtPublicFiles.KeyTest.jobFolded.members)
    (hf : JU.fresh = AtPublicFiles.KeyTest.jobFolded.fresh)
    (hp' : JO.p = piKOFull) (hm' : JO.members = AtPublicFiles.KeyTest.jobOmega.members)
    (hf' : JO.fresh = AtPublicFiles.KeyTest.jobOmega.fresh)
    (h7 : ∀ k w h, (t7 k w h).2.logLength = 13) :
    DepthsDeclared (threadKey Xs Nr PF K ℓ Nm Mg₀
      (tbKey QK weights rand tk (ttPlaced K₀ JU JO own₀ t7)) rest Kp Vd w₁) 11 :=
  declared_of K₀ hK₀ weights rand tk _ Xs Nr K ℓ Nm Mg₀ rest Kp Vd w₁ e 11 depths_eleven
    opensR_eleven fun j h3 hs k w h => by
      rw [sum_eleven] at hs
      by_cases c7 : j < 7
      · exact depth_tt_U K₀ hK₀ JU JO own₀ t7 hp hm hf h3 c7 k w h
      · by_cases c : j = 7
        · subst c
          show (ttPlaced K₀ JU JO own₀ t7 7 k w h).2.logLength = _
          unfold ttPlaced
          rw [if_neg (by omega), if_pos rfl, seven_is]
          exact h7 k w h
        · exact depth_tt_O K₀ hK₀ JU JO own₀ t7 hp' hm' hf' (by omega) hs k w h

include hK₀ in
/-- The same at 12. -/
theorem declared_twelve (e : parKey Xs PF = QK) (JU JO : TestJob (Common W₀ Rc TableKey) X₀)
    (own₀ : X₀)
    (t7 : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (hp : JU.p = piKUFull) (hm : JU.members = AtPublicFiles.KeyTest.jobFolded.members)
    (hf : JU.fresh = AtPublicFiles.KeyTest.jobFolded.fresh)
    (hp' : JO.p = piKOFull) (hm' : JO.members = AtPublicFiles.KeyTest.jobOmega.members)
    (hf' : JO.fresh = AtPublicFiles.KeyTest.jobOmega.fresh)
    (h7 : ∀ k w h, (t7 k w h).2.logLength = 13) :
    DepthsDeclared (threadKey Xs Nr PF K ℓ Nm Mg₀
      (tbKey QK weights rand tk (ttPlaced K₀ JU JO own₀ t7)) rest Kp Vd w₁) 12 :=
  declared_of K₀ hK₀ weights rand tk _ Xs Nr K ℓ Nm Mg₀ rest Kp Vd w₁ e 12 depths_twelve
    opensR_twelve fun j h3 hs k w h => by
      rw [sum_twelve] at hs
      by_cases c7 : j < 7
      · exact depth_tt_U K₀ hK₀ JU JO own₀ t7 hp hm hf h3 c7 k w h
      · by_cases c : j = 7
        · subst c
          show (ttPlaced K₀ JU JO own₀ t7 7 k w h).2.logLength = _
          unfold ttPlaced
          rw [if_neg (by omega), if_pos rfl, seven_is]
          exact h7 k w h
        · exact depth_tt_O K₀ hK₀ JU JO own₀ t7 hp' hm' hf' (by omega) hs k w h

include hK₀ in
/-- **DepthsAt at 10, at every k and m**: no premise on own 7. -/
theorem depthsAt_ten (e : parKey Xs PF = QK) (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (t7 : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (hp : JU.p = piKUFull) (hm : JU.members = AtPublicFiles.KeyTest.jobFolded.members)
    (hf : JU.fresh = AtPublicFiles.KeyTest.jobFolded.fresh)
    (k : Coins (keyBook K₀)) (m : Mid (Common W₀ Rc TableKey) X₀) :
    DepthsAt (threadKey Xs Nr PF K ℓ Nm Mg₀
      (tbKey QK weights rand tk (ttPlaced K₀ JU JO own₀ t7)) rest Kp Vd w₁) 10 k m :=
  depthsAt_of_declared (declared_ten K₀ hK₀ weights rand tk Xs Nr K ℓ Nm Mg₀ rest Kp Vd w₁ e JU JO own₀
    t7 hp hm hf) k m

include hK₀ in
/-- **DepthsAt at 11, at every k and m**, under h7. -/
theorem depthsAt_eleven (e : parKey Xs PF = QK) (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (t7 : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (hp : JU.p = piKUFull) (hm : JU.members = AtPublicFiles.KeyTest.jobFolded.members)
    (hf : JU.fresh = AtPublicFiles.KeyTest.jobFolded.fresh)
    (hp' : JO.p = piKOFull) (hm' : JO.members = AtPublicFiles.KeyTest.jobOmega.members)
    (hf' : JO.fresh = AtPublicFiles.KeyTest.jobOmega.fresh)
    (h7 : ∀ k w h, (t7 k w h).2.logLength = 13)
    (k : Coins (keyBook K₀)) (m : Mid (Common W₀ Rc TableKey) X₀) :
    DepthsAt (threadKey Xs Nr PF K ℓ Nm Mg₀
      (tbKey QK weights rand tk (ttPlaced K₀ JU JO own₀ t7)) rest Kp Vd w₁) 11 k m :=
  depthsAt_of_declared (declared_eleven K₀ hK₀ weights rand tk Xs Nr K ℓ Nm Mg₀ rest Kp Vd w₁ e JU JO
    own₀ t7 hp hm hf hp' hm' hf' h7) k m

include hK₀ in
/-- **DepthsAt at 12, at every k and m**, under h7. -/
theorem depthsAt_twelve (e : parKey Xs PF = QK) (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (t7 : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (hp : JU.p = piKUFull) (hm : JU.members = AtPublicFiles.KeyTest.jobFolded.members)
    (hf : JU.fresh = AtPublicFiles.KeyTest.jobFolded.fresh)
    (hp' : JO.p = piKOFull) (hm' : JO.members = AtPublicFiles.KeyTest.jobOmega.members)
    (hf' : JO.fresh = AtPublicFiles.KeyTest.jobOmega.fresh)
    (h7 : ∀ k w h, (t7 k w h).2.logLength = 13)
    (k : Coins (keyBook K₀)) (m : Mid (Common W₀ Rc TableKey) X₀) :
    DepthsAt (threadKey Xs Nr PF K ℓ Nm Mg₀
      (tbKey QK weights rand tk (ttPlaced K₀ JU JO own₀ t7)) rest Kp Vd w₁) 12 k m :=
  depthsAt_of_declared (declared_twelve K₀ hK₀ weights rand tk Xs Nr K ℓ Nm Mg₀ rest Kp Vd w₁ e JU JO
    own₀ t7 hp hm hf hp' hm' hf' h7) k m

end

end AtPublicFiles.KeyDepthsAt

#print axioms AtPublicFiles.KeyDepthsAt.shapes_U
#print axioms AtPublicFiles.KeyDepthsAt.shapes_O
#print axioms AtPublicFiles.KeyDepthsAt.trees_U
#print axioms AtPublicFiles.KeyDepthsAt.trees_O
#print axioms AtPublicFiles.KeyDepthsAt.fit_two
#print axioms AtPublicFiles.KeyDepthsAt.fit_five
#print axioms AtPublicFiles.KeyDepthsAt.tb_low
#print axioms AtPublicFiles.KeyDepthsAt.tb_high
#print axioms AtPublicFiles.KeyDepthsAt.declared_of
#print axioms AtPublicFiles.KeyDepthsAt.ttPlaced
#print axioms AtPublicFiles.KeyDepthsAt.lays_U_at
#print axioms AtPublicFiles.KeyDepthsAt.lays_O_at
#print axioms AtPublicFiles.KeyDepthsAt.next_U
#print axioms AtPublicFiles.KeyDepthsAt.next_O
#print axioms AtPublicFiles.KeyDepthsAt.hk_U
#print axioms AtPublicFiles.KeyDepthsAt.hk_O
#print axioms AtPublicFiles.KeyDepthsAt.len_U
#print axioms AtPublicFiles.KeyDepthsAt.len_O
#print axioms AtPublicFiles.KeyDepthsAt.depth_tt_U
#print axioms AtPublicFiles.KeyDepthsAt.depth_tt_O
#print axioms AtPublicFiles.KeyDepthsAt.sum_ten
#print axioms AtPublicFiles.KeyDepthsAt.sum_eleven
#print axioms AtPublicFiles.KeyDepthsAt.sum_twelve
#print axioms AtPublicFiles.KeyDepthsAt.depths_ten
#print axioms AtPublicFiles.KeyDepthsAt.depths_eleven
#print axioms AtPublicFiles.KeyDepthsAt.opensR_ten
#print axioms AtPublicFiles.KeyDepthsAt.opensR_eleven
#print axioms AtPublicFiles.KeyDepthsAt.opensR_twelve
#print axioms AtPublicFiles.KeyDepthsAt.seven_is
#print axioms AtPublicFiles.KeyDepthsAt.declared_ten
#print axioms AtPublicFiles.KeyDepthsAt.declared_eleven
#print axioms AtPublicFiles.KeyDepthsAt.declared_twelve
#print axioms AtPublicFiles.KeyDepthsAt.depthsAt_ten
#print axioms AtPublicFiles.KeyDepthsAt.depthsAt_eleven
#print axioms AtPublicFiles.KeyDepthsAt.depthsAt_twelve
