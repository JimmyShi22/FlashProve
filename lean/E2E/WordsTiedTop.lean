-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/WordsTiedTop.lean: WordsTied AT MEMBER 9, at the thread at the real
halves, in the form that saysAt_nine (SaysAtNine.lean) asks as hw. Beneath it the members' laws of
WordsTiedNine.lean; the statement's shape comes from doorUF's shape by closed lines: so no fold: the plain
eight's fold that enters_nine drops is not called. The first challenge's length comes from Thr's Fit.

  codes_U, orc_U0, orc_U3, draw_first   closed lines, by the kernel, each can say no
  orc_of_shape   a state's message shapes are its shape's
  decls_nine     the rounds in front of member 9
  point_nine     the first challenge has the point's length, at a stand
  words_tied_nine   the statement

Limits. At keyBook, at the real readers. Thr at 9 and the lent row are premises. NOT IN FRONT OF A LAW OVER
COINS: a tie of the words to the lent coins behind Thr. The job's rows at the members alone: off the members
nothing is asked. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.WordsTiedNine
import E2E.SaysAtNine
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapesLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.Light.WordsTiedNine
open OnBytes (E zeroE TableKey OracleNotice Statement GroupLayout Oracle Group)
open OnBytes.Slice (rdE ofE begun)
open OnBytes.Means (tableSize layoutOf)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (P14 St first withU)
open Desc.K14.Honest
open ProofFile.Honest
open ProofFile.Honest.K14
open ProofFile.Honest.Sh (TestSh testSh)
open AtPublicFiles.KeySharedThread (parKey randKey sentKey threadKey)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.AtFiles (flat₂)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyTreesKey (declOf)
open AtPublicFiles.KeyFixedLines (pre_rounds)
open AtPublicFiles.HalvesAreJobs (pU pO)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.TreesAtNine (JN)
open AtPublicFiles.TableFilled (TU)
open AtPublicFiles.KeyTreesKey (tbKey)
open VerifiableInference.Desc.Key (Source)
open _root_.Desc.K14.Honest (Eight)
open ProofFile.Honest.K12.Light.KeyDoorUClosed (shapeU AQ sentK)
open ProofFile.Honest.K12.Light.ItemLaws (AN members_nine)

theorem codes_U : shapeU.core.st.codes = QK.codes := by decide +kernel

theorem orc_U0 : (shapeU.core.st.oracles[0]?).map (·.shape) = some (shapeAt (jobU AQ) 0) := by
  decide +kernel

theorem orc_U3 : (shapeU.core.st.oracles[3]?).map (·.shape) = some (shapeAt (jobOmega AQ) 1) := by
  decide +kernel

/-- Control: message 1 is not o_sp. -/
theorem orc_U1_bent : (shapeU.core.st.oracles[1]?).map (·.shape) ≠ some (shapeAt (jobOmega AQ) 1) := by
  decide +kernel

theorem draw_first : ((declOf QK).head?).map (·.entry.drawE) = some QK.par.S.kCol := by
  decide +kernel

/-- Control: the second round draws otherwise. -/
theorem draw_second_bent : (((declOf QK).drop 1).head?).map (·.entry.drawE) ≠ some QK.par.S.kCol := by
  decide +kernel

theorem orc_of_shape (t : VerifiableInference.Desc.K12.T12) (N : TestSh) (h : testSh t = N) (i : ℕ) :
    (t.st.oracles[i]?).map (·.shape) = (N.core.st.oracles[i]?).map (·.shape) := by
  subst h
  show _ = ((t.st.oracles.toList.map VerifiableInference.Desc.Ground.Sh.orcSh)[i]?).map (·.shape)
  rw [List.getElem?_map, Array.getElem?_toList, Option.map_map]
  rfl

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF))
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)

include B in
/-- The rounds in front of member 9 are the eight's. -/
theorem decls_nine :
    declsTo (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).bs 9 = declOf (parKey Xs PF) := by
  have hO := AtPublicFiles.KeySharedQuiet.over_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w
  have hp : (H2K.JointK.keySharedPre Xs.chains PF).length = 9 := by
    unfold H2K.JointK.keySharedPre
    rw [List.length_cons, List.length_map, AtPublicFiles.AtFiles.Full.blocksOr_eight B]
    try rfl
  unfold declsTo
  rw [hO.bs]
  show ((flat₂ Xs.chains PF).take 9).flatMap (·.rounds) = _
  rw [AtPublicFiles.AtFiles.flat₂_cut, List.take_left' hp, pre_rounds]

include B in
/-- **At a stand something is heard, and the first challenge has the point's length.** -/
theorem point_nine (e : parKey Xs PF = QK) {k : Coins (keyBook K₀)} {s : St}
    {m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) 9 k s m E) (ds : List Fmt.Drawn) :
    m.st.heard ≠ [] ∧ (m.st.heard ++ ds).take (0 + 1) = m.st.heard.take (0 + 1) ∧
      (Desc.K14.drawn (firstRv (m.st.heard ++ ds))).length = (parKey Xs PF).par.S.kCol := by
  have hd : drawsFit (declsTo (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).bs 9) m.st.heard = true :=
    u.2.1
  rw [decls_nine K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt] at hd
  have hf := draw_first
  rw [← e] at hf
  cases hD : declOf (parKey Xs PF) with
  | nil =>
    rw [hD] at hf
    cases hf
  | cons d tl =>
    rw [hD] at hd hf
    have hdraw : d.entry.drawE = (parKey Xs PF).par.S.kCol := Option.some.inj hf
    cases hh : m.st.heard with
    | nil =>
      rw [hh] at hd
      simp [drawsFit] at hd
    | cons x t =>
      rw [hh] at hd
      simp only [drawsFit, Bool.and_eq_true] at hd
      have h1 := hd.1
      simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h1
      have hlen : x.elems.length = d.entry.drawE := h1.1.1.1.1.1.1.1
      refine ⟨by simp, by simp, ?_⟩
      show (Desc.K14.drawn (rvOf x)).length = _
      rw [← elems_one x, ← hdraw, ← hlen]
      show (x.elems.map OnBytes.E.ofTriple ++ []).length = _
      simp

end

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF))
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)

include hK₀ in
/-- **WordsTied at member 9**, in the form that saysAt_nine asks as hw.
NOT IN FRONT OF A LAW OVER COINS: this file's head. -/
theorem words_tied_nine (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO) {k : Coins (keyBook K₀)} {s : St}
    {m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) 9 k s m E) (ds : List Fmt.Drawn)
    (c : (restPart (AM Xs K₁ B).toRun.toTest : Part Empty _ _).Coins)
    (hlp : lendPart (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) ⟨pU.place, 1⟩
      (restPart (AM Xs K₁ B).toRun.toTest : Part Empty _ _) = .ok c) :
    ∀ G, ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).st.groups[
        ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).g]? = some G →
      WordsTied ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).st
        ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).g G
        (ℓ.get ((TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).wit k m.st.input (m.st.heard ++ ds)))
        (layoutOf ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).st G)
        (plainMany (AN (X₀ := X₀) Xs K₁ B) m.st.input (frontOf m)
          (carriedCoins (AM Xs K₁ B).toRun.toTest (stretches _ c.2.2))) := by
  intro G hG oM ho pt i hi
  obtain ⟨hne, ht1, hpt⟩ := point_nine K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt e u ds
  have hSh : SendShapes (parKey Xs PF) := by
    rw [e]
    exact sendShapes_of_fit ProofFile.Honest.K12.Light.KeyDoorUClosed.sendings_U
  have hS : (parKey Xs PF).S.sharedSplitNeeded = true := hQ.facts.two
  have hu : Desc.K14.withU (parKey Xs PF).S = some (sentKey Xs PF) := hQ.facts.goes
  have hsh : testSh ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)) = shapeU := by
    have er : (AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m) =
        doorUF (parKey Xs PF) (sentKey Xs PF) [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8]
          (fun c : Common W₀ Rc TableKey => c.key)
          (fun c fr => colsLoc (parKey Xs PF) ((keyProver K₁).storedWords c.w₀ c.rc) fr.seen.rounds)
          m.st.input (frontOf m) := rfl
    have e0 : testSh ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)) =
        Desc.K14.Shape.doorU (endOf (parKey Xs PF) (sentKey Xs PF)) := by
      rw [er]
      exact shape_doorUF (parKey Xs PF) _ B.made hS (sentKey Xs PF) hu _ _ _ _
    have e1 : Desc.K14.Shape.doorU (endOf (parKey Xs PF) (sentKey Xs PF)) = shapeU := by
      show Desc.K14.Shape.doorU (endOf (parKey Xs PF) (sentOf (parKey Xs PF).S)) = _
      rw [e]
      unfold shapeU sentK
      rfl
    exact e0.trans e1
  have hcodes : ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).st.codes = (parKey Xs PF).codes := by
    have h1 : (testSh ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m))).core.st.codes =
        ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).st.codes := rfl
    rw [← h1, hsh, e]
    exact codes_U
  have hmem := members_nine Xs K₁ hQ e B m.st.input (frontOf m) G hG
  have hmemA : G.members = #[0, 3] := by
    apply Array.toList_inj.1
    exact hmem
  obtain ⟨hf0, hf3⟩ := VerifiableInference.Desc.K12.Coin.find_two
    (layoutOf ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).st G) 0 3 (by decide)
    (show G.members = #[0, 3] from hmemA)
  have hts : ∀ o' pt', tableSize (begun ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).st
      ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).g G) o' pt' =
      tableSize ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).st o' pt' := fun o' pt' => by
    unfold tableSize OnBytes.Statement.tableBits
    rw [OnBytes.LayLaw.begun_has, OnBytes.Slice.begun_rowBits, OnBytes.LayLaw.begun_placeBits]
  have hcd := (OnBytes.Slice.begun_codes ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).st
    ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).g G).trans hcodes
  have hWit : ℓ.get ((TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).wit k m.st.input
      (m.st.heard ++ ds)) = witAll (parKey Xs PF) (sentKey Xs PF)
        (holds2 (parKey Xs PF) K₁.weights (randKey K₁)) (fun k w h => ℓ.get (rest k w h)) k m.st.input
        (m.st.heard ++ ds) :=
    get_witL ℓ _ _ _ rest k m.st.input (m.st.heard ++ ds)
  rw [hWit]
  unfold witAll
  have h2 : (sentKey Xs PF).size = 2 := hQ.facts.goesTwo
  have hoo : oM = 0 ∨ oM = 3 := by
    have h' : oM ∈ G.members.toList := ho
    rw [hmem] at h'
    simpa using h'
  rcases hoo with rfl | rfl
  · have hy0 : ((begun ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).st
        ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).g G).oracles[0]?).map (·.shape) =
        some (shapeAt (jobU ⟨parKey Xs PF, 0⟩) 0) := by
      rw [OnBytes.Slice.begun_shape, orc_of_shape _ _ hsh, e]
      exact orc_U0
    obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1 hy0
    rw [words2_ours (parKey Xs PF) (sentKey Xs PF) _ _ _ _ 0 (Or.inl (by rw [h2]; decide)) pt i]
    exact tie_U K₀ hK₀ Xs K₁ B e hQ hSh k m.st.input (frontOf m) (m.st.heard ++ ds)
      (by simp [hne]) ht1.symm c hlp hpt _ _ hf0 y hy hys hcd pt i (by rw [hts]; exact hi)
  · have hy3 : ((begun ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).st
        ((AN (X₀ := X₀) Xs K₁ B).rec₀ m.st.input (frontOf m)).g G).oracles[3]?).map (·.shape) =
        some (shapeAt (jobOmega ⟨parKey Xs PF, 0⟩) 1) := by
      rw [OnBytes.Slice.begun_shape, orc_of_shape _ _ hsh, e]
      exact orc_U3
    obtain ⟨y, hy, hys⟩ := Option.map_eq_some_iff.1 hy3
    have hw2 : (Desc.K14.withOmega (parKey Xs PF).S).size = 2 :=
      (Desc.K14.Honest.withOmega_two hQ.facts.two).1
    rw [words2_ours (parKey Xs PF) (sentKey Xs PF) _ _ _ _ 3 (Or.inr ⟨by omega, by rw [hw2]; omega⟩) pt i]
    exact tie_O K₀ hK₀ Xs K₁ B e hQ hSh k m.st.input (frontOf m) (m.st.heard ++ ds)
      (by simp [hne]) ht1.symm c hlp hpt _ _ hf3 y hy hys hcd pt i (by rw [hts]; exact hi)

end

end ProofFile.Honest.K12.Light.WordsTiedNine

end

#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.codes_U
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.orc_U0
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.orc_U3
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.orc_U1_bent
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.draw_first
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.draw_second_bent
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.orc_of_shape
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.decls_nine
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.point_nine
#print axioms ProofFile.Honest.K12.Light.WordsTiedNine.words_tied_nine
