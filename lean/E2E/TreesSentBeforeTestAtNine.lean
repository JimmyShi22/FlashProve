-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/TreesSentBeforeTestAtNine.lean: OldAt AT MEMBER 9, at the thread at the real halves
(TableFilled.lean's TU): the trees that the test on G_u opens are the sendings' own, column for column.
So K12At.opens' last conjunct, at keyBook K₀.

  low_sent       tree 0 goes out after the first challenge
  col_of_send    at a stand, a tree in front that a sending lays shows the sending's column
  oldAt_nine     OldAt at JN, at own 0 and own 2

PREMISES. e, hs, hK₀ as in TableFilled.lean. Thr at 9: the trees at hand show the thread's tables. The row of
the two parts is lent c. What is had inside: the closed lines over the book and the sendings, tree0_lent_U,
tree1_lent_U, col_sent, readsBelow.

Limits. At wts := K₁.weights, rnd := randKey K₁ and at keyBook alone: at free readers hv fails. Own 0 and own 2
of this job alone. Thr's own E: a law on columns at hand; nothing of an accepted column. NOT IN FRONT OF A LAW
OVER COINS: it stands behind Thr and ties a job's trees to the lent coins. Nothing on completeness, on
soundness or on what is hidden.
-/
import E2E.TableFilled
import E2E.KeyNineLinesKernel
import E2E.KeyDoorUClosedKernel
import Johnson.Desc.ProofFile.Honest.K12.CutOfBookAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.OldAtNine
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block sendRound)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source descriptionFromSource)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey parKey randKey)
open AtPublicFiles.KeyThread (sendRound_append rootsOf decl₂)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyTblTrial (sendings_count)
open AtPublicFiles.KeyTreesKey (treesOf5)
open AtPublicFiles.KeyFixedLines (trees_key decl_front10 declO roots_closed_O)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub of_atFull)
open AtPublicFiles.KeyDepthsAt (tb_low fit_two fit_five)
open AtPublicFiles.HalvesAreJobs (pU pO)
open AtPublicFiles.TreesAtNine (JN)
open AtPublicFiles.TableFilled (TU)
open AtPublicFiles.AtFiles.Full (QK PF)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open H2K.Member (piKUFull)
open ProofFile.Honest.K12.Light (jobAtU col_sent widthFits tree0_lent_U tree1_lent_U)
open ProofFile.Honest.K12.Light.KeyDoorUClosed (col_fit fresh_fit cuts_fit sendings_U width_U room_U)

/-- Tree 0 goes out behind the first challenge. By the kernel. -/
theorem low_sent : 1 ≤ (sendRound declO 0).getD 0 := by decide +kernel

theorem treesU_one : treesU QK = 1 := by decide +kernel

/-- The two trees' depths at the place. By the kernel. -/
theorem depths_place : ProofFile.Honest.K12.Light.depthOf piKUFull 0 = 24 ∧
    ProofFile.Honest.K12.Light.depthOf piKUFull 1 = 13 := by decide +kernel

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF))
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)

include hK₀ B in
/-- **At a stand a tree in front that a sending lays shows the sending's column.** -/
theorem col_of_send (e : parKey Xs PF = QK) {k : Coins (keyBook K₀)} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) 9 k s m E)
    {n : ℕ} (hn : n < 3) (Jd : SendJob) (pl : Place) (i : ℕ)
    (harm : tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt (.own n) =
      sendTable Jd (witOf (parKey Xs PF) K₁.weights (randKey K₁)) pl 1 i)
    (own : Cs (sendingPart Jd).takes)
    (hcut : (k.look 1 ⟨pl, 0⟩).2.cut ⟨0, 0⟩ (sendingPart Jd).takes = some own)
    (hw : widthFits Jd i = true) (x : ℕ) (hx : x < 2 ^ (AtPublicFiles.KeyOpens.depthOf.getD n 0)) :
    colAt E.tree (.own n) x = columnOf Jd.Q.codes Jd.Q.sent
      (Jd.rows ⟨witOf (parKey Xs PF) K₁.weights (randKey K₁) m.st.input,
        m.st.heard.take ((TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).fixed (.own n)), ()⟩
        (coinsE own).toArray) i x := by
  obtain ⟨⟨-, hH⟩, -⟩ := u
  have e3 := trees_key Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w e B
  have hin : Fmt.TreeSource.own n ∈ (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).hand 9 := by
    show _ ∈ [] ++ (List.range (treesTo _ 9)).map Fmt.TreeSource.own
    rw [e3]
    exact List.mem_append_right _ (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩)
  obtain ⟨pt, hE, -, hs⟩ := Thread.handAt_elim _ (hH _ hin)
  obtain ⟨hlen, hcol⟩ := Table.same_elim hs
  obtain ⟨Tt, hT, hc⟩ := col_sent Jd (Jd.rows ⟨witOf (parKey Xs PF) K₁.weights (randKey K₁) m.st.input,
    m.st.heard.take ((TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).fixed (.own n)), ()⟩
    (coinsE own).toArray) i hw
  have htab : ((TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).tableAt (.own n) k m).2 = Tt := by
    show (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt (.own n) k m.st.input
      (m.st.heard.take ((TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).fixed (.own n)))).2 = Tt
    rw [harm]
    unfold sendTable
    simp only [hcut]
    unfold sendTablesAt
    rw [List.getD_eq_getElem?_getD, hT]
    rfl
  have hq : ∀ t, tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk t =
      tbKey QK K₁.weights (randKey K₁) tk t := fun t => by rw [e]
  have hdep : pt.2.logLength = AtPublicFiles.KeyOpens.depthOf.getD n 0 := by
    rw [hlen]
    show (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt (.own n) k m.st.input
      _).2.logLength = _
    rw [hq]
    exact tb_low K₀ hK₀ K₁.weights (randKey K₁) tk _ k _ _ hn
  unfold colAt
  rw [hE]
  show pt.2.col x = _
  rw [hcol x (by rw [hdep]; exact hx), htab, hc]

include hK₀ in
/-- **OldAt at member 9.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem oldAt_nine (e : parKey Xs PF = QK) {k : Coins (keyBook K₀)} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt) 9 k s m E)
    (c : RowCoins [(firstPart (JN Xs K₁ B) : Part Empty _ _), restPart (JN Xs K₁ B)])
    (hc : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) (JN Xs K₁ B).p.place
      [(firstPart (JN Xs K₁ B) : Part Empty _ _), restPart (JN Xs K₁ B)] 0 = .ok c) :
    OldAt E ((JN Xs K₁ B).trees₀ m.st.input (frontOf m) (restCoins (JN Xs K₁ B) c.2.1).mem
      ((JN Xs K₁ B).first m.st.input (frontOf m) (restCoins (JN Xs K₁ B) c.2.1)))
      (fun j => [Fmt.TreeSource.own 0, .own 2].getD j (.own 0)) := by
  have hP : pU = piKUFull := place_full
  have hu : treesU (parKey Xs PF) = 1 := by
    rw [e]
    exact treesU_one
  have hc3 := sendings_count
  rw [← e] at hc3
  have hQ : sendingsFit (⟨parKey Xs PF, 0⟩ : SendPub).P = true := by
    show sendingsFit (parKey Xs PF) = true
    rw [e]
    exact sendings_U
  have hb : ProofFile.Honest.K12.Light.bookCutsU (keyBook K₀) ⟨parKey Xs PF, 0⟩ pU = true := by
    rw [e, hP]
    exact of_atFull ProofFile.Honest.K12.Light.KeyDoorUClosed.cuts_fit hK₀
  have hcf : ProofFile.Honest.K12.Light.colFitsU ⟨parKey Xs PF, 0⟩ pU = true := by
    rw [e, hP]
    exact col_fit
  have hfr : ProofFile.Honest.K12.Light.freshFitsU ⟨parKey Xs PF, 0⟩ pU = true := by
    rw [e, hP]
    exact fresh_fit
  have hroom : 2 * (ProofFile.Honest.K12.Light.stage₀ pU).k + 1 ≤
      (ProofFile.Honest.K12.Light.stage₀ pU).h + (ProofFile.Honest.K12.Light.stage₀ pU).Z.l := by
    rw [hP]
    exact of_decide_eq_true room_U
  have hwU : widthFits (jobU ⟨parKey Xs PF, 0⟩) 0 = true := by
    rw [e]
    exact width_U.1
  have hwO : widthFits (jobOmega ⟨parKey Xs PF, 0⟩) 1 = true := by
    rw [e]
    exact width_U.2
  have fU : (sendingPart (jobU ⟨parKey Xs PF, 0⟩)).takes.f ≤
        (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 2, 0⟩).f ∧
      (sendingPart (jobU ⟨parKey Xs PF, 0⟩)).takes.e ≤
        (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 2, 0⟩).e := by
    rw [e]
    exact fit_two K₀ hK₀
  have fO : (sendingPart (jobOmega ⟨parKey Xs PF, 0⟩)).takes.f ≤
        (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 5, 0⟩).f ∧
      (sendingPart (jobOmega ⟨parKey Xs PF, 0⟩)).takes.e ≤
        (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 5, 0⟩).e := by
    rw [e]
    exact fit_five K₀ hK₀
  obtain ⟨ownU, hU⟩ := Option.isSome_iff_exists.1 (cut_of_due k 1 (by omega) ⟨sendPlace 2, 0⟩ _ fU)
  obtain ⟨ownO, hO⟩ := Option.isSome_iff_exists.1 (cut_of_due k 1 (by omega) ⟨sendPlace 5, 0⟩ _ fO)
  have hl := lendRow_second hc
  have hf1 : 1 ≤ (TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).fixed (.own 0) := by
    have hr : 11 ≤ rootsOf ((AtPublicFiles.KeyTreesKey.declOf QK ++ (H2K.JointK.keyGu PF).rounds) ++
        (H2K.JointK.keyOmega (PF.O.getD PF.U)).rounds) := roots_closed_O
    show 1 ≤ AtPublicFiles.KeyThread.sentIn (decl₂ (descriptionFromSource Xs Nr PF)) 0
    unfold AtPublicFiles.KeyThread.sentIn
    rw [decl_front10, e, sendRound_append _ _ _ (by omega)]
    exact low_sent
  refine ⟨fun j hj n hn => ?_, fun j hj x hx => ?_⟩
  · have e3 := trees_key Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
      (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk tt) rest Kp Vd w e B
    have hsent : E.sent = 3 := by
      have h := u.2.2.2.2.1.2.2.1
      exact h.trans e3
    have hj2 : j < 2 := hj
    rw [hsent]
    have h' : [Fmt.TreeSource.own 0, .own 2].getD j (.own 0) = .own n := hn
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · injection h' with h''
      omega
    · injection h' with h''
      omega
  · have hj2 : j < 2 := hj
    have hd := depths_place
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · have hx' : x < 2 ^ 24 := by
        have e0 : ProofFile.Honest.K12.Light.depthOf pU 0 = 24 := by
          rw [hP]
          exact hd.1
        rw [← e0]
        exact hx
      have hd0 : (AtPublicFiles.KeyOpens.depthOf.getD 0 0) = 24 := rfl
      have hcol := col_of_send K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt e u (n := 0) (by omega)
        (jobU ⟨parKey Xs PF, 0⟩) (sendPlace 2) 0
        (by
          show (if 0 < treesU (parKey Xs PF) then _ else _) = _
          rw [if_pos (by omega)]) ownU hU hwU x (by rw [hd0]; exact hx')
      refine hcol.trans ?_
      have hv : ProofFile.Honest.K12.Light.vecAt (jobU ⟨parKey Xs PF, 0⟩) 0
          (ProofFile.Honest.K12.Light.askOf ⟨parKey Xs PF, 0⟩ (fun c => K₁.weights c.w₀)
            (fun c => randKey K₁ c.rc)) none m.st.input (frontOf m) =
          (jobU ⟨parKey Xs PF, 0⟩).data ⟨witOf (parKey Xs PF) K₁.weights (randKey K₁) m.st.input,
            m.st.heard.take ((TU K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w tt).fixed (.own 0)), ()⟩ 0 :=
        congrFun (readsBelow_mono (jobU_readsBelow ⟨parKey Xs PF, 0⟩) hf1 _ m.st.heard).symm 0
      exact (tree0_lent_U (keyBook K₀) _ _ ⟨parKey Xs PF, 0⟩ pU _ _ _ none ownU hU ownO hO hQ
        m.st.input (frontOf m) _ x c.2.1 hl hb hcf hfr hroom hv).symm
    · have hx' : x < 2 ^ 13 := by
        have e1 : ProofFile.Honest.K12.Light.depthOf pU 1 = 13 := by
          rw [hP]
          exact hd.2
        rw [← e1]
        exact hx
      have hd2 : (AtPublicFiles.KeyOpens.depthOf.getD 2 0) = 13 := rfl
      have hcol := col_of_send K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B tt e u (n := 2) (by omega)
        (jobOmega ⟨parKey Xs PF, 0⟩) (sendPlace 5) 1
        (by
          show (if 2 < treesU (parKey Xs PF) then _ else
            if 2 < treesU (parKey Xs PF) + treesOf5 (parKey Xs PF) then _ else _) = _
          rw [if_neg (by omega), if_pos (by omega), hu]) ownO hO hwO x (by rw [hd2]; exact hx')
      refine hcol.trans ?_
      exact (tree1_lent_U (keyBook K₀) _ _ ⟨parKey Xs PF, 0⟩ pU _ _ _ none ownU hU ownO hO hQ
        m.st.input (frontOf m) _ x c.2.1 hl hb hcf hfr).symm

end

end AtPublicFiles.OldAtNine

end

#print axioms AtPublicFiles.OldAtNine.low_sent
#print axioms AtPublicFiles.OldAtNine.treesU_one
#print axioms AtPublicFiles.OldAtNine.depths_place
#print axioms AtPublicFiles.OldAtNine.col_of_send
#print axioms AtPublicFiles.OldAtNine.oldAt_nine
