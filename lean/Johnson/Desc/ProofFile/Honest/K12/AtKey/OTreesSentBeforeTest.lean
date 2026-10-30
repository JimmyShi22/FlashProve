-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OTreesSentBeforeTest.lean: at a stand of the filled key thread at border 10, the job's two trees
that were sent in front show the columns of the sending, and its third is the next to be sent.

  `column_of_sending`   a tree in front that a sending lays shows the sending's column
  `fixed_own_one`       the challenges that fix own 1 hold at least the first
  `oldAtO_at_ten`       `OldAtO` at the job of the test on G_omega

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `column_of_sending`, `oldAtO_at_ten` bear this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their
  ground: the thread from Thr as a premise.
- At the readers that the parts hold.
- That a stand at 10 is reached is not said.
- Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.TreesSentBeforeTestAtNine
import E2E.KeyFixedLinesO
import E2E.KeyTenLinesKernel
import Johnson.Desc.ProofFile.Honest.K12.Own.ColsTermOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block sendRound)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source descriptionFromSource)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey parKey randKey)
open AtPublicFiles.KeyThread (sendRound_append rootsOf decl₂)
open AtPublicFiles.KeyTblTrial (sendings_count)
open AtPublicFiles.KeyTreesKey (tbKey treesOf5)
open AtPublicFiles.KeyFixedLines (trees_key_O decl_front10 declO roots_closed_O)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub of_atFull)
open AtPublicFiles.KeyDepthsAt (tb_low fit_five)
open AtPublicFiles.HalvesAreJobs (pU pO pO_full JO)
open AtPublicFiles.TableFilled (TR ttF)
open AtPublicFiles.OldAtNine (treesU_one)
open AtPublicFiles.AtFiles.Full (QK PF)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open H2K.Member (piKOFull)
open ProofFile.Honest.K12.Own (OldAtO)
open ProofFile.Honest.K12.Light (col_sent widthFits tree0_lent_Omega tree1_lent_Omega bookCutsOmega colFitsOmega
  vecAt askOf)
open ProofFile.Honest.K12.Light.KeyDoorUClosed (sendings_U cuts_O col_O width_O_both)

/-- Tree 1 goes out behind the first challenge. By the kernel. -/
theorem own_one_sent : 1 ≤ (sendRound declO 1).getD 0 := by decide +kernel

/-- The depths of the two trees at the place. By the kernel. -/
theorem depths_at_place : ProofFile.Honest.K12.Light.depthOf piKOFull 0 = 22 ∧ ProofFile.Honest.K12.Light.depthOf piKOFull 1 = 13 := by decide +kernel

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)

include hK₀ in
/-- **At a stand a tree in front that a sending lays shows the sending's column.** -/
theorem column_of_sending (e : parKey Xs PF = QK) {k : Coins (keyBook K₀)} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) 10 k s m E)
    {n : ℕ} (hn : n < 3) (Jd : SendJob) (pl : Place) (i : ℕ)
    (harm : tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀) (.own n) =
      sendTable Jd (witOf (parKey Xs PF) K₁.weights (randKey K₁)) pl 1 i)
    (own : Cs (sendingPart Jd).takes)
    (hcut : (k.look 1 ⟨pl, 0⟩).2.cut ⟨0, 0⟩ (sendingPart Jd).takes = some own)
    (hw : widthFits Jd i = true) (x : ℕ) (hx : x < 2 ^ (AtPublicFiles.KeyOpens.depthOf.getD n 0)) :
    colAt E.tree (.own n) x = columnOf Jd.Q.codes Jd.Q.sent
      (Jd.rows ⟨witOf (parKey Xs PF) K₁.weights (randKey K₁) m.st.input,
        m.st.heard.take ((TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).fixed (.own n)), ()⟩
        (coinsE own).toArray) i x := by
  obtain ⟨⟨-, hH⟩, -⟩ := u
  have e7 := trees_key_O Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w e B
  have hin : Fmt.TreeSource.own n ∈ (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).hand 10 := by
    show _ ∈ [] ++ (List.range (treesTo _ 10)).map Fmt.TreeSource.own
    rw [e7]
    exact List.mem_append_right _ (List.mem_map.2 ⟨n, List.mem_range.2 (by omega), rfl⟩)
  obtain ⟨pt, hE, -, hs⟩ := Thread.handAt_elim _ (hH _ hin)
  obtain ⟨hlen, hcol⟩ := Table.same_elim hs
  obtain ⟨Tt, hT, hc⟩ := col_sent Jd (Jd.rows ⟨witOf (parKey Xs PF) K₁.weights (randKey K₁) m.st.input,
    m.st.heard.take ((TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).fixed (.own n)), ()⟩
    (coinsE own).toArray) i hw
  have htab : ((TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).tableAt (.own n) k m).2 = Tt := by
    show (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀) (.own n) k m.st.input
      (m.st.heard.take ((TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).fixed (.own n)))).2 = Tt
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
    show (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀) (.own n) k m.st.input
      _).2.logLength = _
    rw [hq]
    exact tb_low K₀ hK₀ K₁.weights (randKey K₁) tk _ k _ _ hn
  unfold colAt
  rw [hE]
  show pt.2.col x = _
  rw [hcol x (by rw [hdep]; exact hx), htab, hc]

/-- **The challenges that fix own 1 hold at least the first.** -/
theorem fixed_own_one (e : parKey Xs PF = QK) :
    1 ≤ (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).fixed (.own 1) := by
  have hr : 11 ≤ rootsOf ((AtPublicFiles.KeyTreesKey.declOf QK ++ (H2K.JointK.keyGu PF).rounds) ++
      (H2K.JointK.keyOmega (PF.O.getD PF.U)).rounds) := roots_closed_O
  show 1 ≤ AtPublicFiles.KeyThread.sentIn (decl₂ (descriptionFromSource Xs Nr PF)) 1
  unfold AtPublicFiles.KeyThread.sentIn
  rw [decl_front10, e, sendRound_append _ _ _ (by omega)]
  exact own_one_sent

include hK₀ in
/-- **`OldAtO` at the job of the test on G_omega, at a stand at 10.** -/
theorem oldAtO_at_ten (e : parKey Xs PF = QK) {k : Coins (keyBook K₀)} {s : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) 10 k s m E)
    (c : RowCoins [(firstPart (JO Xs K₁ B) : Part Empty _ _), restPart (JO Xs K₁ B)])
    (hc : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) (JO Xs K₁ B).p.place
      [(firstPart (JO Xs K₁ B) : Part Empty _ _), restPart (JO Xs K₁ B)] 0 = .ok c) :
    OldAtO E ((JO Xs K₁ B).trees₀ m.st.input (frontOf m) (restCoins (JO Xs K₁ B) c.2.1).mem
      ((JO Xs K₁ B).first m.st.input (frontOf m) (restCoins (JO Xs K₁ B) c.2.1)))
      (fun j => [Fmt.TreeSource.own 1, .own 2, .own 7].getD j (.own 0)) 2 := by
  have hP : pO = piKOFull := pO_full
  have hu : treesU (parKey Xs PF) = 1 := by
    rw [e]
    exact treesU_one
  have hc3 := sendings_count
  rw [← e] at hc3
  have hQ : sendingsFit (⟨parKey Xs PF, 0⟩ : SendPub).P = true := by
    show sendingsFit (parKey Xs PF) = true
    rw [e]
    exact sendings_U
  have hb : bookCutsOmega (keyBook K₀) ⟨parKey Xs PF, 0⟩ pO = true := by
    rw [e, hP]
    exact of_atFull cuts_O hK₀
  have hcf : colFitsOmega ⟨parKey Xs PF, 0⟩ pO = true := by
    rw [e, hP]
    exact col_O
  have hw0 : widthFits (jobOmega ⟨parKey Xs PF, 0⟩) 0 = true := by
    rw [e]
    exact width_O_both.1
  have hw1 : widthFits (jobOmega ⟨parKey Xs PF, 0⟩) 1 = true := by
    rw [e]
    exact width_O_both.2
  have fO : (sendingPart (jobOmega ⟨parKey Xs PF, 0⟩)).takes.f ≤
        (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 5, 0⟩).f ∧
      (sendingPart (jobOmega ⟨parKey Xs PF, 0⟩)).takes.e ≤
        (dueAt ((keyBook K₀).rowsOf 1) ⟨sendPlace 5, 0⟩).e := by
    rw [e]
    exact fit_five K₀ hK₀
  obtain ⟨ownO, hO⟩ := Option.isSome_iff_exists.1 (cut_of_due k 1 (by omega) ⟨sendPlace 5, 0⟩ _ fO)
  have hl := lendRow_second hc
  have hf1 := fixed_own_one K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e
  have e7 := trees_key_O Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w e B
  have hsent : E.sent = 7 := by
    have h := u.2.2.2.2.1.2.2.1
    exact h.trans e7
  refine ⟨fun j hj hn n hm => ?_, fun j hj hn x hx => ?_, ?_⟩
  · have hj3 : j < 3 := hj
    rw [hsent]
    have h' : [Fmt.TreeSource.own 1, .own 2, .own 7].getD j (.own 0) = .own n := hm
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · injection h' with h''
      omega
    · injection h' with h''
      omega
  · have hj3 : j < 3 := hj
    have hd := depths_at_place
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · have hx' : x < 2 ^ 22 := by
        have e0 : ProofFile.Honest.K12.Light.depthOf pO 0 = 22 := by
          rw [hP]
          exact hd.1
        rw [← e0]
        exact hx
      have hd0 : (AtPublicFiles.KeyOpens.depthOf.getD 1 0) = 22 := rfl
      have hcol := column_of_sending K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e u (n := 1)
        (by omega) (jobOmega ⟨parKey Xs PF, 0⟩) (sendPlace 5) 0
        (by
          show (if 1 < treesU (parKey Xs PF) then _ else
            if 1 < treesU (parKey Xs PF) + treesOf5 (parKey Xs PF) then _ else _) = _
          rw [if_neg (by omega), if_pos (by omega), hu]) ownO hO hw0 x (by rw [hd0]; exact hx')
      refine hcol.trans ?_
      have hv : vecAt (jobOmega ⟨parKey Xs PF, 0⟩) 0
          (askOf ⟨parKey Xs PF, 0⟩ (fun c => K₁.weights c.w₀) (fun c => randKey K₁ c.rc)) none
          m.st.input (frontOf m) =
          (jobOmega ⟨parKey Xs PF, 0⟩).data ⟨witOf (parKey Xs PF) K₁.weights (randKey K₁) m.st.input,
            m.st.heard.take ((TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).fixed (.own 1)), ()⟩ 0 :=
        congrFun (readsBelow_mono (jobOmega_readsBelow ⟨parKey Xs PF, 0⟩) hf1 _ m.st.heard).symm 0
      exact (tree0_lent_Omega (keyBook K₀) _ _ ⟨parKey Xs PF, 0⟩ pO _ _ _ none ownO hO hQ
        m.st.input (frontOf m) _ x c.2.1 hl hb hcf hv).symm
    · have hx' : x < 2 ^ 13 := by
        have e1 : ProofFile.Honest.K12.Light.depthOf pO 1 = 13 := by
          rw [hP]
          exact hd.2
        rw [← e1]
        exact hx
      have hd2 : (AtPublicFiles.KeyOpens.depthOf.getD 2 0) = 13 := rfl
      have hcol := column_of_sending K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e u (n := 2)
        (by omega) (jobOmega ⟨parKey Xs PF, 0⟩) (sendPlace 5) 1
        (by
          show (if 2 < treesU (parKey Xs PF) then _ else
            if 2 < treesU (parKey Xs PF) + treesOf5 (parKey Xs PF) then _ else _) = _
          rw [if_neg (by omega), if_pos (by omega), hu]) ownO hO hw1 x (by rw [hd2]; exact hx')
      refine hcol.trans ?_
      exact (tree1_lent_Omega (keyBook K₀) _ _ ⟨parKey Xs PF, 0⟩ pO _ _ _ none ownO hO hQ
        m.st.input (frontOf m) _ x c.2.1 hl hb hcf).symm
  · show (Fmt.TreeSource.own 7 : Fmt.TreeSource) = _
    rw [hsent]

end

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.own_one_sent
#print axioms ProofFile.Honest.K12.AtKey.depths_at_place
#print axioms ProofFile.Honest.K12.AtKey.column_of_sending
#print axioms ProofFile.Honest.K12.AtKey.fixed_own_one
#print axioms ProofFile.Honest.K12.AtKey.oldAtO_at_ten
