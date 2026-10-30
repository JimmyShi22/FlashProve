-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: carryRows returns at a run.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/CarryAtFirst.lean: at a called second part of the test right
behind the finish of the code switch, the sender's text that jobL calls returns: the limit of
AtProof/JobL.lean, «till then "carryRows returns" is a named premise», is paid at a run. The middle of
the proof of trees_first (Sim2/TreesL.lean), lifted out: a second text of it, made by program.


  carry_returns_first   the statement

Conditional on the run's returning. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block FileDescription Oracle)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open Johnson.Prover.Send (col Rows)

section Main
variable {Xi W₀ Rc Ky Tr X₀ Y Pb : Type}

local notation "JL" => jobL (W₀ := W₀) (Rc := Rc) (Xi := Xi) (Tr := Tr) (X := Y)

/-- **The sender's text returns at a run.** -/
theorem carry_returns_first {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (q : VerifiableInference.Desc.K12.P12)
    (door : Local W₀ Rc Xi Tr → Front Y → VerifiableInference.Desc.K12.T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (pl : K2.SwitchPlace)
    (Js : SimJob Pb)
    (σ : Side F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Pb)
    (pre : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl) (t : List (Block F.S₁ F.Cl))
    (S : StandsAt F.first.blocksInOrder R.first σ (restMember (JL q door D readers closing pl) Js)
      (pre ++ [b]) t (firstLen q.nums.stages))
    (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hgK : (P.first.find? fun g => g.place == b.place) =
      some (K2.switchHalf (K2.coreSender K2.freshTable) D readers closing pl))
    (hfit : fitsL q pl = true)
    (hT : bookTiesAtFinish Bk ⟨σ.block.place, 1⟩ ⟨b.place, 0⟩ pl = true)
    (st : List (ℕ × ℕ × List UInt64)) (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
    (hm : midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m))
    (ca : CsAll (restPart (JL q door D readers closing pl) :
      Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).carries)
    (hca : carriedAt Bk k 0 ⟨σ.block.place, 1⟩ (restPart (JL q door D readers closing pl) :
      Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y) = .ok ca) :
    ∃ Rw, carryRows D readers closing pl m.st.input
      (heardL (restFront (JL q door D readers closing pl) m))
      (carriedCoins (JL q door D readers closing pl) (stretches _ ca)).mem = .ok Rw := by
  have F' := fitsL_facts hfit
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨lS, -, -⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  -- the stand
  obtain ⟨m', hm', hin, hheard, -, -, hbf, -, -, -, -⟩ :=
    frame_at_first hpl hR hrun σ (restMember (JL q door D readers closing pl) Js) (pre ++ [b]) t _ _
      S rfl hc st
  obtain rfl : m = m' := Option.some.inj (Except.ok.inj (hm.symm.trans hm'))
  obtain ⟨a₁, y, m₂, ha₁, hw, hyl, hym, -⟩ :=
    played_at_first hpl hR hrun σ (restMember (JL q door D readers closing pl) Js) (pre ++ [b]) t _ _
      S rfl hc
  have hcut : F.first.blocksInOrder = pre ++ b :: (σ.block :: t) := by
    rw [S.cut]
    simp
  have hb : b.rounds.length = 2 := (block_rounds_at_first hR pre b _ hcut _ hgK).symm
  have hlenpre : ((pre ++ [b]).flatMap (·.rounds)).length = (pre.flatMap (·.rounds)).length + 2 := by
    simp [List.flatMap_append, hb]
  obtain ⟨zᵢ, mᵢ, c₂, qd, Dt, Ts, hpi, hmi, hlend, hq, hqT, hDt, hTs⟩ :=
    switch_in_front hR pre b (σ.block :: t) hcut
      (fun h => by rw [h] at hb; cases hb) (K2.coreSender K2.freshTable) D readers closing pl hgK _
      (by rw [hlenpre]; omega) _ a₁ y (start_laid ha₁) (by have := S.fits; simp only [restMember] at this; omega) hw
      (by rw [hym]; rfl)
  -- the challenges and the input
  have hlenR : ((pre ++ [b]).flatMap (·.rounds)).length + firstLen q.nums.stages ≤
      ρ.first.length := by
    have e := lS.1
    have := S.fits
    omega
  have hh : mᵢ.st.heard = ρ.first.take (pre.flatMap (·.rounds)).length := by
    have a3 := walk_hears _ _ _ _ a₁ zᵢ (start_hears ha₁) hpi mᵢ hmi
    have a4 := walk_laid_drawn _ _ _ a₁ zᵢ hpi
    rw [start_laid ha₁, List.map_nil, List.nil_append] at a4
    rw [a4] at a3
    exact a3.trans (List.nil_append _)
  have hinp : mᵢ.st.input = m.st.input := by
    rw [hin]
    exact (walk_mid ha₁ hpi hmi).1
  have hheardL : heardL (restFront (JL q door D readers closing pl) m) = mᵢ.st.heard := by
    rw [hh]
    show ((m.st.heard.take (m.st.heard.length - firstLen q.nums.stages))).take
      ((m.st.heard.take (m.st.heard.length - firstLen q.nums.stages)).length - 2) = _
    rw [hheard]
    exact take_three _ _ _ _ _ (by rw [hlenpre]) hlenR
  -- the coins
  have hown := own_of_lendPart hlend
  have hcar₂ := carried_of_lendPart _ _ _ _ _ c₂ hlend
  unfold carriedAt at hca
  obtain ⟨c₁, hl₁, e₁⟩ := exMap_ok hca
  subst e₁
  have hcar₁ := carried_of_lendPart _ _ _ _ _ c₁ hl₁
  obtain ⟨tA, tB, tC⟩ := bookTiesAtFinish_parts hT
  -- the sender's rows
  unfold K2.switchRowsAt at hDt
  obtain ⟨Wl, hWl, eD⟩ := exMap_ok hDt
  simp only [K2.coreSender] at hTs
  obtain ⟨VS, hVS, eT⟩ := exMap_ok hTs
  have h2 : (K2.switchSent pl.sizes pl.others).size = 2 := F'.two
  obtain ⟨s₀, hs₀, hr₀⟩ := rowsAll_at hVS 0 (by omega)
  obtain ⟨s₁, hs₁, hr₁⟩ := rowsAll_at hVS 1 (by omega)
  have hf0 : K2.foldAt (K2.switchFresh pl.sizes pl.others pl.foldVars) 0 = none := by
    simp [K2.foldAt, K2.switchFresh, h2]
  have hf1 : K2.foldAt (K2.switchFresh pl.sizes pl.others pl.foldVars) 1 = some pl.foldVars := by
    simp [K2.foldAt, K2.switchFresh, h2]
  have hsh1 : ((K2.switchSent pl.sizes pl.others).getD 1 default).shape = freshShapeL pl := by
    show _ = (((K2.switchSent pl.sizes pl.others).getD
      ((K2.switchSent pl.sizes pl.others).size - 1) default).shape)
    rw [h2]
  rw [hf0] at hs₀ hr₀
  rw [hf1, hsh1] at hs₁ hr₁
  have hd0 : K2.dueBefore pl.sizes.codes (K2.switchSent pl.sizes pl.others)
      (K2.switchFresh pl.sizes pl.others pl.foldVars) 0 = ⟨0, 0⟩ := by
    simp [K2.dueBefore]
  rw [hd0] at hs₀
  have hJm : (JL q door D readers closing pl : TestJob (Local W₀ Rc Xi Tr) Y).members.length =
      pl.front.length + 1 := by
    simp [jobL, membersL]
  obtain ⟨e₀, he₀, ho₀, hst₀, hc₀⟩ := tB
  obtain ⟨e₁', he₁, ho₁, hst₁, hc₁⟩ := tC
  have A0 := lent_is_cut hcar₁ _ e₀ he₀ _ _ _ ho₀ hst₀ hc₀ c₂.1 hown s₀ hs₀
  have A1 := lent_is_cut hcar₁ _ e₁' he₁ _ _ _ ho₁ hst₁ hc₁ c₂.1 hown s₁ hs₁
  have hmem : ∀ n < pl.front.length, stretches _ c₁.2.2 n = stretches pl.carries c₂.2.2 n := by
    intro n hn
    obtain ⟨e, e', a1, a2, a3⟩ := tA n hn
    exact stretches_same hcar₁ hcar₂ n e e' a1 a2 a3
  have hWl' : closing pl (D mᵢ.st.input.x) (readers mᵢ.st.input) mᵢ.st.heard
      (K2.Stretch.carried pl.carries c₂.2.2) = .ok Wl :=
    (congrArg (fun l => closing pl (D mᵢ.st.input.x) (readers mᵢ.st.input) l
      (K2.Stretch.carried pl.carries c₂.2.2)) (by simp; rfl)).trans hWl
  subst eD
  have hcarry : carryRows D readers closing pl m.st.input
      (heardL (restFront (JL q door D readers closing pl) m)) (stretches _ c₁.2.2) =
      .ok (VS 0) := by
    have hbeg : Begins (membersL pl) (restPart (JL q door D readers closing pl) :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).carries :=
      begins_runs (JL q door D readers closing pl) _ _
    have hfun : (fun n => if n < pl.front.length then K2.Stretch.carried _ c₁.2.2 n
        else (Except.error "a stretch is asked beyond the list" : Except String K2.Stretch)) =
        K2.Stretch.carried pl.carries c₂.2.2 := by
      funext n
      by_cases hn : n < pl.front.length
      · have hx : pl.carries[n]? = some (carriedName pl.front[n].1 pl.front[n].2.1 ⟨pl.place, 0⟩,
            pl.front[n].2.2) := by
          simp [K2.SwitchPlace.carries, hn]
        obtain ⟨s', hs'⟩ := hbeg n pl.front[n] (by simp [membersL, List.getElem?_append_left hn])
        rw [if_pos hn, carried_asK2 pl.carries _ n _ hx, carried_asK2 _ _ n _ hs', hmem n hn]
      · rw [if_neg hn]
        exact (carried_beyond pl.carries _ n
          (by simp [K2.SwitchPlace.carries]; omega)).1.symm
    obtain ⟨s'', hs''⟩ := hbeg pl.front.length
      (⟨pl.place, 0⟩, 0, K2.messageDue pl.sizes.codes (shapeL pl) none) (by simp [membersL])
    rw [carryRows_by_carried D readers closing pl _ _ _ hbeg c₁.2.2]
    unfold carryBy
    rw [hfun, ← hinp, hheardL, hWl', carried_asK2 _ _ _ _ hs'']
    show K2.messageRows K2.freshTable pl.sizes.codes (shapeL pl) none _
      (asK2 _ (stretches _ c₁.2.2 pl.front.length)) = .ok (VS 0)
    rw [← A0.1]
    exact hr₀
  exact ⟨VS 0, hcarry⟩

end Main

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.carry_returns_first
