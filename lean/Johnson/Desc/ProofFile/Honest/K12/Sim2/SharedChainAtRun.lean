-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the seat and the five clauses at a proximity test of the shared chain, at every description.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/SharedChainAtRun.lean: what a test of the shared chain gets at a run,
at every description whose block at the test's place has the test's rounds. No E2E file beneath it.

  draws_fit_shared_chain, five_at_test₂   a stretch of the challenges; the seat and the five clauses
  pre_of_cut, both_of_cut   of a list with all keys different, what stands around an element is one

Limits. Conditional on ready and runC and the part's being called; of the walk. Nothing on completeness,
soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.Clauses
import Johnson.Desc.ProofFile.Honest.K12.FiveAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtPlace
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudOwnAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.ShowsFirst
import Johnson.Desc.ProofFile.Honest.K12.FormPubAt
import Johnson.Desc.ProofFile.Honest.K12.TreeInFront
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12
import Johnson.Desc.ProofFile.Honest.K12.HalfSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block FileDescription Oracle Place)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts T12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light

/-- A stretch of the shared chain's challenges that passes Draws.due has the declared form. -/
theorem draws_fit_shared_chain {Xi : Type} {F : FileDescription Xi} {ρ : Draws} (hρ : ρ.due F = true)
    (pre t : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl)
    (hcut : F.shared.blocksInOrder = pre ++ b :: t) (n : ℕ) (hn : n ≤ b.rounds.length) :
    drawsFit (b.rounds.take n) ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take n) = true := by
  unfold Draws.due at hρ
  simp only [Bool.and_eq_true] at hρ
  have h2 : drawsFit (F.shared.blocksInOrder.flatMap (·.rounds)) ρ.shared = true := hρ.1.1.2
  rw [hcut, List.flatMap_append, List.flatMap_cons] at h2
  have h3 := (drawsFit_cut (pre.flatMap (·.rounds)).length _ _ h2).2
  rw [List.drop_left] at h3
  have h4 := (drawsFit_cut b.rounds.length _ _ h3).1
  rw [List.take_left] at h4
  have h5 := (drawsFit_cut n _ _ h4).1
  rw [List.take_take, Nat.min_eq_left hn] at h5
  exact h5

/-- **The seat at a proximity test of the shared chain**, and the five clauses there. -/
theorem five_at_test₂ {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hρ : ρ.due F = true) (hR : ready F Bk P w₀ rc x k = .ok R)
    (J : TestJob (Common W₀ Rc Ky) X₀) {ds : List Fmt.Drawn} (Fc : PlaceFacts J.p ds)
    (f : Addr × ℕ) (hfr : J.fresh = some f)
    (hrows : ∀ (s : Fmt.M1.Stage) (w : Common W₀ Rc Ky) (fr : Front X₀) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) →
      Johnson.Prover.Link.μOf (H2K.Pub.sgOf s) (J.rows₀ w fr mem) =
        Johnson.Prover.Link.μOf (H2K.Pub.sgOf s) (J.rows₀ w fr mem'))
    (Js : SimJob Ky) (hs : Js.p = J.p) (ho : Js.own = false) (fs : List (Fall F.S₂))
    (σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hσ : testSide F.shared.blocksInOrder J Js fs = some σ)
    (b : Block F.S₂ F.Cl) (hf : (F.shared.blocksInOrder.find? fun b => b.place == J.p.place) = some b)
    (hbp : b.place = J.p.place)
    (hr : b.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds)
    (hor : b.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hT : tiesB Bk J.p.place J.members.length = true)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r) (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hpos : restLen J.p.nums.stages ≠ 0) (st : List (ℕ × ℕ × List UInt64)) :
    ∃ (pre t : List (Block F.S₂ F.Cl))
      (c : RowCoins [(firstPart J : Part Empty (Common W₀ Rc Ky) X₀), restPart J])
      (m : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀),
      StandsAt F.shared.blocksInOrder R.shared σ (restMember J Js) pre t (firstLen J.p.nums.stages) ∧
      midSharedAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      carriedAt Bk k 1 ⟨σ.block.place, 1⟩ (restMember (V := Empty) J Js).part = .ok c.2.1.2.2 ∧
      m.st.input = ⟨w₀, rc, P.key x⟩ ∧
      FiveAt J (stretches _ c.2.1.2.2) m (r.run.beforeAt st ⟨σ.block.place, 1⟩) := by
  have hfrN : J.fresh.isNone = false := by rw [hfr]; rfl
  obtain ⟨-, -, hall⟩ := any_at_place (V := Empty) J Js Fc _ b hf hbp hr hor hfrN hs ho
  obtain ⟨f1, f2, -, -, -⟩ := hall fs σ hσ
  have hσ' := hσ
  unfold testSide Side.seated at hσ'
  obtain ⟨b', hb', e⟩ := Option.map_eq_some_iff.1 hσ'
  have hbb : b' = b := Option.some.inj (hb'.symm.trans hf)
  subst hbb
  have hblk : σ.block ∈ F.shared.blocksInOrder := by
    rw [← e]
    exact List.mem_of_find?_eq_some hb'
  have hrow : σ.row = testPairs J Js := by rw [← e]
  have eb : σ.block = b' := by rw [← e]
  have hmem : restMember J Js ∈ σ.members := by
    have f2' : σ.members = [firstMember J Js, restMember J Js] := f2
    rw [f2']
    simp
  obtain ⟨s, next, rest, hst⟩ : ∃ s next rest, J.p.nums.stages = s :: next :: rest := by
    have hform := Fc.form
    unfold formPubB at hform
    cases hs' : J.p.nums.stages with
    | nil => rw [hs'] at hform; cases hform
    | cons a l =>
      cases l with
      | nil => rw [hs'] at hform; cases hform
      | cons b' r' => exact ⟨a, b', r', rfl⟩
  have FP := formPub_of_B J.p s next rest hst Fc.form
  have hk : s.k = (H2K.Pub.sgOf s).h + (H2K.Pub.sgOf s).g := by
    have := FP.hk
    show s.k = s.h + (s.k - s.h)
    omega
  have l2 : (restPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length =
      restLen J.p.nums.stages := by
    rw [rest_moves J s next rest hst]
    exact (List.length_map _).trans List.length_range
  have hpos' : (restPart J : Part Empty (Common W₀ Rc Ky) X₀).moves.length ≠ 0 := by
    rw [l2]
    exact hpos
  obtain ⟨pre, t, S⟩ := stands_rest hpl hR J Js σ hblk hrow f1 hmem hpos' (proverSideOfProximityTest J) hg rfl
  have hzip : σ.block.rounds.zip σ.block.oracles = J.laid := by
    rw [eb, hr, hor]
    show _ = H2K.JointK.laidOf J.p
    exact zip_laid _ Fc.plan
  have hsh : σ.block.shaped = true := planOk_shaped hpl σ.block hblk
  have hol := shaped_len σ.block hsh
  have hlenb : σ.block.rounds.length = (H2K.JointK.laidOf J.p).length := by
    show _ = J.laid.length
    rw [← hzip, List.length_zip, hol, Nat.min_self]
  have hcut : F.shared.blocksInOrder = pre ++ σ.block :: t := S.cut
  have g0 := draws_fit_shared_chain (F := F) hρ pre t σ.block hcut (firstLen J.p.nums.stages)
    (by rw [hlenb]; exact Fc.enough)
  have e1 : ((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1) =
      σ.block.rounds.take (firstLen J.p.nums.stages) := by
    have hz : H2K.JointK.laidOf J.p = σ.block.rounds.zip σ.block.oracles := hzip.symm
    rw [List.map_take, hz, List.map_fst_zip (by rw [hol])]
  have hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true := by
    rw [e1]
    exact g0
  have hlen : ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take
      (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    have hh := ProofFile.Honest.drawsFit_length _ _ hfit
    rw [hh, List.length_map, List.length_take]
    exact Nat.min_eq_left Fc.enough
  have T : FirstTies J s next rest (byNo ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take
      (firstLen J.p.nums.stages)))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) :=
    ⟨hst, Fc.enough, FP.sorts, by rw [tablesFitB_eq, hfrN]; exact Fc.tab, hlen,
      fun n hn => (List.getD_eq_getElem _ _ hn).symm⟩
  obtain ⟨c, m, hm, hca, hin, le, leS, hF, hH, hFold⟩ := five_at_run (F := F) hpl J f
    hfr Js hR σ pre t S hg hzip hT s next rest _ T hk
    (fun w fr mem mem' hh => hrows s w fr mem mem' hh) hfit hrun hc st
  exact ⟨pre, t, c, m, S, hm, hca, hin, ⟨le, leS, hF, hH, hFold⟩⟩

/-- Of a list with all keys different, what stands in front of an element is one list. -/
theorem pre_of_cut {α β : Type} (f : α → β) (l pre t pre' t' : List α) (b : α)
    (h1 : l = pre ++ b :: t) (h2 : l = pre' ++ b :: t') (hn : (l.map f).Nodup) : pre = pre' := by
  subst h1
  exact (cut_unique f _ _ _ _ _ h2 hn).1

/-- The same of what stands on both sides. -/
theorem both_of_cut {α β : Type} (f : α → β) (l pre t pre' t' : List α) (b : α)
    (h1 : l = pre ++ b :: t) (h2 : l = pre' ++ b :: t') (hn : (l.map f).Nodup) :
    pre = pre' ∧ t = t' := by
  subst h1
  exact cut_unique f _ _ _ _ _ h2 hn


end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.draws_fit_shared_chain
#print axioms ProofFile.Honest.K12.Sim2.five_at_test₂
#print axioms ProofFile.Honest.K12.Sim2.pre_of_cut
#print axioms ProofFile.Honest.K12.Sim2.both_of_cut
