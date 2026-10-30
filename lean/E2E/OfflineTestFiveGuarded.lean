-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineTestFiveGuarded.lean: E2E/OfflineTestFive.lean's theorem at the shared chain, at a proximity test whose first fold
sends its own fresh table and whose two parts stand behind the guard (`Part.needsField`,
Johnson/Desc/ProofFile/Honest/K12/FieldGuard.lean): the five clauses le, leS, heardFit, heard, fold AT A RUN's OWN VALUES, in
the form in which `owedAt_shared_at` (E2E/OfflineOwedChains.lean) asks On: at EVERY carried block that the book gives the
part and every state that the frame returns at the part's address, at the run's own front. General in the
description, the book, the prover, the lists and the job.

  `five_at_shared_guarded_row`  the theorem: by `five_own_at_run` (…/K12/SimO/FiveOwn.lean)

The five are `FiveAtEntry` (E2E/OfflineTestFive.lean) unchanged: the condition at a test with its own table has these five
clauses in the same text. The book's premise is the test `tiesOB` (…/K12/Own/AgreeOwn.lean): the second part's carried
entry behind the members' is the first part's own coins from their start, and the two parts carry the members alike.

It pays none of door, trees, asks. At a state on entry that is the job's own letter rec₀, not shown to be the
verifier's. That a run returns, or calls the part, is not shown here. Nothing on any property.
-/
import E2E.OfflineTestFive
import E2E.OfflineOwedChains
import Johnson.Desc.ProofFile.Honest.K12.Own.AgreeOwn
import Johnson.Desc.ProofFile.Honest.K12.SimO.FiveOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc (Block FileDescription Place)
open Johnson.Prover.Link (μOf rowOf asked bodyItems)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {k : Coins Bk} {ρ : Draws} {r : RunC F}

/-- **The five clauses at a run's own values, at the second part of a proximity test of the shared chain whose
first fold sends its own table, behind the guard.** Js: any simulators' job: nothing is read of it. -/
theorem five_at_shared_guarded_row (plan : F.planOk = true) (book : Bk.word F = none)
    (due : ρ.due F = true) (h : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky} (hL : L ∈ G.shared)
    {σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    (hσ : L.side F.shared.blocksInOrder = some σ) (J : TestJob (Common W₀ Rc Ky) X₀) (Js : SimJob Ky)
    (hfr : J.fresh = none) (hpl : L.place = J.p.place)
    (hparts : L.row.map (·.1) = [(firstPart J).needsField, (restPart J).needsField])
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hT : Own.tiesOB Bk J.p.place J.members.length = true) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (P : TestPublic J s next rest) (st : List (ℕ × ℕ × List UInt64)) :
    ∀ u ∈ σ.members, u.number = 1 → r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      FiveAtEntry J (stretches _ ca) m (r.run.beforeAt st ⟨L.place, u.number⟩) := by
  intro u hu hn hc ca m hca hm
  obtain ⟨R, -, -, -, -, -, -, hR, -⟩ := runC_parts h
  have hbp : σ.block.place = L.place := side_place hσ
  have hrowσ : σ.row = L.row := OnBytes.SendSim.Seat.row_of_seated hσ
  obtain ⟨s0, s1, hrow⟩ := two_of_map hparts
  obtain ⟨⟨hsum, hor⟩, hst⟩ := shared_stands plan book hR L hL σ hσ
  have e0 : (firstPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField.moves.length =
      firstLen J.p.nums.stages := (needsField_length _).trans (Light.first_moves_len J)
  have e1 : (restPart J : Part Empty (Common W₀ Rc Ky) X₀).needsField.moves.length =
      restLen J.p.nums.stages := by
    rw [needsField_length, rest_moves J s next rest P.stages]
    exact (List.length_map _).trans List.length_range
  have hlen : J.laid.length = firstLen J.p.nums.stages + restLen J.p.nums.stages := by
    rw [← hlaid, List.length_zip, hor, Nat.min_self, ← hsum, hrowσ, hrow]
    simp [e0, e1]
  have ht : (J.laid.drop (firstLen J.p.nums.stages)).take (restLen J.p.nums.stages) =
      J.laid.drop (firstLen J.p.nums.stages) :=
    List.take_of_length_le (by rw [List.length_drop]; omega)
  have hmem : σ.members = [⟨0, J.laid.take (firstLen J.p.nums.stages), (firstPart J).needsField, s0⟩,
      ⟨1, J.laid.drop (firstLen J.p.nums.stages), (restPart J).needsField, s1⟩] := by
    unfold Side.members
    rw [hrowσ, hrow, hlaid]
    show [_, _] = _
    simp only [e0, e1, ht, Nat.zero_add]
  rw [hmem] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact absurd (show (0 : ℕ) = 1 from hn) (by decide)
  obtain ⟨⟨pre, t, A⟩, -⟩ := hst ⟨1, J.laid.drop (firstLen J.p.nums.stages), (restPart J).needsField, s1⟩
    (by rw [hmem]; exact List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))
  have hto : σ.roundsTo 1 = firstLen J.p.nums.stages := by
    unfold Side.roundsTo
    rw [hrowσ, hrow]
    simp [e0]
  have A' : StandsAt F.shared.blocksInOrder R.shared σ
      ⟨1, J.laid.drop (firstLen J.p.nums.stages), (restPart J).needsField, s1⟩ pre t
      (firstLen J.p.nums.stages) := StandsAt.of_same rfl rfl hto A
  obtain ⟨hte, -⟩ := ready_ok hR
  obtain ⟨-, t1, -⟩ := tests_twice hte
  have hgm : (proverSideOfProximityTest J : Placed Empty (Common W₀ Rc Ky) X₀).needsField ∈ (G.prover H).shared :=
    List.mem_map.2 ⟨L, hL, by rw [hpl, hparts]; rfl⟩
  have hg : ((G.prover H).shared.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest J : Placed Empty (Common W₀ Rc Ky) X₀).needsField := by
    rw [hbp, hpl]
    exact find_of_nodup (nodup_of_twice t1) hgm
  have hd1 : drawsFit F.roundsDeclaredByBlocks.2.1 ρ.shared = true := by
    unfold Draws.due at due
    simp only [Bool.and_eq_true] at due
    exact due.1.1.2
  have hdecl : F.roundsDeclaredByBlocks.2.1 =
      pre.flatMap (·.rounds) ++ (σ.block.rounds ++ t.flatMap (·.rounds)) := by
    show F.shared.blocksInOrder.flatMap (·.rounds) = _
    rw [A.cut, List.flatMap_append, List.flatMap_cons]
  have hfst : J.laid.map (·.1) = σ.block.rounds := by
    rw [← hlaid]
    exact List.map_fst_zip (le_of_eq hor.symm)
  have hle : firstLen J.p.nums.stages ≤ σ.block.rounds.length := by
    rw [← hfst, List.length_map, hlen]
    omega
  have hfit : drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true := by
    have h2 := (drawsFit_cut (pre.flatMap (·.rounds)).length _ _ hd1).2
    rw [hdecl, List.drop_left] at h2
    have h3 := (drawsFit_cut (firstLen J.p.nums.stages) _ _ h2).1
    rw [List.take_append_of_le_length hle] at h3
    rw [List.map_take]
    show drawsFit ((J.laid.map (·.1)).take _) _ = true
    rw [hfst]
    exact h3
  have hdl := ProofFile.Honest.drawsFit_length _ _ hfit
  have T : FirstTies J s next rest
      (fun i => ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take
        (firstLen J.p.nums.stages)).getD i noDraw)
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) :=
    ⟨P.stages, P.enough, P.sorts, P.tables, by
      rw [hdl, List.length_map, List.length_take]
      exact Nat.min_eq_left P.enough, fun n hn' => (List.getD_eq_getElem _ _ hn').symm⟩
  -- the book's test, clause by clause
  unfold Own.tiesOB at hT
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hT
  obtain ⟨⟨t2, t3⟩, t4⟩ := hT
  obtain ⟨e₂, he₂, k2⟩ := Option.map_eq_some_iff.1 t2
  have hmems : ∀ i, i < J.members.length → ∃ a a', (carryE Bk ⟨J.p.place, 0⟩)[i]? = some a ∧
      (carryE Bk ⟨J.p.place, 0 + 1⟩)[i]? = some a' ∧ a.owner = a'.owner ∧ a.start = a'.start ∧
      a.count = a'.count := by
    intro i hi
    have e := congrArg (·[i]?) t4
    simp only [List.getElem?_map, List.getElem?_take, if_pos hi] at e
    obtain ⟨a, ha⟩ : ∃ a, (carryE Bk ⟨J.p.place, 0⟩)[i]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [ha, Option.map_some] at e
    obtain ⟨a', ha', k3⟩ := Option.map_eq_some_iff.1 e.symm
    exact ⟨a, a', ha, ha', (congrArg (·.1) k3).symm, (congrArg (·.2.1) k3).symm,
      (congrArg (·.2.2) k3).symm⟩
  obtain ⟨c, m', hm', hca', -, a1, a2, a3, a4, a5⟩ := Light.five_own_at_run plan J hfr Js hR σ
    ⟨1, J.laid.drop (firstLen J.p.nums.stages), (restPart J).needsField, s1⟩ rfl pre t A' hg hlaid e₂ he₂
    (congrArg (·.1) k2) (congrArg (·.2) k2) hmems s next rest _ T P.split P.rows hfit h
    (by rw [hbp]; exact hc) st
  rw [hbp] at hm' hca' a4 a5
  have em : m' = m := by
    have e : orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩) = .ok m' := by
      rw [show midSharedAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩ = .ok (some m') from hm']
      rfl
    exact Except.ok.inj (e.symm.trans hm)
  have ec : c.2.1.2.2 = ca := Except.ok.inj (hca'.symm.trans hca)
  subst em
  subst ec
  exact ⟨a1, a2, a3, a4, a5⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.five_at_shared_guarded_row
