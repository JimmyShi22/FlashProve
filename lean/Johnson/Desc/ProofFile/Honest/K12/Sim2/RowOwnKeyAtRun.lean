-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the offline row of the key file's own test, at a run.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowOwnKeyAtRun.lean: OnAtRun₃ (Law/OwedAtRun.lean) at the list of
the key file's own test, behind the guard, at the job that proverSideOfGuardedSending lays at the identity reader.

  five_at_test₃, door_at_last_any   the seat, the five clauses and the door, at every description
  k1_tree_plain      what the front of a part of the last chain lists of a plain K1 sending's tree
  trees_at_plain_own_test, tie_plain_index, tie_plain_riding, trees_at_plain_job   the clause trees,
                     as trees_at_own_test and trees_at_job_own_test at senders that K1.proverSideOfSending lays
  carriedAt_guarded  the carried blocks do not see the guard
  jobOwnKey, LeftAtOwnKey, onAtRun_own_key   the job; what is left at a stand; the statement

Paid at every stand: that the field holds columns, at both parts; the door (no patch); FiveAt. Left:
hTrees (trees_at_plain_job states what gives it), hleft (the asks); on the filling hg; on the book hT.
trees_at_plain_job's hdata asks that W's data reads of a front only the challenges in front of W's
sender: not shown here at the key's job.

Limits. The rule moves the debt and pays none of it. The condition reads the input and the carried
values: no later law may take it as a hypothesis on a run and then speak of the random values as sampled
anew. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowOwnKey
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowRangesAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesOwnTestRun
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesOwnTestJob
import Johnson.Desc.ProofFile.Honest.K12.Sim2.OwnTestEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain OpenedColumn FileDescription foldBlocks Oracle Place)
open Johnson.Prover.Link (μOf rowOf)
open H2K.Pub (sgOf)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light

/-- **The seat at a guarded proximity test of the last chain**, and the five clauses there: at every
description whose block at the test's place has the test's rounds. -/
theorem five_at_test₃ {Xi W₀ Rc Ky Tr X₀ Y Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hρ : ρ.due F = true) (hR : ready F Bk P w₀ rc x k = .ok R)
    (J : TestJob (Local W₀ Rc Xi Tr) Y) {ds : List Fmt.Drawn} (Fc : PlaceFacts J.p ds)
    (f : Addr × ℕ) (hfr : J.fresh = some f)
    (hrows : ∀ (s : Fmt.M1.Stage) (w : Local W₀ Rc Xi Tr) (fr : Front Y) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf s) (J.rows₀ w fr mem) = μOf (sgOf s) (J.rows₀ w fr mem'))
    (Js : SimJob Pb) (hs : Js.p = J.p) (ho : Js.own = false) (fs : List (Fall F.S₃))
    (σ : Side F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Pb)
    (hσ : Side.seated F.second.blocksInOrder J.p.place (guardRow (testPairs J Js)) fs = some σ)
    (b' : Block F.S₃ F.Cl) (hf : (F.second.blocksInOrder.find? fun b => b.place == J.p.place) = some b')
    (hpl' : b'.place = J.p.place)
    (hr : b'.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds)
    (hor : b'.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles)
    (hg : (P.second.find? fun g => g.place == σ.block.place) =
      some ((proverSideOfProximityTest J : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).needsField))
    (hT : tiesB Bk J.p.place J.members.length = true)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r) (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hrest : restLen J.p.nums.stages ≠ 0) (st : List (ℕ × ℕ × List UInt64)) :
    ∃ (pre t : List (Block F.S₃ F.Cl))
      (c : RowCoins [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y), restPart J])
      (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y),
      StandsAt F.second.blocksInOrder R.second σ (restMember J Js).guarded pre t (firstLen J.p.nums.stages) ∧
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      carriedAt Bk k 2 ⟨σ.block.place, 1⟩
        (restMember (V := Local W₀ Rc Xi Tr) J Js).part = .ok c.2.1.2.2 ∧
      m.st.input = R.own ∧
      FiveAt J (stretches _ c.2.1.2.2) m (r.run.beforeAt st ⟨σ.block.place, 1⟩) := by
  have hfrN : J.fresh.isNone = false := by rw [hfr]; rfl
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 hσ
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hf)
  have hbare : testSide (V := Local W₀ Rc Xi Tr) F.second.blocksInOrder J Js fs =
      some (⟨b, testPairs J Js, fallOf fs J.p.place⟩ :
        Side F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Pb) := by
    unfold testSide Side.seated
    show Option.map _ (F.second.blocksInOrder.find? fun b => b.place == J.p.place) = _
    rw [hb]
    rfl
  obtain ⟨-, -, hall⟩ := any_at_place (V := Local W₀ Rc Xi Tr) J Js Fc _ b hf hpl' hr hor hfrN hs ho
  obtain ⟨hfit, hmem, -⟩ := hall fs _ hbare
  have hrow : σ.row = guardRow (testPairs J Js) := by rw [← e]
  have hblk : σ.block ∈ F.second.blocksInOrder := by
    rw [← e]
    exact List.mem_of_find?_eq_some hb
  have hfitg : σ.fits = true := by
    rw [← e]
    show (⟨b, guardRow _, _⟩ : Side F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Pb).fits = true
    rw [fits_guarded_row]
    exact hfit
  have hmemg : (restMember J Js).guarded ∈ σ.members := by
    have e2 : σ.members = [(firstMember J Js).guarded, (restMember J Js).guarded] := by
      rw [← e]
      show membersOf (guardRow _) 0 _ = _
      rw [membersOf_guardRow]
      exact congrArg (List.map Member.guarded) hmem
    rw [e2]
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
  have hk : s.k = (sgOf s).h + (sgOf s).g := by
    have := FP.hk
    show s.k = s.h + (s.k - s.h)
    omega
  have l2 : (restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length =
      restLen J.p.nums.stages := by
    rw [rest_moves J s next rest hst]
    exact (List.length_map _).trans List.length_range
  have hpos : (restMember (V := Local W₀ Rc Xi Tr) J Js).guarded.part.moves.length ≠ 0 := by
    show (restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).needsField.moves.length ≠ 0
    rw [needsField_length, l2]
    exact hrest
  obtain ⟨pre, t, S'⟩ := stands_member_last hpl hR σ hblk hfitg
    (restMember J Js).guarded hmemg hpos (proverSideOfProximityTest J).needsField hg (by rw [hrow]; rfl)
  have eN : ((σ.row.take (restMember (V := Local W₀ Rc Xi Tr) J Js).guarded.number).map
      (·.1.moves.length)).sum = firstLen J.p.nums.stages := by
    rw [hrow]
    show (firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).needsField.moves.length + 0 = _
    rw [Nat.add_zero, needsField_length, ProofFile.Honest.K12.Light.first_moves_len]
  rw [eN] at S'
  have eb : σ.block = b := by rw [← e]
  have hzip : σ.block.rounds.zip σ.block.oracles = J.laid := by
    rw [eb, hr, hor]
    show _ = H2K.JointK.laidOf J.p
    exact zip_laid _ Fc.plan
  have hsh : σ.block.shaped = true := planOk_shaped_second hpl σ.block hblk
  have hol := shaped_len σ.block hsh
  have hlenb : σ.block.rounds.length = (H2K.JointK.laidOf J.p).length := by
    show _ = J.laid.length
    rw [← hzip, List.length_zip, hol, Nat.min_self]
  have hcut : F.second.blocksInOrder = pre ++ σ.block :: t := S'.cut
  have g0 := draws_fit_last_chain hρ pre t σ.block hcut (firstLen J.p.nums.stages)
    (by rw [hlenb]; exact Fc.enough)
  have e1 : ((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1) =
      σ.block.rounds.take (firstLen J.p.nums.stages) := by
    have hz : H2K.JointK.laidOf J.p = σ.block.rounds.zip σ.block.oracles := hzip.symm
    rw [List.map_take, hz, List.map_fst_zip (by rw [hol])]
  have hfitd : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.second.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true := by
    rw [e1]
    exact g0
  have hlen : ((ρ.second.drop (pre.flatMap (·.rounds)).length).take
      (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    have hh := ProofFile.Honest.drawsFit_length _ _ hfitd
    rw [hh, List.length_map, List.length_take]
    exact Nat.min_eq_left Fc.enough
  have T : FirstTies J s next rest (byNo ((ρ.second.drop (pre.flatMap (·.rounds)).length).take
      (firstLen J.p.nums.stages)))
      ((ρ.second.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) :=
    ⟨hst, Fc.enough, FP.sorts, by rw [tablesFitB_eq, hfrN]; exact Fc.tab, hlen,
      fun n hn => (List.getD_eq_getElem _ _ hn).symm⟩
  obtain ⟨c, m, hm, hca, hin, le, leS, hF, hH, hFold⟩ := five_at_second_guarded (F := F)
    hpl J f hfr Js hR σ pre t S' hg hzip hT s next rest _ T hk
    (fun w fr mem mem' hh => hrows s w fr mem mem' hh) hfitd hrun hc st
  exact ⟨pre, t, c, m, S', hm, hca, hin, ⟨le, leS, hF, hH, hFold⟩⟩

/-- **The door at a test of the last chain**: door_at_own_test at every description, at the state of
stateFromViewOnLastChain. -/
theorem door_at_last_any {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F}
    (hpl : F.planOk = true) (hR : ready F Bk P w₀ rc x k = .ok R)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r) (enter : F.S₃ → Except String T12) (pla : Place)
    (J : TestJob (Local W₀ Rc Xi Tr) Y)
    (hJ : J.rec₀ = doorW F (·.x) enter pla idleT12)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre t : List (Block F.S₃ F.Cl))
    (S : StandsAt F.second.blocksInOrder R.second σ u pre t (firstLen J.p.nums.stages))
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (ha : σ.block.place = pla) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (cs : List OpenedColumn),
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m) ∧
      m.opened = some cs ∧ m.st.input.x = x ∧
      J.rec₀ m.st.input (restFront J m) = stateFromViewOnLastChain F
        (F.second.blocksInOrder.takeWhile (·.place != pla)) enter idleT12 x
        ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
          ⟨σ.block.place, u.number⟩).cut (firstLen J.p.nums.stages)) := by
  obtain ⟨m, e₁, e₂, v₀, s, cols, tr, hm, hin, hlen, hop, he₁, he₂, hst, hfold, hfill, hd⟩ :=
    door_last_with_columns hpl hR σ u pre t _ S hrun hc
  obtain ⟨e₁', e₂', v₀', s', cols', he₁', he₂', hst', hfold', hfill', hval⟩ :=
    state_on_last_chain_with_columns hpl hR hrun σ u pre t _ S hc enter idleT12
  obtain rfl : e₁' = e₁ := Option.some.inj (he₁'.symm.trans he₁)
  obtain rfl : e₂' = e₂ := Option.some.inj (he₂'.symm.trans he₂)
  obtain rfl : v₀' = v₀ := Except.ok.inj (hst'.symm.trans hst)
  obtain rfl : cols' = cols := Except.ok.inj (hfill'.symm.trans hfill)
  have hs : s' = s := (Prod.mk.inj (Except.ok.inj (hfold'.symm.trans hfold))).1
  subst hs
  have hn := (places_nodup ((F.planOk_ok).1 hpl).places).2.2
  have hcut : F.second.blocksInOrder = pre ++ σ.block :: t := S.cut
  have hn' : ((pre ++ σ.block :: t).map (·.place)).Nodup := hcut ▸ hn
  have hpre : F.second.blocksInOrder.takeWhile (·.place != pla) = pre := by
    rw [← ha, hcut]
    exact Blind.takeWhile_cut pre t σ.block (Blind.apart_of_nodup hn')
  have hx : (fun w : Local W₀ Rc Xi Tr => w.x) m.st.input = x := by rw [hin]
  refine ⟨m, _, hm, hop, hx, ?_⟩
  have hk : (F.first.blocksInOrder.flatMap (·.rounds)).length + (F.shared.blocksInOrder.flatMap (·.rounds)).length +
      (pre.flatMap (·.rounds)).length ≤ m.seen.length - firstLen J.p.nums.stages := by
    omega
  have hdoor := hd (fun w : Local W₀ Rc Xi Tr => w.x) m.st.input enter (restFront J m)
    (m.seen.length - firstLen J.p.nums.stages) hx hk rfl rfl
  rw [hpre, hval, hJ]
  unfold doorW doorLast
  rw [hpre, hdoor]

/-! ## The first chain's plain senders, at a part of the last chain -/

section Plain
open Johnson.Prover.Send (col)

/-- **What the front of a called part of the last chain lists of a tree that a plain sending of the
first chain sent**: columns of the sending's written column. -/
theorem k1_tree_plain {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre' t' : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (pre : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl) (t : List (Block F.S₁ F.Cl))
    (hcut : F.first.blocksInOrder = pre ++ b :: t) (hb : b.rounds ≠ [])
    (J : K1.SendJob (Local W₀ Rc Xi Tr) Y)
    (hg : (P.first.find? fun g => g.place == b.place) =
      some (K1.proverSideOfSending (V := Local W₀ Rc Xi Tr) J))
    (τ j : ℕ) (sh : OnBytes.TreeShape) (hτ : J.P.trees[τ]? = some sh)
    (hW : columnWidth J.P τ = sh.mainWidth + sh.maskWidth)
    (hj : treesTo F.first.blocksInOrder pre.length + τ = j) (st : List (ℕ × ℕ × List UInt64)) :
    ∃ (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
      (c : (K1.sendPart (V := Local W₀ Rc Xi Tr) J :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).Coins) (cols : List (ℕ × List UInt64)),
      lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨b.place, 0⟩ (K1.sendPart (V := Local W₀ Rc Xi Tr) J) = .ok c ∧
      mᵢ.st.input = R.own ∧ mᵢ.st.heard = ρ.first.take (pre.flatMap (·.rounds)).length ∧
      (r.run.beforeAt st ⟨σ.block.place, u.number⟩).treeCols 0 j = some cols ∧
      ∀ q ∈ cols, q.2 = col J.P (J.rows c.1 mᵢ.shown mᵢ.st 0) τ q.1 := by
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨lS, -, -⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  obtain ⟨m₁, m₂, m, a₁, z₁, a₂, z₂, a₃, y, ha₁, hz₁, hl₁, hm₁, -⟩ :=
    played_at_second hpl hR hrun σ u pre' t' i _ S rfl hc
  obtain ⟨-, -, -, -, -, -, hbf, -⟩ := frame_at_second hpl hR hrun σ u pre' t' i _ S rfl hc st
  have hlen : R.first.length = (F.first.blocksInOrder.flatMap (·.rounds)).length := by
    rw [chainSteps_length _ _ s1, List.length_flatMap]
  have hlt : (pre.flatMap (·.rounds)).length < R.first.length := by
    rw [hlen, hcut, List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
    have : 0 < b.rounds.length := List.length_pos_iff.2 hb
    omega
  have hρ : ρ.first.take R.first.length = ρ.first := by
    rw [← lS.1]
    exact List.take_length
  have hw : walk ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩ (R.first.take R.first.length)
      (ρ.first.take R.first.length) a₁ = .ok z₁ := by
    rw [List.take_length, hρ]
    exact hz₁
  obtain ⟨zᵢ, mᵢ, c, q, z, hwi, hmi, hlend, hq, hqT, hsay⟩ := first_round_at_first hR pre b t hcut hb
    (K1.proverSideOfSending (V := Local W₀ Rc Xi Tr) J).place (K1.sendPart (V := Local W₀ Rc Xi Tr) J) _ rfl hg _
    hlt _ a₁ z₁ (start_laid ha₁) (Nat.le_refl _) hw (by rw [hm₁]; rfl)
  have hz : z = ⟨[], K1.treeTables J.P (J.rows c.1 mᵢ.shown mᵢ.st 0)⟩ := by
    have h' : (if !K1.sendFits J.P J.ride then (.error "K1: the job does not fit its place" :
        Except String Sending) else .ok ⟨[], K1.treeTables J.P (J.rows c.1 mᵢ.shown mᵢ.st 0)⟩) =
        .ok z := hsay
    split at h'
    · cases h'
    · exact (Except.ok.inj h').symm
  subst hz
  rw [hl₁] at hq
  have hlt' : τ < J.P.trees.length := (List.getElem?_eq_some_iff.1 hτ).1
  have hTl : τ < q.tables.length := by
    rw [hqT, List.length_map]
    unfold K1.treeTables
    rw [List.length_map, List.length_zipIdx]
    exact hlt'
  have hat := tab_at_round r.run.played.1 _ τ q hq hTl
  have hjl : ((r.run.played.1.take (pre.flatMap (·.rounds)).length).map (·.tables.length)).sum + τ =
      j := by
    have hsh : ∀ y ∈ pre, y.oracles.length = y.rounds.length := fun y hy => by
      have h1 := planOk_shaped_first hpl y (by rw [hcut]; simp [hy])
      unfold Block.shaped at h1
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      exact h1.1
    have hc' := rows_count pre hsh (b :: t)
    rw [← hcut] at hc'
    have ht : treesTo F.first.blocksInOrder pre.length =
        (pre.flatMap fun y => y.oracles.flatMap id).length := by
      unfold treesTo
      rw [hcut, List.take_left']
      rfl
    have e2 : (R.first.take (pre.flatMap (·.rounds)).length).map (·.oracles.length) =
        ((rowsOfChain F.first.blocksInOrder).take (pre.flatMap (·.rounds)).length).map (·.2.length) := by
      rw [← steps_pairs s1, ← List.map_take, List.map_map]
      rfl
    rw [← hj, ht, ← hc', ← e2, List.map_take, laidAs_tables lS, List.map_take]
  rw [hjl] at hat
  have hT : q.tables[τ]? = some (some (⟨sh.logN, sh.mainWidth + sh.maskWidth, fun x w =>
      OnBytes.Slice.toF ((col J.P (J.rows c.1 mᵢ.shown mᵢ.st 0) τ x).getD w.val 0)⟩ : Table)) := by
    rw [hqT, List.getElem?_map]
    unfold K1.treeTables
    rw [List.getElem?_map, List.getElem?_zipIdx, hτ]
    simp only [Nat.zero_add]
    rfl
  rw [hT] at hat
  refine ⟨mᵢ, c, colsOfT (some ⟨sh.logN, sh.mainWidth + sh.maskWidth, fun x w =>
      OnBytes.Slice.toF ((col J.P (J.rows c.1 mᵢ.shown mᵢ.st 0) τ x).getD w.val 0)⟩)
      (treeAsks F ρ 0 j), hlend, (walk_mid ha₁ hwi hmi).1, ?_, ?_, ?_⟩
  · have a3 := walk_hears _ _ _ _ a₁ zᵢ (start_hears ha₁) hwi mᵢ hmi
    have a4 := walk_laid_drawn _ _ _ a₁ zᵢ hwi
    rw [start_laid ha₁, List.map_nil, List.nil_append] at a4
    rw [a4] at a3
    exact a3.trans (List.nil_append _)
  · rw [hbf, treeCols_at F ρ _ _ _ st 0 j (by decide)]
    show (((allTabs r.run.played.1)[j]?).map _) = _
    rw [hat]
    rfl
  · intro q' hq'
    obtain ⟨x', -, rfl⟩ := List.mem_map.1 hq'
    show Table.col _ x' = _
    exact table_column _ _ _ x' (by rw [column_length]; exact hW) (column_words_canonical _ _ _ _)

section Clause
open OnBytes.Slice (codeOf)
open Johnson.Prover.Send (mainSyms maskSyms Rows shapeAt)
open Johnson.Prover.Link (packedN)
open ProofFile.Honest.K14 (SendJob jobOmega Ask columnOf sendingsFit)

variable {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type}

/-- **The clause trees at a test of three members of the last chain, at plain senders**. -/
theorem trees_at_plain_own_test {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre' t' : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (st : List (ℕ × ℕ × List UInt64))
    -- the job
    (B : ManyJob (Local W₀ Rc Xi Tr) Y) (hk : B.s₀.h ≤ B.s₀.k) (Pq : Desc.K14.P14)
    (hQ : sendingsFit Pq = true) (a a' : ℕ) (m₀ m₁ : Mem (Local W₀ Rc Xi Tr) Y) (at_ : Addr)
    (fs : Option ℕ × Option ℕ) (ask : Local W₀ Rc Xi Tr → Ask)
    (hm : B.mems = [m₀, m₁, memOfSending (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none])
    (d₀ d₁ d₂ : ℕ)
    (ht : B.trees = [(d₀, [.mask 0]), (d₁, [.main 1, .mask 1, .fresh]), (d₂, [.main 2])])
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hd : [d₀, d₁, d₂] = os.map (·.1.a))
    (j₀ j₁ j₂ : ℕ) (hsrc : os.map (fun o => ProofFile.Honest.srcOf 2 o.2) = [(0, j₀), (0, j₁), (1, j₂)])
    -- the state and the members' stretches
    (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (mem : ℕ → Stretch)
    -- the first chain's two senders
    (preI preW : List (Block F.S₁ F.Cl)) (bI bW : Block F.S₁ F.Cl) (tI tW : List (Block F.S₁ F.Cl))
    (hcutI : F.first.blocksInOrder = preI ++ bI :: tI) (hcutW : F.first.blocksInOrder = preW ++ bW :: tW)
    (hbI : bI.rounds ≠ []) (hbW : bW.rounds ≠ [])
    (JI JW : K1.SendJob (Local W₀ Rc Xi Tr) Y)
    (hgI : (P.first.find? fun g => g.place == bI.place) =
      some (K1.proverSideOfSending (V := Local W₀ Rc Xi Tr) JI))
    (hgW : (P.first.find? fun g => g.place == bW.place) =
      some (K1.proverSideOfSending (V := Local W₀ Rc Xi Tr) JW))
    (τI τW kI : ℕ) (shI shW : OnBytes.TreeShape) (hτI : JI.P.trees[τI]? = some shI)
    (hτW : JW.P.trees[τW]? = some shW)
    (hWI : columnWidth JI.P τI = shI.mainWidth + shI.maskWidth)
    (hWW : columnWidth JW.P τW = shW.mainWidth + shW.maskWidth)
    (hjI : treesTo F.first.blocksInOrder preI.length + τI = j₀)
    (hjW : treesTo F.first.blocksInOrder preW.length + τW = j₁)
    -- what the two members are, of their senders' rows at this run
    (hI : ∀ (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
      (c : (K1.sendPart (V := Local W₀ Rc Xi Tr) JI :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).Coins),
      lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨bI.place, 0⟩
        (K1.sendPart (V := Local W₀ Rc Xi Tr) JI) = .ok c →
      mᵢ.st.input = R.own → mᵢ.st.heard = ρ.first.take (preI.flatMap (·.rounds)).length →
      m₀.rows m.st.input (restFront B.toRun.toTest m) (mem 0) =
        psOfRows JI.P kI (JI.rows c.1 mᵢ.shown mᵢ.st 0 kI))
    (hW : ∀ (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
      (c : (K1.sendPart (V := Local W₀ Rc Xi Tr) JW :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).Coins),
      lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨bW.place, 0⟩
        (K1.sendPart (V := Local W₀ Rc Xi Tr) JW) = .ok c →
      mᵢ.st.input = R.own → mᵢ.st.heard = ρ.first.take (preW.flatMap (·.rounds)).length →
      m₁.rows m.st.input (restFront B.toRun.toTest m) (mem 1) =
          psOfRows JW.P 0 (JW.rows c.1 mᵢ.shown mᵢ.st 0 0) ∧
        (∀ r < 2 ^ B.s₀.h, ∀ j < B.s₀.Z.l, (JW.rows c.1 mᵢ.shown mᵢ.st 0 1).mask r j =
          (rowsAt B.toRun.toTest mem m).fM r j) ∧
        ∀ r < 2 ^ B.s₀.h, ∀ q < B.s₀.Z.r, (JW.rows c.1 mᵢ.shown mᵢ.st 0 1).maskTl r q =
          (rowsAt B.toRun.toTest mem m).fT r q)
    -- public, at the two senders
    (hinZ₀ : m₀.shape.maskFirst + m₀.shape.maskRows ≤ 2 ^ B.s₀.h)
    (hnI : m₀.shape.maskRows = (Johnson.Prover.Send.shapeAt JI.P kI).maskRows)
    (hzI : codeOf (JI.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JI.P kI).maskCode default) =
      B.s₀.Z)
    (hmineI : (List.range JI.P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade JI.P.codes JI.P.sent).getD {}).tree[k]? == some τI) =
        [kI])
    (hmainI : (Johnson.Prover.Send.shapeAt JI.P kI).mainRows = 0)
    (hbase₁ : m₁.shape.base = false)
    (hoffM : ∀ b, m₁.shape.mainFirst ≤ b → b < m₁.shape.mainFirst + m₁.shape.mainRows →
      ¬ (m₀.shape.mainFirst ≤ b ∧ b < m₀.shape.mainFirst + m₀.shape.mainRows))
    (hoffZ : ∀ b, m₁.shape.maskFirst ≤ b → b < m₁.shape.maskFirst + m₁.shape.maskRows →
      ¬ (m₀.shape.maskFirst ≤ b ∧ b < m₀.shape.maskFirst + m₀.shape.maskRows))
    (hinM : m₁.shape.mainFirst + m₁.shape.mainRows ≤ 2 ^ B.s₀.k)
    (hinZ : m₁.shape.maskFirst + m₁.shape.maskRows ≤ 2 ^ B.s₀.h)
    (hnM : m₁.shape.mainRows = (Johnson.Prover.Send.shapeAt JW.P 0).mainRows)
    (hnZ : m₁.shape.maskRows = (Johnson.Prover.Send.shapeAt JW.P 0).maskRows)
    (hdW : (Johnson.Prover.Send.shapeAt JW.P 0).mainDeg = 3)
    (hzC : codeOf (JW.P.codes.base.getD (Johnson.Prover.Send.shapeAt JW.P 0).code default) = B.s₀.C)
    (hzZ : codeOf (JW.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JW.P 0).maskCode default) =
      B.s₀.Z)
    (hzF : codeOf (JW.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JW.P 1).maskCode default) =
      B.s₀.Z)
    (hnF : (Johnson.Prover.Send.shapeAt JW.P 1).maskRows = 2 ^ B.s₀.h)
    (hmF : (Johnson.Prover.Send.shapeAt JW.P 1).mainRows = 0)
    (hmineW : (List.range JW.P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade JW.P.codes JW.P.sent).getD {}).tree[k]? == some τW) =
        [0, 1])
    -- the shared chain's sender
    (preO : List (Block F.S₂ F.Cl)) (bO : Block F.S₂ F.Cl) (tO : List (Block F.S₂ F.Cl))
    (hcutO : F.shared.blocksInOrder = preO ++ bO :: tO) (hbO : bO.rounds ≠ [])
    (witO : Common W₀ Rc Ky → Ask)
    (hgO : (P.shared.find? fun g => g.place == bO.place) =
      some ⟨bO.place, [(ProofFile.Honest.K14.liftSend witO (ProofFile.Honest.K14.sendingPart (jobOmega ⟨Pq, a⟩)) :
        Part Empty (Common W₀ Rc Ky) X₀)]⟩)
    (hwO : widthFits (jobOmega ⟨Pq, a⟩) 0 = true)
    (hjO : Johnson.G.OfPlan.rootsOf (preO.flatMap (·.rounds)) + 0 = j₂)
    (hO : ∀ (mᵢ : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
      (c : (ProofFile.Honest.K14.liftSend witO (ProofFile.Honest.K14.sendingPart (jobOmega ⟨Pq, a⟩)) :
        Part Empty (Common W₀ Rc Ky) X₀).Coins),
      lendPart Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) ⟨bO.place, 0⟩
        (ProofFile.Honest.K14.liftSend witO (ProofFile.Honest.K14.sendingPart (jobOmega ⟨Pq, a⟩))) = .ok c →
      mᵢ.st.input = R.common → mᵢ.st.heard = ρ.shared.take (preO.flatMap (·.rounds)).length →
      (jobOmega ⟨Pq, a'⟩).data ⟨ask m.st.input, (restFront B.toRun.toTest m).heard, ()⟩ 0 =
          (jobOmega ⟨Pq, a⟩).data (mᵢ.st.narrow witO fun _ => ()) 0 ∧
        SameCut (jobOmega ⟨Pq, a⟩) 0 (coinsE c.1).toArray (mem 2))
    (hbaseO : (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.base = false)
    (hoffO : ∀ y ∈ [m₀, m₁], ∀ b,
      (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst ≤ b →
      b < (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst +
        (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainRows →
      ¬ (y.shape.mainFirst ≤ b ∧ b < y.shape.mainFirst + y.shape.mainRows))
    (hinO : (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst +
      (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainRows ≤ 2 ^ B.s₀.k)
    (hcO : sameCode ((jobOmega ⟨Pq, a⟩).Q.codes.base.getD
      (Light.shapeAt (jobOmega ⟨Pq, a⟩) 0).code default) B.s₀.C = true)
    (hmineO : mineOf (jobOmega ⟨Pq, a⟩) 0 = [0])
    (hmaskO : (Light.shapeAt (jobOmega ⟨Pq, a⟩) 0).maskRows = 0) :
    TreesAt B.toRun.toTest 2 os mem m (r.run.beforeAt st ⟨σ.block.place, u.number⟩) := by
  obtain ⟨o₀, o₁, o₂, hos⟩ : ∃ o₀ o₁ o₂, os = [o₀, o₁, o₂] := by
    have hl := congrArg List.length hsrc
    rw [List.length_map] at hl
    match os, hl with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  subst hos
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsrc hd
  obtain ⟨s₀, s₁, s₂⟩ := hsrc
  obtain ⟨e₀, e₁, e₂⟩ := hd
  have hT : B.toRun.toTest.trees₀ m.st.input (restFront B.toRun.toTest m) mem
      (rowsAt B.toRun.toTest mem m) = B.trees.map fun T =>
        Light.treeOf B.s₀ (T.1, T.2.flatMap (selsOf B.s₀ (B.mems.map (·.shape))))
          (rowsAt B.toRun.toTest mem m) :=
    trees₀_many B _ _ mem _
  refine ⟨?_, fun n o T ho hTn => ?_⟩
  · rw [hT, ht]
    show [d₀, d₁, d₂] = _
    rw [e₀, e₁, e₂]
    rfl
  · have hcol : ∀ (n : ℕ) (T : Tree) (z : ℕ), (B.toRun.toTest.trees₀ m.st.input
        (restFront B.toRun.toTest m) mem (rowsAt B.toRun.toTest mem m))[n]? = some T →
        T.2 z = ((B.toRun.toTest.trees₀ m.st.input (restFront B.toRun.toTest m) mem
          (B.toRun.toTest.first m.st.input (restFront B.toRun.toTest m)
            (carriedCoins B.toRun.toTest mem))).getD n (0, fun _ => [])).2 z := by
      intro n T z h
      show _ = ((B.toRun.toTest.trees₀ m.st.input (restFront B.toRun.toTest m) mem
        (rowsAt B.toRun.toTest mem m)).getD n (0, fun _ => [])).2 z
      rw [List.getD_eq_getElem?_getD, h]
      rfl
    match n, ho, hTn with
    | 0, ho, hTn =>
      obtain rfl : o₀ = o := Option.some.inj ho
      rw [s₀]
      obtain ⟨mᵢ, c, cols, hl, hin, hh, hf, hq⟩ := k1_tree_plain hpl hR hrun σ u pre' t' i S hc
        preI bI tI hcutI hbI JI hgI τI j₀ shI hτI hWI hjI st
      refine ⟨cols, hf, fun q hq' => ?_⟩
      rw [hq q hq', hcol 0 T q.1 hTn]
      exact (tree_of_mask_member B m.st.input (restFront B.toRun.toTest m)
        (carriedCoins B.toRun.toTest mem) m₀ _ hm d₀ (by rw [ht]; rfl) hinZ₀ JI.P kI τI _
        (hI mᵢ c hl hin hh) hnI hzI hmineI hmainI q.1).symm
    | 1, ho, hTn =>
      obtain rfl : o₁ = o := Option.some.inj ho
      rw [s₁]
      obtain ⟨mᵢ, c, cols, hl, hin, hh, hf, hq⟩ := k1_tree_plain hpl hR hrun σ u pre' t' i S hc
        preW bW tW hcutW hbW JW hgW τW j₁ shW hτW hWW hjW st
      refine ⟨cols, hf, fun q hq' => ?_⟩
      obtain ⟨w1, w2, w3⟩ := hW mᵢ c hl hin hh
      rw [hq q hq', hcol 1 T q.1 hTn]
      exact (tree_of_riding_member B hk m.st.input (restFront B.toRun.toTest m)
        (carriedCoins B.toRun.toTest mem) m₀ m₁ _ hm d₁ (by rw [ht]; rfl) hbase₁ hoffM hoffZ hinM hinZ
        JW.P τW _ w1 hnM hnZ hdW hzC hzZ hzF hnF hmF hmineW w2 w3 q.1).symm
    | 2, ho, hTn =>
      obtain rfl : o₂ = o := Option.some.inj ho
      rw [s₂]
      obtain ⟨mᵢ, c, cols, hl, hin, hh, hf, hq⟩ := sending_tree_in_front hpl hR hrun σ u pre' t' i S hc
        preO bO tO hcutO hbO (jobOmega ⟨Pq, a⟩) witO hgO 0 j₂ hwO hjO st
      refine ⟨cols, hf, fun q hq' => ?_⟩
      obtain ⟨o1, o2⟩ := hO mᵢ c hl hin hh
      rw [hq q hq', hcol 2 T q.1 hTn]
      exact (tree_of_sending_member hQ (jobOmega ⟨Pq, a⟩) (jobOmega ⟨Pq, a'⟩) (.inr ⟨rfl, rfl⟩) rfl rfl
        _ rfl B hk m.st.input (restFront B.toRun.toTest m)
        (carriedCoins B.toRun.toTest mem) m₀ m₁ at_ fs ask hm d₂ (by rw [ht]; rfl) hbaseO hoffO hinO
        _ _ o1 o2 hcO hmineO hmaskO q.1).symm
    | _ + 3, ho, _ => cases ho


/-- **The index-mask member is its sender's**, at a plain sender. -/
theorem tie_plain_index {Bk : ProverCoinCounts} (k : Coins Bk) (a : Addr)
    (JS : K1.SendJob (Local W₀ Rc Xi Tr) Y) (at_ : Addr) (fs : Option ℕ × Option ℕ) (b : Place)
    (w : Local W₀ Rc Xi Tr) (fr : Front Y) (kI : ℕ) (hk : kI < JS.P.sent.size)
    (hm : (shapeAt JS.P kI).mainRows = 0)
    (hpos : 0 < (K1.dueR JS.P JS.ride).f + (K1.dueR JS.P JS.ride).e)
    (ds : List (String × Due)) (ca : CsAll ds) (hcar : lend (k.look 2) ds (Light.carriedOf Bk a) = .ok ca)
    (hf : k1CutFits Bk a 0 ⟨b, 0⟩ JS.P JS.ride kI = true)
    (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
    (c : (K1.sendPart (V := Local W₀ Rc Xi Tr) JS :
      Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).Coins)
    (hl : lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨b, 0⟩ (K1.sendPart (V := Local W₀ Rc Xi Tr) JS) = .ok c) :
    (memK1 JS id at_ kI fs).rows w fr (stretches ds ca 0) =
      psOfRows JS.P kI (JS.rows c.1 mᵢ.shown mᵢ.st 0 kI) := by
  obtain ⟨P₁, f₁, r₁, d₁⟩ := JS
  dsimp only at hk hm hpos hf
  have hown := own_of_lendPart hl
  obtain ⟨f, e⟩ := k1_member_coins k a ⟨b, 0⟩ P₁ r₁ c.1 hown hpos ds ca hcar 0 kI hf
  show psOfRows P₁ kI (K1.rowsR P₁ r₁ (d₁ w fr) (csAt _ (K1.startR P₁ r₁ kI) _) kI) =
    psOfRows P₁ kI (K1.rowsR P₁ r₁ _ c.1 kI)
  rw [rowsR_no_main P₁ r₁ (d₁ w fr) _ _ kI hm, rowsR_csAt P₁ r₁ _ kI hk _ c.1 f e]

/-- **W's member is its sender's**, at a plain sender, and the fresh message's rows are the table that
the test's state packs. -/
theorem tie_plain_riding {Bk : ProverCoinCounts} (k : Coins Bk) (a : Addr)
    (JS : K1.SendJob (Local W₀ Rc Xi Tr) Y) (b : Place) (at_ : Addr)
    (fs : Option ℕ × Option ℕ) (w : Local W₀ Rc Xi Tr) (fr : Front Y)
    (N : ℕ) (ρ₁ : List Fmt.Drawn) (hfr : fr.heard.take N = ρ₁.take N)
    (hdata : ∀ fr₁ fr₂ : Front Y, fr₁.heard.take N = fr₂.heard.take N → JS.data w fr₁ = JS.data w fr₂)
    (h0 : 0 < JS.P.sent.size)
    (hpos : 0 < (K1.dueR JS.P JS.ride).f + (K1.dueR JS.P JS.ride).e)
    (ds : List (String × Due)) (ca : CsAll ds) (hcar : lend (k.look 2) ds (Light.carriedOf Bk a) = .ok ca)
    (nW nF : ℕ) (hf0 : k1CutFits Bk a nW ⟨b, 0⟩ JS.P JS.ride 0 = true)
    (hf1 : k1CutFits Bk a nF ⟨b, 0⟩ JS.P JS.ride 1 = true)
    (s : Fmt.M1.Stage) (hride : JS.ride 1 = some ⟨s.k, s.h⟩) (hh : s.h ≤ s.k)
    (hroom : 2 * s.k + 1 ≤ s.h + s.Z.l) (hd : ((shapeAt JS.P 1).mainDeg == 3) = false)
    (hn : (shapeAt JS.P 1).maskRows = 2 ^ s.h)
    (hl : (JS.P.codes.mask.getD (shapeAt JS.P 1).maskCode default).ell = s.Z.l)
    (hr : (JS.P.codes.mask.getD (shapeAt JS.P 1).maskCode default).r = s.Z.r)
    (hdue : 2 * s.k + 1 + 2 ^ s.h * s.Z.r ≤ (K1.dueMsg JS.P.codes (shapeAt JS.P 1) (JS.ride 1)).e)
    (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
    (c : (K1.sendPart (V := Local W₀ Rc Xi Tr) JS :
      Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).Coins)
    (hlend : lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨b, 0⟩ (K1.sendPart (V := Local W₀ Rc Xi Tr) JS) = .ok c)
    (hin : mᵢ.st.input = w) (hh₂ : mᵢ.st.heard = ρ₁.take N) :
    (memK1 JS id at_ 0 fs).rows w fr (stretches ds ca nW) =
        psOfRows JS.P 0 (JS.rows c.1 mᵢ.shown mᵢ.st 0 0) ∧
      (∀ r < 2 ^ s.h, ∀ j < s.Z.l, (JS.rows c.1 mᵢ.shown mᵢ.st 0 1).mask r j =
        packedN (sgOf s) (hideAt ((sgOf s).h + (sgOf s).g) (stretches ds ca nF).e) r j) ∧
      ∀ r < 2 ^ s.h, ∀ q < s.Z.r, (JS.rows c.1 mᵢ.shown mᵢ.st 0 1).maskTl r q =
        tailsIn s (stretches ds ca nF).e r q := by
  have hown := own_of_lendPart hlend
  obtain ⟨f0, e0⟩ := k1_member_coins k a ⟨b, 0⟩ JS.P JS.ride c.1 hown hpos ds ca hcar nW 0 hf0
  obtain ⟨-, e1⟩ := k1_member_coins k a ⟨b, 0⟩ JS.P JS.ride c.1 hown hpos ds ca hcar nF 1 hf1
  subst hin
  obtain ⟨g1, g2⟩ := fresh_of_ride JS.P JS.ride
    (JS.data mᵢ.st.input
      { heard := mᵢ.st.heard.take (mᵢ.st.heard.length - 0), own := mᵢ.st.own,
        seen := mᵢ.shown.front 0 }) c.1 1 s hride hh hroom hd hn hl hr (stretches ds ca nF).e
    fun i hi => e1 i (by omega)
  refine ⟨?_, g1, g2⟩
  have ed : JS.data mᵢ.st.input fr = JS.data mᵢ.st.input
      { heard := mᵢ.st.heard.take (mᵢ.st.heard.length - 0), own := mᵢ.st.own,
        seen := mᵢ.shown.front 0 } := hdata _ _ (by
    show _ = (mᵢ.st.heard.take (mᵢ.st.heard.length - 0)).take N
    rw [Nat.sub_zero, List.take_length, hh₂, hfr, List.take_take, Nat.min_self])
  show psOfRows JS.P 0 (K1.rowsR JS.P JS.ride (JS.data mᵢ.st.input fr)
    (csAt _ (K1.startR JS.P JS.ride 0) _) 0) = psOfRows JS.P 0 (K1.rowsR JS.P JS.ride _ c.1 0)
  rw [ed, rowsR_csAt JS.P JS.ride _ 0 h0 _ c.1 f0 e0]

/-- **The clause trees at a job whose members are made of their plain senders' jobs.** -/
theorem trees_at_plain_job {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre' t' : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (st : List (ℕ × ℕ × List UInt64))
    -- the job
    (B : ManyJob (Local W₀ Rc Xi Tr) Y) (hk : B.s₀.h ≤ B.s₀.k) (Pq : Desc.K14.P14)
    (hQ : sendingsFit Pq = true) (a a' : ℕ) (m₀ m₁ : Mem (Local W₀ Rc Xi Tr) Y) (at_ : Addr)
    (fs : Option ℕ × Option ℕ) (ask : Local W₀ Rc Xi Tr → Ask)
    (hm : B.mems = [m₀, m₁, memOfSending (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none])
    (d₀ d₁ d₂ : ℕ)
    (ht : B.trees = [(d₀, [.mask 0]), (d₁, [.main 1, .mask 1, .fresh]), (d₂, [.main 2])])
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hd : [d₀, d₁, d₂] = os.map (·.1.a))
    (j₀ j₁ j₂ : ℕ) (hsrc : os.map (fun o => ProofFile.Honest.srcOf 2 o.2) = [(0, j₀), (0, j₁), (1, j₂)])
    -- the state and the members' stretches
    (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
    (hmid : midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m))
    (hi : i = firstLen B.toRun.toTest.p.nums.stages)
    (Vc Wc Xc : Type) (pc : Part Vc Wc Xc) (cc : pc.Coins)
    (hlp : lendPart Bk (Bk.rowsOf 2) (k.look 2) ⟨σ.block.place, u.number⟩ pc = .ok cc)
    -- the first chain's two senders
    (preI preW : List (Block F.S₁ F.Cl)) (bI bW : Block F.S₁ F.Cl) (tI tW : List (Block F.S₁ F.Cl))
    (hcutI : F.first.blocksInOrder = preI ++ bI :: tI) (hcutW : F.first.blocksInOrder = preW ++ bW :: tW)
    (hbI : bI.rounds ≠ []) (hbW : bW.rounds ≠ [])
    (JI JW : K1.SendJob (Local W₀ Rc Xi Tr) Y)
    (hgI : (P.first.find? fun g => g.place == bI.place) =
      some (K1.proverSideOfSending (V := Local W₀ Rc Xi Tr) JI))
    (hgW : (P.first.find? fun g => g.place == bW.place) =
      some (K1.proverSideOfSending (V := Local W₀ Rc Xi Tr) JW))
    (τI τW kI : ℕ) (shI shW : OnBytes.TreeShape) (hτI : JI.P.trees[τI]? = some shI)
    (hτW : JW.P.trees[τW]? = some shW)
    (hWI : columnWidth JI.P τI = shI.mainWidth + shI.maskWidth)
    (hWW : columnWidth JW.P τW = shW.mainWidth + shW.maskWidth)
    (hjI : treesTo F.first.blocksInOrder preI.length + τI = j₀)
    (hjW : treesTo F.first.blocksInOrder preW.length + τW = j₁)
    -- what the two members are
    (at₀ at₁ : Addr) (fs₀ fs₁ : Option ℕ × Option ℕ) (hm₀ : m₀ = memK1 JI id at₀ kI fs₀)
    (hkI : kI < JI.P.sent.size)
    (hposI : 0 < (K1.dueR JI.P JI.ride).f + (K1.dueR JI.P JI.ride).e)
    (hbkI : k1CutFits Bk ⟨σ.block.place, u.number⟩ 0 ⟨bI.place, 0⟩ JI.P JI.ride kI = true)
    (hm₁ : m₁ = memK1 JW id at₁ 0 fs₁)
    (hdata : ∀ (w : Local W₀ Rc Xi Tr) (fr fr' : Front Y),
      fr.heard.take (preW.flatMap (·.rounds)).length =
        fr'.heard.take (preW.flatMap (·.rounds)).length → JW.data w fr = JW.data w fr')
    (h0W : 0 < JW.P.sent.size)
    (hposW : 0 < (K1.dueR JW.P JW.ride).f + (K1.dueR JW.P JW.ride).e)
    (hbkW : k1CutFits Bk ⟨σ.block.place, u.number⟩ 1 ⟨bW.place, 0⟩ JW.P JW.ride 0 = true)
    (hbkF : k1CutFits Bk ⟨σ.block.place, u.number⟩ 3 ⟨bW.place, 0⟩ JW.P JW.ride 1 = true)
    (hride : JW.ride 1 = some ⟨B.s₀.k, B.s₀.h⟩)
    (hroom : 2 * B.s₀.k + 1 ≤ B.s₀.h + B.s₀.Z.l) (hdF : ((shapeAt JW.P 1).mainDeg == 3) = false)
    (hdue : 2 * B.s₀.k + 1 + 2 ^ B.s₀.h * B.s₀.Z.r ≤
      (K1.dueMsg JW.P.codes (shapeAt JW.P 1) (JW.ride 1)).e)
    -- public, at the two senders
    (hinZ₀ : m₀.shape.maskFirst + m₀.shape.maskRows ≤ 2 ^ B.s₀.h)
    (hnI : m₀.shape.maskRows = (Johnson.Prover.Send.shapeAt JI.P kI).maskRows)
    (hzI : codeOf (JI.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JI.P kI).maskCode default) =
      B.s₀.Z)
    (hmineI : (List.range JI.P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade JI.P.codes JI.P.sent).getD {}).tree[k]? == some τI) =
        [kI])
    (hmainI : (Johnson.Prover.Send.shapeAt JI.P kI).mainRows = 0)
    (hbase₁ : m₁.shape.base = false)
    (hoffM : ∀ b, m₁.shape.mainFirst ≤ b → b < m₁.shape.mainFirst + m₁.shape.mainRows →
      ¬ (m₀.shape.mainFirst ≤ b ∧ b < m₀.shape.mainFirst + m₀.shape.mainRows))
    (hoffZ : ∀ b, m₁.shape.maskFirst ≤ b → b < m₁.shape.maskFirst + m₁.shape.maskRows →
      ¬ (m₀.shape.maskFirst ≤ b ∧ b < m₀.shape.maskFirst + m₀.shape.maskRows))
    (hinM : m₁.shape.mainFirst + m₁.shape.mainRows ≤ 2 ^ B.s₀.k)
    (hinZ : m₁.shape.maskFirst + m₁.shape.maskRows ≤ 2 ^ B.s₀.h)
    (hnM : m₁.shape.mainRows = (Johnson.Prover.Send.shapeAt JW.P 0).mainRows)
    (hnZ : m₁.shape.maskRows = (Johnson.Prover.Send.shapeAt JW.P 0).maskRows)
    (hdW : (Johnson.Prover.Send.shapeAt JW.P 0).mainDeg = 3)
    (hzC : codeOf (JW.P.codes.base.getD (Johnson.Prover.Send.shapeAt JW.P 0).code default) = B.s₀.C)
    (hzZ : codeOf (JW.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JW.P 0).maskCode default) =
      B.s₀.Z)
    (hzF : codeOf (JW.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JW.P 1).maskCode default) =
      B.s₀.Z)
    (hnF : (Johnson.Prover.Send.shapeAt JW.P 1).maskRows = 2 ^ B.s₀.h)
    (hmF : (Johnson.Prover.Send.shapeAt JW.P 1).mainRows = 0)
    (hmineW : (List.range JW.P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade JW.P.codes JW.P.sent).getD {}).tree[k]? == some τW) =
        [0, 1])
    -- the shared chain's sender
    (preO : List (Block F.S₂ F.Cl)) (bO : Block F.S₂ F.Cl) (tO : List (Block F.S₂ F.Cl))
    (hcutO : F.shared.blocksInOrder = preO ++ bO :: tO) (hbO : bO.rounds ≠ [])
    (witO : Common W₀ Rc Ky → Ask)
    (hgO : (P.shared.find? fun g => g.place == bO.place) =
      some ⟨bO.place, [(ProofFile.Honest.K14.liftSend witO (ProofFile.Honest.K14.sendingPart (jobOmega ⟨Pq, a⟩)) :
        Part Empty (Common W₀ Rc Ky) X₀)]⟩)
    (hwO : widthFits (jobOmega ⟨Pq, a⟩) 0 = true)
    (hjO : Johnson.G.OfPlan.rootsOf (preO.flatMap (·.rounds)) + 0 = j₂)
    (hnotO : ∀ r ∈ Bk.first, r.1 ≠ ⟨bO.place, 0⟩)
    (hposO : 0 < (ProofFile.Honest.K14.takesOf (jobOmega ⟨Pq, a⟩).Q.codes (jobOmega ⟨Pq, a⟩).Q.sent
        (jobOmega ⟨Pq, a⟩).sort).f +
      (ProofFile.Honest.K14.takesOf (jobOmega ⟨Pq, a⟩).Q.codes (jobOmega ⟨Pq, a⟩).Q.sent
        (jobOmega ⟨Pq, a⟩).sort).e)
    (hbkO : Light.cutFits Bk ⟨σ.block.place, u.number⟩ 2 ⟨bO.place, 0⟩ (jobOmega ⟨Pq, a⟩) 0 = true)
    (hatO : a < (preO.flatMap (·.rounds)).length)
    (ha' : a' = ρ.first.length + a)
    (haskO : witO R.common = ask m.st.input)
    (hbaseO : (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.base = false)
    (hoffO : ∀ y ∈ [m₀, m₁], ∀ b,
      (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst ≤ b →
      b < (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst +
        (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainRows →
      ¬ (y.shape.mainFirst ≤ b ∧ b < y.shape.mainFirst + y.shape.mainRows))
    (hinO : (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst +
      (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainRows ≤ 2 ^ B.s₀.k)
    (hcO : sameCode ((jobOmega ⟨Pq, a⟩).Q.codes.base.getD
      (Light.shapeAt (jobOmega ⟨Pq, a⟩) 0).code default) B.s₀.C = true)
    (hmineO : mineOf (jobOmega ⟨Pq, a⟩) 0 = [0])
    (hmaskO : (Light.shapeAt (jobOmega ⟨Pq, a⟩) 0).maskRows = 0) :
    TreesAt B.toRun.toTest 2 os (stretches pc.carries cc.2.2) m
      (r.run.beforeAt st ⟨σ.block.place, u.number⟩) := by
  subst hm₀ hm₁ ha'
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨lS₁, lS₂, lS₃⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  obtain ⟨m', hm', hin', hheard', -⟩ := frame_at_second hpl hR hrun σ u pre' t' i _ S rfl hc st
  obtain rfl : m = m' := Option.some.inj (Except.ok.inj (hmid.symm.trans hm'))
  have hcar := carried_of_lendPart Bk _ _ _ pc cc hlp
  -- what the part's front has heard
  obtain ⟨e', hrest⟩ : ∃ e', (restFront B.toRun.toTest m).heard = ρ.first ++ (ρ.shared ++ e') := by
    have hT : i ≤ (ρ.second.take ((pre'.flatMap (·.rounds)).length + i)).length := by
      have := S.fits
      have := lS₃.1
      rw [List.length_take]
      omega
    refine ⟨(ρ.second.take ((pre'.flatMap (·.rounds)).length + i)).take
      ((ρ.second.take ((pre'.flatMap (·.rounds)).length + i)).length - i), ?_⟩
    show m.st.heard.take (m.st.heard.length - firstLen B.toRun.toTest.p.nums.stages) = _
    rw [← hi, hheard', List.append_assoc, List.length_append, List.length_append,
      show ρ.first.length + (ρ.shared.length + (ρ.second.take ((pre'.flatMap (·.rounds)).length +
        i)).length) - i = ρ.first.length + (ρ.shared.length + ((ρ.second.take
        ((pre'.flatMap (·.rounds)).length + i)).length - i)) by omega,
      List.take_length_add_append, List.take_length_add_append]
  have hN : (preW.flatMap (·.rounds)).length ≤ ρ.first.length := by
    rw [lS₁.1, chainSteps_length _ _ s1, ← List.length_flatMap, hcutW, List.flatMap_append,
      List.length_append]
    exact Nat.le_add_right _ _
  have hfr : (restFront B.toRun.toTest m).heard.take (preW.flatMap (·.rounds)).length =
      ρ.first.take (preW.flatMap (·.rounds)).length := by
    rw [hrest, List.take_append_of_le_length hN]
  have hlen3 : B.toRun.toTest.members.length = 3 := by
    show (B.mems.map (·.sent)).length = 3
    rw [hm]
    rfl
  refine trees_at_plain_own_test hpl hR hrun σ u pre' t' i S hc st B hk Pq hQ a _ _ _ at_ fs ask hm d₀ d₁
    d₂ ht os hd j₀ j₁ j₂ hsrc m (stretches pc.carries cc.2.2) preI preW bI bW tI tW hcutI hcutW hbI hbW
    JI JW hgI hgW τI τW kI shI shW hτI hτW hWI hWW hjI hjW
    (fun mᵢ c hl _ _ => tie_plain_index k _ JI at₀ fs₀ bI.place m.st.input
      (restFront B.toRun.toTest m) kI hkI hmainI hposI _ _ hcar hbkI mᵢ c hl)
    (fun mᵢ c hl hin hh => ?_) hinZ₀ hnI hzI hmineI hmainI hbase₁ hoffM hoffZ hinM hinZ hnM hnZ hdW
    hzC hzZ hzF hnF hmF hmineW preO bO tO hcutO hbO witO hgO hwO hjO
    (fun mᵢ c hl hin hh => ?_) hbaseO hoffO hinO hcO hmineO hmaskO
  · have hh₀ := hin.trans hin'.symm
    obtain ⟨r1, r2, r3⟩ := tie_plain_riding k _ JW bW.place at₁ fs₁ m.st.input
      (restFront B.toRun.toTest m) _ ρ.first hfr (hdata m.st.input) h0W hposW _ _ hcar 1 3 hbkW hbkF B.s₀
      hride hk hroom hdF hnF (congrArg Fmt.M1.Code.l hzF) (congrArg Fmt.M1.Code.r hzF) hdue mᵢ c hl hh₀ hh
    refine ⟨r1, fun r hr j hj => ?_, fun r hr q hq => ?_⟩
    · refine (r2 r hr j hj).trans ?_
      show _ = packedN (sgOf B.s₀) (hideAt ((sgOf B.s₀).h + (sgOf B.s₀).g)
        (stretches pc.carries cc.2.2 B.toRun.toTest.members.length).e) r j
      rw [hlen3]
    · refine (r3 r hr q hq).trans ?_
      show _ = tailsIn B.s₀ (stretches pc.carries cc.2.2 B.toRun.toTest.members.length).e r q
      rw [hlen3]
  · have e := tie_omega_member (X₀ := X₀) k _ Pq a witO bO.place hnotO hposO pc cc hlp 2 hbkO (ask m.st.input)
      ρ.first (ρ.shared.take (preO.flatMap (·.rounds)).length)
      (ρ.shared.drop (preO.flatMap (·.rounds)).length ++ e') (by
        have hlen : (preO.flatMap (·.rounds)).length ≤ ρ.shared.length := by
          rw [lS₂.1, chainSteps_length _ _ s2, ← List.length_flatMap, hcutO, List.flatMap_append,
            List.length_append]
          exact Nat.le_add_right _ _
        rw [List.length_take]
        omega) mᵢ c hl (by rw [hin]; exact haskO) hh
    have e3 : ρ.shared ++ e' = ρ.shared.take (preO.flatMap (·.rounds)).length ++
        (ρ.shared.drop (preO.flatMap (·.rounds)).length ++ e') := by
      rw [← List.append_assoc, List.take_append_drop]
    rw [hrest, e3]
    exact e


end Clause

end Plain

/-! ## On at a run -/

section Run
open VerifiableInference.Desc.Key (Xi LaterPlaces Source)
open H2K.Member (piKWFull codesKeyFull)
open AtPublicFiles.AtFiles (keyFileDescription KeySourced)
open AtPublicFiles.KeyLay (jobKWAt pWK)
open ProofFile.Honest.K14 (SendPub Ask)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc Ky X₀ Y : Type}

theorem first_KW_pos : firstLen piKWFull.nums.stages ≠ 0 := by decide +kernel

theorem rest_KW_pos : restLen piKWFull.nums.stages ≠ 0 := by decide +kernel

/-- The carried blocks do not see the guard. -/
theorem carriedAt_guarded {V W X : Type} (Bk : ProverCoinCounts) (k : Coins Bk) (c : ℕ) (a : Addr)
    (p : Part V W X) : carriedAt Bk k c a p.needsField = carriedAt Bk k c a p := by
  unfold carriedAt
  rw [lendPart_guarded]
  rfl

/-- The job that proverSideOfGuardedSending lays at the identity reader. -/
abbrev jobOwnKey (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
    (JI JW : K1.SendJob (Local W₀ Rc Xi Unit) Y) (A : SendPub) (ask : Local W₀ Rc Xi Unit → Ask) :
    TestJob (Local W₀ Rc Xi Unit) Y :=
  (jobKWAt Xs N Pl JI JW A id ask).toRun.toTest

/-- **What is left at a stand**: the two clauses on the asks, at the job. -/
def LeftAtOwnKey (J : TestJob (Local W₀ Rc Xi Unit) Y) (K : OnBytes.Codes)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (mem : ℕ → Stretch)
    (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) Y) : Prop :=
  ∃ Dp cc Rw, Dp.ts.length = os.length ∧
    ShapeAsksD J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc Rw

/-- **The clause of the rule at the list of the key file's own test.** hTrees: the clause trees at each
stand (trees_at_plain_job pays it from the senders); hleft: the asks. -/
theorem onAtRun_own_key (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {Bk : ProverCoinCounts}
    {H : Prover W₀ Rc Xi Ky Unit X₀ Y}
    {G : Sides (keyFileDescription Xs N Pl) Bk W₀ Rc Ky Unit X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Unit X₀ Y} {r : RunC (keyFileDescription Xs N Pl)}
    (T : ThreadsP (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hR : ready (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k ρ = .ok r)
    (JI JW : K1.SendJob (Local W₀ Rc Xi Unit) Y) (A : SendPub) (ask : Local W₀ Rc Xi Unit → Ask)
    (L : Lettered Bk (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit)
      (Local W₀ Rc Xi Unit) Y Xi)
    (hplace : L.place = placeW)
    (hrow : L.row = guardRow (testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)))
    (hOn : L.On = OnOwnTestEntry Face.own (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)
      codesKeyFull 2 piKWFull.nums.first)
    (hg : ((G.prover H).second.find? fun g => g.place == placeW) =
      some ((proverSideOfProximityTest (jobOwnKey Xs N Pl JI JW A ask) :
        Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y).needsField))
    (hT : tiesB Bk placeW (jobOwnKey Xs N Pl JI JW A ask).members.length = true)
    (hTrees : ∀ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) Y)
      (cc : (restMember (V := Local W₀ Rc Xi Unit) (jobOwnKey Xs N Pl JI JW A ask)
        (simOwnKey Xs N Pl)).part.Coins)
      (σ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y Xi)
      (pre' t' : List (Block (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl)),
      Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder (jobOwnKey Xs N Pl JI JW A ask).p.place
        (guardRow (testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl))) [] = some σ →
      StandsAt (keyFileDescription Xs N Pl).second.blocksInOrder R.second σ (restMember (V := Local W₀ Rc Xi Unit)
                            (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)).guarded pre' t'
        (firstLen (jobOwnKey Xs N Pl JI JW A ask).p.nums.stages) →
      InsideOf .own Bk 2 (G.prover H).second σ.block (T.I₃ pre'.length) (σ.roundsTo 1) k m
        (envOf (H.storedWords w₀ rc) (taken₃ r.run.played.1 r.run.played.2.1)
          (r.run.played.2.2.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1))) →
      m.seen = roundsOf r.run.played.1 ++ roundsOf r.run.played.2.1 ++
        roundsOf (r.run.played.2.2.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1)) →
      r.called ⟨L.place, 1⟩ = true →
      midAtW (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩ = .ok (some m) →
      lendPart Bk (Bk.rowsOf 2) (k.look 2) ⟨L.place, 1⟩ (restMember (V := Local W₀ Rc Xi Unit)
        (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)).part = .ok cc →
      (laidOf (keyFileDescription Xs N Pl) ρ r.run.played.1 r.run.played.2.1
          (r.run.played.2.2.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1))).front 2
          (storedShown (H.storedWords w₀ rc) (storedAsks (keyFileDescription Xs N Pl) ρ)) =
        r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, 1⟩ →
      TreesAt (jobOwnKey Xs N Pl JI JW A ask) 2 piKWFull.nums.first (stretches _ cc.2.2) m
        (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, 1⟩))
    (hleft : ∀ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) Y)
      (ca : CsAll (restMember (V := Local W₀ Rc Xi Unit) (jobOwnKey Xs N Pl JI JW A ask)
        (simOwnKey Xs N Pl)).part.carries)
      (σ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y Xi)
      (pre' t' : List (Block (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl)),
      Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder (jobOwnKey Xs N Pl JI JW A ask).p.place
        (guardRow (testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl))) [] = some σ →
      StandsAt (keyFileDescription Xs N Pl).second.blocksInOrder R.second σ (restMember (V := Local W₀ Rc Xi Unit)
                            (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)).guarded pre' t'
        (firstLen (jobOwnKey Xs N Pl JI JW A ask).p.nums.stages) →
      InsideOf .own Bk 2 (G.prover H).second σ.block (T.I₃ pre'.length) (σ.roundsTo 1) k m
        (envOf (H.storedWords w₀ rc) (taken₃ r.run.played.1 r.run.played.2.1)
          (r.run.played.2.2.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1))) →
      m.seen = roundsOf r.run.played.1 ++ roundsOf r.run.played.2.1 ++
        roundsOf (r.run.played.2.2.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1)) →
      r.called ⟨L.place, 1⟩ = true →
      midAtW (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩ = .ok (some m) →
      carriedAt Bk k 2 ⟨L.place, 1⟩ (restMember (V := Local W₀ Rc Xi Unit)
        (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)).part = .ok ca →
      (laidOf (keyFileDescription Xs N Pl) ρ r.run.played.1 r.run.played.2.1
          (r.run.played.2.2.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1))).front 2
          (storedShown (H.storedWords w₀ rc) (storedAsks (keyFileDescription Xs N Pl) ρ)) =
        r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, 1⟩ →
      LeftAtOwnKey (jobOwnKey Xs N Pl JI JW A ask) codesKeyFull piKWFull.nums.first
        (stretches _ ca) m) :
    OnAtRun₃ T ρ r L := by
  intro σ hσ u hu pre' t' hcut m ca hin hseen hca hc hmid hfr
  have hpl : σ.block.place = L.place := side_place hσ
  have hp := own_sourced hS scope
  have hJ : (jobOwnKey Xs N Pl JI JW A ask).p = piKWFull := hp
  have hPW : (jobOwnKey Xs N Pl JI JW A ask).p.place = placeW := by
    rw [hJ]
    exact place_KW
  have hσ' : Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder (jobOwnKey Xs N Pl JI JW A ask).p.place
      (guardRow (testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl))) [] = some σ := by
    rw [hPW, ← hplace, ← hrow]
    exact hσ
  have hg' : ((G.prover H).second.find? fun g => g.place == σ.block.place) =
      some ((proverSideOfProximityTest (jobOwnKey Xs N Pl JI JW A ask) :
        Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y).needsField) := by
    rw [hpl, hplace]
    exact hg
  obtain ⟨b, hf, hbp, hr, hor⟩ := find_own_key (Xs := Xs) (N := N) (Pl := Pl)
    (jobOwnKey Xs N Pl JI JW A ask) rfl (by rw [hp]; exact place_KW)
  have F : PlaceFacts (jobOwnKey Xs N Pl JI JW A ask).p dsKW := by
    rw [hJ]
    exact facts_KWFull
  have hrest : restLen (jobOwnKey Xs N Pl JI JW A ask).p.nums.stages ≠ 0 := by
    rw [hJ]
    exact rest_KW_pos
  -- the members
  obtain ⟨b₀, hb₀, e₀⟩ := Option.map_eq_some_iff.1 hσ'
  obtain rfl : b₀ = b := Option.some.inj (hb₀.symm.trans hf)
  have hbare : testSide (V := Local W₀ Rc Xi Unit) (keyFileDescription Xs N Pl).second.blocksInOrder
      (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl) [] =
      some (⟨b₀, testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl),
        fallOf [] (jobOwnKey Xs N Pl JI JW A ask).p.place⟩ :
        Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y
          Xi) := by
    unfold testSide Side.seated
    show Option.map _ ((keyFileDescription Xs N Pl).second.blocksInOrder.find? fun b => b.place == _) = _
    rw [hb₀]
    rfl
  obtain ⟨-, -, hall⟩ := any_at_place (V := Local W₀ Rc Xi Unit) (jobOwnKey Xs N Pl JI JW A ask)
    (simOwnKey Xs N Pl) F _ b₀ hf hbp hr hor rfl hJ.symm rfl
  obtain ⟨hfit₀, hmem₀, -⟩ := hall [] _ hbare
  have hmem : σ.members = [(firstMember (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)).guarded,
      (restMember (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)).guarded] := by
    rw [← e₀]
    show membersOf (guardRow _) 0 _ = _
    rw [membersOf_guardRow]
    exact congrArg (List.map Member.guarded) hmem₀
  have hrowσ : σ.row = guardRow (testPairs (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)) := by
    rw [← e₀]
  have hblk : σ.block ∈ (keyFileDescription Xs N Pl).second.blocksInOrder := by
    rw [← e₀]
    exact List.mem_of_find?_eq_some hb₀
  have hfitg : σ.fits = true := by
    rw [← e₀]
    show (⟨b₀, guardRow _, _⟩ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit)
      (Local W₀ Rc Xi Unit) Y Xi).fits = true
    rw [fits_guarded_row]
    exact hfit₀
  rw [hOn, hfr]
  rw [hmem] at hu
  have hc' : r.called ⟨σ.block.place, u.number⟩ = true := by
    rw [hpl]
    exact hc
  have hmid' : orRefused (midAtW (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) =
      .ok m := hmid
  rcases List.mem_cons.1 hu with rfl | hu'
  · -- the first part: the field holds columns
    have hpos₁ : (firstMember (V := Local W₀ Rc Xi Unit) (jobOwnKey Xs N Pl JI JW A ask)
        (simOwnKey Xs N Pl)).guarded.part.moves.length ≠ 0 := by
      show (firstPart (jobOwnKey Xs N Pl JI JW A ask) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y).needsField.moves.length ≠ 0
      rw [needsField_length, ProofFile.Honest.K12.Light.first_moves_len, hJ]
      exact first_KW_pos
    obtain ⟨pre, t, S₀⟩ := stands_member_last hS.named.plan hR σ hblk hfitg _
      (by rw [hmem]; exact List.mem_cons_self) hpos₁ _ hg' (by rw [hrowσ]; rfl)
    obtain ⟨m₂, e₁, e₂, v₀, s, cols, tr, hm₂, -, -, hop, -⟩ :=
      door_last_with_columns hS.named.plan hR σ _ pre t _ S₀ hrun hc'
    rw [hpl] at hm₂
    rw [hm₂] at hmid'
    obtain rfl : m₂ = m := Except.ok.inj (show (Except.ok m₂ : Except Refusal _) = .ok m from hmid')
    exact ⟨⟨_, hop⟩, fun hn => by cases hn⟩
  obtain rfl := List.mem_singleton.1 hu'
  have hc₁ : r.called ⟨σ.block.place, 1⟩ = true := hc'
  obtain ⟨pre, t, c, m₁, S, hm₁, hca₁, hin₁, F5⟩ := five_at_test₃ hS.named.plan hρ hR
    (jobOwnKey Xs N Pl JI JW A ask) F _ rfl
    (fun s w fr mem mem' hh => rowsMu_many _ s w fr mem mem' hh) (simOwnKey Xs N Pl) hJ.symm rfl [] σ
    hσ' b₀ hf hbp hr hor hg' (by rw [hPW]; exact hT) hrun hc₁ hrest
    (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
  have hndF := (places_nodup (((keyFileDescription Xs N Pl).planOk_ok).1 hS.named.plan).places).2.2
  obtain ⟨rfl, rfl⟩ := cut_both (fun b : Block (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl => b.place)
    _ _ _ _ _ _ hcut S.cut hndF
  obtain ⟨m₂, cs, hm₂, hop, hx, hdoor⟩ := door_at_last_any hS.named.plan hR hrun enterOwn placeW
    (jobOwnKey Xs N Pl JI JW A ask) rfl σ _ _ _ S hc' (hpl.trans hplace)
  obtain rfl : m₁ = m₂ := Option.some.inj (Except.ok.inj (hm₁.symm.trans hm₂))
  rw [hpl] at hm₁ hca₁ F5 hdoor
  have hmid₂ : orRefused (midAtW (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩) =
      .ok m := hmid'
  rw [hm₁] at hmid₂
  obtain rfl : m₁ = m := Except.ok.inj (show (Except.ok m₁ : Except Refusal _) = .ok m from hmid₂)
  have hcaG : carriedAt Bk k 2 ⟨L.place, 1⟩ (restMember (V := Local W₀ Rc Xi Unit)
      (jobOwnKey Xs N Pl JI JW A ask) (simOwnKey Xs N Pl)).part = .ok ca :=
    (carriedAt_guarded _ _ _ _ _).symm.trans hca
  obtain rfl : c.2.1.2.2 = ca := Except.ok.inj (hca₁.symm.trans hcaG)
  have hca₂ := hcaG
  unfold carriedAt at hca₂
  obtain ⟨c₁, hl₁, e₁⟩ := exMap_ok hca₂
  have hTr := hTrees m₁ c₁ σ _ _ hσ' S hin hseen hc hm₁ hl₁ hfr
  rw [e₁] at hTr
  refine ⟨⟨_, hop⟩, onEntry_of_free Face.own _ _ _ 2 _ _ _ m₁ _ ?_⟩
  refine ⟨F5.le, F5.leS, F5.heardFit, F5.heard, ?_, F5.fold,
    hleft m₁ _ σ _ _ hσ' S hin hseen hc hm₁ hcaG hfr, hTr⟩
  show _ = stateAtOwnKey Xs N Pl m₁.st.input.x _
  rw [hx]
  exact hdoor

end Run

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.five_at_test₃
#print axioms ProofFile.Honest.K12.Sim2.door_at_last_any
#print axioms ProofFile.Honest.K12.Sim2.k1_tree_plain
#print axioms ProofFile.Honest.K12.Sim2.trees_at_plain_own_test
#print axioms ProofFile.Honest.K12.Sim2.tie_plain_index
#print axioms ProofFile.Honest.K12.Sim2.tie_plain_riding
#print axioms ProofFile.Honest.K12.Sim2.trees_at_plain_job
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_own_key
