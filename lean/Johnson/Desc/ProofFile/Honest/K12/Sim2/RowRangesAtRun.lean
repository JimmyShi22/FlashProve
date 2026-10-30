-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the offline row of the test on the ranges, at a run.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowRangesAtRun.lean: OnAtRun₁ (Law/OwedAtRun.lean) at the list of
the test on the ranges, at the key file's first chain.

  k1_tree_first_stand   what the front of a called part of the first chain lists of a K1 sending's tree
  rest_seen, five_at_test   the rounds cut back; the seat and the five clauses, at every description
  col_two_messages, k1_coins_same_chain, OneSenderPub, col_one_tie   a one-member job's column is its
                        sender's, at the coins that the book lends
  trees_one_at          the clause trees at a job of one member
  LeftAtRanges          what is left at a stand: the two clauses on the asks
  onAtRun_ranges        the statement

Paid at every stand: the door (recRanges_is_view: no patch, the job's own state stands), FiveAt,
TreesAt. Left: hleft (LeftAtRanges); on the filling hg, hgS; on the book hT, hf0, hf1; public hP, hr',
hd, hcutS, hbS, hfront, hτ, hW, hj, hlog, hsrc, hN.

Limits. The rule moves the debt and pays none of it. The condition reads the input and the carried
values: no later law may take it as a hypothesis on a run and then speak of the random values as sampled
anew. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowRanges
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesOwnTest
import Johnson.Desc.ProofFile.Honest.K12.FiveAtFirst
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtFirst
import Johnson.Desc.ProofFile.Honest.K12.Sim2.StandL
import Johnson.Desc.ProofFile.Honest.K12.Sim2.DoorTrue
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesOwnTestJob
import Johnson.Desc.ProofFile.Honest.K12.JobOne
import Johnson.Desc.ProofFile.Honest.Law.OwedAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block FileDescription Oracle Place)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts T12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light
open Johnson.Prover.Send (col)

/-- **What the front of a called part of the first chain lists of a tree of that chain that a sending
of the kind K1 sent, in front of the part.** -/
theorem k1_tree_first_stand {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₁ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre' t' : List (Block F.S₁ F.Cl)) (i : ℕ) (S : StandsAt F.first.blocksInOrder R.first σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (pre : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl) (t : List (Block F.S₁ F.Cl))
    (hcut : F.first.blocksInOrder = pre ++ b :: t) (hb : b.rounds ≠ [])
    (hin : (pre.flatMap (·.rounds)).length < (pre'.flatMap (·.rounds)).length + i)
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
  obtain ⟨a₁, y, m₂, ha₁, hw, hyl, hym, -⟩ := played_at_first hpl hR hrun σ u pre' t' i _ S rfl hc
  obtain ⟨-, -, -, -, -, -, hbf, -⟩ := frame_at_first hpl hR hrun σ u pre' t' i _ S rfl hc st
  obtain ⟨zᵢ, mᵢ, c, q, z, hwi, hmi, hlend, hq, hqT, hsay⟩ := first_round_at_first hR pre b t hcut hb
    (K1.proverSideOfSending (V := Local W₀ Rc Xi Tr) J).place (K1.sendPart (V := Local W₀ Rc Xi Tr) J) _ rfl hg _
    hin _ a₁ y (start_laid ha₁) (by have := S.fits; simp only at this; omega) hw (by rw [hym]; rfl)
  have hz : z = ⟨[], K1.treeTables J.P (J.rows c.1 mᵢ.shown mᵢ.st 0)⟩ := by
    have h' : (if !K1.sendFits J.P J.ride then (.error "K1: the job does not fit its place" :
        Except String Sending) else .ok ⟨[], K1.treeTables J.P (J.rows c.1 mᵢ.shown mᵢ.st 0)⟩) =
        .ok z := hsay
    split at h'
    · cases h'
    · exact (Except.ok.inj h').symm
  subst hz
  have hlt : τ < J.P.trees.length := (List.getElem?_eq_some_iff.1 hτ).1
  have hTl : τ < q.tables.length := by
    rw [hqT, List.length_map]
    unfold K1.treeTables
    rw [List.length_map, List.length_zipIdx]
    exact hlt
  rw [hyl] at hq
  have hat := tab_at_round (r.run.played.1.take ((pre'.flatMap (·.rounds)).length + i)) _ τ q hq hTl
  have hjl : (((r.run.played.1.take ((pre'.flatMap (·.rounds)).length + i)).take
      (pre.flatMap (·.rounds)).length).map (·.tables.length)).sum + τ = j := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hin)]
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
      (treeAsks F ρ 0 j), hlend, ?_, ?_, ?_, ?_⟩
  · exact (walk_mid ha₁ hwi hmi).1
  · have a3 := walk_hears _ _ _ _ a₁ zᵢ (start_hears ha₁) hwi mᵢ hmi
    have a4 := walk_laid_drawn _ _ _ a₁ zᵢ hwi
    rw [start_laid ha₁, List.map_nil, List.nil_append] at a4
    rw [a4] at a3
    exact a3.trans (List.nil_append _)
  · have hbf' : r.run.beforeAt st ⟨σ.block.place, u.number⟩ = _ := hbf
    rw [hbf']
    show (⟨shownBy 0 (treeAsks F ρ 0) _ 0, st⟩ : Before).treeCols 0 j = _
    rw [treeCols_first, hat]
    rfl
  · intro q' hq'
    obtain ⟨x', -, rfl⟩ := List.mem_map.1 hq'
    show Table.col _ x' = _
    exact table_column _ _ _ x' (by rw [column_length]; exact hW) (column_words_canonical _ _ _ _)

/-- The rounds that a stand's front shows, cut back, are the job's front's. -/
theorem rest_seen {W X : Type} (J : TestJob W X) (m : ProofFile.Honest.Mid W X) (front : Before)
    (h : m.seen = front.seen) :
    (restFront J m).seen.rounds = (front.cut (firstLen J.p.nums.stages)).seen := by
  show m.seen.take (m.seen.length - firstLen J.p.nums.stages) = _
  rw [h]
  unfold ProofFile.Honest.Before.cut Before.seen
  rw [List.length_map, List.map_take]

/-- **The seat at a proximity test of the first chain**, and the five clauses there: at every
description whose block at the test's place has the test's rounds. -/
theorem five_at_test {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hρ : ρ.due F = true) (hR : ready F Bk P w₀ rc x k = .ok R)
    (J : TestJob (Local W₀ Rc Xi Tr) Y) {ds : List Fmt.Drawn} (Fc : PlaceFacts J.p ds)
    (f : Addr × ℕ) (hfr : J.fresh = some f)
    (hrows : ∀ (w : Local W₀ Rc Xi Tr) (fr : Front Y) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) → J.rows₀ w fr mem = J.rows₀ w fr mem')
    (Js : SimJob Xi) (hs : Js.p = J.p) (ho : Js.own = false) (fs : List (Fall F.S₁))
    (σ : Side F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Xi)
    (hσ : testSide F.first.blocksInOrder J Js fs = some σ)
    (b : Block F.S₁ F.Cl) (hf : (F.first.blocksInOrder.find? fun b => b.place == J.p.place) = some b)
    (hbp : b.place = J.p.place)
    (hr : b.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds)
    (hor : b.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles)
    (hg : (P.first.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hT : tiesB Bk J.p.place J.members.length = true)
    (hrun : runC F Bk P w₀ rc x k ρ = .ok r) (hc : r.called ⟨σ.block.place, 1⟩ = true)
    (hpos : restLen J.p.nums.stages ≠ 0) (st : List (ℕ × ℕ × List UInt64)) :
    ∃ (pre t : List (Block F.S₁ F.Cl))
      (c : RowCoins [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y), restPart J])
      (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y),
      StandsAt F.first.blocksInOrder R.first σ (restMember J Js) pre t (firstLen J.p.nums.stages) ∧
      midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, 1⟩ = .ok (some m) ∧
      carriedAt Bk k 0 ⟨σ.block.place, 1⟩
        (restMember (V := Local W₀ Rc Xi Tr) J Js).part = .ok c.2.1.2.2 ∧
      m.st.input = R.own ∧
      FiveAt J (stretches _ c.2.1.2.2) m (r.run.beforeAt st ⟨σ.block.place, 1⟩) := by
  have hfrN : J.fresh.isNone = false := by rw [hfr]; rfl
  obtain ⟨-, -, hall⟩ := any_at_place (V := Local W₀ Rc Xi Tr) J Js Fc _ b hf hbp hr hor hfrN hs ho
  obtain ⟨f1, f2, -, -, -⟩ := hall fs σ hσ
  have hσ' := hσ
  unfold testSide Side.seated at hσ'
  obtain ⟨b', hb', e⟩ := Option.map_eq_some_iff.1 hσ'
  have hbb : b' = b := Option.some.inj (hb'.symm.trans hf)
  subst hbb
  have hblk : σ.block ∈ F.first.blocksInOrder := by
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
  have l2 : (restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length =
      restLen J.p.nums.stages := by
    rw [rest_moves J s next rest hst]
    exact (List.length_map _).trans List.length_range
  have hpos' : (restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).moves.length ≠ 0 := by
    rw [l2]
    exact hpos
  obtain ⟨pre, t, S⟩ := stands_rest_own hpl hR J Js σ hblk hrow f1 hmem hpos' (proverSideOfProximityTest J) hg rfl
  have hzip : σ.block.rounds.zip σ.block.oracles = J.laid := by
    rw [eb, hr, hor]
    show _ = H2K.JointK.laidOf J.p
    exact zip_laid _ Fc.plan
  have hsh : σ.block.shaped = true := planOk_shaped_first hpl σ.block hblk
  have hol := shaped_len σ.block hsh
  have hlenb : σ.block.rounds.length = (H2K.JointK.laidOf J.p).length := by
    show _ = J.laid.length
    rw [← hzip, List.length_zip, hol, Nat.min_self]
  have hcut : F.first.blocksInOrder = pre ++ σ.block :: t := S.cut
  have g0 := draws_fit_first_chain (F := F) hρ pre t σ.block hcut (firstLen J.p.nums.stages)
    (by rw [hlenb]; exact Fc.enough)
  have e1 : ((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1) =
      σ.block.rounds.take (firstLen J.p.nums.stages) := by
    have hz : H2K.JointK.laidOf J.p = σ.block.rounds.zip σ.block.oracles := hzip.symm
    rw [List.map_take, hz, List.map_fst_zip (by rw [hol])]
  have hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.first.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true := by
    rw [e1]
    exact g0
  have hlen : ((ρ.first.drop (pre.flatMap (·.rounds)).length).take
      (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    have hh := ProofFile.Honest.drawsFit_length _ _ hfit
    rw [hh, List.length_map, List.length_take]
    exact Nat.min_eq_left Fc.enough
  have T : FirstTies J s next rest (byNo ((ρ.first.drop (pre.flatMap (·.rounds)).length).take
      (firstLen J.p.nums.stages)))
      ((ρ.first.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) :=
    ⟨hst, Fc.enough, FP.sorts, by rw [tablesFitB_eq, hfrN]; exact Fc.tab, hlen,
      fun n hn => (List.getD_eq_getElem _ _ hn).symm⟩
  obtain ⟨c, m, hm, hca, hin, le, leS, hF, hH, hFold⟩ := five_at_first (F := F) hpl J f
    hfr Js hR σ pre t S hg hzip hT s next rest _ T hk
    (fun w fr mem mem' hh => congrArg _ (hrows w fr mem mem' hh)) hfit hrun hc st
  exact ⟨pre, t, c, m, S, hm, hca, hin, ⟨le, leS, hF, hH, hFold⟩⟩

/-! ## The tree of a job of one member -/

section One
open Johnson.Prover.Send (mainSyms maskSyms shapeAt)
open OnBytes.Slice (GE ofE)
open Johnson.Prover.Link (PS symG_congr words3 packedN)
open H2K.Pub (sgOf)

variable {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type}

theorem mainSyms_congr (P : VerifiableInference.Desc.K1.Par) (U U' : ℕ → Johnson.Prover.Send.Rows) (k x : ℕ)
    (h : U k = U' k) : mainSyms P U k x = mainSyms P U' k x := by
  unfold mainSyms
  rw [h]

theorem maskSyms_congr (P : VerifiableInference.Desc.K1.Par) (U U' : ℕ → Johnson.Prover.Send.Rows) (k x : ℕ)
    (h : U k = U' k) : maskSyms P U k x = maskSyms P U' k x := by
  unfold maskSyms
  rw [h]

/-- **Two sendings' columns agree** where message 0 is one, and message 1 has one mask. -/
theorem col_two_messages (P : VerifiableInference.Desc.K1.Par) (U U' : ℕ → Johnson.Prover.Send.Rows) (x : ℕ)
    (hmine : (List.range P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree[k]? == some 0) = [0, 1])
    (h0 : U 0 = U' 0) (hm : (shapeAt P 1).mainRows = 0)
    (hz : ∀ r < (shapeAt P 1).maskRows, ∀ j < (P.codes.mask.getD (shapeAt P 1).maskCode default).ell,
      (U 1).mask r j = (U' 1).mask r j)
    (ht : ∀ r < (shapeAt P 1).maskRows, ∀ q < (P.codes.mask.getD (shapeAt P 1).maskCode default).r,
      (U 1).maskTl r q = (U' 1).maskTl r q) :
    col P U 0 x = col P U' 0 x := by
  rw [col_of_mine P U 0 x _ hmine, col_of_mine P U' 0 x _ hmine]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have e0 : ∀ T : ℕ → Johnson.Prover.Send.Rows, mainSyms P T 1 x = [] := fun T => by
    unfold mainSyms
    simp [hm]
  rw [e0, e0, mainSyms_congr P U U' 0 x h0, maskSyms_congr P U U' 0 x h0]
  have e1 : maskSyms P U 1 x = maskSyms P U' 1 x := by
    unfold maskSyms
    refine congrArg List.flatten (List.map_congr_left fun r hr => ?_)
    have hr' := List.mem_range.1 hr
    exact congrArg (fun y => words3 (ofE y)) (symG_congr _ _ _ _ _ _
      (fun j hj => hz r hr' j hj) fun q hq => ht r hr' q hq)
  rw [e1]

/-- **What a part of the first chain is lent is the sender's own coins**, message by message. -/
theorem k1_coins_same_chain {Bk : ProverCoinCounts} (k : Coins Bk) (a s : Addr)
    (Q : VerifiableInference.Desc.K1.Par) (ride : ℕ → Option K1.Ride) (own : Cs (K1.dueR Q ride))
    (hown : (k.look 0 s).2.cut ⟨0, 0⟩ (K1.dueR Q ride) = some own)
    (ds : List (String × Due)) (ca : CsAll ds) (hl : lend (k.look 0) ds (Light.carriedOf Bk a) = .ok ca)
    (n kk : ℕ) (hf : k1CutFits Bk a n s Q ride kk = true) :
    (∀ i, i < (K1.dueMsg Q.codes (shapeAt Q kk) (ride kk)).f →
      K1.cf own ((K1.startR Q ride kk).f + i) = (stretches ds ca n).f i) ∧
    (∀ i, i < (K1.dueMsg Q.codes (shapeAt Q kk) (ride kk)).e →
      K1.ce own ((K1.startR Q ride kk).e + i) = (stretches ds ca n).e i) := by
  unfold k1CutFits at hf
  split at hf
  · rename_i e he
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
    obtain ⟨⟨⟨⟨ho, hs⟩, hc⟩, b1⟩, b2⟩ := hf
    obtain ⟨x, hx, hst⟩ := lend_cut (k.look 0) ds _ ca hl n e he
    rw [hst]
    rw [ho] at hx
    obtain ⟨en, eo, es, ec, ep, eb⟩ := e
    dsimp only at ho hs hc b1 b2 hx
    subst hs hc
    exact lent_agrees _ own x hown hx b1 b2
  · cases hf

/-- **The clause trees at a job of one member**, from what ties its column to the sender's. -/
theorem trees_one_at {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₁ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre' t' : List (Block F.S₁ F.Cl)) (i : ℕ) (S : StandsAt F.first.blocksInOrder R.first σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (st : List (ℕ × ℕ × List UInt64))
    (p : VerifiableInference.Desc.K12.P12) (Q : OneSent (Local W₀ Rc Xi Tr))
    (rec₀ : Local W₀ Rc Xi Tr → Front Y → T12)
    (pre : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl) (t : List (Block F.S₁ F.Cl))
    (hcut : F.first.blocksInOrder = pre ++ b :: t) (hb : b.rounds ≠ [])
    (hin : (pre.flatMap (·.rounds)).length < (pre'.flatMap (·.rounds)).length + i)
    (J : K1.SendJob (Local W₀ Rc Xi Tr) Y)
    (hg : (P.first.find? fun g => g.place == b.place) =
      some (K1.proverSideOfSending (V := Local W₀ Rc Xi Tr) J))
    (j : ℕ) (sh : OnBytes.TreeShape) (hτ : J.P.trees[0]? = some sh)
    (hW : columnWidth J.P 0 = sh.mainWidth + sh.maskWidth)
    (hj : treesTo F.first.blocksInOrder pre.length + 0 = j) (o : Fmt.Shape × Fmt.TreeSource)
    (hlog : (Q.P.trees.getD 0 {}).logN = o.1.a) (hsrc : ProofFile.Honest.srcOf 0 o.2 = (0, j))
    (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y) (mem : ℕ → Stretch)
    (hcol : ∀ (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
      (c : (K1.sendPart (V := Local W₀ Rc Xi Tr) J :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).Coins),
      lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨b.place, 0⟩ (K1.sendPart (V := Local W₀ Rc Xi Tr) J) =
        .ok c →
      mᵢ.st.input = R.own → mᵢ.st.heard = ρ.first.take (pre.flatMap (·.rounds)).length → ∀ z,
      col Q.P (Q.rows m.st.input (mem 0) (rowsAt (jobOne p Q rec₀) mem m)) 0 z =
        col J.P (J.rows c.1 mᵢ.shown mᵢ.st 0) 0 z) :
    TreesAt (jobOne p Q rec₀) 0 [o] mem m (r.run.beforeAt st ⟨σ.block.place, u.number⟩) := by
  refine ⟨?_, fun n o' T ho hT => ?_⟩
  · show [(Q.P.trees.getD 0 {}).logN] = [o.1.a]
    rw [hlog]
  · match n, ho, hT with
    | 0, ho, hT =>
      obtain rfl : o = o' := Option.some.inj ho
      obtain rfl : ((Q.P.trees.getD 0 {}).logN,
          col Q.P (Q.rows m.st.input (mem 0) (rowsAt (jobOne p Q rec₀) mem m)) 0) = T :=
        Option.some.inj hT
      rw [hsrc]
      obtain ⟨mᵢ, c, cols, hl, hin', hh, hf, hq⟩ := k1_tree_first_stand hpl hR hrun σ u pre' t' i S hc
        pre b t hcut hb hin J hg 0 j sh hτ hW hj st
      refine ⟨cols, hf, fun q hq' => ?_⟩
      rw [hq q hq']
      exact (hcol mᵢ c hl hin' hh q.1).symm
    | _ + 1, ho, _ => cases ho

/-- **The public numbers of a sending of two messages, at a test's first stage.** -/
structure OneSenderPub (P : VerifiableInference.Desc.K1.Par) (ride : ℕ → Option K1.Ride)
    (s : Fmt.M1.Stage) : Prop where
  two : 0 < P.sent.size
  mine : (List.range P.sent.size).filter (fun k =>
    ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree[k]? == some 0) = [0, 1]
  main1 : (shapeAt P 1).mainRows = 0
  rows1 : (shapeAt P 1).maskRows = 2 ^ s.h
  ell : (P.codes.mask.getD (shapeAt P 1).maskCode default).ell = s.Z.l
  tail : (P.codes.mask.getD (shapeAt P 1).maskCode default).r = s.Z.r
  ride1 : ride 1 = some ⟨s.k, s.h⟩
  hk : s.h ≤ s.k
  room : 2 * s.k + 1 ≤ s.h + s.Z.l
  deg : ((shapeAt P 1).mainDeg == 3) = false
  due : 2 * s.k + 1 + 2 ^ s.h * s.Z.r ≤ (K1.dueMsg P.codes (shapeAt P 1) (ride 1)).e

/-- **The member's column is the sender's**, at the coins that the book lends. -/
theorem col_one_tie {W Wd : Type} {Bk : ProverCoinCounts} (k : Coins Bk) (a : Addr) (b : Place)
    (Q : OneSent W) (JS : K1.SendJob Wd Y) (hP : Q.P = JS.P) (hr : Q.ride = JS.ride)
    (w : W) (wd : Wd) (hd : ∀ fr, Q.data w = JS.data wd fr)
    (p : VerifiableInference.Desc.K12.P12) (rec₀ : W → Front Y → T12)
    (hN : OneSenderPub JS.P JS.ride (jobOne p Q rec₀).s₀)
    (ds : List (String × Due)) (ca : CsAll ds) (hl : lend (k.look 0) ds (Light.carriedOf Bk a) = .ok ca)
    (hf0 : k1CutFits Bk a 0 ⟨b, 0⟩ JS.P JS.ride 0 = true)
    (hf1 : k1CutFits Bk a 1 ⟨b, 0⟩ JS.P JS.ride 1 = true)
    (own : Cs (K1.dueR JS.P JS.ride))
    (hown : (k.look 0 ⟨b, 0⟩).2.cut ⟨0, 0⟩ (K1.dueR JS.P JS.ride) = some own)
    (sn : Seen) (t : State Wd Y) (ht : t.input = wd) (fr : Front Y) (z : ℕ) :
    col Q.P (Q.rows w (stretches ds ca 0) ((jobOne p Q rec₀).first w fr
        (carriedCoins (jobOne p Q rec₀) (stretches ds ca)))) 0 z =
      col JS.P (JS.rows own sn t 0) 0 z := by
  obtain ⟨f0, e0⟩ := k1_coins_same_chain k a ⟨b, 0⟩ JS.P JS.ride own hown ds ca hl 0 0 hf0
  obtain ⟨-, e1⟩ := k1_coins_same_chain k a ⟨b, 0⟩ JS.P JS.ride own hown ds ca hl 1 1 hf1
  subst ht
  obtain ⟨g1, g2⟩ := fresh_of_ride JS.P JS.ride
    (JS.data t.input { heard := t.heard.take (t.heard.length - 0), own := t.own, seen := sn.front 0 })
    own 1 _ hN.ride1 hN.hk hN.room hN.deg hN.rows1 hN.ell hN.tail (stretches ds ca 1).e
    fun i hi => e1 i (by have := hN.due; omega)
  rw [hP]
  refine col_two_messages JS.P _ _ z hN.mine ?_ hN.main1 (fun r hr' j hj => ?_) fun r hr' q hq => ?_
  · show K1.rowsR Q.P Q.ride (Q.data w) (csOfStretch _ (stretches ds ca 0)) 0 =
      K1.rowsR JS.P JS.ride (JS.data t.input _) own 0
    rw [hd { heard := t.heard.take (t.heard.length - 0), own := t.own, seen := sn.front 0 }]
    have e := ProofFile.Honest.K12.AtProof.rowsR_csAt JS.P JS.ride (JS.data t.input
            { heard := t.heard.take (t.heard.length - 0), own := t.own, seen := sn.front 0 }) 0 hN.two
      (stretches ds ca 0) own f0 e0
    have e' : ∀ (P' : VerifiableInference.Desc.K1.Par) (r' : ℕ → Option K1.Ride)
        (h₁ : P' = JS.P) (h₂ : r' = JS.ride),
        K1.rowsR P' r' (JS.data t.input
          { heard := t.heard.take (t.heard.length - 0), own := t.own, seen := sn.front 0 })
          (csOfStretch _ (stretches ds ca 0)) 0 =
        K1.rowsR JS.P JS.ride (JS.data t.input
          { heard := t.heard.take (t.heard.length - 0), own := t.own, seen := sn.front 0 }) own 0 := by
      intro P' r' h₁ h₂
      subst h₁ h₂
      exact e
    exact e' _ _ hP hr
  · have hr₂ : r < 2 ^ (jobOne p Q rec₀).s₀.h := by rw [← hN.rows1]; exact hr'
    have hj₂ : j < (jobOne p Q rec₀).s₀.Z.l := by rw [← hN.ell]; exact hj
    exact (g1 r hr₂ j hj₂).symm
  · have hr₂ : r < 2 ^ (jobOne p Q rec₀).s₀.h := by rw [← hN.rows1]; exact hr'
    have hq₂ : q < (jobOne p Q rec₀).s₀.Z.r := by rw [← hN.tail]; exact hq
    exact (g2 r hr₂ q hq₂).symm

end One

/-! ## On at a run -/

section Run
open VerifiableInference.Desc.Key (Xi rangesParams LaterPlaces Source)
open H2K.Member (piKRFull codesKeyFull)
open AtPublicFiles.AtFiles (keyFileDescription KeySourced)
open AtPublicFiles.KeyThread (rangesTestJob recRanges sentRanges place_sourced)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc Ky X₀ Y : Type}

theorem first_KR_one : piKRFull.nums.first = [piKRFull.nums.first.headD default] := rfl

theorem rest_KR : restLen piKRFull.nums.stages ≠ 0 := by decide +kernel

/-- **What is left at a stand**: the two clauses on the asks, at the job. -/
def LeftAtRanges (J : TestJob (Local W₀ Rc Xi Unit) Y) (K : OnBytes.Codes)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (mem : ℕ → Stretch)
    (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) Y) : Prop :=
  ∃ Dp cc Rw, Dp.ts.length = os.length ∧
    ShapeAsksD J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc Rw

/-- What stands on both sides of an element of a list with all keys different is one. -/
theorem cut_both {α β : Type} (f : α → β) (l pre t pre' t' : List α) (b : α)
    (h1 : l = pre ++ b :: t) (h2 : l = pre' ++ b :: t') (hn : (l.map f).Nodup) :
    pre = pre' ∧ t = t' := by
  subst h1
  exact cut_unique f _ _ _ _ _ h2 hn

/-- **The clause of the rule at the list of the test on the ranges.** What stays: hleft at each stand;
where the multiplicities' sender stands, its numbers and the book's two tests. -/
theorem onAtRun_ranges (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {Bk : ProverCoinCounts}
    {H : Prover W₀ Rc Xi Ky Unit X₀ Y}
    {G : Sides (keyFileDescription Xs N Pl) Bk W₀ Rc Ky Unit X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc Xi Ky Unit X₀ Y} {r : RunC (keyFileDescription Xs N Pl)}
    (T : ThreadsP (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hR : ready (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k ρ = .ok r)
    (entry : Local W₀ Rc Xi Unit → ℕ → ℕ → OnBytes.Slice.GF) (groups : List (List ℕ)) (first : ℕ)
    (L : Lettered Bk (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit)
      (Local W₀ Rc Xi Unit) Y Xi)
    (hplace : L.place = (rangesTestJob (X' := Y) Xs N Pl entry groups first).p.place)
    (hrow : L.row = testPairs (rangesTestJob (X' := Y) Xs N Pl entry groups first) (simRanges Xs N Pl))
    (hOn : L.On = OnEntry Face.own (rangesTestJob (X' := Y) Xs N Pl entry groups first) (simRanges Xs N Pl)
      codesKeyFull 0 piKRFull.nums.first)
    (hg : ((G.prover H).first.find? fun g =>
      g.place == (rangesTestJob (X' := Y) Xs N Pl entry groups first).p.place) =
        some (proverSideOfProximityTest (rangesTestJob (X' := Y) Xs N Pl entry groups first)))
    (hT : tiesB Bk (rangesTestJob (X' := Y) Xs N Pl entry groups first).p.place 1 = true)
    -- the sender
    (JS : K1.SendJob (Local W₀ Rc Xi Unit) Y)
    (hP : (sentRanges Xs entry groups first).P = JS.P)
    (hr' : (sentRanges Xs entry groups first).ride = JS.ride)
    (hd : ∀ w fr, (sentRanges Xs entry groups first).data w = JS.data w fr)
    (preS : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl))
    (bS : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)
    (tS : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl))
    (hcutS : (keyFileDescription Xs N Pl).first.blocksInOrder = preS ++ bS :: tS) (hbS : bS.rounds ≠ [])
    (hgS : ((G.prover H).first.find? fun g => g.place == bS.place) =
      some (K1.proverSideOfSending (V := Local W₀ Rc Xi Unit) JS))
    (hfront : ∀ (pre' t' : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl))
      (blk : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl),
      (keyFileDescription Xs N Pl).first.blocksInOrder = pre' ++ blk :: t' →
      blk.place = (rangesTestJob (X' := Y) Xs N Pl entry groups first).p.place →
      (preS.flatMap (·.rounds)).length <
        (pre'.flatMap (·.rounds)).length + firstLen piKRFull.nums.stages)
    (j : ℕ) (sh : OnBytes.TreeShape) (hτ : JS.P.trees[0]? = some sh)
    (hW : columnWidth JS.P 0 = sh.mainWidth + sh.maskWidth)
    (hj : treesTo (keyFileDescription Xs N Pl).first.blocksInOrder preS.length + 0 = j)
    (hlog : ((sentRanges Xs entry groups first).P.trees.getD 0 {}).logN =
      (piKRFull.nums.first.headD default).1.a)
    (hsrc : ProofFile.Honest.srcOf 0 (piKRFull.nums.first.headD default).2 = (0, j))
    (hN : OneSenderPub JS.P JS.ride (rangesTestJob (X' := Y) Xs N Pl entry groups first).s₀)
    (hf0 : k1CutFits Bk ⟨L.place, 1⟩ 0 ⟨bS.place, 0⟩ JS.P JS.ride 0 = true)
    (hf1 : k1CutFits Bk ⟨L.place, 1⟩ 1 ⟨bS.place, 0⟩ JS.P JS.ride 1 = true)
    (hleft : ∀ (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) Y)
      (ca : CsAll (restMember (V := Local W₀ Rc Xi Unit)
        (rangesTestJob (X' := Y) Xs N Pl entry groups first) (simRanges Xs N Pl)).part.carries)
      (σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Y Xi)
      (pre' t' : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)),
      testSide (keyFileDescription Xs N Pl).first.blocksInOrder (rangesTestJob (X' := Y) Xs N Pl entry groups first)
        (simRanges Xs N Pl) [] = some σ →
      StandsAt (keyFileDescription Xs N Pl).first.blocksInOrder R.first σ (restMember (V := Local W₀ Rc Xi Unit)
                            (rangesTestJob (X' := Y) Xs N Pl entry groups first) (simRanges Xs N Pl)) pre' t'
        (firstLen (rangesTestJob (X' := Y) Xs N Pl entry groups first).p.nums.stages) →
      InsideOf .own Bk 0 (G.prover H).first σ.block (T.I₁ pre'.length) (σ.roundsTo 1) k m
        (envOf (H.storedWords w₀ rc) (fun _ _ => none)
          (r.run.played.1.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1))) →
      m.seen = roundsOf (r.run.played.1.take ((pre'.flatMap (·.rounds)).length + σ.roundsTo 1)) →
      r.called ⟨L.place, 1⟩ = true →
      midAtW (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩ = .ok (some m) →
      carriedAt Bk k 0 ⟨L.place, 1⟩ (restMember (V := Local W₀ Rc Xi Unit)
        (rangesTestJob (X' := Y) Xs N Pl entry groups first) (simRanges Xs N Pl)).part = .ok ca →
      (laidOf (keyFileDescription Xs N Pl) ρ (r.run.played.1.take ((pre'.flatMap (·.rounds)).length +
                     σ.roundsTo 1)) [] []).front 0
          (storedShown (H.storedWords w₀ rc) (storedAsks (keyFileDescription Xs N Pl) ρ)) =
        r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨L.place, 1⟩ →
      LeftAtRanges (rangesTestJob (X' := Y) Xs N Pl entry groups first) codesKeyFull piKRFull.nums.first
        (stretches _ ca) m) :
    OnAtRun₁ T ρ r L := by
  intro σ hσ u hu pre' t' hcut m ca hin hseen hca hc hmid hfr
  have hpl : σ.block.place = L.place := side_place hσ
  have hp := place_sourced hS scope
  have hJ : (rangesTestJob (X' := Y) Xs N Pl entry groups first).p = piKRFull := hp
  have hσ' : testSide (keyFileDescription Xs N Pl).first.blocksInOrder (rangesTestJob (X' := Y) Xs N Pl entry groups first)
      (simRanges Xs N Pl) [] = some σ := by
    unfold testSide
    rw [← hplace, ← hrow]
    exact hσ
  obtain ⟨b, hf, hbp, hr, hor⟩ := find_ranges scope hS.named
    (rangesTestJob (X' := Y) Xs N Pl entry groups first) rfl
  have F : PlaceFacts (rangesTestJob (X' := Y) Xs N Pl entry groups first).p dsKR := by
    rw [hJ]
    exact facts_KRFull
  obtain ⟨-, -, hall⟩ := any_at_place (V := Local W₀ Rc Xi Unit)
    (rangesTestJob (X' := Y) Xs N Pl entry groups first) (simRanges Xs N Pl) F _ b hf hbp hr hor rfl hJ.symm
    rfl
  obtain ⟨-, hmem, -⟩ := hall [] σ hσ'
  rw [hOn, hfr]
  rw [hmem] at hu
  rcases List.mem_cons.1 hu with rfl | hu'
  · intro hn
    cases hn
  obtain rfl := List.mem_singleton.1 hu'
  have hpos : restLen (rangesTestJob (X' := Y) Xs N Pl entry groups first).p.nums.stages ≠ 0 := by
    rw [hJ]
    exact rest_KR
  have hg' : ((G.prover H).first.find? fun g => g.place == σ.block.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := Y) Xs N Pl entry groups first)) := by
    rw [hpl, hplace]
    exact hg
  have hc' : r.called ⟨σ.block.place, 1⟩ = true := by
    rw [hpl]
    exact hc
  obtain ⟨pre, t, c, m₁, S, hm₁, hca₁, hin₁, F5⟩ := five_at_test hS.named.plan hρ hR
    (rangesTestJob (X' := Y) Xs N Pl entry groups first) F (AtPublicFiles.KeyTest.sMsg, 1) rfl
    (fun w fr mem mem' hh => ProofFile.Honest.K12.rows_one _ _ _ w fr mem mem' hh) (simRanges Xs N Pl)
    hJ.symm rfl [] σ hσ' b hf hbp hr hor hg' hT hrun hc' hpos
    (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
  have hndF := (places_nodup (((keyFileDescription Xs N Pl).planOk_ok).1 hS.named.plan).places).1
  obtain ⟨rfl, rfl⟩ := cut_both (fun b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl => b.place)
    _ _ _ _ _ _ hcut S.cut hndF
  obtain ⟨m', hm', -, -, -, -, -, hse, -⟩ := frame_at_first hS.named.plan hR hrun σ
    (restMember (V := Local W₀ Rc Xi Unit) (rangesTestJob (X' := Y) Xs N Pl entry groups first) (simRanges Xs N Pl))
    _ _ _ _ S rfl hc' (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
  obtain rfl : m₁ = m' := Option.some.inj (Except.ok.inj (hm₁.symm.trans hm'))
  rw [hpl] at hm₁ hca₁ hse F5
  have hmid' : orRefused (midAtW (keyFileDescription Xs N Pl) Bk (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩) =
      .ok m := hmid
  rw [hm₁] at hmid'
  obtain rfl : m₁ = m := Except.ok.inj (show (Except.ok m₁ : Except Refusal _) = .ok m from hmid')
  obtain rfl : c.2.1.2.2 = ca := Except.ok.inj (hca₁.symm.trans hca)
  have hca₂ := hca
  unfold carriedAt at hca₂
  obtain ⟨c₁, hl₁, e₁⟩ := exMap_ok hca₂
  have hcar := carried_of_lendPart _ _ _ _ _ c₁ hl₁
  rw [e₁] at hcar
  have hn : firstLen (rangesTestJob (X' := Y) Xs N Pl entry groups first).p.nums.stages =
      firstLen piKRFull.nums.stages := by
    rw [hJ]
  have hinS := hfront _ _ σ.block S.cut (hpl.trans hplace)
  rw [← hn] at hinS
  refine onEntry_of_free Face.own _ _ _ 0 _ _ _ m₁ _ ?_
  refine ⟨F5.le, F5.leS, F5.heardFit, F5.heard,
    recRanges_is_view m₁.st.input _ _ (rest_seen _ m₁ _ hse), F5.fold,
    hleft m₁ _ σ _ _ hσ' S hin hseen hc hm₁ hca hfr, ?_⟩
  have hTr := trees_one_at hS.named.plan hR hrun σ
    (restMember (V := Local W₀ Rc Xi Unit) (rangesTestJob (X' := Y) Xs N Pl entry groups first) (simRanges Xs N Pl))
    _ _ _ S hc' (storedShown (H.storedWords w₀ rc) r.run.storedAsked) (rangesParams N) (sentRanges Xs entry groups first) (recRanges Xs N Pl) preS bS tS
    hcutS hbS hinS JS hgS j sh hτ hW hj (piKRFull.nums.first.headD default) hlog hsrc m₁ _
    (fun mᵢ c' hl hi hh z => by
      have e : mᵢ.st.input = m₁.st.input := hi.trans hin₁.symm
      exact col_one_tie k ⟨L.place, 1⟩ bS.place (sentRanges Xs entry groups first) JS hP hr'
        m₁.st.input mᵢ.st.input (fun fr => by rw [e]; exact hd _ fr) (rangesParams N)
        (recRanges Xs N Pl) hN _ _ hcar hf0 hf1 c'.1 (own_of_lendPart hl) mᵢ.shown mᵢ.st rfl _ z)
  rw [hpl] at hTr
  exact hTr

end Run

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.k1_tree_first_stand
#print axioms ProofFile.Honest.K12.Sim2.rest_seen
#print axioms ProofFile.Honest.K12.Sim2.five_at_test
#print axioms ProofFile.Honest.K12.Sim2.col_two_messages
#print axioms ProofFile.Honest.K12.Sim2.k1_coins_same_chain
#print axioms ProofFile.Honest.K12.Sim2.trees_one_at
#print axioms ProofFile.Honest.K12.Sim2.col_one_tie
#print axioms ProofFile.Honest.K12.Sim2.onAtRun_ranges
