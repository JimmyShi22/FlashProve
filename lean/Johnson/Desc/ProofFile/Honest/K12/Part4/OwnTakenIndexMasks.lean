--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/OwnTakenIndexMasks.lean: THE KEY FILE's OWN PROXIMITY TEST:
TREE NUMBER 0 OF THE JOB IS THE TABLE OF THE INDEX MASKS' SENDING: the proof of `TakenIndexMasks`
(K12/Part4/OwnTakenStatements.lean).

WHAT IT IS NOT. All that the head of the statements' file says it is not. NOT IN FRONT OF A LAW OVER
COINS. Under `OwnTestGround`, whose fields on letters can be false at a filling. The closed lines are
evaluations by Lean's kernel at written values: that a public file has these values is not said.
THIS MEMBER IS ALL COINS: the message has no main row, so no data is read. Nothing on completeness,
on soundness or on what is hidden.

  `indexBookB`, `indexBook_full`   the key file's book at the written sizes: the first entry that the
                 test's second part carries is all 305 coins of the sender; the sender has a row in
                 the first chain alone
  `IndexFacts`, `indexFacts_written`   the public facts of the member, general in the parameters; and
                 at the written values, field by field by Lean's kernel
  `takenIndexMasks`   the statement

CALLED: `member_held` (K12/AtProof/HandedW.lean) · `rowsR_csAt` (K12/AtProof/JobW.lean) ·
`rowsR_no_main` (K12/AtProof/SendersW.lean) · `column_three`, `depth_three`
(K12/AtFile/WJointTree.lean) · `cut_of_due` (K12/DepthsOfText.lean) · this folder's
OwnTakenPieces.lean and, for the members and the lending, OwnTakenOmega.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Part4.OwnTakenOmega
import Johnson.Desc.ProofFile.Honest.K12.Part4.OwnTakenPieces
import Johnson.Desc.ProofFile.Honest.K12.TreesSentBeforeTestAtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Part4
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource)
open H2K.Member (piKWFull)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull)
open AtPublicFiles.KeyFile (KeyParts In1 In2 randK14)
open AtPublicFiles.KeyLay (jobKWAt parIK parWK pWK)
open AtPublicFiles.KeyTest (sIdx sW)
open AtPublicFiles.AtFiles.Full (QK)
open Johnson.Prover.Send (col mainSyms maskSyms)
open ProofFile.Honest.K14 (jobOmega)
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (memK1 csAt rowsR_csAt rowsR_no_main member_held)
open ProofFile.Honest.K12.AtFile (TakenIs)

/-- The book's lines at the index masks' member. -/
def indexBookB (K : KeyPub) : Bool :=
  (((carryE (keyBook K) ⟨piKWFull.place, 1⟩)[0]?).map fun e => (e.owner, e.start, e.count)) ==
      some (sIdx, ⟨0, 0⟩, ⟨0, 305⟩) &&
    dueAt (keyBook K).first sIdx == ⟨0, 305⟩ &&
    !((keyBook K).shared.any fun r => r.1 == sIdx) &&
    !((keyBook K).second.any fun r => r.1 == sIdx)

/-- **The book's lines hold at the written sizes.** By Lean's kernel. -/
theorem indexBook_full : atFull indexBookB = true := by decide +kernel

/-- **The public facts of the index masks' member.** -/
structure IndexFacts (PI PW : VerifiableInference.Desc.K1.Par) (J : K14.SendJob)
    (ride : ℕ → Option K1.Ride) (q : VerifiableInference.Desc.K12.P12) : Prop where
  size : PI.sent.size = 1
  noMain : (Johnson.Prover.Send.shapeAt PI 0).mainRows = 0
  code : OnBytes.Slice.codeOf
    (PI.codes.mask.getD (Johnson.Prover.Send.shapeAt PI 0).maskCode default) =
      (q.nums.stages.headD default).Z
  room : ((firstRows PI PW J).getD 0 (none, none)).2.getD 0 +
    (Johnson.Prover.Send.shapeAt PI 0).maskRows ≤ 2 ^ (q.nums.stages.headD default).h
  plan : VerifiableInference.Desc.K1.planOkOwn PI = true
  trees : 0 < PI.trees.length
  logN : (PI.trees.getD 0 {}).logN = 13
  width : (PI.trees.getD 0 {}).mainWidth + (PI.trees.getD 0 {}).maskWidth = 3
  mine : ((List.range PI.sent.size).filter fun k =>
    ((VerifiableInference.Desc.Own.treesMade PI.codes PI.sent).getD {}).tree[k]? == some 0) = [0]
  depth : Light.depthOf q 0 = 13
  start : K1.startR PI ride 0 = ⟨0, 0⟩
  count : K1.dueMsg PI.codes (Johnson.Prover.Send.shapeAt PI 0) (ride 0) = ⟨0, 305⟩
  due : K1.dueR PI ride = ⟨0, 305⟩

/-- **They hold at the written values.** Field by field, by Lean's kernel. -/
theorem indexFacts_written :
    IndexFacts parIK parWK (jobOmega ⟨QK, 0⟩) (fun _ => none) piKWFull where
  size := by decide +kernel
  noMain := by decide +kernel
  code := by decide +kernel
  room := by decide +kernel
  plan := by decide +kernel
  trees := by decide +kernel
  logN := by decide +kernel
  width := by decide +kernel
  mine := by decide +kernel
  depth := by decide +kernel
  start := by decide +kernel
  count := by decide +kernel
  due := by decide +kernel

/-- The facts read of the two sendings their codes and messages alone. -/
theorem IndexFacts.alike {PI' PI PW' PW : VerifiableInference.Desc.K1.Par} {J : K14.SendJob}
    {ride : ℕ → Option K1.Ride} {q : VerifiableInference.Desc.K12.P12}
    (F : IndexFacts PI PW J ride q) (hc : PI'.codes = PI.codes) (hI : PI'.sent = PI.sent)
    (hW : PW'.sent = PW.sent) : IndexFacts PI' PW' J ride q :=
  { size := by rw [hI]; exact F.size
    noMain := by rw [shapeAt_alike hI]; exact F.noMain
    code := by rw [hc, shapeAt_alike hI]; exact F.code
    room := by rw [firstRows_alike hI hW, shapeAt_alike hI]; exact F.room
    plan := by rw [planOwn_congr PI' PI hc hI]; exact F.plan
    trees := by rw [trees_alike hc hI]; exact F.trees
    logN := by rw [trees_alike hc hI]; exact F.logN
    width := by rw [trees_alike hc hI]; exact F.width
    mine := by rw [hc, hI]; exact F.mine
    depth := F.depth
    start := by rw [startR_alike hc hI]; exact F.start
    count := by rw [hc, shapeAt_alike hI]; exact F.count
    due := by rw [dueR_alike hc hI]; exact F.due }

section
variable {S Cl V Pb W₀ Rc X₀ X Wk : Type} {K₀ : KeyPub}
  {T : Thread (keyBook K₀) S Cl V (In1 W₀ Rc) X Pb} {K : KeyParts W₀ Rc X₀ X Wk} {Xs : Source}
  {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {toCommon : In1 W₀ Rc → In2 W₀ Rc}

/-- The first rows do not read the number of "LIN point". -/
theorem firstRows_moved (PI PW : VerifiableInference.Desc.K1.Par) (P : Desc.K14.P14) (a b : ℕ) :
    firstRows PI PW (jobOmega ⟨P, a⟩) = firstRows PI PW (jobOmega ⟨P, b⟩) := by
  unfold firstRows
  rw [omega_par P a b]

/-- The public facts at the parts. -/
theorem index_facts_at (G : OwnTestGround T K Xs Nr Pl toCommon) :
    IndexFacts K.idx.P K.w.P (omegaMoved K Xs Nr Pl) K.idx.ride (pWK Pl) := by
  have h : IndexFacts K.idx.P K.w.P (jobOmega ⟨K.send.P, 0⟩) K.idx.ride (pWK Pl) := by
    rw [G.senders.idxRide, G.senders.sendPar, G.place]
    exact indexFacts_written.alike G.senders.idxCodes G.senders.idxSent G.senders.wSent
  exact ⟨h.size, h.noMain, h.code, by rw [firstRows_moved _ _ _ _ 0]; exact h.room, h.plan, h.trees,
    h.logN, h.width, h.mine, h.depth, h.start, h.count, h.due⟩

/-- The book's lines at the book of the ground. -/
theorem index_book_at (G : OwnTestGround T K Xs Nr Pl toCommon) :
    ∃ e, (carryE (keyBook K₀) ⟨(ownTestJob K Xs Nr Pl).p.place, 1⟩)[0]? = some e ∧
      e.owner = sIdx ∧ e.start = ⟨0, 0⟩ ∧ e.count = ⟨0, 305⟩ ∧
      dueAt (keyBook K₀).first sIdx = ⟨0, 305⟩ ∧
      ((keyBook K₀).shared.any fun r => r.1 == sIdx) = false ∧
      ((keyBook K₀).second.any fun r => r.1 == sIdx) = false := by
  have hB : indexBookB K₀ = true := by
    have h := indexBook_full
    unfold atFull at h
    rw [G.book] at h
    exact h
  unfold indexBookB at hB
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hB
  obtain ⟨⟨⟨hE, hdue⟩, hshared⟩, hsecond⟩ := hB
  obtain ⟨e, he, q⟩ := Option.map_eq_some_iff.1 hE
  obtain ⟨eo, es, ec⟩ : e.owner = sIdx ∧ e.start = ⟨0, 0⟩ ∧ e.count = ⟨0, 305⟩ := by
    simpa [Prod.mk.injEq] using q
  refine ⟨e, ?_, eo, es, ec, hdue, hshared, hsecond⟩
  show (carryE (keyBook K₀) ⟨(pWK Pl).place, 1⟩)[0]? = some e
  rw [G.place]
  exact he

/-- The sender's own coins are there, at all of a run's coins. -/
theorem index_cut (G : OwnTestGround T K Xs Nr Pl toCommon) (k : Coins (keyBook K₀)) :
    ∃ c₀ : Cs (K1.dueR K.idx.P K.idx.ride),
      K1.lentCut k 0 ⟨K.idx.P.place, 0⟩ (K1.dueR K.idx.P K.idx.ride) = some c₀ := by
  have F := index_facts_at G
  obtain ⟨e, he, eo, es, ec, hdue, hshared, hsecond⟩ := index_book_at G
  have hplace : (⟨K.idx.P.place, 0⟩ : Addr) = sIdx := by
    rw [G.idxPlace]
    rfl
  rw [hplace]
  exact Option.isSome_iff_exists.1 (cut_of_due k 0 (Nat.zero_le 1) sIdx
    (K1.dueR K.idx.P K.idx.ride) (by
      show _ ≤ (dueAt (keyBook K₀).first sIdx).f ∧ _ ≤ (dueAt (keyBook K₀).first sIdx).e
      rw [F.due, hdue]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩))

/-- **The sender's own coins are there, and at the message's coins the stretch that the test carries
reads them.** -/
theorem index_coins (G : OwnTestGround T K Xs Nr Pl toCommon) {k : Coins (keyBook K₀)}
    {c : OwnTestCoins V K Xs Nr Pl} (hl : Lent T K Xs Nr Pl k c) :
    ∃ c₀ : Cs (K1.dueR K.idx.P K.idx.ride),
      K1.lentCut k 0 ⟨K.idx.P.place, 0⟩ (K1.dueR K.idx.P K.idx.ride) = some c₀ ∧
      (∀ i, i < (K1.dueMsg K.idx.P.codes (Johnson.Prover.Send.shapeAt K.idx.P 0)
          (K.idx.ride 0)).f →
        K1.cf c₀ ((K1.startR K.idx.P K.idx.ride 0).f + i) =
          ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 0).f i) ∧
      ∀ i, i < (K1.dueMsg K.idx.P.codes (Johnson.Prover.Send.shapeAt K.idx.P 0)
          (K.idx.ride 0)).e →
        K1.ce c₀ ((K1.startR K.idx.P K.idx.ride 0).e + i) =
          ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 0).e i := by
  have F := index_facts_at G
  obtain ⟨e, he, eo, es, ec, hdue, hshared, hsecond⟩ := index_book_at G
  have hplace : (⟨K.idx.P.place, 0⟩ : Addr) = sIdx := by
    rw [G.idxPlace]
    rfl
  obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.1 (cut_of_due k 0 (Nat.zero_le 1) sIdx
    (K1.dueR K.idx.P K.idx.ride) (by
      show _ ≤ (dueAt (keyBook K₀).first sIdx).f ∧ _ ≤ (dueAt (keyBook K₀).first sIdx).e
      rw [F.due, hdue]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩))
  refine ⟨c₀, ?_, member_held k (lent_second G hl) he K.idx.P K.idx.ride 0
    (by rw [F.size]; exact Nat.zero_lt_one) (by rw [es, F.start]) (by rw [ec, F.count])
    (by rw [eo, hdue, F.due]) (by rw [eo]; exact hshared) (by rw [eo]; exact hsecond)
    (by rw [eo]; exact hc₀)⟩
  rw [hplace]
  exact hc₀

/-- The member's rows, of the stretch that the test carries. -/
abbrev indexRows (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums)
    (Pl : LaterPlaces) (m : Mid (In1 W₀ Rc) X) (c : OwnTestCoins V K Xs Nr Pl) :
    Johnson.Prover.Send.Rows :=
  K1.rowsR K.idx.P K.idx.ride (K.idx.data (id m.st.input) (frontOf m))
    (csAt _ (K1.startR K.idx.P K.idx.ride 0)
      ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 0)) 0

/-- **They are the rows that the sender lays**, at every list of challenges. -/
theorem index_rows (G : OwnTestGround T K Xs Nr Pl toCommon) (m : Mid (In1 W₀ Rc) X)
    {c : OwnTestCoins V K Xs Nr Pl} (c₀ : Cs (K1.dueR K.idx.P K.idx.ride))
    (hf : ∀ i, i < (K1.dueMsg K.idx.P.codes (Johnson.Prover.Send.shapeAt K.idx.P 0)
        (K.idx.ride 0)).f →
      K1.cf c₀ ((K1.startR K.idx.P K.idx.ride 0).f + i) =
        ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 0).f i)
    (he : ∀ i, i < (K1.dueMsg K.idx.P.codes (Johnson.Prover.Send.shapeAt K.idx.P 0)
        (K.idx.ride 0)).e →
      K1.ce c₀ ((K1.startR K.idx.P K.idx.ride 0).e + i) =
        ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 0).e i)
    (h : List Fmt.Drawn) :
    K1.rowsLaid K.idx K.own₀ c₀ (id m.st.input) h 0 = indexRows K Xs Nr Pl m c := by
  have F := index_facts_at G
  unfold indexRows K1.rowsLaid
  rw [rowsR_csAt K.idx.P K.idx.ride _ 0 (by rw [F.size]; exact Nat.zero_lt_one) _ c₀ hf he]
  exact rowsR_no_main _ _ _ _ _ 0 F.noMain

/-- **The job's column of tree 0, the first rows of the blocks as letters.** -/
theorem index_column (G : OwnTestGround T K Xs Nr Pl toCommon) (m : Mid (In1 W₀ Rc) X)
    (c : OwnTestCoins V K Xs Nr Pl) (fs0 fs1 fs2 : Option ℕ × Option ℕ)
    (hm : (ownTestJob K Xs Nr Pl).mems =
      [memK1 K.idx id sIdx 0 fs0, memK1 K.w id sW 0 fs1,
        memOfSending (omegaMoved K Xs Nr Pl) AtProof.senderO 0 fs2 (askAt K) none])
    (room : fs0.2.getD 0 + (Johnson.Prover.Send.shapeAt K.idx.P 0).maskRows ≤
      2 ^ ((pWK Pl).nums.stages.headD default).h) (x : ℕ) :
    ((ownTestTrees K Xs Nr Pl m c).getD 0 (0, fun _ => [])).2 x =
      (List.range (Johnson.Prover.Send.shapeAt K.idx.P 0).maskRows).flatMap fun r =>
        Johnson.Prover.Link.words3 (OnBytes.Slice.ofE (Johnson.Prover.Link.symG
          ((pWK Pl).nums.stages.headD default).Z
          (x % 2 ^ ((pWK Pl).nums.stages.headD default).Z.a)
          ((indexRows K Xs Nr Pl m c).mask r) ((indexRows K Xs Nr Pl m c).maskTl r))) := by
  have F := index_facts_at G
  obtain ⟨t1, t2⟩ := first_three_mask (ownTestJob K Xs Nr Pl) _ _ _ hm m.st.input (frontOf m)
    (restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1)
  rw [column_three (ownTestJob K Xs Nr Pl) _ _ _ hm m.st.input (frontOf m) _ _ 0
    (Light.depthOf (pWK Pl) 0) [.mask 0] rfl x]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [mask_piece_first (ownTestJob K Xs Nr Pl).s₀ _ _ _ _ _ _ (indexRows K Xs Nr Pl m c).mask
    (indexRows K Xs Nr Pl m c).maskTl (Johnson.Prover.Send.shapeAt K.idx.P 0).maskRows _ x
    (by
      rw [stage_own, ← F.code]
      rfl)
    (by
      rw [stage_own, ← F.code]
      rfl)
    (by rw [shape_ofK1])
    (by
      rw [shape_ofK1, stage_own]
      exact room) t1 t2, stage_own]

end

theorem takenIndexMasks : TakenIndexMasks := by
  intro S Cl V Pb W₀ Rc X₀ X Wk K₀ T K Xs Nr Pl toCommon G k m c hl
  have F := index_facts_at G
  obtain ⟨c₀, hcut, hf, he⟩ := index_coins G hl
  obtain ⟨td, -, tc⟩ := treeTbl_at 0 id K.idx K.own₀ 0 k c₀ hcut F.plan F.trees m.st.input
    (m.st.heard.take (T.fixed (.taken 0 0)))
  have hk0 : K.idx.P.sent.size - 1 = 0 := by rw [F.size]
  have hm := members_own K Xs Nr Pl
  rw [hk0] at hm
  refine ⟨?_, fun x _ => ?_⟩
  · rw [depth_three (ownTestJob K Xs Nr Pl) _ _ _ hm m.st.input (frontOf m) _ _ 0
      (Light.depthOf (pWK Pl) 0) [.mask 0] rfl, F.depth]
    show 13 = (T.table (.taken 0 0) k m.st.input _).2.logLength
    rw [G.tables.indexMasks, td, F.logN]
  · show (T.table (.taken 0 0) k m.st.input (m.st.heard.take (T.fixed (.taken 0 0)))).2.col x = _
    rw [G.tables.indexMasks, tc x, col_of_mine _ _ 0 x [0] F.mine,
      index_column G m c _ _ _ hm F.room x]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have e1 : mainSyms K.idx.P (K1.rowsLaid K.idx K.own₀ c₀ (id m.st.input)
        (m.st.heard.take (T.fixed (.taken 0 0)))) 0 x = [] := by
      unfold mainSyms
      simp only [F.noMain, List.range_zero, List.flatMap_nil]
    rw [e1, List.nil_append]
    unfold maskSyms
    simp only [index_rows G m c₀ hf he, F.code]

end ProofFile.Honest.K12.Part4

#print axioms ProofFile.Honest.K12.Part4.indexBook_full
#print axioms ProofFile.Honest.K12.Part4.indexFacts_written
#print axioms ProofFile.Honest.K12.Part4.IndexFacts.alike
#print axioms ProofFile.Honest.K12.Part4.index_facts_at
#print axioms ProofFile.Honest.K12.Part4.index_book_at
#print axioms ProofFile.Honest.K12.Part4.index_cut
#print axioms ProofFile.Honest.K12.Part4.index_coins
#print axioms ProofFile.Honest.K12.Part4.index_rows
#print axioms ProofFile.Honest.K12.Part4.index_column
#print axioms ProofFile.Honest.K12.Part4.takenIndexMasks
