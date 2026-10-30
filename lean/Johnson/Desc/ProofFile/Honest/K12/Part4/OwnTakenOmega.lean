--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/OwnTakenOmega.lean: THE KEY FILE's OWN PROXIMITY TEST: TREE
NUMBER 2 OF THE JOB IS THE TABLE OF "send o_omega": the proof of `TakenOmega`
(K12/Part4/OwnTakenStatements.lean).

WHAT IT IS NOT. All that the head of the statements' file says it is not. NOT IN FRONT OF A LAW OVER
COINS. Under `OwnTestGround`, whose fields on letters can be false at a filling. The sixteen closed
lines are evaluations by Lean's kernel at written values: that a public file has these values is not
said.
Nothing on completeness, on soundness or on what is hidden.

  `omegaBookB`, `omegaBook_full`   the key file's book at the written sizes: the third entry that the
                 test's second part carries is the sender's coins from 0 on, 1,177 of its 1,387; the
                 sender has a row in the shared chain alone
  `OmegaFacts`, `omegaFacts_written`   the public facts of Omega's member, general in the two sendings'
                 parameters, the shared chain's and the place; and at the written values, field by
                 field by Lean's kernel
  `takenOmega`   the statement

CALLED: `taken_omega`, `omega_data_behind`, `cut_same_due` (K12/AtFile/WJointTaken.lean) ·
`tree_third_column` (WJointOmega.lean) · `depth_three` (WJointTree.lean) · `member_held_shared`
(K12/AtProof/HandedW.lean) · `mem_rows_below` (K12/LaidBelow.lean) · `omega_rows_are_sent`
(K12/AtProof/LettersOmega.lean) · `lendRow_snd` (K12/CutOfBook.lean) · `cut_of_due`,
`sendTable_depth` (K12/DepthsOfText.lean).
-/
import Johnson.Desc.ProofFile.Honest.K12.Part4.OwnTakenStatements
import Johnson.Desc.ProofFile.Honest.K12.Part4.OwnTakenPieces
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointTaken
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HandedW
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LettersOmega
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook
import Johnson.Desc.ProofFile.Honest.K12.DepthsOfText

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Part4
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource)
open H2K.Member (piKWFull)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull)
open AtPublicFiles.KeyFile (KeyParts In1 In2 randK14)
open AtPublicFiles.KeyLay (jobKWAt parIK parWK pWK)
open AtPublicFiles.AtFiles.Full (QK)
open ProofFile.Honest.K14 (SendPub jobOmega sendingPart dueOf)
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (senderO shapesW memShape member_held_shared omega_rows_are_sent)
open ProofFile.Honest.K12.AtFile (TakenIs)

/-- The book's lines at Omega's member. -/
def omegaBookB (K : KeyPub) : Bool :=
  (((carryE (keyBook K) ⟨piKWFull.place, 1⟩)[2]?).map fun e => (e.owner, e.start, e.count)) ==
      some (senderO, ⟨0, 0⟩, ⟨0, 1177⟩) &&
    dueAt (keyBook K).shared senderO == ⟨0, 1387⟩ &&
    !((keyBook K).first.any fun r => r.1 == senderO) &&
    !((keyBook K).second.any fun r => r.1 == senderO)

/-- **The book's lines hold at the written sizes.** By Lean's kernel. -/
theorem omegaBook_full : atFull omegaBookB = true := by decide +kernel

/-- The first rows of the three members' blocks. PI, PW: the two sendings' parameters. J: Omega's
sending. -/
abbrev firstRows (PI PW : VerifiableInference.Desc.K1.Par) (J : K14.SendJob) :
    List (Option ℕ × Option ℕ) :=
  firstsOf (shapesW PI PW (J.Q.sent.getD 0 default).shape)

/-- **The public facts of Omega's member.** J: Omega's sending: of it the parameters and the sorts
alone are read. high: the sort of its messages. -/
structure OmegaFacts (PI PW : VerifiableInference.Desc.K1.Par) (J : K14.SendJob) (high : Bool)
    (q : VerifiableInference.Desc.K12.P12) : Prop where
  stage : (q.nums.stages.headD default).h ≤ (q.nums.stages.headD default).k
  code : sameCode (J.Q.codes.base.getD (shapeAt J 0).code default)
    (q.nums.stages.headD default).C = true
  base : ((shapeAt J 0).mainDeg == 1) = false
  room : ((firstRows PI PW J).getD 2 (none, none)).1.getD 0 + (shapeAt J 0).mainRows ≤
    2 ^ (q.nums.stages.headD default).k
  clear₀ : (Johnson.Prover.Send.shapeAt PI (PI.sent.size - 1)).mainRows = 0
  clear₁ : ((firstRows PI PW J).getD 2 (none, none)).1.getD 0 + (shapeAt J 0).mainRows ≤
    ((firstRows PI PW J).getD 1 (none, none)).1.getD 0
  mine : mineOf J 0 = [0]
  noMask : (shapeAt J 0).maskRows = 0
  rows : (shapeAt J 0).mainRows = 12
  width : widthFits J 0 = true
  depth : Light.depthOf q 2 = 22
  tree : (((VerifiableInference.Desc.Own.treesMade J.Q.codes J.Q.sent).getD {}).shapes.toList.map
    (·.logN)) = [22, 13]
  words : (((VerifiableInference.Desc.Own.treesMade J.Q.codes J.Q.sent).getD {}).shapes.toList.map
    fun t => t.mainWidth + t.maskWidth).getD 0 0 = 36
  due : dueOf J.Q.codes (shapeAt J 0) (.plain high) = 1177
  takes : (sendingPart J).takes = ⟨0, 1387⟩

/-- **They hold at the written values.** Field by field, by Lean's kernel. -/
theorem omegaFacts_written :
    OmegaFacts parIK parWK (jobOmega ⟨QK, 0⟩) QK.S.omegaRowsHigh piKWFull where
  stage := by decide +kernel
  code := by decide +kernel
  base := by decide +kernel
  room := by decide +kernel
  clear₀ := by decide +kernel
  clear₁ := by decide +kernel
  mine := by decide +kernel
  noMask := by decide +kernel
  rows := by decide +kernel
  width := by decide +kernel
  depth := by decide +kernel
  tree := by decide +kernel
  words := by decide +kernel
  due := by decide +kernel
  takes := by decide +kernel

/-- The facts read of the sending its parameters and its sorts alone. -/
theorem OmegaFacts.congr {PI PW : VerifiableInference.Desc.K1.Par} {J J' : K14.SendJob}
    {high : Bool} {q : VerifiableInference.Desc.K12.P12} (F : OmegaFacts PI PW J high q)
    (hQ : J'.Q = J.Q) (hs : J'.sort = J.sort) : OmegaFacts PI PW J' high q := by
  have e1 : ∀ k, shapeAt J' k = shapeAt J k := fun k => by
    unfold shapeAt
    rw [hQ]
  have e2 : ∀ μ, mineOf J' μ = mineOf J μ := fun μ => by
    unfold mineOf
    rw [hQ]
  have e3 : widthFits J' 0 = widthFits J 0 := by
    unfold widthFits
    simp only [e1, e2, hQ]
  have e4 : (sendingPart J').takes = (sendingPart J).takes := by
    show K14.takesOf J'.Q.codes J'.Q.sent J'.sort = K14.takesOf J.Q.codes J.Q.sent J.sort
    rw [hQ, hs]
  have e5 : firstRows PI PW J' = firstRows PI PW J := by
    unfold firstRows
    rw [hQ]
  exact
    { stage := F.stage
      code := by rw [hQ, e1]; exact F.code
      base := by rw [e1]; exact F.base
      room := by rw [e5, e1]; exact F.room
      clear₀ := F.clear₀
      clear₁ := by rw [e5, e1]; exact F.clear₁
      mine := by rw [e2]; exact F.mine
      noMask := by rw [e1]; exact F.noMask
      rows := by rw [e1]; exact F.rows
      width := by rw [e3]; exact F.width
      depth := F.depth
      tree := by rw [hQ]; exact F.tree
      words := by rw [hQ]; exact F.words
      due := by rw [hQ, e1]; exact F.due
      takes := by rw [e4]; exact F.takes }

/-- The first rows read of the two sendings their messages alone. -/
theorem firstRows_alike {PI' PI PW' PW : VerifiableInference.Desc.K1.Par} (hI : PI'.sent = PI.sent)
    (hW : PW'.sent = PW.sent) (J : K14.SendJob) : firstRows PI' PW' J = firstRows PI PW J := by
  unfold firstRows AtProof.shapesW
  rw [shapeAt_alike hI, shapeAt_alike hW, hI]

/-- The facts read of the two sendings of the kind K1 their messages alone. -/
theorem OmegaFacts.alike {PI' PI PW' PW : VerifiableInference.Desc.K1.Par} {J : K14.SendJob}
    {high : Bool} {q : VerifiableInference.Desc.K12.P12} (F : OmegaFacts PI PW J high q)
    (hI : PI'.sent = PI.sent) (hW : PW'.sent = PW.sent) : OmegaFacts PI' PW' J high q :=
  { stage := F.stage, code := F.code, base := F.base
    room := by rw [firstRows_alike hI hW]; exact F.room
    clear₀ := by rw [shapeAt_alike hI, hI]; exact F.clear₀
    clear₁ := by rw [firstRows_alike hI hW]; exact F.clear₁
    mine := F.mine, noMask := F.noMask, rows := F.rows, width := F.width, depth := F.depth
    tree := F.tree, words := F.words, due := F.due, takes := F.takes }

/-- Two sendings with these facts have as many main rows in message 0. -/
theorem OmegaFacts.rowsSame {PI PW : VerifiableInference.Desc.K1.Par} {J J' : K14.SendJob}
    {high : Bool} {q : VerifiableInference.Desc.K12.P12} (F : OmegaFacts PI PW J high q)
    (F' : OmegaFacts PI PW J' high q) : (shapeAt J' 0).mainRows = (shapeAt J 0).mainRows := by
  rw [F.rows, F'.rows]

/-- Omega's sending's parameters do not read the number of "LIN point". -/
theorem omega_par (P : Desc.K14.P14) (a b : ℕ) : (jobOmega ⟨P, a⟩).Q = (jobOmega ⟨P, b⟩).Q := by
  simp only [jobOmega]

/-- Nor do its sorts. -/
theorem omega_sort (P : Desc.K14.P14) (a b : ℕ) :
    (jobOmega ⟨P, a⟩).sort = (jobOmega ⟨P, b⟩).sort := by
  simp only [jobOmega]

section
variable {S Cl V Pb W₀ Rc X₀ X Wk : Type} {K₀ : KeyPub}
  {T : Thread (keyBook K₀) S Cl V (In1 W₀ Rc) X Pb} {K : KeyParts W₀ Rc X₀ X Wk} {Xs : Source}
  {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {toCommon : In1 W₀ Rc → In2 W₀ Rc}

/-- The reader of the shared chain's rows. -/
abbrev askAt (K : KeyParts W₀ Rc X₀ X Wk) : In1 W₀ Rc → K14.Ask :=
  askOf K.send (fun w => K.weights w.w₀) fun w => randK14 (K.rand w.rc)

/-- How many rounds the first chain has. -/
abbrev firstRounds (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) : ℕ :=
  ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length

/-- Omega's sending as the job's member has it: the number of "LIN point" moved by the first chain's
rounds. -/
abbrev omegaMoved (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums)
    (Pl : LaterPlaces) : K14.SendJob :=
  jobOmega ⟨K.send.P, firstRounds Xs Nr Pl + K.send.atPoint⟩

/-- Omega's member of the job. -/
abbrev omegaMember (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums)
    (Pl : LaterPlaces) : Mem (In1 W₀ Rc) X :=
  memOfSending (omegaMoved K Xs Nr Pl) senderO 0
    ((firstRows K.idx.P K.w.P (omegaMoved K Xs Nr Pl)).getD 2 (none, none)) (askAt K) none

/-- The job's three members. -/
theorem members_own (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums)
    (Pl : LaterPlaces) : (ownTestJob K Xs Nr Pl).mems =
      [AtProof.memK1 K.idx id AtPublicFiles.KeyTest.sIdx (K.idx.P.sent.size - 1)
          ((firstRows K.idx.P K.w.P (omegaMoved K Xs Nr Pl)).getD 0 (none, none)),
        AtProof.memK1 K.w id AtPublicFiles.KeyTest.sW 0
          ((firstRows K.idx.P K.w.P (omegaMoved K Xs Nr Pl)).getD 1 (none, none)),
        omegaMember K Xs Nr Pl] := rfl

/-- The public facts at the parts, at every number of "LIN point". -/
theorem facts_at (G : OwnTestGround T K Xs Nr Pl toCommon) (a : ℕ) :
    OmegaFacts K.idx.P K.w.P (jobOmega ⟨K.send.P, a⟩) K.send.P.S.omegaRowsHigh (pWK Pl) := by
  have h : OmegaFacts K.idx.P K.w.P (jobOmega ⟨K.send.P, 0⟩) K.send.P.S.omegaRowsHigh
      (pWK Pl) := by
    rw [G.senders.sendPar, G.place]
    exact omegaFacts_written.alike G.senders.idxSent G.senders.wSent
  exact h.congr (omega_par _ _ _) (omega_sort _ _ _)

/-- The book's lines at the book of the ground. -/
theorem book_at (G : OwnTestGround T K Xs Nr Pl toCommon) :
    ∃ e, (carryE (keyBook K₀) ⟨(ownTestJob K Xs Nr Pl).p.place, 1⟩)[2]? = some e ∧
      e.owner = senderO ∧ e.start = ⟨0, 0⟩ ∧ e.count = ⟨0, 1177⟩ ∧
      dueAt (keyBook K₀).shared senderO = ⟨0, 1387⟩ ∧
      ((keyBook K₀).first.any fun r => r.1 == senderO) = false ∧
      ((keyBook K₀).second.any fun r => r.1 == senderO) = false := by
  have hB : omegaBookB K₀ = true := by
    have h := omegaBook_full
    unfold atFull at h
    rw [G.book] at h
    exact h
  unfold omegaBookB at hB
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hB
  obtain ⟨⟨⟨hE, hdue⟩, hfirst⟩, hsecond⟩ := hB
  obtain ⟨e, he, q⟩ := Option.map_eq_some_iff.1 hE
  obtain ⟨eo, es, ec⟩ : e.owner = senderO ∧ e.start = ⟨0, 0⟩ ∧ e.count = ⟨0, 1177⟩ := by
    simpa [Prod.mk.injEq] using q
  refine ⟨e, ?_, eo, es, ec, hdue, hfirst, hsecond⟩
  show (carryE (keyBook K₀) ⟨(pWK Pl).place, 1⟩)[2]? = some e
  rw [G.place]
  exact he

/-- What the frame lends the second part. -/
theorem lent_second (G : OwnTestGround T K Xs Nr Pl toCommon) {k : Coins (keyBook K₀)}
    {c : OwnTestCoins V K Xs Nr Pl} (hl : Lent T K Xs Nr Pl k c) :
    lendPart (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) ⟨(ownTestJob K Xs Nr Pl).p.place, 1⟩
      (restPart (ownTestJob K Xs Nr Pl).toRun.toTest : Part V (In1 W₀ Rc) X) = .ok c.2.1 := by
  have h := lendRow_snd _ _ _ _ _ _ c hl
  rw [G.tables.chain] at h
  exact h

/-- The sender's own coins are there, at all of a run's coins. -/
theorem omega_cut (G : OwnTestGround T K Xs Nr Pl toCommon) (k : Coins (keyBook K₀)) :
    ∃ own : Cs (sendingPart (jobOmega K.send)).takes,
      (k.look 1 ⟨K14.sendPlace 5, 0⟩).2.cut ⟨0, 0⟩ (sendingPart (jobOmega K.send)).takes =
        some own := by
  obtain ⟨e, he, eo, es, ec, hdue, hfirst, hsecond⟩ := book_at G
  have htk : (sendingPart (jobOmega K.send)).takes = ⟨0, 1387⟩ := (facts_at G K.send.atPoint).takes
  exact Option.isSome_iff_exists.1 (cut_of_due k 1 (Nat.le_refl 1) senderO
    (sendingPart (jobOmega K.send)).takes (by
      show _ ≤ (dueAt (keyBook K₀).shared senderO).f ∧ _ ≤ (dueAt (keyBook K₀).shared senderO).e
      rw [htk, hdue]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩))

/-- **The sender's own coins are there, and the stretch that the test carries reads them.** -/
theorem omega_coins (G : OwnTestGround T K Xs Nr Pl toCommon) {k : Coins (keyBook K₀)}
    {c : OwnTestCoins V K Xs Nr Pl} (hl : Lent T K Xs Nr Pl k c) :
    ∃ own : Cs (sendingPart (jobOmega K.send)).takes,
      (k.look 1 ⟨K14.sendPlace 5, 0⟩).2.cut ⟨0, 0⟩ (sendingPart (jobOmega K.send)).takes =
        some own ∧
      ∃ c₀ : Cs ⟨0, 1387⟩, coinsE c₀ = coinsE own ∧ ∀ i, i < 1177 →
        ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 2).e i = (stretchOf c₀).e i := by
  obtain ⟨e, he, eo, es, ec, hdue, hfirst, hsecond⟩ := book_at G
  have htk : (sendingPart (jobOmega K.send)).takes = ⟨0, 1387⟩ := (facts_at G K.send.atPoint).takes
  obtain ⟨own, hown⟩ := Option.isSome_iff_exists.1 (cut_of_due k 1 (Nat.le_refl 1) senderO
    (sendingPart (jobOmega K.send)).takes (by
      show _ ≤ (dueAt (keyBook K₀).shared senderO).f ∧ _ ≤ (dueAt (keyBook K₀).shared senderO).e
      rw [htk, hdue]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩))
  obtain ⟨c₀, hc₀, ecoins⟩ := cut_same_due htk hown
  have held := member_held_shared k (lent_second G hl) he (t := ⟨0, 1387⟩) (by rw [eo]; exact hdue)
    (by rw [eo]; exact hfirst) (by rw [eo]; exact hsecond) es (by rw [ec])
    (by rw [ec]; decide) (by rw [eo]; exact hc₀)
  refine ⟨own, hown, c₀, ecoins, fun i hi => held i ?_⟩
  rw [ec]
  exact hi

/-- **The member's data is the sender's**, at the challenges that the table reads. -/
theorem omega_data (G : OwnTestGround T K Xs Nr Pl toCommon) (m : Mid (In1 W₀ Rc) X) :
    (omegaMoved K Xs Nr Pl).data ⟨askAt K m.st.input, (frontOf m).heard, ()⟩ 0 =
      (jobOmega K.send).data ⟨K14.witOf K.send.P K.weights (fun c => randK14 (K.rand c))
          (toCommon m.st.input),
        (m.st.heard.take (T.fixed (.taken 1 1))).drop (firstRounds Xs Nr Pl), ()⟩ 0 := by
  rw [G.tables.fixed _ (by simp [AtKey.takenOwn])]
  refine omega_data_behind K.send.P _ K.send.atPoint
    (AtPublicFiles.KeyThread.sentIn (AtPublicFiles.KeyThread.decl₂ (descriptionFromSource Xs Nr Pl)) 1) _ _ ?_ m.st.heard G.omegaReads
  show K14.rowsOf K.send.P.S (K.weights m.st.input.w₀) (randK14 (K.rand m.st.input.rc)) =
    K14.rowsOf K.send.P.S (K.weights (toCommon m.st.input).w₀)
      (randK14 (K.rand (toCommon m.st.input).rc))
  rw [G.tables.index, G.tables.committed]

/-- **The member's rows at the stretch that the test carries are the sender's rows at its own
coins.** -/
theorem omega_rows (G : OwnTestGround T K Xs Nr Pl toCommon) (m : Mid (In1 W₀ Rc) X) {c : OwnTestCoins V K Xs Nr Pl} (c₀ : Cs ⟨0, 1387⟩)
    (held : ∀ i, i < 1177 →
      ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 2).e i = (stretchOf c₀).e i) :
    (omegaMember K Xs Nr Pl).rows m.st.input (frontOf m)
        ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 2) =
      rowsOfLaid (jobOmega K.send).Q.codes ((jobOmega K.send).Q.sent.getD 0 default).shape
        ((jobOmega K.send).rows ⟨K14.witOf K.send.P K.weights (fun c => randK14 (K.rand c))
            (toCommon m.st.input),
          (m.st.heard.take (T.fixed (.taken 1 1))).drop (firstRounds Xs Nr Pl), ()⟩
          (coinsE c₀).toArray 0) := by
  refine (mem_rows_below (omegaMoved K Xs Nr Pl) senderO 0 _ (askAt K) none
    K.send.P.S.omegaRowsHigh rfl m.st.input (frontOf m) _ (stretchOf c₀) fun i hi => held i ?_).trans
    (omega_rows_are_sent K.send _ senderO _ _ m.st.input (frontOf m) _ (omega_data G m) c₀ ?_)
  · rw [← (facts_at G (firstRounds Xs Nr Pl + K.send.atPoint)).due]
    exact hi
  · have h := (facts_at G K.send.atPoint).due
    show dueOf (jobOmega K.send).Q.codes (shapeAt (jobOmega K.send) 0) _ ≤ 1387
    rw [h]
    decide

/-- **The table's depth.** -/
theorem omega_depth (G : OwnTestGround T K Xs Nr Pl toCommon) (k : Coins (keyBook K₀))
    (m : Mid (In1 W₀ Rc) X) {own : Cs (sendingPart (jobOmega K.send)).takes}
    (hown : (k.look 1 ⟨K14.sendPlace 5, 0⟩).2.cut ⟨0, 0⟩ (sendingPart (jobOmega K.send)).takes =
      some own) : (T.tableAt (.taken 1 1) k m).2.logLength = 22 := by
  have F := facts_at G K.send.atPoint
  show (T.table (.taken 1 1) k m.st.input _).2.logLength = 22
  rw [G.tables.omega]
  show (K14.sendTable (jobOmega K.send) _ (K14.sendPlace 5) 1 0 k _ _).2.logLength = 22
  rw [sendTable_depth _ _ _ _ _ _ _ _ (by rw [hown]; rfl) (by
    have h := congrArg List.length F.tree
    rw [List.length_map] at h
    rw [h]
    decide), F.tree]
  rfl

end

section
variable {S Cl V Pb W₀ Rc X₀ X Wk : Type} {K₀ : KeyPub}
  {T : Thread (keyBook K₀) S Cl V (In1 W₀ Rc) X Pb} {K : KeyParts W₀ Rc X₀ X Wk} {Xs : Source}
  {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {toCommon : In1 W₀ Rc → In2 W₀ Rc}

/-- The job's first stage is the place's. -/
theorem stage_own (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums)
    (Pl : LaterPlaces) :
    (ownTestJob K Xs Nr Pl).s₀ = (pWK Pl).nums.stages.headD default := rfl

/-- **The job's column of tree 2, the first rows of the blocks as letters.** -/
theorem omega_column (G : OwnTestGround T K Xs Nr Pl toCommon) (m : Mid (In1 W₀ Rc) X)
    (c : OwnTestCoins V K Xs Nr Pl) (fs0 fs1 fs2 : Option ℕ × Option ℕ)
    (hm : (ownTestJob K Xs Nr Pl).mems =
      [AtProof.memK1 K.idx id AtPublicFiles.KeyTest.sIdx (K.idx.P.sent.size - 1) fs0,
        AtProof.memK1 K.w id AtPublicFiles.KeyTest.sW 0 fs1,
        memOfSending (omegaMoved K Xs Nr Pl) senderO 0 fs2 (askAt K) none])
    (room : fs2.1.getD 0 + 12 ≤ 2 ^ ((pWK Pl).nums.stages.headD default).k)
    (clear : fs2.1.getD 0 + 12 ≤ fs1.1.getD 0) (L : ℕ → K14.Laid)
    (hrows : (memOfSending (omegaMoved K Xs Nr Pl) senderO 0 fs2 (askAt K) none).rows m.st.input
        (frontOf m) ((restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem 2) =
      rowsOfLaid (jobOmega K.send).Q.codes ((jobOmega K.send).Q.sent.getD 0 default).shape (L 0))
    (x : ℕ) :
    ((ownTestTrees K Xs Nr Pl m c).getD 2 (0, fun _ => [])).2 x =
      K14.columnOf (jobOmega K.send).Q.codes (jobOmega K.send).Q.sent L 0 x := by
  have F := facts_at G K.send.atPoint
  have Fm := facts_at G (firstRounds Xs Nr Pl + K.send.atPoint)
  refine tree_third_column (ownTestJob K Xs Nr Pl) _ _ K.send
    (firstRounds Xs Nr Pl + K.send.atPoint) senderO fs2 (askAt K) hm
    (d := Light.depthOf (pWK Pl) 2) rfl m.st.input (frontOf m)
    (restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1) x L hrows F.stage F.code ?_ ?_
    (fun r _ => ?_) (fun r hr => ?_) F.mine F.noMask
  · rw [shape_ofSending]
    exact Fm.base
  · rw [shape_ofSending, stage_own, F.rows]
    exact room
  · rw [shape_ofK1, shape_ofSending]
    show ¬ (fs0.1.getD 0 ≤ fs2.1.getD 0 + r ∧ fs2.1.getD 0 + r < fs0.1.getD 0 +
      (Johnson.Prover.Send.shapeAt K.idx.P (K.idx.P.sent.size - 1)).mainRows)
    rw [F.clear₀]
    omega
  · rw [F.rows] at hr
    rw [shape_ofK1, shape_ofSending]
    show ¬ (fs1.1.getD 0 ≤ fs2.1.getD 0 + r ∧ _)
    omega

end

theorem takenOmega : TakenOmega := by
  intro S Cl V Pb W₀ Rc X₀ X Wk K₀ T K Xs Nr Pl toCommon G k m c hl
  obtain ⟨own, hown, c₀, ecoins, held⟩ := omega_coins G hl
  have hrows := omega_rows G m c₀ held
  rw [ecoins] at hrows
  have F := facts_at G K.send.atPoint
  have Fm := facts_at G (firstRounds Xs Nr Pl + K.send.atPoint)
  have room := Fm.room
  have clear := Fm.clear₁
  rw [Fm.rows] at room clear
  have hm := members_own K Xs Nr Pl
  refine taken_omega T k m _ (jobOmega K.send) _ (K14.sendPlace 5) _ toCommon G.tables.omega hown
    F.width ?_ fun x => ?_
  · rw [omega_depth G k m hown, depth_three (ownTestJob K Xs Nr Pl) _ _ _ hm
      m.st.input (frontOf m) _ _ 2 (Light.depthOf (pWK Pl) 2) [.main 2] rfl]
    exact F.depth
  · exact omega_column G m c _ _ _ hm room clear _ hrows x

end ProofFile.Honest.K12.Part4

#print axioms ProofFile.Honest.K12.Part4.omegaBook_full
#print axioms ProofFile.Honest.K12.Part4.omegaFacts_written
#print axioms ProofFile.Honest.K12.Part4.OmegaFacts.congr
#print axioms ProofFile.Honest.K12.Part4.firstRows_alike
#print axioms ProofFile.Honest.K12.Part4.OmegaFacts.alike
#print axioms ProofFile.Honest.K12.Part4.members_own
#print axioms ProofFile.Honest.K12.Part4.facts_at
#print axioms ProofFile.Honest.K12.Part4.book_at
#print axioms ProofFile.Honest.K12.Part4.lent_second
#print axioms ProofFile.Honest.K12.Part4.omega_cut
#print axioms ProofFile.Honest.K12.Part4.omega_coins
#print axioms ProofFile.Honest.K12.Part4.omega_data
#print axioms ProofFile.Honest.K12.Part4.omega_rows
#print axioms ProofFile.Honest.K12.Part4.omega_depth
#print axioms ProofFile.Honest.K12.Part4.omega_column
#print axioms ProofFile.Honest.K12.Part4.takenOmega
