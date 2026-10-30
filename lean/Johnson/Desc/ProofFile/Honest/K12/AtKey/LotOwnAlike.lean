-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnAlike.lean: THE PUBLIC PREMISES OF THE TIE, AND THE CLAUSE `says`, UNDER WHAT IS
READ of the two sendings' parameters: the notices and the codes.

Why. A sending's parameters hold besides the place, the groups that its messages are told to join and the plan's numbers;
`parIK` and `parWK` write groups := []. At parts whose sendings are made with the description's own groups the record
equations K.idx.P = parIK, K.w.P = parWK fail. The tie reads `sent` and `codes` alone.

  `SendersPlansAlike`        the notices, the codes and the rides of the two sendings are the written ones; the shared
                             chain's parameters are `QK`
  `plansAlike_of_ownSenders`, `ownSenders_of_plansAlike`, `plansAlike_iff_ownSenders`
                             IT IS `OwnSenders` (OwnJob.lean) UNDER OTHER FIELD NAMES: each gives the other, field by field
  `book_of_alike`, `plan_of_alike`, `statement_of_alike`   the three structures of LotOwnWords.lean under it
  `says_clause_of_alike`     `SaysAt` at a stand of the key file's own test under it

By what. `book_lines_full`, `statement_closed` (LotOwnLines.lean, LotOwnStatement.lean): the same kernel lines;
`counts_of_alike`, `carries_of_alike` (LotOwnLines.lean): `dueR`, `startR`, `shapeAt` unfold to `codes` and `sent`.

Limits.
- As LotOwnStand.lean's. K.send.P = QK stays a record equation: in scope the description's own parameters are `QK`
  (`par_sourced`, E2E/KeyShapeSharedTies.lean).
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnStand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (Group)
open OnBytes.Means (AllSay sampleItem)
open OnBytes.Slice (rdE)
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc.Ground.Sh (stTidyB)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi Claim descriptionFromSource)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open H2K.Member (piKWFull)
open AtPublicFiles.KeyLay (pWK parIK parWK)
open AtPublicFiles.AtFiles (Sh₃ sh₃ SF ZW)
open AtPublicFiles.AtFiles.Full (X0 QK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub rideW)
open AtPublicFiles.KeyFile (KeyParts)
open ProofFile.Honest.K12.Light (SaysAt)

variable {V Pb W₀ Rc X₀ X Wk : Type} {K₀ : KeyPub} {Xs : Source} {Nr : H2U.PlaceNums}
  {Pl : LaterPlaces}

/-- **What the tie reads of the parts' public data.** -/
structure SendersPlansAlike (K : KeyParts W₀ Rc X₀ X Wk) : Prop where
  indexMasksNotices : K.idx.P.sent = parIK.sent
  indexMasksCodes : K.idx.P.codes = parIK.codes
  indexMasksRide : K.idx.ride = fun _ => none
  vectorWNotices : K.w.P.sent = parWK.sent
  vectorWCodes : K.w.P.codes = parWK.codes
  vectorWRide : K.w.ride = rideW
  sharedPlan : K.send.P = QK

/-- `OwnSenders` gives it, field by field. -/
theorem plansAlike_of_ownSenders {K : KeyParts W₀ Rc X₀ X Wk} (h : OwnSenders K) :
    SendersPlansAlike K :=
  ⟨h.idxSent, h.idxCodes, h.idxRide, h.wSent, h.wCodes, h.wRide, h.sendPar⟩

/-- It gives `OwnSenders`, field by field. -/
theorem ownSenders_of_plansAlike {K : KeyParts W₀ Rc X₀ X Wk} (h : SendersPlansAlike K) :
    OwnSenders K :=
  ⟨h.indexMasksNotices, h.indexMasksCodes, h.indexMasksRide, h.vectorWNotices, h.vectorWCodes,
    h.vectorWRide, h.sharedPlan⟩

/-- **The two structures are one.** -/
theorem plansAlike_iff_ownSenders {K : KeyParts W₀ Rc X₀ X Wk} :
    SendersPlansAlike K ↔ OwnSenders K :=
  ⟨ownSenders_of_plansAlike, plansAlike_of_ownSenders⟩

variable {K : KeyParts W₀ Rc X₀ X Wk}

/-- **`BookAtOwnTest` at the key file's book.** -/
theorem book_of_alike (hK₀ : fullPub = some K₀) (h : SendersPlansAlike K)
    (hPl : pWK Pl = piKWFull) : BookAtOwnTest (keyBook K₀) K (pWK Pl).place := by
  have b := book_lines_full
  unfold AtPublicFiles.KeyBook.atFull at b
  rw [hK₀] at b
  have b' : bookLinesAtOwnTest (keyBook K₀) piKWFull.place = true := b
  unfold bookLinesAtOwnTest at b'
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at b'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, r0⟩, r1⟩, r2⟩, n0⟩, n1⟩, n2⟩, n3⟩, n4⟩, n5⟩ := b'
  rw [hPl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, n0, n1, n2, n3, n4, n5⟩
  · rw [carries_of_alike h.indexMasksNotices h.indexMasksCodes, h.indexMasksRide,
      h.indexMasksNotices]
    exact c0
  · rw [carries_of_alike h.vectorWNotices h.vectorWCodes, h.vectorWRide]
    exact c1
  · rw [h.sharedPlan]
    exact c2
  · rw [(counts_of_alike h.indexMasksNotices h.indexMasksCodes _).1, h.indexMasksRide]
    exact r0
  · rw [(counts_of_alike h.vectorWNotices h.vectorWCodes _).1, h.vectorWRide]
    exact r1
  · rw [h.sharedPlan]
    exact r2

/-- **`SharedPlanAtOwnTest` at the written plan.** -/
theorem plan_of_alike (h : SendersPlansAlike K) : SharedPlanAtOwnTest K.send.P := by
  rw [h.sharedPlan]
  exact ⟨ProofFile.Honest.K12.Light.KeyDoorUClosed.sendings_U, length_full,
    AtPublicFiles.AtFiles.Full.plan2_full,
    K14.sendShapes_of_fit ProofFile.Honest.K12.Light.KeyDoorUClosed.sendings_U⟩

/-- **`StatementAtOwnTest` at a state of the closed shape.** -/
theorem statement_of_alike (h : SendersPlansAlike K) {A₀ A₂ : Sh₃} (h₀ : X0 = some A₀)
    (h₂ : ZW.run 2 A₀ = .ok A₂) {st : S₃} (hsh : sh₃ SF st = A₂)
    (challengesBeforeVectorW challengesOfFirstChain : ℕ) :
    StatementAtOwnTest st.st st.loc.own K
      (numbersAtFullSize challengesBeforeVectorW challengesOfFirstChain) := by
  have c := statement_closed
  unfold statementClosedB at c
  rw [h₀] at c
  have c₁ : (match ZW.run 2 A₀ with
    | .ok b => statementLinesB (id b)
    | .error _ => false) = true := c
  rw [h₂] at c₁
  have c₂ : statementLinesB A₂ = true := c₁
  unfold statementLinesB at c₂
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c₂
  obtain ⟨⟨⟨⟨⟨⟨gm, s0⟩, s9⟩, s11⟩, cd⟩, n1⟩, n2⟩ := c₂
  subst hsh
  have orc : ∀ i : ℕ, (st.st.oracles[i]?).map (fun x : OnBytes.Oracle => x.shape) =
      (((sh₃ SF st).1.st.oracles[i]?).map
        fun x : VerifiableInference.Desc.Ground.Sh.OrcSh => x.shape) := fun i => by
    show _ = (((VerifiableInference.Desc.Ground.Sh.stSh st.st).oracles[i]?).map
      fun x : VerifiableInference.Desc.Ground.Sh.OrcSh => x.shape)
    rw [VerifiableInference.Desc.Ground.Sh.orc_get, Option.map_map]
    rfl
  have z1 : K.idx.P.sent.size = 1 := by rw [h.indexMasksNotices]; exact n1
  have z2 : K.w.P.sent.size = 2 := by rw [h.vectorWNotices]; exact n2
  refine ⟨fun G hG => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (sh₃ SF st).1.st.groups[(sh₃ SF st).2.own]? =
        some (VerifiableInference.Desc.Ground.Sh.grpSh G) := by
      show (VerifiableInference.Desc.Ground.Sh.stSh st.st).groups[st.loc.own]? = _
      rw [VerifiableInference.Desc.Ground.Sh.grp_get, hG]
      rfl
    rw [e] at gm
    have g' : ((VerifiableInference.Desc.Ground.Sh.grpSh G).members == [0, 9, 11]) = true := gm
    have g'' : G.members.toList = [0, 9, 11] := beq_iff_eq.1 g'
    rw [z1]
    exact Array.toList_inj.1 g''
  · rw [z1, z2]
    show 0 + 1 ≤ 9 ∧ 9 + 2 ≤ 11
    exact ⟨by decide, by decide⟩
  · rw [z1]
    decide
  · rw [z2]
    decide
  · rw [z1, (counts_of_alike h.indexMasksNotices h.indexMasksCodes fun _ => none).2.2]
    exact (orc _).trans s0
  · rw [(counts_of_alike h.vectorWNotices h.vectorWCodes fun _ => none).2.2]
    exact (orc _).trans s9
  · rw [h.sharedPlan]
    exact (orc _).trans s11
  · rw [h.sharedPlan]
    exact cd

/-- **`SaysAt` AT A STAND OF THE KEY FILE's OWN TEST, UNDER `SendersPlansAlike`.** NOT IN FRONT OF A
LAW OVER COINS: LotOwnStand.lean's head. -/
theorem says_clause_of_alike (hK₀ : fullPub = some K₀) (K : KeyParts W₀ Rc X₀ X Wk)
    {T : Thread (keyBook K₀) S₃ Claim V (Local W₀ Rc Xi Unit) X Pb}
    {Said : ℕ → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop}
    (stand : StandFactsAtOwnTest T Said (jobAtKeyOwnTest K Xs Nr Pl))
    (written : pWK Pl = piKWFull) (senders : SendersPlansAlike K)
    (challengesBeforeVectorW challengesOfFirstChain : ℕ)
    (hfirst : challengesOfFirstChain = ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length)
    (reads : SendersReadInFront K
      (numbersAtFullSize challengesBeforeVectorW challengesOfFirstChain))
    (rounds : RoundsInFrontOfOwnTest T Xs Nr Pl K.send.P.par.S.kCol)
    (openRows : ∀ k st m E, ThrS T Said 2 k st m E → ∀ G : Group,
      st.st.groups[st.loc.own]? = some G → AllSay rdE st.st G.rows.toList
        (wordsAtKeyOwnTest K (numbersAtFullSize challengesBeforeVectorW challengesOfFirstChain) k
          m.st.input m.st.heard))
    (sampleRows : ∀ k st m E, ThrS T Said 2 k st m E → ∀ G : Group,
      st.st.groups[st.loc.own]? = some G → sampleItem rdE st.st G.members.toList
        (wordsAtKeyOwnTest K (numbersAtFullSize challengesBeforeVectorW challengesOfFirstChain) k
          m.st.input m.st.heard)) :
    ∀ k st m E (c : RowCoins [(firstPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest :
        Part V (Local W₀ Rc Xi Unit) X), restPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest]),
      ThrS T Said 2 k st m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf T.chain) (k.look T.chain)
        (jobAtKeyOwnTest K Xs Nr Pl).p.place
        [(firstPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest :
          Part V (Local W₀ Rc Xi Unit) X), restPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest] 0 =
          .ok c →
      SaysAt (jobAtKeyOwnTest K Xs Nr Pl) m.st.input (frontOf m)
        (restCoins (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest c.2.1) := by
  intro k st m E c u hc
  obtain ⟨A₀, A₂, h₀, h₂, hL, -, -⟩ := own_closed
  obtain ⟨hen, hsh⟩ := stand k st m E u A₀ A₂ h₀ h₂
  have htidy : stTidyB st.st = true := by
    rw [← (show (sh₃ SF st).2.tidy = stTidyB st.st from rfl), hsh]
    exact tidy_of_line hL
  have hS := statement_of_alike senders h₀ h₂ hsh challengesBeforeVectorW challengesOfFirstChain
  obtain ⟨d, rest, hr, hd⟩ := rounds.point
  have hfit : drawsFit ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds) ++ d :: rest) m.st.heard =
      true := by
    rw [← hr]
    exact u.1.2.1
  have hear := heard_at_own_test K
    (numbersAtFullSize challengesBeforeVectorW challengesOfFirstChain) _ d rest m.st.heard hfit
    hfirst.symm hd
  rw [rounds.chain] at hc
  exact says_at_stand _ _ _ _ hen htidy _ (openSays_of_group _ _ _ (openRows k st m E u))
    (sampleRows k st m E u)
    (wordsTied_at_key_own_test K Xs Nr Pl _ reads (book_of_alike hK₀ senders written)
      (plan_of_alike senders) hfirst k m.st.input (frontOf m) m.st.heard hear c hc st.st
      st.loc.own hS)

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.SendersPlansAlike
#print axioms ProofFile.Honest.K12.AtKey.plansAlike_of_ownSenders
#print axioms ProofFile.Honest.K12.AtKey.ownSenders_of_plansAlike
#print axioms ProofFile.Honest.K12.AtKey.plansAlike_iff_ownSenders
#print axioms ProofFile.Honest.K12.AtKey.book_of_alike
#print axioms ProofFile.Honest.K12.AtKey.plan_of_alike
#print axioms ProofFile.Honest.K12.AtKey.statement_of_alike
#print axioms ProofFile.Honest.K12.AtKey.says_clause_of_alike
