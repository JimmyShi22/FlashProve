-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/PaysAtHead.lean: the closing of a segment (K10): under the library's head, at the book of whatever the maker
`onlineProverFromPublicFiles` returns, at any filling, each side of the closings' lot pays (`SidePays`, Honest/Law/ReadyOfSides.lean): at the
closing's block `chainSteps` returns, at every view and every run's coins.

  `xs_at_head`, `pars_at_head`, `borne_at_head`   the places that the lot reads and the lists that its parts carry are the written
                    ones (AtFullSide/K10/PaysWritten.lean)
  `close_block`     a place that the lot reads has its block in the chain, with the closing's rounds
  `sidePays_job`    a side with the closing's one part pays, at the written book
  **`sidePays_close`**   each side of `seatLotC` pays at the maker's book; the filling is a letter
  `sidePays_closeLotAt`   the same of the closings' list at the wide filling
  **`kindPays_close`**   every side of the kind K10 in the maker's first list pays, where these sides are that lot's

Limits. The head and that the maker returns are premises. That a side pays says that the set-up lays its steps: nothing on
whether a part plays or a verifier accepts. The full size and the older hash alone.
-/
import AtFullSide.K10.PaysBook
import AtFullSide.K10.PaysSenders
import AtFullSide.K14.MakersBookOne
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.AtFull.Shape.LinkNumbersAtHead
import Johnson.Desc.ProofFile.Honest.K10.SeatLotC
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10
import Johnson.Desc.ProofFile.Honest.K10.LotAll
import Johnson.Desc.ProofFile.Honest.K10.Xch.Height
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.Small.RoundsOfCut
import Johnson.Desc.ProofFile.Honest.Small.CutOfBook
import Johnson.RunOne.Sound.KeyListsAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10 AtFullSide.K14
open VerifiableInference.Desc (Block Chain KindName FileDescription)
open VerifiableInference.Desc.First.Close (Par entries)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (codesFull2 proofSendsFull)
open P2Law.ProofPlan (WP)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- The places with their stretches, under the head, are the written ones. -/
theorem xs_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) : ProofFile.k9Stretches Zp = xsW := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  unfold ProofFile.k9Stretches xsW
  rw [K2.Law.spots_at_head h.toAtMg O, K14.pub_decl_at_laid h.scope h.laid]
  rfl

/-- The numbers of a closing, under the head, are the written text's. -/
theorem par_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (xs : List (ProofFile.Spot × List Fmt.DeclaredRound × Nat)) (p : VerifiableInference.Desc.K9.Where) :
    ProofFile.k10Par Zp xs p = parW xs p := by
  have hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp := h.toAtMg.laid.pub
  have e : Zp.s₀.check.frame.groups = OnBytes.reqGroups shapeFull := by
    rw [first_frame_groups hZ, h.toAtMg.shape_full]
  unfold ProofFile.k10Par parW
  rw [e]
  refine congrArg (Option.bind _) (funext fun x => congrArg (Option.bind _) (funext fun Gr => ?_))
  rcases x with ⟨_, ds, _⟩
  rcases ds with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

/-- **The closings that the lot reads, under the head, are the 25 written ones.** -/
theorem pars_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) : closePars Zp = parsW := by
  show ((ProofFile.k9Links (ProofFile.k9Stretches Zp)).filterMap fun l =>
    (ProofFile.k9Where (ProofFile.k9Stretches Zp) l).bind fun p => ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) p) = _
  rw [xs_at_head h]
  simp only [par_at_head h]
  rfl

/-- **What a closing's part carries, under the head, is the written list.** -/
theorem borne_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {P : Par} (hP : P.link < 25) :
    borneAt Zp P = borneW P := by
  have s : Zp.first.shape = shapeFull := h.toAtMg.shape_full
  have c : Zp.first.codes = codesFull2 := h.toAtMg.codes_full
  have e : ∀ j, sendersIn (ProofFile.k9Stretches Zp) j = sendersE Johnson.AtFull.Desc.Lots.xsW j := fun j => by
    rw [sendersIn_eq, Johnson.AtFull.Shape.stretches_at_head h.toAtMg]
  unfold borneAt borneAtOf borneW
  rw [s, c]
  refine borneOf_congr fun j hj => ?_
  have hj25 : j < 25 := by omega
  have hw : sendersE Johnson.AtFull.Desc.Lots.xsW j = sendW j :=
    beq_iff_eq.1 (List.all_eq_true.1 senders_written j (List.mem_range.2 hj25))
  funext t
  rw [e, hw]

/-- A place that the lot reads has its block in the chain, with the closing's rounds. -/
theorem close_block (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Q : Par} (hQ : Q ∈ closePars Zp) :
    ∃ b ∈ cF.blocksInOrder, b.place = closePlace Q ∧ b.rounds = (closeRounds Q).map (·.1) ∧
      b.oracles = (closeRounds Q).map (·.2) := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  obtain ⟨l, -, hf⟩ := List.mem_filterMap.1 hQ
  obtain ⟨p, hp, hq⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨sub, -, -, h2, -, -⟩ := where_is O hp
  obtain ⟨q1, -⟩ := IM.k10Par_fields hq
  have hl : l < 25 := by
    have t := (closeOk_open (pars_at_head h ▸ hQ)).1
    omega
  obtain ⟨p', Q', b, Td⟩ := tied_at_scope h.toAtMg.scope h.toAtMg.reads O l hl
  obtain rfl : p' = p := Option.some.inj (Td.1.symm.trans hp)
  obtain rfl : Q' = Q := Option.some.inj (Td.2.1.symm.trans hq)
  obtain ⟨-, -, hb, -, -, hpl, hr, ho⟩ := Td
  exact ⟨b, List.mem_of_getElem? hb, hpl, hr, ho⟩

/-- **A side with the closing's one part pays, at the written book.** J: the part's job; its public data are the
written ones. -/
theorem sidePays_job (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B)
    (hB2 : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    {V W X : Type} {Q : Par} (hQ : Q ∈ closePars Zp) (J : CloseJob W) (hJ : J.pub = ⟨Q, borneW Q⟩) :
    SidePays B 0 cF.blocksInOrder
      (⟨closePlace Q, [closePart (V := V) (X := X) (foldShellT true J foldWords)]⟩ : Placed V W X) := by
  have hW : Q ∈ parsW := pars_at_head h ▸ hQ
  obtain ⟨blk, hbm, hpl, hr, ho⟩ := close_block h hQ
  obtain ⟨-, -, -, t4, -, -, t7, t8⟩ := closeOk_open hW
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  have hn : ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hp)).1).1
  refine sidePays_of_tests _ _ _ _ fun b hb hbp => ?_
  obtain rfl : b = blk := List.inj_on_of_nodup_map hn hb hbm (hbp.trans hpl.symm)
  have e1 : ((closeRounds Q).map (·.1)).map (·.entry.name) = (entries Q).map (·.name) := by
    simp [closeRounds, Function.comp_def]
  have hcut : partsCut b = [(entries Q).length] := by
    unfold partsCut
    rw [hr, e1, hpl]
    exact t8
  have hne : b.rounds ≠ [] := by
    rw [hr]
    simpa [closeRounds] using t7
  have hm : ((⟨closePlace Q, [closePart (V := V) (X := X) (foldShellT true J foldWords)]⟩ : Placed V W X).parts.map
      (·.moves.length)) = partsCut b := by
    rw [hcut]
    show [(closePart (V := V) (X := X) (foldShellT true J foldWords)).moves.length] = _
    rw [moves_len, hJ]
    simp [closeRounds]
  refine ⟨?_, rounds_of_cut hm, ?_, ?_, ?_, ?_⟩
  · rw [hr, ho, List.length_map, List.length_map]
  · exact (bookWhole_cut_first hB2 hp hb hne).trans (congrArg some hm.symm)
  · show B.first.any (fun r => r.1.place == b.place && decide (1 ≤ r.1.part)) = false
    rw [close_rows hB, hpl]
    exact t4
  · rw [hpl]
    exact close_beyond hB hW
  · rw [hpl]
    obtain ⟨c, hc⟩ := close_lends hB hW (p := closePart (V := V) (X := X) (foldShellT true J foldWords)) rfl
      (by
        show [] ++ closeSpends J.pub.par = _
        rw [hJ]
        rfl)
      (by
        show [] ++ closeCarries J.pub = _
        rw [hJ]
        rfl) default
    exact ⟨default, c, hc⟩

/-- **EACH SIDE OF THE CLOSINGS' LOT PAYS**, at the book of whatever the maker returns. The filling P is a letter. -/
theorem sidePays_close (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {W₁ Rc₁ Tr₁ X₁ : Type}
    (readers : Local W₁ Rc₁ ProofFile.Inst Tr₁ → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (G : ProofFile.Ground) :
    ∀ g ∈ (seatLotC (X := X₁) readers rows stAt).halves Zp G, SidePays A.B 0 cF.blocksInOrder g := by
  intro g hg
  obtain ⟨B, hB, hB2, -, -, hall⟩ := makers_book_one h
  obtain ⟨eB, -⟩ := hall _ _ _ _ _ P A hA
  rw [eB]
  rw [seatLotC_halves] at hg
  obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hg
  exact sidePays_job h hB hB2 hQ _ (by
    show (⟨Q, borneAt Zp Q⟩ : ClosePub) = _
    rw [borne_at_head h (closeOk_open (pars_at_head h ▸ hQ)).1])

/-- **Each side of the closings' list at the wide filling pays**, at the book of whatever the maker returns: the lot
`closeLotAt` (Honest/AtPureWiderK10.lean) is `seatLotC` where the first chain is made, and lays no side where it is not. -/
theorem sidePays_closeLotAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {W₁ X₁ : Type} (I : WiderIn W₁)
    (S : OnBytes.HonestTrace.Sz) (G : ProofFile.Ground) :
    ∀ g ∈ (closeLotAt (X := X₁) I S).halves Zp G, SidePays A.B 0 cF.blocksInOrder g := by
  intro g hg
  cases hc : ProofFile.onlineFirstChainAt Zp with
  | ok c =>
    rw [closeLotAt_ok I S G hc] at hg
    exact sidePays_close h hA _ _ _ G g hg
  | error e =>
    rw [closeLotAt_error I S G hc] at hg
    cases hg

/-- **EVERY SIDE OF THE KIND K10 IN THE MAKER's FIRST LIST PAYS**, where one lot of the filling lays the closings' halves
and every lot either lays no half of the kind or lays these same halves. -/
theorem kindPays_close (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    {Lc : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X}
    (hLc : Lc.halves A.Z A.G = (seatLotC (X := X) readers rows stAt).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ e ∈ M.halves A.Z A.G, e.place.kind ≠ KindName.K10) ∨
      M.halves A.Z A.G = Lc.halves A.Z A.G) :
    KindPays A.B 0 cF.blocksInOrder A.H.first KindName.K10 := by
  intro g hg hk
  obtain ⟨e1, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  rw [(atPure_ok hA).2.2.2.2.2.2.2.1] at hg
  obtain ⟨M, hM, hgM⟩ := List.mem_flatMap.1 hg
  rcases ho M hM with h1 | h2
  · exact absurd hk (h1 g hgM)
  · rw [h2, hLc, eZ] at hgM
    exact sidePays_close h hA readers rows stAt A.G g hgM

end AtFullSide.K10

#print axioms AtFullSide.K10.xs_at_head
#print axioms AtFullSide.K10.par_at_head
#print axioms AtFullSide.K10.pars_at_head
#print axioms AtFullSide.K10.borne_at_head
#print axioms AtFullSide.K10.close_block
#print axioms AtFullSide.K10.sidePays_job
#print axioms AtFullSide.K10.sidePays_close
#print axioms AtFullSide.K10.sidePays_closeLotAt
#print axioms AtFullSide.K10.kindPays_close
