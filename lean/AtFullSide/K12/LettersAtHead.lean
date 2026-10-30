-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/LettersAtHead.lean: under the library's head, where onlineProverFromPublicFiles returns at the filling
onlineProverPartsInUse, at any index type: the letters of the last chain's proximity test are the
filling's own, and the book of what the pair is lent is the maker's written book.

  job_at_filling            the job is made at the ground that onlineProverFromPublicFiles hands, at the filling's
                            letters, and the prover's last chain is that job's pair
  description_at_filling    what onlineProverFromPublicFiles returns has the head's public part and description, and
                            the last chain's pair stands at that description
  first_member_at_filling   the index-mask member is memK1 of the sender's job, and the search at
                            the first opening's place finds that job's half: hm is paid
  w_member_at_filling       W's member is memK1 of the sender's job, and the search at W's place
                            finds that job's half
  omega_member_at_filling   Omega's member is made of the sending at the public data with which the
                            shared chain's sides are laid
  book_at_filling           the book that onlineProverFromPublicFiles returns is the written description's: so every
                            law of HeldAtHeadW.lean that takes hB holds at it, and the book's
                            entries are the written ones. General in the filling
  seven_at_filling          the seven entries that the pair carries, owner and start, at that book
  lent_at_filling           each side of the prover's last chain is lent its row, at every run's
                            coins
  one_coin_at_filling       the five entries of o_sp's values at that book: one owner, one start
  entry_of_map, spent_of_map   an entry of a carried or spent list, from its image
  osp_one_coin_at_filling   what the frame hands at the four carried entries, at number 0, is the
                            coin that the part at "SPLIT" spends
  omega_row_at_head         under the head Omega's member is the written row
  omega_is_sent             at that book, the rows of Omega's member at the stretch that the frame
                            carries are the sender's rows at its own coins
  first_test_laid           the first chain's proximity test has a side at the blank ground

By what. filling_at_head (DescAtHeadW.lean), ground_at_head (GroundAtHeadW.lean), second_made
(SecondMadeW.lean), atPure_book_at_head, bookWhole_same_at_made, bookWhole_same_at_laid (the book
at the head), halfW_lent (HalfAtHeadW.lean), entries_W (HandedAtHeadW.lean), omega_held
(HeldAtHeadW.lean), one_coin_at_laid (CutsOmegaAtLaid.lean), fitsL_head_L (FitsAtHeadL.lean), and
LettersFirst.lean, LettersOmega.lean and LettersCoin.lean (Johnson/Desc/ProofFile/Honest/K12/AtProof/).

Limits.
- Conditional on the head and on onlineProverFromPublicFiles's return (hA), but for three groups: omega_is_sent, at any
  book that hB names; first_test_laid, at the head and the blank ground (hG); entry_of_map and
  spent_of_map, general in the book. The return at the filling is had at any index whose named
  member is in range: AtFullSide/K12/ReturnsAtAnyIndex.lean.
- The full size and the format's second hash function alone; first_test_laid is at any earlier hash.
- Nothing here is read through OnlineProverParts.through: book_at_filling and ground_at_head are general in the
  filling; the statements on a search are at the filling before it is read through.
- omega_is_sent takes as premises the data's agreement (omega_data_at_run has it at a run), hq, that
  the member's row is the written row (omega_row_at_head has it), and h₀, the sender's own cut.
- Having a side is no ground that it plays. Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.FirstAtHeadW
import AtFullSide.K12.GroundAtHeadW
import AtFullSide.K12.DescAtHeadW
import AtFullSide.K12.SecondMadeW
import AtFullSide.K12.HeldAtHeadW
import AtFullSide.K12.HalfAtHeadW
import AtFullSide.K12.FitsAtHeadL
import AtFullSide.K12.CutsOmegaAtLaid
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LettersFirst
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LettersOmega
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LettersCoin
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open VerifiableInference.Desc (Block Chain Place)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K12.Light (ManyJob askOf memOfSending rowsOfLaid carriedOf)
open ProofFile.Honest.K14 (SendPub jobOmega proverSidesOfSharedSendings sendPlace dueOf)
open ProofFile (Pub Ground SecondHashFunctionArgument)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The job at the last chain's test, at the filling's letters. -/
abbrev jobAtFill {W₀ : Type} (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (G : Ground) :
    Option (ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit) :=
  jobRealW S (P5J.F0T OnBytes.secondHashFunction Zp Np cF) VerifiableInference.Desc.K12.Seat.enterOwn O.pile
    (K1.lotNo OnBytes.secondHashFunction Zp) (lettersW I Zp) (fun w => I.weights Zp w.w₀)
    (fun P w => randAt P w.rc) Zp G

section Filling
variable {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
  (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
include h hA

/-- **The job is made at the filling's letters, and the last chain is its pair.** -/
theorem job_at_filling :
    ∃ M, jobAtFill Zp Np cF I S O A.G = some M ∧
      A.H.second =
        [(proverSideOfProximityTest M.toRun.toTest : Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) _ Unit).needsField] := by
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  obtain ⟨J, hJ, hs⟩ := second_made h Op I S O A.G
  unfold realW at hJ
  obtain ⟨M, hM, rfl⟩ := Option.map_eq_some_iff.1 hJ
  have hZ := (atPure_at_laid h.laid hA).1
  obtain ⟨-, -, -, -, -, -, -, -, -, h2, -⟩ := atPure_ok hA
  refine ⟨M, hM, ?_⟩
  rw [h2, hZ]
  exact hs

/-- **What onlineProverFromPublicFiles returns has the head's description, and the pair stands at it.** -/
theorem description_at_filling :
    (∃ G B H rd rw, A = ⟨Zp, G, P5J.F0T OnBytes.secondHashFunction Zp Np cF, B, H, rd, rw⟩) ∧
      A.H.second =
        halfW S (P5J.F0T OnBytes.secondHashFunction Zp Np cF) VerifiableInference.Desc.K12.Seat.enterOwn O.pile
          (K1.lotNo OnBytes.secondHashFunction Zp) (lettersW I Zp) (fun w => I.weights Zp w.w₀)
          (fun P w => randAt P w.rc) Zp A.G :=
  filling_at_head h I S O hA (ProofFile.Honest.K14.nowSharedBy_at_head h (I.weights Zp))

/-- **The index-mask member at the filling.** -/
theorem first_member_at_filling {M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hM : jobAtFill Zp Np cF I S O A.G = some M) :
    ∃ fs, M.mems[0]? = some (memK1 (firstOfLot OnBytes.secondHashFunction S Zp A.G) (inOf (lettersW I Zp))
        senderI ((firstParOf Zp A.G).sent.size - 1) fs) ∧
      A.H.first.find? (fun g => g.place == ⟨1, some 0, 1, .K1⟩) =
        some (K1.placeHalf (inOf (lettersW I Zp)) (firstOfLot OnBytes.secondHashFunction S Zp A.G)) := by
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  have eZ := (atPure_at_laid h.laid hA).1
  have eG := ground_at_head h.laid Op hA
  have hm : (shapeAt (firstParOf Zp A.G) ((firstParOf Zp A.G).sent.size - 1)).mainRows = 0 := by
    rw [eG]
    exact first_no_main_head h Op
  obtain ⟨fs, e, -⟩ := first_member_is_sent I OnBytes.secondHashFunction S O _ _ Zp A.G hM hm
  have hf := first_found I OnBytes.secondHashFunction S O hA
  rw [eZ] at hf
  exact ⟨fs, e, hf⟩

/-- **W's member at the filling.** -/
theorem w_member_at_filling {M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hM : jobAtFill Zp Np cF I S O A.G = some M) :
    ∃ fs, M.mems[1]? = some (memK1 (wJobOf OnBytes.secondHashFunction O Zp A.G
        VerifiableInference.Desc.K13.Law.wMsgFull) (inOf (lettersW I Zp)) senderW 0 fs) ∧
      (A.H.first.find? fun g => g.place == (wJobOf (X := Unit) OnBytes.secondHashFunction O Zp A.G
        VerifiableInference.Desc.K13.Law.wMsgFull).P.place) =
        some (K1.placeHalf (inOf (lettersW I Zp)) (wJobOf OnBytes.secondHashFunction O Zp A.G
          VerifiableInference.Desc.K13.Law.wMsgFull)) := by
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  have eZ := (atPure_at_laid h.laid hA).1
  obtain ⟨msg, fs, hmsg, e, -⟩ := wMember_is_sent I OnBytes.secondHashFunction S O _ _ Zp A.G hM
  obtain rfl : msg = VerifiableInference.Desc.K13.Law.wMsgFull :=
    Option.some.inj (hmsg.symm.trans (ProofFile.Honest.K1.msg_w_head h Op))
  have hf := half_w_wM h I OnBytes.secondHashFunction S O hA
    (J := wJobOf OnBytes.secondHashFunction O Zp A.G VerifiableInference.Desc.K13.Law.wMsgFull) rfl
  rw [eZ] at hf
  exact ⟨fs, e, hf⟩

/-- **Omega's member at the filling**: it is made of the sending at the public data with which the
shared chain's sides are laid. -/
theorem omega_member_at_filling {M : ManyJob (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hM : jobAtFill Zp Np cF I S O A.G = some M) :
    ∃ (An : SendPub) (fs : Option Nat × Option Nat)
      (pre : List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)),
      M.mems[2]? = some (memOfSending (jobOmega ⟨An.P,
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.flatMap (·.rounds)).length + An.atPoint⟩)
        senderO 0 fs
        (askOf An (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => I.weights Zp w.w₀)
          (fun w => randAt An.P w.rc)) none) ∧
      A.H.shared = (pre ++ proverSidesOfSharedSendings An (I.weights Zp) (fun rc : IndexCommitterCoins => randAt An.P rc)) ++
        halfU (I.weights Zp) (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp ++
        halfO (I.weights Zp) Zp := by
  obtain ⟨six, h6⟩ : ∃ six, nowSharedBy (I.weights Zp) Zp = .ok six :=
    ⟨_, ProofFile.Honest.K14.nowSharedBy_at_head h (I.weights Zp)⟩
  obtain ⟨An, pre, hAn, hsix⟩ := one_A (I.weights Zp) Zp h6
  have hZ := (atPure_at_laid h.laid hA).1
  obtain ⟨-, -, -, -, -, -, -, -, hs, -⟩ := atPure_ok hA
  unfold jobAtFill jobRealW at hM
  obtain ⟨F, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A', hA', hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain rfl : An = A' := Option.some.inj (hAn.symm.trans hA')
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hM
  refine ⟨An, _, pre, rfl, ?_⟩
  rw [hs, hZ]
  show sharedWithUO I Zp = _
  rw [sharedWithUO_ok I h6, sharedWithU_ok I h6, hsix]

/-- **Each side of the prover's last chain is lent its row, at every run's coins.** -/
theorem lent_at_filling (k : Coins A.B) :
    ∀ g ∈ A.H.second, ∃ c, lendRow A.B (A.B.rowsOf 2) (k.look 2) placeW g.parts 0 = .ok c := by
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  have eG := ground_at_head h.laid Op hA
  obtain ⟨-, hs⟩ := description_at_filling h I S O hA
  intro g hg
  rw [hs, eG] at hg
  exact halfW_lent h Op (ProofFile.Honest.K14.atPure_book_at_head h hA) S _ _ _ _ _ _ _ hg k

end Filling

/-- **The book that onlineProverFromPublicFiles returns is the written description's.** General in the filling. -/
theorem book_at_filling (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok A.B := by
  obtain ⟨B, hB, -⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  have e : A.B = B := Except.ok.inj
    ((ProofFile.Honest.K14.atPure_book_at_head h hA).symm.trans
      (ProofFile.Honest.K14.bookWhole_same_at_made hB h))
  rw [e]
  exact hB

/-- **The seven entries that the pair carries, owner and start, at that book.** -/
theorem seven_at_filling (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    (carryE A.B ⟨placeW, 0⟩).map (fun e => (e.owner, e.start)) =
      [(senderI, startI), (senderW, startW 0), (senderO, ⟨0, 0⟩)] ∧
    (carryE A.B ⟨placeW, 1⟩).map (fun e => (e.owner, e.start)) =
      [(senderI, startI), (senderW, startW 0), (senderO, ⟨0, 0⟩), (senderW, startW 1)] := by
  have hB := book_at_filling h hA
  rw [carryE_at_W hB (Or.inl rfl), carryE_at_W hB (Or.inr rfl)]
  exact ⟨entries_W.1, entries_W.2.1⟩

/-- **The five entries of o_sp's values, at that book**: the part at "SPLIT" spends one coin from
coin 42853 of the second sending's part on, and each of the four parts of the two tests on the
shared chain carries 216 from that coin on, each under its name. -/
theorem one_coin_at_filling (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ((A.B.ahead.filter fun e => e.spender == ⟨ProofFile.Honest.K14.place 8, 0⟩).filter (·.once)).map
        (fun e => (e.owner, e.start, e.count)) = [(⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 1⟩)] ∧
    ((carriedOf A.B ⟨placeU, 0⟩)[1]?).map (fun e => (e.owner, e.start, e.count)) =
      some (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩) ∧
    ((carriedOf A.B ⟨placeU, 1⟩)[1]?).map (fun e => (e.owner, e.start, e.count)) =
      some (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩) ∧
    ((carriedOf A.B ⟨placeO, 0⟩)[1]?).map (fun e => (e.owner, e.start, e.count)) =
      some (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩) ∧
    ((carriedOf A.B ⟨placeO, 1⟩)[1]?).map (fun e => (e.owner, e.start, e.count)) =
      some (⟨sendPlace 5, 0⟩, ⟨0, 42853⟩, ⟨0, 216⟩) ∧
    ((carriedOf A.B ⟨placeU, 0⟩)[1]?).map (·.name) =
      some "message 1 of 2.-.5.0 to 2.-.9.0: carried" ∧
    ((carriedOf A.B ⟨placeU, 1⟩)[1]?).map (·.name) =
      some "message 1 of 2.-.5.0 to 2.-.9.1: carried" ∧
    ((carriedOf A.B ⟨placeO, 0⟩)[1]?).map (·.name) =
      some "message 1 of 2.-.5.0 to 2.-.10.0: carried" ∧
    ((carriedOf A.B ⟨placeO, 1⟩)[1]?).map (·.name) =
      some "message 1 of 2.-.5.0 to 2.-.10.1: carried" :=
  one_coin_at_laid h.scope h.laid
    (ProofFile.Honest.K14.bookWhole_same_at_laid (book_at_filling h hA) h.scope h.laid)

/-- Entry number 1 of a carried list, from its image. -/
theorem entry_of_map {B : ProverCoinCounts} {a : Addr} {o : Addr} {s c : Due}
    (h : ((carriedOf B a)[1]?).map (fun e => (e.owner, e.start, e.count)) = some (o, s, c)) :
    ∃ e, (carryE B a)[1]? = some e ∧ e.owner = o ∧ e.start = s ∧ e.count = c := by
  obtain ⟨e, he, q⟩ := Option.map_eq_some_iff.1 h
  have q₁ := Prod.mk.inj q
  have q₂ := Prod.mk.inj q₁.2
  exact ⟨e, he, q₁.1, q₂.1, q₂.2⟩

/-- The one entry of a spent list, from its image. -/
theorem spent_of_map {B : ProverCoinCounts} {a : Addr} {o : Addr} {s c : Due}
    (h : ((B.ahead.filter fun e => e.spender == a).filter (·.once)).map
      (fun e => (e.owner, e.start, e.count)) = [(o, s, c)]) :
    ∃ e, (spentE B a)[0]? = some e ∧ e.owner = o ∧ e.start = s ∧ e.count = c := by
  have h' : (spentE B a).map (fun e => (e.owner, e.start, e.count)) = [(o, s, c)] := h
  cases hs : spentE B a with
  | nil =>
    rw [hs] at h'
    simp at h'
  | cons e l =>
    rw [hs] at h'
    simp only [List.map_cons, List.cons.injEq] at h'
    have q₁ := Prod.mk.inj h'.1
    have q₂ := Prod.mk.inj q₁.2
    exact ⟨e, rfl, q₁.1, q₂.1, q₂.2⟩

/-- **At the filling's book, what the frame hands at number 0 of o_sp's four carried entries is the
coin that the part at "SPLIT" spends.** look: one reader of coins. -/
theorem osp_one_coin_at_filling (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {look : Addr → (d : Due) × Cs d}
    {V₁ W₁ X₁ V₂ W₂ X₂ : Type} {pS : Part V₁ W₁ X₁} {yS : pS.Coins} {rS rows : List (Addr × Due)}
    (hS : lendPart A.B rS look ⟨ProofFile.Honest.K14.place 8, 0⟩ pS = .ok yS) {a : Addr}
    (ha : a ∈ [(⟨placeU, 0⟩ : Addr), ⟨placeU, 1⟩, ⟨placeO, 0⟩, ⟨placeO, 1⟩]) {p : Part V₂ W₂ X₂}
    {y : p.Coins} (hl : lendPart A.B rows look a p = .ok y) :
    (stretches p.carries y.2.2 1).e 0 = (stretches pS.spends yS.2.1 0).e 0 := by
  obtain ⟨s1, u0, u1, o0, o1, -⟩ := one_coin_at_filling h hA
  obtain ⟨eS, heS, so, ss, sc⟩ := spent_of_map s1
  have hq : ∃ e, (carryE A.B a)[1]? = some e ∧ e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, 42853⟩ ∧
      e.count = ⟨0, 216⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact entry_of_map u0
    · exact entry_of_map u1
    · exact entry_of_map o0
    · exact entry_of_map o1
  obtain ⟨e, he, eo, es, ec⟩ := hq
  refine (spent_one_coin hS hl heS he (so.trans eo.symm) (ss.trans es.symm) 0 ?_ ?_).symm
  · rw [sc]
    exact Nat.one_pos
  · rw [ec]
    decide

/-- **Under the head the member's row is the written row**, at any number of "LIN point": hq of
omega_is_sent, at the public data that sendPub returns. -/
theorem omega_row_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {An : SendPub}
    (hAn : sendPub Zp = some An) (n : Nat) :
    msgOf senderO (jobOmega ⟨An.P, n⟩) 0 = rowOF := by
  have eA : An.P = VerifiableInference.Desc.K1.qAt Zp Np := by
    unfold sendPub at hAn
    rw [(ProofFile.Honest.K14.readers_at Zp Np h.laid.places).1] at hAn
    change Option.map _ _ = some An at hAn
    obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 hAn
    rfl
  have ho : omegaDueB ⟨An.P, n⟩ = true := by
    rw [eA]
    exact omegaDue_head h.toAtMg _
  unfold omegaDueB at ho
  have e := beq_iff_eq.1 ho
  unfold ProofFile.Honest.K12.AtProof.msgOf rowOF
  rw [e]

/-- **At that book the rows of Omega's member at the stretch that the frame carries are the
sender's rows at its own coins**, at a state at which the two data agree. -/
theorem omega_is_sent {V W X : Type} {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {p : Part V W X} {y : p.Coins} {j : Nat}
    (hj : j ∈ [0, 1]) (k : Coins B)
    (hl : lendPart B (B.rowsOf 2) (k.look 2) ⟨placeW, j⟩ p = .ok y) (An : SendPub) (n : Nat)
    (fs : Option Nat × Option Nat) (ask : W → ProofFile.Honest.K14.Ask)
    (hq : msgOf senderO (jobOmega ⟨An.P, n⟩) 0 = rowOF)
    {c₀ : Cs (dueAt AtFullSide.K14.rawRowsSharedW senderO)}
    (h₀ : (k.look 1 senderO).2.cut ⟨0, 0⟩ (dueAt AtFullSide.K14.rawRowsSharedW senderO) = some c₀)
    (w : W) (fr : Front X) (t : State ProofFile.Honest.K14.Ask Unit)
    (hd : (jobOmega ⟨An.P, n⟩).data ⟨ask w, fr.heard, ()⟩ 0 = (jobOmega An).data t 0) :
    (memOfSending (jobOmega ⟨An.P, n⟩) senderO 0 fs ask none).rows w fr
        (stretches p.carries y.2.2 2) =
      rowsOfLaid (jobOmega An).Q.codes ((jobOmega An).Q.sent.getD 0 default).shape
        ((jobOmega An).rows t (ProofFile.Honest.coinsE c₀).toArray 0) := by
  obtain ⟨-, -, -, -, be⟩ := written_O
  have e₁ : (msgOf senderO (jobOmega ⟨An.P, n⟩) 0).2.2.e = rowOF.2.2.e :=
    congrArg (fun r : Addr × Nat × Due => r.2.2.e) hq
  have e₂ : (msgOf senderO (jobOmega ⟨An.P, n⟩) 0).2.2.e =
      dueOf (jobOmega An).Q.codes ((jobOmega An).Q.sent.getD 0 default).shape
        (.plain An.P.S.omegaRowsHigh) := rfl
  have hb : dueOf (jobOmega An).Q.codes ((jobOmega An).Q.sent.getD 0 default).shape
      (.plain An.P.S.omegaRowsHigh) ≤ (dueAt AtFullSide.K14.rawRowsSharedW senderO).e := by
    rw [← e₂, e₁]
    exact be
  exact (omega_held hB hj k hl (jobOmega ⟨An.P, n⟩) fs ask An.P.S.omegaRowsHigh rfl hq h₀ w
    fr).trans
    (omega_rows_are_sent An n senderO fs ask w fr t hd c₀ hb)

/-- **The first chain's proximity test has a side at the blank ground.** -/
theorem first_test_laid {o : ProofFile.SecondHashFunctionArgument} {W₀ X : Type} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) : (proxLotAt (X := X) I S).halves Zp G ≠ [] := by
  rw [proxLotAt_made I S G h.laid.chain]
  obtain ⟨pl, hf, hfit⟩ := fitsL_head_L h hG
  obtain ⟨g, e⟩ : ∃ g, (proxLotOf (X := X) I S).halves Zp G = [g] :=
    ⟨_, halves_lotAtDoor _ _ _ Zp G pl hf hfit⟩
  rw [e]
  exact List.cons_ne_nil _ _

end AtFullSide.K12

#print axioms AtFullSide.K12.job_at_filling
#print axioms AtFullSide.K12.description_at_filling
#print axioms AtFullSide.K12.first_member_at_filling
#print axioms AtFullSide.K12.w_member_at_filling
#print axioms AtFullSide.K12.omega_member_at_filling
#print axioms AtFullSide.K12.lent_at_filling
#print axioms AtFullSide.K12.book_at_filling
#print axioms AtFullSide.K12.seven_at_filling
#print axioms AtFullSide.K12.one_coin_at_filling
#print axioms AtFullSide.K12.entry_of_map
#print axioms AtFullSide.K12.spent_of_map
#print axioms AtFullSide.K12.osp_one_coin_at_filling
#print axioms AtFullSide.K12.omega_row_at_head
#print axioms AtFullSide.K12.omega_is_sent
#print axioms AtFullSide.K12.first_test_laid
