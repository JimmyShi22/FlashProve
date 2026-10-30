-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K5/TieAtJoin.lean: conditional: the pieces from which what the attention sub-protocol (K5)
asks of the Script is stated at the joined Script (joinQ, Honest/Thread/Join.lean) and at the book A.B
that the maker onlineProverFromPublicFiles returns. The statements at joinQ itself stand in TieAtJoinTop.lean in this folder.
No definition; three theorems. K5 lays no lot of its own: it reads messages that the code switch (K2) and
the shared sending (K1) send.

  shareAt_msgs_mem          each place's lots of messages lie in K2's share of the joined list
  k5ScriptQ_of_lists        K5's premise on the Script (K5ScriptQ) at a Script laid from lots, from the
                            premise on lists HL and the opening's premise SO. The lists are letters
  planSwitchLists_at_join   HL (PlanSwitchLists) holds at the joined list of message lots joinMl

The premises of k5ScriptQ_of_lists: h, the library's head; hSz, the sizes S give the reference planes;
hg, the group is below 12; hA, the maker returns A at a filling P; hFull, at every input that meets
ReadyInput the trace is a full-size trace (TraceIsFull); HL; and SO, asked at group 0 alone.
The premises of planSwitchLists_at_join: h; hA; hm, all lots of one message in the joined list agree;
hml, the message lots of K2's share lie among the message lots that the other senders hand in; hv, at
each switch into a link below 24 K2's public test says yes at every input that meets ReadyInput.

How. HL's four clauses at a place p: contained in the list by shareAt_msgs_mem, hml and the list's own
append; agrees with the others by hm; the book's test by switch_lends_at_maker_closed; the public test by
hv. k5ScriptQ_of_lists is calls alone, and hQ_of_senders (Honest/K5/Law/SendersScript.lean).

Limits.
  * Conditional. This file proves none of its premises of any list, reader, book, instance or filling.
  * K5ScriptQ speaks of the inputs that meet ReadyInput alone: where no input does, it says nothing.
  * The index type W₀ and its reader wt are letters, and so are the cells cq. Their values come from the
    caller's filling.
  * NOT IN FRONT OF A LAW OVER COINS. The full size alone, the first chain alone, at the
    earlier hash OnBytes.secondHashFunction, a fixed function.
  * Through its imports it stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import AtFullSide.K5.ReturnsClosed
import Johnson.Desc.ProofFile.Honest.K5.Law.SendersMaskTied
import Johnson.Desc.ProofFile.Honest.K5.Law.SendersLists
import AtFullSide.K5.SwitchesLendAtMakerClosed
import Johnson.Desc.ProofFile.Honest.K5.Law.PublicOkAtReady
import Johnson.Desc.ProofFile.Honest.K2.JoinShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K5
open ProofFile ProofFile.Honest ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head MsgLot PadLot TreeLot LotsAgree MsgsAgree Covers
  Others JoinFit joinQ joinMl joinPl joinTl)
open P5J (AtMgA TS CellsM)

/-! ## 1 K2's share, two small facts -/

variable {W₀ : Type} {wt : W₀ → Weights} {cellsOf : W₀ → P5J.CellsM OnBytes.Flat.numsFull}

section
variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- Each place's lots of messages lie in K2's share at a plan's own letters. -/
theorem shareAt_msgs_mem (bs : List (Block TS ProofFile.Cl)) (front : ℕ) (Zq : ProofFile.Pub) (G : ProofFile.Ground)
    (Dq : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (rest : ℕ → TreeLot Bk (Local W₀ Rc Xi Tr)) {p : K2.SwitchPlace}
    (hp : p ∈ K2.switchPlaces Zq G) :
    ∀ L ∈ K2.switchMsgLots 0 Dq readers (K2.lotClosingAt G.first.layout (K2.segmentsOf Zq G)) p
        (K2.switchNum Zq p) (front + roundsTo bs (borderNo bs p.place)),
      L ∈ (K2.switchShareAt Bk bs front Zq G Dq readers rest).ml :=
  fun _ hL => List.mem_flatMap.2 ⟨p, hp, hL⟩

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {S : OnBytes.HonestTrace.Sz} {X₀ X : Type}

section
variable {P : OnlineProverParts W₀ IndexCommitterCoins Cells X₀ X} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells X₀ X}

/-! ## 2 K5's premise on the `Script`, from the premise on lists -/

/-- **K5's premise on the `Script` at a `Script` laid from lots, from the premise on lists and the
opening's premise.** The lists pl, tl, ml are letters. Conditional: h; hSz; hg; hA; hFull; HL; SO, which
is asked at group 0 alone. It speaks of the inputs that meet `ReadyInput` alone.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem k5ScriptQ_of_lists
    (cq : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → P5J.At.Tok)
    (pl : List (PadLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)))
    (tl : ℕ → TreeLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))
    (ml : List (MsgLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)))
    (lay : OnBytes.Params.ReqLayout)
    (hSz : planesAtRef S = Sz.ref) {g : ℕ} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hFull : TraceIsFull (P5J.At.X Zp) (ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H) (id : Cells → Cells))
    (HL : PlanSwitchLists Zp ml (ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H) S A.G
      (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) lay)
    (SO : g = 0 → ∀ (Ad : MsgAddr) (m : ℕ), typedSeat h A.G (2 * g) Ad = some (2 * g, m) →
      OpeningLotForFillLean Zp ml S A.G
        (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) Ad m) :
    ∀ a x₁, (P5J.At.X Zp).A[g]? = some a → lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h (Script.ofLots cF.blocksInOrder 0 cq tok pl tl ml)
        (ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H)
        (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (ProofFile.Honest.K5.seatOf keyOfK3 Zp A.G cF g a)
        (OnBytes.Model.Forest.elems a.fs) := by
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    obtain ⟨h1, h2, -⟩ := atPure_ok hA
    rw [← (Except.ok.inj (h1.symm.trans h.laid.pub) : A.Z = Zp)]
    exact h2
  have SF0 : ∀ (Ad : MsgAddr) (m : ℕ), typedSeat h A.G (2 * g) Ad = some (2 * g, m) →
      ∃ Ls ∈ ml, LotsAgree ml Ls ∧
        Covers (ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H)
          (roundsTo cF.blocksInOrder (borderOf g)) Ls (fillLot h S
                     (fun v => ⟨v.trace, wt v.w₀, v.rc⟩)
                     (typedSeat h A.G (2 * g)) (fun _ => 0) Ad (2 * g) m) := by
    intro Ad m hAd
    by_cases g0 : g = 0
    · subst g0
      exact covers_of_openingLotForFillLean h hG hAd _ _ (SO rfl Ad m hAd)
    · exact covers_of_planSwitchLotForFillLean h hG (by omega) hAd _
        (planSwitchLotForFillLean_of_plain h hG (planSwitchLotForFillPlain_of_lends
          (planSwitchLotForFillLends_of_lists h hG (by omega) (by omega) hAd HL)))
  exact hQ_of_senders h cF.blocksInOrder 0 cq tok pl tl ml hSz hg A.G
    (fun a ha => (lends5_iff A.B _ _).2 (k5_lends_paid_fill h hg hA a ha))
    (rd := (fun v => ⟨v.trace, wt v.w₀, v.rc⟩))
    (seat₀ := typedSeat h A.G (2 * g)) (seat₁ := typedSeat h A.G (2 * g + 1))
    (heard₀ := fun _ => 0) (heard₁ := fun _ => 0) (fun _ => rfl)
    (hqa_of_traceIsFull h (hFull) hg)
    (fun _ ha => hSm_of_traceIsFull h (hFull) hg ha rfl rfl)
    (fun a x₁ kM hk ha hx hm' => covers_of_planSwitchLotForMask h hG hg ha rfl rfl id
      (k5_lends_paid_fill h hg hA a ha) _
      (planSwitchLotForMask_of_plain h hG
        (planSwitchLotForMaskPlain_of_tied h hG hg (VerifiableInference.OnPublicFiles.lookAt_link hx) hm'
          (hT_at_maker_closed h hA hg) (planSwitchLotForMaskTied_of_lists h hG hg HL))))
    (reach_typedSeat h hG _ (by omega)) SF0
    (reach_typedSeat h hG _ (by omega))
    (fun Ad m hAd => covers_of_planSwitchLotForFillLean h hG (by omega) hAd _
      (planSwitchLotForFillLean_of_plain h hG (planSwitchLotForFillPlain_of_lends
        (planSwitchLotForFillLends_of_lists h hG (by omega) (by omega) hAd HL))))

/-! ## 3 The premise on lists holds at the joined list -/

include h in
/-- **The premise on lists holds at the joined list of message lots.** Conditional: h; hA; hm; hml;
hv. The book's test inside it says whether the book lends the switch's first part a stretch of the
right name and count: not what, and not whose. NOT IN FRONT OF A LAW OVER COINS. -/
theorem planSwitchLists_at_join
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {arr : ℕ → ℕ → ℕ} {Xj Xo : Type}
    {wit : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → K1.PlaceIn Xj} {own₀ : Xo}
    {jobs : List (ℕ × K1.SendJob (K1.PlaceIn Xj) Xo)}
    {O : Others A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)}
    (hm : MsgsAgree (joinMl cF.blocksInOrder 0 arr wit own₀ jobs O))
    {rest : ℕ → TreeLot A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)}
    (hml : ∀ L ∈ (K2.switchShareAt A.B cF.blocksInOrder 0 Zp A.G (K2.withSwitchData S (K1.lotData S) Zp A.G)
      (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) rest).ml, L ∈ O.ml)
    (hv : ∀ p ∈ K2.switchPlaces Zp A.G, p.link < 24 → ∀ w,
      ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H w →
      K2.publicOk (K2.withSwitchData S (K1.lotData S) Zp A.G) A.G.first.layout p
        ((K2.segmentsOf Zp A.G).take p.link) w.x = true) :
    PlanSwitchLists Zp (joinMl cF.blocksInOrder 0 arr wit own₀ jobs O)
      (ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H) S A.G
      (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) A.G.first.layout := by
  intro p hp hl
  have hsub : ∀ L ∈ K2.switchMsgLots 0 (K2.withSwitchData S (K1.lotData S) Zp A.G)
      (fun v => ⟨v.trace, wt v.w₀, v.rc⟩)
      (K2.lotClosingAt A.G.first.layout (K2.segmentsOf Zp A.G)) p (K2.switchNum Zp p)
      (0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place)),
      L ∈ joinMl cF.blocksInOrder 0 arr wit own₀ jobs O := fun L hL =>
    List.mem_append.2 (Or.inr (hml L (shareAt_msgs_mem cF.blocksInOrder 0 Zp A.G _ _ rest hp L hL)))
  exact ⟨K1.lotData S, 0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place), fun L hL => hsub L hL,
    fun L hL => hm L (hsub L hL), switch_lends_at_maker_closed h hA p hp, hv p hp hl⟩

end

/-! ## 4 K5's bound on the tree lots -/

section
variable {Bk : ProverCoinCounts} {Wl Xj Xo : Type}

end

end AtFullSide.K5

#print axioms AtFullSide.K5.shareAt_msgs_mem
#print axioms AtFullSide.K5.k5ScriptQ_of_lists
#print axioms AtFullSide.K5.planSwitchLists_at_join
