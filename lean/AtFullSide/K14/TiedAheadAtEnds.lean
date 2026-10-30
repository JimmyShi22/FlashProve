-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/TiedAheadAtEnds.lean: the linear claim's second part ("K14, second part", the first
member of a proof file's last chain): THE TEST tiedAheadB
(Johnson/Desc/ProofFile/Honest/K14/TiedAhead.lean) SAYS YES AT THE RECORD THAT THE LAST CHAIN's
START RETURNS, FROM THE TWO EARLIER CHAINS' INVARIANTS AT THEIR LAST BORDERS, under the library's
hypothesis at the full size (P5J.AtMgA, Johnson/P5J/MgAtAll.lean), at the format's second hash
function.
With tied_of_ahead it gives Tied (Johnson/Desc/Third/Law/Sources.lean) behind the member 0's yes; by
the library's takenSources_exact that is just where the decision of the member 1 ("the taken trees'
sources") says yes. That last step is not taken here.

The test compares the sources that the own proximity test's rounds declare as taken over with four
pairs (chain, tree's number). AT THESE SIZES THE FOUR PAIRS NAME THREE TREES: W and the mask share
the tree 82. What fixes each pair:
  the index masks' message, W   their places in the first chain's book are the plan's (the library's
                  ownSitsB, off the first chain's invariant: four_at_end,
                  AtFullSide/K14/FirstDoorAtEnd.lean), which are written: (1, 0) and (82, 0)
  the mask        it is the statement's last message (mask_last_of_reach,
                  AtFullSide/K14/MaskAtEnd.lean), the statement has 199, and the book's places are
                  the written list's: (82, 1)
  a tree's number in the first chain's book is its place there (the library's atFirstBook_all)
  Omega           its seat in the shared chain's book at that chain's end
                  (omega_written_at_shared_end,
                  Johnson/Desc/ProofFile/Honest/K14/OmegaSeatAtEnd.lean): tree 1
  the declared rounds   the own test's numbers are the written record (p12_four_at_head,
                  Johnson/AtFull/Shape/TestNumbersAtHead.lean)

  place_mask_written, omega_tenant_written, sources_written   three closed facts, by Lean's kernel
  sources_rejects, sources_rejects_more   two controls, one for each clause: with Omega's pair left
                                          out the test says no (a declared source is not among the
                                          pairs); with a pair added that no round declares it says
                                          no
  sources_blind   WHAT THE TEST CANNOT SEE: with one of the two equal pairs left out it still says
                  yes: so at these sizes the mask's pair is not tested apart; what is shown of the
                  mask serves that the pairs can be read at all, not the verdict
  firstOfS_mask   what is handed of the first chain's last state bears the claim's mask
  own_rounds_written   under the hypothesis the own test's declared rounds are the written ones
  first_pairs_at_end   the first chain's three pairs, off that chain's invariant at its last border
  omega_pair_at_end   Omega's pair, off the shared chain's invariant at its last border
  tied_ahead_at_ends   **the test says yes at the start's record**

What is not claimed. That either invariant holds at any state, or that the start returns: NO STATE
IS KNOWN HERE AT WHICH tied_ahead_at_ends SPEAKS; the closed facts alone stand under no premise.
Nothing on completeness, soundness or hiding. Terms. border: lean/GLOSSARY.md. A thread is the
invariant along a chain with its parameters (Johnson/Desc/ProofFile/Honest/Thread/Thr.lean).
-/
import AtFullSide.K14.MaskAtEnd
import AtFullSide.K14.FirstDoorAtEnd
import Johnson.Desc.ProofFile.Honest.K14.TiedAhead
import Johnson.Desc.ProofFile.Honest.K14.OmegaSeatAtEnd
import Johnson.AtFull.Shape.TestNumbersAtHead
import Johnson.AtFull.Desc.SecondShare
import Johnson.LLT25R.LastSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Door (seatsCarriedB place_of_seats numbers_of_book0)
open VerifiableInference.Desc.K13.Law (LFull linAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Third (S₃ FirstEnd₃ firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law (start₃E_inv start₃_inv firstOutFrom_inv)
open VerifiableInference.Desc.Last
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.AtFull.Desc (piW)
open ProofFile.Honest.FirstThread (Script WtF lettersHead noStrs)
open P5J (AtMgA CellsM TS)
open Desc.K14 (St)

/-! ## Closed facts -/

set_option maxRecDepth 1000000 in
/-- Seat number 198 of the written list of places. -/
theorem place_mask_written : LFull.places[198]? = some (82, 1) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Omega's seat by the written layouts of the shared chain's two sendings. -/
theorem omega_tenant_written :
    Desc.K14.Law.Fence.tenantSh 0 Desc.K14.Law.layUFull Desc.K14.Law.layOFull .oOmega = (1, 0) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The two clauses at the four written pairs, against the own test's written rounds.** -/
theorem sources_written :
    sourcesB (proximityTestKind guardedProximityTestParts piW : Block T12 Unit).rounds [(1, 1), (0, 1), (0, 82), (0, 82)] =
      true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with Omega's pair left out the test says no. -/
theorem sources_rejects :
    sourcesB (proximityTestKind guardedProximityTestParts piW : Block T12 Unit).rounds [(0, 1), (0, 82), (0, 82)] = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control for the other clause: with a pair added that no round declares the test says no. -/
theorem sources_rejects_more :
    sourcesB (proximityTestKind guardedProximityTestParts piW : Block T12 Unit).rounds
      [(0, 2), (1, 1), (0, 1), (0, 82), (0, 82)] = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- What the test cannot see: W and the mask share a tree, so their pairs are equal; with one of the
two left out it still says yes. -/
theorem sources_blind :
    sourcesB (proximityTestKind guardedProximityTestParts piW : Block T12 Unit).rounds [(1, 1), (0, 1), (0, 82)] = true := by
  decide +kernel

/-! ## What is handed -/

/-- What is handed of the first chain's last state: its statement and book, and the claim's numbers
of the own group and of the mask. -/
theorem firstOfS_mask {s : VerifiableInference.Desc.First.S} {f : FirstEnd₃}
    (hf : firstOfS s = some f) :
    ∃ l, linAt s = some l ∧ f.st = s.st ∧ f.book = s.book ∧ f.own = l.own ∧ f.mask = l.mask := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hf
  unfold VerifiableInference.Desc.First.S.firstEnd? at he
  unfold linAt
  split at he
  · rename_i a ha
    cases hl : a.lin with
    | none =>
      rw [hl] at he
      cases he
    | some l =>
      rw [hl] at he
      have he' : (if l.w != noId then some (⟨s.st, s.book, l⟩ : Proof.FirstEnd) else none) =
          some e := he
      split at he'
      · obtain rfl := Option.some.inj he'
        exact ⟨l, by rw [ha]; exact hl, rfl, rfl, rfl, rfl⟩
      · cases he'
  · cases he

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **Under the hypothesis the own test's declared rounds are the written ones.** -/
theorem own_rounds_written (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    (LLT25.c2 Np).rounds = (proximityTestKind guardedProximityTestParts piW : Block T12 Unit).rounds := by
  obtain ⟨N, hN, hW⟩ := Johnson.AtFull.Desc.places_of_own Zp.made
    (Johnson.AtFull.Shape.p12_four_at_head h.toAtMg).2.2.2
  obtain rfl : N = Np := Except.ok.inj (hN.symm.trans h.laid.places)
  have hW' : H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W = piW := hW
  rw [LLT25.c2_is]
  show (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 ProofFile.Cl).rounds = _
  rw [hW']
  rfl

section ends
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **The first chain's three pairs**: at the first chain's last state, under its invariant: what is
handed has the own group with two members; the places of these two and of the mask are the written
ones; a tree stands at each, and bears its place as its number. -/
theorem first_pairs_at_end {k₁ : Coins Bk} {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E₁ : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread 358 k₁ e₁ m₁ E₁)
    {f : FirstEnd₃} (hf : firstOfS e₁ = some f) :
    ∃ (G : OnBytes.Group) (i₁ i₂ : Nat) (T₁ T₂ : OnBytes.Tree),
      f.st.groups[f.own]? = some G ∧ G.members.toList = [i₁, i₂] ∧ f.mask = some 198 ∧
      f.book.place[i₁]? = some (1, 0) ∧ f.book.place[i₂]? = some (82, 0) ∧
      f.book.place[198]? = some (82, 1) ∧ f.book.trees[1]? = some T₁ ∧ T₁.number = 1 ∧
      f.book.trees[82]? = some T₂ ∧ T₂.number = 82 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hlen : cF.blocksInOrder.length = 358 := flat_358 h.scope h.reads O
  obtain ⟨hm, -, hbk, -, hown⟩ := four_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT
  have hoc := ocEnd_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT
  have hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 358 (m₁.st.input.x.pub, e₁) := thr_reach_of
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).first
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).pubOf m₁.st.input.x)
    (le_of_eq hlen.symm) (fun _ h0 => h0) hT
  have hp := flat_planOk_at h.toAtMg
  have hB := Meaning.K2.sendsAre_of_madeRow h.scope h.reads O h.laid.planOk h.toAtMg.pins.1
  have hy := VerifiableInference.PlanWritten.pinnedAt_of_row h.toAtMg.row_at_head
  have hseats : seatsCarriedB LFull e₁.book = true :=
    IM.seatsCarried_field h.scope h.reads O (fun k a => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) id
      (fun _ _ g => let ⟨_, rs, cols, f⟩ := g.fold; ⟨rs, cols, [], [], f⟩) h.laid.planOk hB
      h.toAtMg.laid_codes_at_head 358 (m₁.st.input.x.pub, e₁) hr hm
  have T := Second.Seam.planSits_at_N h.scope h.laid.pub hy (Desc.K14.Law.Sh.laidPOf_at_head h) cF
  obtain ⟨hps, hos⟩ := book_of_ocEnd _ _ _ _ _ _ _ hoc hm
  have hsz : e₁.st.oracles.size = 199 := hos.trans h.toAtMg.msgs_end
  have hpz : e₁.book.place.size = 199 := hps.trans hsz
  obtain ⟨l, hl, q1, q2, q3, q4⟩ := firstOfS_mask hf
  obtain ⟨G, i₁, i₂, hG, hml, p1, p2, -, -⟩ := (ownSitsB_iff _ e₁).1 hown f hf
  have hV1 : (LLT25.vAt Zp (P5J.At.N Zp cF)).index = (1, 0) :=
    Option.some.inj (T.seatI.symm.trans P5J.places_written.1)
  have hV2 : (LLT25.vAt Zp (P5J.At.N Zp cF)).w = (82, 0) :=
    Option.some.inj (T.seatW.symm.trans P5J.places_written.2)
  have hmk : f.mask = some 198 := by
    rw [q4, mask_last_of_reach h hr l hl, hsz]
  have p3 : f.book.place[198]? = some (82, 1) := by
    rw [q2, place_of_seats hseats 198 (by omega)]
    exact place_mask_written
  have hfits : VerifiableInference.Desc.Book.BookFits f.book := by
    rw [q2]
    exact (VerifiableInference.Desc.Sound.bookFitsB_iff _).1 hbk
  have hord := Meaning.K2.atFirstBook_all O hp hr
  rw [hV1] at p1
  rw [hV2] at p2
  have t1 : (1 : Nat) < f.book.trees.size :=
    VerifiableInference.Desc.Book.placed_of_fits hfits i₁ _ p1
  have t2 : (82 : Nat) < f.book.trees.size :=
    VerifiableInference.Desc.Book.placed_of_fits hfits i₂ _ p2
  refine ⟨G, i₁, i₂, f.book.trees[1], f.book.trees[82], hG, hml, hmk, p1, p2, p3,
    Array.getElem?_eq_getElem t1, ?_, Array.getElem?_eq_getElem t2, ?_⟩
  · refine numbers_of_book0 (B := e₁.book) hord 1 _ ?_
    rw [← q2]
    exact Array.getElem?_eq_getElem t1
  · refine numbers_of_book0 (B := e₁.book) hord 82 _ ?_
    rw [← q2]
    exact Array.getElem?_eq_getElem t2

section shared
variable {Bk₂ : ProverCoinCounts} {V₀ Rc₂ Tr₂ Y₀ Y P₁ Wt : Type}
  (H₂ : Prover V₀ Rc₂ ProofFile.Inst OnBytes.TableKey Tr₂ Y₀ Y)
  (N : VerifiableInference.Desc.Shared.NumbersS)
  (Mg : Common V₀ Rc₂ OnBytes.TableKey → VerifiableInference.Desc.Shared.MeaningS St P₁ Wt)
  (shape : Nat → St → Bool) (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk₂ → Common V₀ Rc₂ OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk₂ → Common V₀ Rc₂ OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (m₁ m₂ : Nat) (Vd₂ : Common V₀ Rc₂ OnBytes.TableKey → Prop)
  (Rd₂ : Nat → Common V₀ Rc₂ OnBytes.TableKey → St → Prop) (Kp₂ : Place → St → St → Prop)
  (w₂ : Common V₀ Rc₂ OnBytes.TableKey)

include h in
/-- **Omega's pair**: at the shared chain's last state, under its invariant: in what is handed of
that chain's end Omega has a place, a tree stands there, and it bears the number 1. -/
theorem omega_pair_at_end {k₂ : Coins Bk₂} {e₂ : St}
    {mid₂ : Mid (Common V₀ Rc₂ OnBytes.TableKey) Y₀} {E₂ : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H₂ N Mg shape nothingLeft order wit table fixed
      m₁ m₂ Vd₂ Rd₂ Kp₂ w₂).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k₂ e₂ mid₂
      E₂)
    {e : OnBytes.Proof.SharedEnd} (he : Desc.K14.ended e₂ = some e) :
    ∃ (q : Nat × Nat) (T : OnBytes.Tree),
      (sharedOfEnd e).book.place[(sharedOfEnd e).omega]? = some q ∧
      (sharedOfEnd e).book.trees[q.1]? = some T ∧ T.number = 1 := by
  obtain ⟨ho, -, -, hseat⟩ := omega_written_at_shared_end Zp Np cF H₂ N Mg shape nothingLeft order
    wit table fixed m₁ m₂ Vd₂ Rd₂ Kp₂ w₂ h hA
  have h0 := hseat 0
  rw [omega_tenant_written] at h0
  unfold VerifiableInference.Desc.Sound.seatBy at h0
  obtain ⟨q, hq, hT⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨T, hT, e0⟩ := Option.map_eq_some_iff.1 hT
  have hn : 0 + T.number = 1 := congrArg Prod.fst e0
  unfold Desc.K14.ended at he
  dsimp only at he
  split at he
  · obtain rfl := Option.some.inj he
    refine ⟨q, T, ?_, hT, by omega⟩
    show e₂.book.place[e₂.loc.oOmega]? = some q
    rw [ho]
    exact hq
  · cases he

/-- **THE TEST SAYS YES AT THE RECORD THAT THE LAST CHAIN's START RETURNS**, from the two earlier
chains' invariants at their last borders. -/
theorem tied_ahead_at_ends {k₁ : Coins Bk} {e₁ : TS} {mid₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E₁ : Env}
    (hT₁ : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cF.blocksInOrder.length k₁
      e₁ mid₁ E₁)
    {k₂ : Coins Bk₂} {e₂ : St} {mid₂ : Mid (Common V₀ Rc₂ OnBytes.TableKey) Y₀} {E₂ : Env}
    (hT₂ : Thr (SharedThread.lettersShared Zp Np cF H₂ N Mg shape nothingLeft order wit table fixed
      m₁ m₂ Vd₂ Rd₂ Kp₂ w₂).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k₂ e₂ mid₂
      E₂)
    (x : ProofFile.InstPub) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x e₁ e₂ = .ok s) :
    tiedAheadB (LLT25.c2 Np).rounds s = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  rw [flat_358 h.scope h.reads O] at hT₁
  obtain ⟨f, e, -, hf, he, hst⟩ := start_at_last Zp Np cF x e₁ e₂ s hs
  obtain ⟨G, i₁, i₂, T₁, T₂, hG, hml, hmk, p1, p2, p3, t1, a1, t2, a2⟩ :=
    first_pairs_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT₁ hf
  obtain ⟨q, T, hq, hT, hn⟩ := omega_pair_at_end h H₂ N Mg shape nothingLeft order wit table fixed
    m₁ m₂ Vd₂ Rd₂ Kp₂ w₂ hT₂ he
  obtain ⟨⟨g, hb⟩, -, -, -, e5, e6, -, e8, -, -, -⟩ := start_gives _ f _ s hst
  have hmask : s.loc.mask = f.mask := by
    obtain ⟨fo, hfo, h3⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hst
    obtain ⟨-, -, -, -, q4, -⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hfo
    obtain ⟨-, -, es⟩ := start₃_inv _ _ _ _ h3
    rw [es]
    exact q4
  have htk : takenAhead s = some [(1, 1), (0, 1), (0, 82), (0, 82)] := by
    simp [takenAhead, hb, e5, e6, e8, hG, hq, hT, hml, hmask, hmk, p1, p2, p3, t1, t2, a1, a2, hn]
  unfold tiedAheadB
  rw [htk, own_rounds_written h]
  exact sources_written

end shared

end ends

end AtFullSide.K14

#print axioms AtFullSide.K14.place_mask_written
#print axioms AtFullSide.K14.omega_tenant_written
#print axioms AtFullSide.K14.sources_written
#print axioms AtFullSide.K14.sources_rejects
#print axioms AtFullSide.K14.sources_rejects_more
#print axioms AtFullSide.K14.sources_blind
#print axioms AtFullSide.K14.firstOfS_mask
#print axioms AtFullSide.K14.own_rounds_written
#print axioms AtFullSide.K14.first_pairs_at_end
#print axioms AtFullSide.K14.omega_pair_at_end
#print axioms AtFullSide.K14.tied_ahead_at_ends
