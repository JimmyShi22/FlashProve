-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/HasCoinsOfRows.lean: THE SHARED "SENDING" (the kind K1) AND THE
BOOK OF COINS: THE RECORD's FIELD hasCoins (K1Seated, Honest/K1/Seated.lean) AT EACH OF THE KIND's
52 SENDERS ON THE FIRST CHAIN, IN THE FIELD's OWN TEXT, AT ANY BOOK WHOSE FIRST TABLE BEGINS WITH
THE MAKER's ROWS AT THE WRITTEN DATA. PUBLIC DATA ALONE: how many coins a part has, never what they
are. Eight theorems; no definition.

THE ONE PREMISE ON THE BOOK, hB, in every statement's own binders: there are rs and sw with rowsIn
‹the written description's first chain› ‹the written sendings› ‹its second chain's rounds› = .ok rs
and Bk.first = rs ++ sw. IT IS PAID NOWHERE HERE. At the prover's own book A.B it wants three things
of other houses' files: what "bookWhole returns" gives of the first table · the congruence from the
head's description to the written one · that the maker's sendings are the written ones.

  - dueAt_append_hit: general: a look-up that hits in r0 answers alike in r0 ++ sw.
  - k1Rows_hit: k1RowsW (HasCoinsWritten.lean) as sentences, WITH "= some": a row IS there at each
    of the 52 addresses. (hasCoinsW there says less: dueAt has a default.)
  - hasCoins_written_of: under hB: the field's equation at the three kinds of written plans.
  - hasCoins_short_fails: A NEGATIVE TEST ON THE PREMISE's USE: at the book with no row the
    opening's equation is false: so the equations are no gift of dueAt's default.
  - hasCoins_head_of: UNDER h (the library's head: A HYPOTHESIS), O (the description opened), hB:
    at the plans and rides of the description's own ground: the opening, the fifty, AND W.
  - hasCoins_two_of, hasCoins_fifty_of, hasCoins_w_of: UNDER h, hA (onlineProverFromPublicFiles returns A, at any
    filling), hB, and hJ (an equation that a caller meets by rfl): THE FIELD, TO THE LETTER: dueAt
    (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride, at the jobs of RecordPaid.lean and
    RecordAtW.lean, ACROSS THE TWO GROUNDS (atPure_at_laid_ground, Honest/AtHeadGround.lean).

Limits. Bk IS A FREE LETTER: that A.B meets hB is not said. THE FULL SIZE ALONE. THE FIRST CHAIN
ALONE. IT STANDS OVER FILES OF ProofFile's THAT ARE ON NO SEAL. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.HasCoinsWritten
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.PiecesAndPort
import Johnson.Desc.ProofFile.Honest.AtHeadGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K1 (parGF parWF placeL fiftyB fifty_of)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)

/-- A look-up that hits in r0 answers alike in r0 ++ sw. General. -/
theorem dueAt_append_hit {r0 sw : List (Addr × Due)} {a : Addr} {d : Due}
    (h : r0.lookup a = some d) : dueAt (r0 ++ sw) a = d := by
  unfold dueAt
  rw [List.lookup_append, h]
  rfl

/-- **A ROW IS THERE AT EACH OF THE 52 ADDRESSES, AND ITS COUNT IS OURS**: k1RowsW as sentences. -/
theorem k1Rows_hit : ∃ rs, rowsIn P2Law.ProofPlan.WP.first.blocksInOrder Johnson.G.proofSendsFull.1
      (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds)) = .ok rs ∧
    rs.lookup (⟨parGF.place, 0⟩ : Addr) = some (dueR parGF (rideOf (firstFold K1.qFull))) ∧
    (∀ l, l < 25 → ∀ d, rs.lookup (⟨(placeL l d).place, 0⟩ : Addr) =
      some (dueR (placeL l d) (rideOf none))) ∧
    rs.lookup (⟨parWF.place, 0⟩ : Addr) = some (dueR parWF (rideOf (wFold K1.qFull.lin))) := by
  have h := k1RowsW
  cases e : (rowsIn P2Law.ProofPlan.WP.first.blocksInOrder Johnson.G.proofSendsFull.1
      (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds))) with
  | error s =>
    rw [e] at h
    simp at h
  | ok rs =>
    rw [e] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨rs, rfl, h.1.1, fun l hl d => of_decide_eq_true (fifty_of h.1.2 l hl d), h.2⟩

/-- **THE FIELD's EQUATION AT THE WRITTEN PLANS**, at a book whose first table begins with the
written rows. -/
theorem hasCoins_written_of {Bk : ProverCoinCounts}
    (hB : ∃ rs sw, rowsIn P2Law.ProofPlan.WP.first.blocksInOrder Johnson.G.proofSendsFull.1
      (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds)) = .ok rs ∧ Bk.first = rs ++ sw) :
    dueAt (Bk.rowsOf 0) ⟨parGF.place, 0⟩ = dueR parGF (rideOf (firstFold K1.qFull)) ∧
    (∀ l, l < 25 → ∀ d,
      dueAt (Bk.rowsOf 0) ⟨(placeL l d).place, 0⟩ = dueR (placeL l d) (rideOf none)) ∧
    dueAt (Bk.rowsOf 0) ⟨parWF.place, 0⟩ = dueR parWF (rideOf (wFold K1.qFull.lin)) := by
  obtain ⟨rs, sw, e, hf⟩ := hB
  obtain ⟨rs', e', h1, h2, h3⟩ := k1Rows_hit
  obtain rfl : rs = rs' := Except.ok.inj (e.symm.trans e')
  have hr : Bk.rowsOf 0 = rs ++ sw := hf
  rw [hr]
  exact ⟨dueAt_append_hit h1, fun l hl d => dueAt_append_hit (h2 l hl d), dueAt_append_hit h3⟩

/-- A negative test: at the book with no row the opening's equation is false. -/
theorem hasCoins_short_fails :
    dueAt ((⟨[], [], [], [], []⟩ : ProverCoinCounts).rowsOf 0) ⟨parGF.place, 0⟩ ≠
      dueR parGF (rideOf (firstFold K1.qFull)) := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **AT THE PLANS AND RIDES OF THE DESCRIPTION's OWN GROUND**, under the head: the opening, the
fifty and W. -/
theorem hasCoins_head_of (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np)) {Bk : ProverCoinCounts}
    (hB : ∃ rs sw, rowsIn P2Law.ProofPlan.WP.first.blocksInOrder Johnson.G.proofSendsFull.1
      (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds)) = .ok rs ∧ Bk.first = rs ++ sw) :
    dueAt (Bk.rowsOf 0) ⟨(K1.firstPar Bs.G₀.first (K1.gpOf Zp)).place, 0⟩ =
      dueR (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (rideOf (firstFold Bs.G₀.first)) ∧
    (∀ l, l < 25 → ∀ d, dueAt (Bk.rowsOf 0) ⟨(K1.parL Zp Bs.G₀ l d).place, 0⟩ =
      dueR (K1.parL Zp Bs.G₀ l d) (rideOf none)) ∧
    dueAt (Bk.rowsOf 0) ⟨(K1.parW Zp.first (wGp Zp) 4 wMsgFull).place, 0⟩ =
      dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin)) := by
  obtain ⟨h1, h2, h3⟩ := hasCoins_written_of hB
  refine ⟨?_, ?_, ?_⟩
  · rw [K1.eG_atAll h O (K1.pin1_atAll h),
      firstFold_shape (q' := K1.qFull) ((K1.hs_atAll h O (K1.pin1_atAll h)).trans ?_)]
    · exact h1
    · rfl
  · intro l hl d
    rw [parL_written h O l d]
    exact h2 l hl d
  · rw [parW_written h O,
      (K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h)).lin]
    exact h3

/-- **hasCoins AT NUMBER 2**, in the record's own text, at the job of RecordPaid.lean. -/
theorem hasCoins_two_of (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {Bk : ProverCoinCounts}
    (hB : ∃ rs sw, rowsIn P2Law.ProofPlan.WP.first.blocksInOrder Johnson.G.proofSendsFull.1
      (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds)) = .ok rs ∧ Bk.first = rs ++ sw)
    {Xi Y : Type} (first : Nat) (Dd : RowDataOf Xi) {J : SendJob (PlaceIn Xi) Y}
    (hJ : J = placeJob (K1.firstPar A.G.first (K1.gpOf A.Z)) first (firstFold A.G.first) Dd) :
    dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  subst hJ
  show dueAt (Bk.rowsOf 0) ⟨(K1.firstPar A.G.first (K1.gpOf A.Z)).place, 0⟩ =
    dueR (K1.firstPar A.G.first (K1.gpOf A.Z)) (rideOf (firstFold A.G.first))
  rw [eZ, eG]
  exact (hasCoins_head_of h O hB).1

/-- **hasCoins AT EACH OF THE FIFTY**, in the record's own text, at the job of RecordPaid.lean. -/
theorem hasCoins_fifty_of (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {Bk : ProverCoinCounts}
    (hB : ∃ rs sw, rowsIn P2Law.ProofPlan.WP.first.blocksInOrder Johnson.G.proofSendsFull.1
      (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds)) = .ok rs ∧ Bk.first = rs ++ sw)
    {Xi Y : Type} {l : ℕ} (hl : l < 25) (d : Bool) (first : Nat) (Dd : RowDataOf Xi)
    {J : SendJob (PlaceIn Xi) Y}
    (hJ : J = laterJobAt A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1) first
      Dd) :
    dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  subst hJ
  show dueAt (Bk.rowsOf 0)
      ⟨(K1.parLater A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1)).place, 0⟩ =
    dueR (K1.parLater A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1))
      (rideOf none)
  rw [eZ, eG, ← parL_later]
  exact (hasCoins_head_of h O hB).2.1 l hl d

/-- **hasCoins AT NUMBER 356**, in the record's own text, at the job of RecordAtW.lean. -/
theorem hasCoins_w_of (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    (hB : ∃ rs sw, rowsIn P2Law.ProofPlan.WP.first.blocksInOrder Johnson.G.proofSendsFull.1
      (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds)) = .ok rs ∧ Bk.first = rs ++ sw)
    {Xi Y : Type} (first : Nat) (Dw : RowDataOf Xi) {J : SendJob (PlaceIn Xi) Y}
    (hJ : J = wJobAt Zp.first (wGp Zp) 4 wMsgFull first Dw) :
    dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  subst hJ
  exact (hasCoins_head_of h O hB).2.2

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.dueAt_append_hit
#print axioms ProofFile.Honest.K1.k1Rows_hit
#print axioms ProofFile.Honest.K1.hasCoins_written_of
#print axioms ProofFile.Honest.K1.hasCoins_short_fails
#print axioms ProofFile.Honest.K1.hasCoins_head_of
#print axioms ProofFile.Honest.K1.hasCoins_two_of
#print axioms ProofFile.Honest.K1.hasCoins_fifty_of
#print axioms ProofFile.Honest.K1.hasCoins_w_of
