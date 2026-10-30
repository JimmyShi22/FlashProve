-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/SideAtFilling.lean: THE OUTPUT HEAD's OWN ROUNDS (kind K6):
which side the prover has at the member's place, at the base filling and at that filling read
through two readers. The first-chain clauses of SideIsTheHeadRowAtTheBase and
SideIsTheHeadRowAtTheFilling (Honest/K6/Term/Statements.lean).

WHAT IT IS NOT. Equations on lists of sides. Nothing on whether the side plays or is accepted. The
library's hypothesis on the first chain and "the maker returns" are premises.

  lotsApartAtTheBase        every lot of the base filling has no side of the kind, or K6's sides
  lotsApartAtTheFilling     the same at the filling read through
  sideIsTheOnlyOne_of_lots  from such a list of lots, at any filling: the first side at the member's
                            place is the row, and no other side of the first chain is of the kind
  sideAtTheBase, sideAtTheFilling   at the two fillings
  seatAtTheBase, seatAtTheFilling   the seat (K6HalfAt), the premise of the statements (P2)
-/
import Johnson.Desc.ProofFile.Honest.K6.Term.Statements
import Johnson.Desc.ProofFile.Honest.K6.Term.RowThrough
import Johnson.Desc.ProofFile.Honest.K6.Law.HalfAtWiderAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open VerifiableInference.Desc (Chain Place KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {W₀ W₀' Rc Rc' X₀ : Type}

/-- K6's lot as a filling holds it, at a reader of the committed digits by public part. -/
abbrev headLotAt (weights : Pub → W₀ → Weights) :
    HLot (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) Unit :=
  HLot.byPub weights fun wt => headLot headFitsB (headWit' id wt)

/-- **Every lot of the base filling has no side of the kind K6, or has K6's sides.** No premise. -/
theorem lotsApartAtTheBase (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      (∀ y ∈ M.halves Zq G, y.place.kind ≠ (IM.k6Place).kind) ∨
        M.halves Zq G = (headLotAt (Rc := IndexCommitterCoins) I.weights).halves Zq G := by
  intro M hM
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((hM | rfl) | rfl) | rfl
  · exact ho_wider I o S O Zq G M hM
  · refine .inl fun y hy e => ?_
    have hk := closeLotAt_kinds I S Zq G y hy
    rw [e] at hk
    cases hk
  · refine .inl fun y hy e => ?_
    have hk := proxLotAt_kinds I S Zq G y hy
    rw [e] at hk
    cases hk
  · refine .inl fun y hy e => ?_
    rw [wLotAt_halves] at hy
    cases hm : OnBytes.linMessageW Zq.first.lin with
    | none =>
      rw [hm] at hy
      cases hy
    | some msg =>
      rw [hm] at hy
      obtain rfl := List.mem_singleton.1 hy
      cases e

/-- K6's lot is among the base filling's. -/
theorem headLot_mem_base (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : headLotAt (Rc := IndexCommitterCoins) I.weights ∈ (onlineProverPartsInUse I o S O).lots := by
  rw [widerFillAtCPUOWM_lots]
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))

/-- K6's lot at the reader composed is K6's lot read through (headLot_through,
Honest/K6/Term/RowThrough.lean). -/
theorem headLotAt_through (readIndex : W₀' → W₀) (readRandomness : Rc' → Rc)
    (weights : Pub → W₀ → Weights) :
    (headLotAt (Rc := Rc') fun Z w => weights Z (readIndex w)) =
      HLot.thru (Local.thru readIndex readRandomness) (Local.thru readIndex readRandomness)
        (headLotAt (Rc := Rc) weights) :=
  (headLot_through readIndex readRandomness weights).symm

/-- **The same at the filling read through.** No premise. -/
theorem lotsApartAtTheFilling (readIndex : W₀' → W₀) (readRandomness : Rc' → IndexCommitterCoins)
    (namedIndex : W₀') (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zq : Pub)
    (G : Ground) :
    ∀ M ∈ (onlineFillingAt readIndex readRandomness namedIndex I S O).lots,
      (∀ y ∈ M.halves Zq G, y.place.kind ≠ (IM.k6Place).kind) ∨
        M.halves Zq G =
          (headLotAt (Rc := Rc') fun Z w => I.weights Z (readIndex w)).halves Zq G := by
  intro M hM
  obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.1 hM
  rcases lotsApartAtTheBase I OnBytes.secondHashFunction S O Zq G M₀ hM₀ with hk | he
  · refine .inl fun y hy => ?_
    obtain ⟨y₀, hy₀, rfl⟩ := List.mem_map.1 hy
    exact hk y₀ hy₀
  · refine .inr ?_
    rw [headLotAt_through readIndex readRandomness I.weights]
    show (M₀.halves Zq G).map _ = ((headLotAt (Rc := IndexCommitterCoins) I.weights).halves Zq G).map _
    rw [he]

/-- K6's lot, read through, is among the filling's. -/
theorem headLot_mem_filling (readIndex : W₀' → W₀) (readRandomness : Rc' → IndexCommitterCoins)
    (namedIndex : W₀') (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (headLotAt (Rc := Rc') fun Z w => I.weights Z (readIndex w)) ∈
      (onlineFillingAt readIndex readRandomness namedIndex I S O).lots := by
  rw [headLotAt_through readIndex readRandomness I.weights]
  exact List.mem_map_of_mem (headLot_mem_base I OnBytes.secondHashFunction S O)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : Pub} {Np : H2U.Places4}
  {cF : Chain TS Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **From such a list of lots, at any filling.** The library's hypothesis on the first chain and
"the maker returns" are premises. -/
theorem sideIsTheOnlyOne_of_lots (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Cells X₀ Unit} {A : OnlineProverWithDescription W₀ Rc Cells X₀ Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (weights : Pub → W₀ → Weights)
    (member : headLotAt weights ∈ P.lots)
    (apart : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ (IM.k6Place).kind) ∨
      M.halves A.Z A.G = (headLotAt weights).halves A.Z A.G) :
    SideIsTheOnlyOne A.H.first
      ⟨IM.k6Place, headRow (headWit' id (weights Zp) Zp A.G) (headNumbers Zp) IM.k6Place⟩ := by
  obtain ⟨G, hG⟩ := head_ground_at_head h
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid hG hA
  have one : (headLotAt (Rc := Rc) weights).halves A.Z A.G =
      [⟨IM.k6Place, headRow (headWit' id (weights Zp) Zp A.G) (headNumbers Zp) IM.k6Place⟩] := by
    rw [eZ, eG]
    exact headLot_one_half h hG fun Z' G' => headWit' id (weights Zp) Z' G'
  refine ⟨atPure_first_find_kind hA member apart ?_, fun q hq hk => ?_⟩
  · rw [one]
    exact List.find?_cons_of_pos (by simp)
  · rw [(atPure_ok hA).2.2.2.2.2.2.2.1] at hq
    obtain ⟨M, hM, hqM⟩ := List.mem_flatMap.1 hq
    rcases apart M hM with hn | he
    · exact absurd hk (hn q hqM)
    · rw [he, one] at hqM
      exact List.mem_singleton.1 hqM

/-- **At the base filling.** -/
theorem sideAtTheBase (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SideIsTheOnlyOne A.H.first (headSide id I Zp A.G) :=
  sideIsTheOnlyOne_of_lots h hA I.weights (headLot_mem_base I OnBytes.secondHashFunction S O)
    (lotsApartAtTheBase I OnBytes.secondHashFunction S O A.Z A.G)

/-- **At the filling read through.** -/
theorem sideAtTheFilling (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (readIndex : W₀' → W₀)
    (readRandomness : Rc' → IndexCommitterCoins) (namedIndex : W₀') (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineFillingAt readIndex readRandomness namedIndex I S O) = .ok A) :
    SideIsTheOnlyOne A.H.first (headSide readIndex I Zp A.G) :=
  sideIsTheOnlyOne_of_lots h hA (fun Z w => I.weights Z (readIndex w))
    (headLot_mem_filling readIndex readRandomness namedIndex I S O)
    (lotsApartAtTheFilling readIndex readRandomness namedIndex I S O A.Z A.G)

/-- **The seat, at the base filling**: the premise of the statements (P2). -/
theorem seatAtTheBase (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    K6HalfAt Zp A.H (headWit' id (I.weights Zp) Zp A.G) :=
  (sideAtTheBase h I S O hA).1

/-- **The seat, at the filling read through.** -/
theorem seatAtTheFilling (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (readIndex : W₀' → W₀)
    (readRandomness : Rc' → IndexCommitterCoins) (namedIndex : W₀') (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineFillingAt readIndex readRandomness namedIndex I S O) = .ok A) :
    K6HalfAt Zp A.H (headWit' id (fun w => I.weights Zp (readIndex w)) Zp A.G) :=
  (sideAtTheFilling h readIndex readRandomness namedIndex I S O hA).1

end ProofFile.Honest.K6.Term

#print axioms ProofFile.Honest.K6.Term.lotsApartAtTheBase
#print axioms ProofFile.Honest.K6.Term.headLot_mem_base
#print axioms ProofFile.Honest.K6.Term.headLotAt_through
#print axioms ProofFile.Honest.K6.Term.lotsApartAtTheFilling
#print axioms ProofFile.Honest.K6.Term.headLot_mem_filling
#print axioms ProofFile.Honest.K6.Term.sideIsTheOnlyOne_of_lots
#print axioms ProofFile.Honest.K6.Term.sideAtTheBase
#print axioms ProofFile.Honest.K6.Term.sideAtTheFilling
#print axioms ProofFile.Honest.K6.Term.seatAtTheBase
#print axioms ProofFile.Honest.K6.Term.seatAtTheFilling
