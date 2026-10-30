-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/AtBase355.lean: kind K13, the members' batching: THE FIVE
STATEMENTS AT NUMBER 355 OF THE PROOF FILE's FIRST CHAIN (FiveAt355.lean of this folder) AT THE
PROVER THAT THE MAKER `onlineProverFromPublicFiles` RETURNS AT THE WIDE FILLING `onlineProverPartsInUse I o S O`
(Honest/K1/Law/WSideAtFill.lean): the filling which the honest prover's text reads through. The
index's type, the input I and the book at which the thread is typed are variables. Statements with
their proofs: calls; no definition. THE FULL SIZE ALONE, AT THE FORMAT's SECOND HASH FUNCTION ALONE:
all
under the library's one hypothesis h (`P5J.AtMgA`) and hA: the maker returns A.

Main names, each with ALL its premises beside h and hA:
  `k13_lot_in_wide`, `k13_alone_in_wide`: the kind's lot is one of the filling's thirteen; each of
    the thirteen has no side at a place of the kind K13, or is that lot. No premise at all.
  `k13_half_at_base`: **the sender that a search of A.H.first finds at the place of number 355 is
    `proverSideOfClaimCombination (I.weights Zp) (O.pile Zp A.G) h.𝔇.P13`.** None.
  `k13_playsS_at_base`: **`PlaysS` at 355.** None.
  `k13_acceptedS_at_base`: **`AcceptedS` at 355.** hO: O.pile is the written filler `pileAnyK3`; hb:
    b₀ ≤ 355.
  `k13_left_at_csHead`: `K13Left` at b₀ := 339 and the written list `csHead`, at any prover: hTo,
    hOf: the two sentences on the clause Kp. (It takes neither hA nor the filling.)
  `k13_ties_at_base`: `K13Ties`: hO; hM (`MatTie`); hC (`CoinsTie`).
  `k13_five_at_base`: **the five at 355**, at b₀ := 339 and `csHead`: hO; `K13Left`; hM; hC.

What hM and hC speak of. hM: the Script, the one input w, and I.weights. hC: the Script, the
book at which the thread is typed, and kind K1's sender of the index masks' message. The book is a
variable here; the proofs of hC that are known ask that it be the maker's own, A.B; the first of
them asks beside that kind K1's record at the opening and that job's plan and ride:
`k13_coinsTie_at_maker` (AtFullSide/K13/CoinsTieAtMaker.lean).

Limits. The filling is defined in Honest/K1/Law/WSideAtFill.lean. This file does not show that the
maker returns at it: these statements are worth what that filling is worth. No
statement here is at a named O: that the honest prover's O has the written filler is by its text
(`openHonest`, Honest/OpenHonest.lean).

What is not claimed. `MatTie`, `CoinsTie` at any Script; anything on Kp. That h holds at any public
files; that the maker returns. Anything at the prover read through: the statements stand at the
prover before it is read through. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.FiveAt355
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13.Honest (K13KeepsAll)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)

variable {W₀ : Type}

/-! ## The kind's lot in the wide filling -/

/-- The kind's lot is one of the filling's. -/
theorem k13_lot_in_wide (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) :
    HLot.byPub I.weights (LongLots.plain o S O).k13 ∈ (onlineProverPartsInUse I o S O).lots := by
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots]
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  exact List.mem_map.2 ⟨(HLot.byPub I.weights (LongLots.plain o S O).k13, .K13),
    by simp [widerPairs], rfl⟩

/-- **Each of the filling's lots has no side at a place of the kind K13, or is the kind's lot.** No
premise. -/
theorem k13_alone_in_wide (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      (∀ y ∈ M.halves Zq G, y.place.kind ≠ KindName.K13) ∨
        M.halves Zq G = (HLot.byPub I.weights (LongLots.plain o S O).k13).halves Zq G := by
  intro M hM
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((hM | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at hM
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hM
    by_cases e : q.2 = .K13
    · have e' : q = (HLot.byPub I.weights (LongLots.plain o S O).k13, .K13) :=
        List.inj_on_of_nodup_map widerPairs_nodup hq (by simp [widerPairs]) e
      rw [e']
      exact .inr rfl
    · refine .inl fun y hy hk => e ?_
      rw [← (FirstFill.widerKinds I o S O Zq G).all q hq y hy, hk]
  · refine .inl fun y hy hk => ?_
    rw [closeLotAt_kinds I S Zq G y hy] at hk
    cases hk
  · refine .inl fun y hy hk => ?_
    rw [proxLotAt_kinds I S Zq G y hy] at hk
    cases hk
  · refine .inl fun y hy hk => ?_
    rw [wLotAt_halves] at hy
    cases hm : OnBytes.linMessageW Zq.first.lin with
    | none =>
      rw [hm] at hy
      cases hy
    | some msg =>
      rw [hm] at hy
      obtain rfl := List.mem_singleton.1 hy
      cases hk

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
  (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A)

include hA in
/-- **WHICH SENDER IS FOUND AT THE PLACE OF NUMBER 355.** -/
theorem k13_half_at_base :
    ∀ blk, cF.blocksInOrder[355]? = some blk →
      (A.H.first.find? fun g => g.place == blk.place) =
        some (proverSideOfClaimCombination (I.weights Zp) (O.pile Zp A.G) h.𝔇.P13) := by
  obtain ⟨hZ, -⟩ := atPure_at_laid h.laid hA
  have q := k13_half_of_lots h hA (I.weights A.Z) O.pile (k13_lot_in_wide I o S O) rfl
    (k13_alone_in_wide I o S O A.Z A.G)
  rw [hZ] at q
  exact q

variable {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

include hA in
/-- **`PlaysS` AT 355, AT THE BASE PROVER**: from h and hA alone. -/
theorem k13_playsS_at_base :
    PlaysS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 355 :=
  k13_playsS_at_355 h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
    (k13_half_at_base h I o S O hA)

include hA in
/-- **`AcceptedS` AT 355, AT THE BASE PROVER**, at every fall: from h, hA, that the filling's filler
of the pile is the written one, and b₀ ≤ 355. -/
theorem k13_acceptedS_at_base (hO : O.pile = pileAnyK3) (hb : b₀ ≤ 355)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall 355 :=
  k13_accepted_of_lots h hA (I.weights A.Z) (k13_lot_in_wide I o S O)
    (by rw [← hO]; rfl) (k13_alone_in_wide I o S O A.Z A.G) Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said hb fall

variable (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)

/-- **WHAT IS LEFT OF `K13Left`**, at b₀ := 339 and the written list of the thread's other clauses:
the two sentences on Kp. General in the prover. -/
theorem k13_left_at_csHead {W₁ Rc Ky Tr X₀ X : Type} (H : Prover W₁ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q' : Script Bk (Local W₁ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (Vd' : Local W₁ Rc ProofFile.Inst Tr → Prop) (w' : Local W₁ Rc ProofFile.Inst Tr)
    (hTo : ∀ s s', Kp ⟨1, none, 3, .K13⟩ s s' → K13KeepsAll h.𝔇.P13 s s')
    (hOf : ∀ blk, cF.blocksInOrder[355]? = some blk → ∀ k s m E ds y cols s',
      Thr (lettersHead h H Q' test carryX item n₁ n₂ 339 Vd' (ridersOf (csHead ν st R)) Kp
        w').thread 355 k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q' test carryX item n₁ n₂ 339 Vd' (ridersOf (csHead ν st R)) Kp
        w').thread.Stepped blk k s m E ds y cols s' →
      Kp ⟨1, none, 3, .K13⟩ s s') :
    K13Left h H Q' test carryX item n₁ n₂ 339 Vd' (csHead ν st R) Kp w' where
  reply := by omega
  keepsTo := hTo
  keepsOf := hOf
  stays := fun c hc _ h2 => absurd h2 (by have := (csHead_none_at_355 hc).1; omega)
  none := fun c hc => (csHead_none_at_355 hc).2

include hA in
/-- **WHAT IS LEFT OF `K13Ties` AT THE BASE PROVER**: the two ties. -/
theorem k13_ties_at_base (hO : O.pile = pileAnyK3)
    (hM : MatTie (lettersHead h A.H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) Kp w)
      (I.weights Zp) (pileAnyK3 Zp A.G) h.𝔇.P13 (k13ReaderAt h))
    (hC : CoinsTie (lettersHead h A.H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) Kp w)
      355 (I.weights Zp) (pileAnyK3 Zp A.G) h.𝔇.P13 (k13ReaderAt h)) :
    K13Ties h A.H Q test carryX item n₁ n₂ 339 Vd (csHead ν st R) Kp w (I.weights Zp) A.G where
  half := by
    rw [← hO]
    exact k13_half_at_base h I o S O hA
  mat := hM
  coins := hC

include hA in
/-- **THE FIVE STATEMENTS AT 355, AT THE BASE PROVER.** -/
theorem k13_five_at_base (hO : O.pile = pileAnyK3)
    (L : K13Left h A.H Q test carryX item n₁ n₂ 339 Vd (csHead ν st R) Kp w)
    (hM : MatTie (lettersHead h A.H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) Kp w)
      (I.weights Zp) (pileAnyK3 Zp A.G) h.𝔇.P13 (k13ReaderAt h))
    (hC : CoinsTie (lettersHead h A.H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) Kp w)
      355 (I.weights Zp) (pileAnyK3 Zp A.G) h.𝔇.P13 (k13ReaderAt h))
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    PlaysS (lettersHead h A.H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) Kp w).thread
        Said 355 ∧
      BehindS (lettersHead h A.H Q test carryX item n₁ n₂ 339 Vd
        (ridersOf (csHead ν st R)) Kp w).thread
        Said 355 ∧
      ExchangeS (lettersHead h A.H Q test carryX item n₁ n₂ 339 Vd
        (ridersOf (csHead ν st R)) Kp w).thread
        Said 355 ∧
      RidesPastS (lettersHead h A.H Q test carryX item n₁ n₂ 339 Vd
        (ridersOf (csHead ν st R)) Kp w).thread
        Said 355 ∧
      AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ 339 Vd
        (ridersOf (csHead ν st R)) Kp w).thread
        Said fall 355 := by
  obtain ⟨Bs, hB⟩ := base_at_head h
  obtain ⟨hZ, -⟩ := atPure_at_laid h.laid hA
  exact k13_five_at_355 h A.H Q test carryX item n₁ n₂ 339 Vd (csHead ν st R) Kp w L
    (k13_ties_at_base h I o S O hA Q test carryX item n₁ n₂ Vd Kp w ν st R hO hM hC) hB
    (base_ground_atPure hB hA hZ) Said fall

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_lot_in_wide
#print axioms ProofFile.Honest.K13.k13_alone_in_wide
#print axioms ProofFile.Honest.K13.k13_half_at_base
#print axioms ProofFile.Honest.K13.k13_playsS_at_base
#print axioms ProofFile.Honest.K13.k13_acceptedS_at_base
#print axioms ProofFile.Honest.K13.k13_left_at_csHead
#print axioms ProofFile.Honest.K13.k13_ties_at_base
#print axioms ProofFile.Honest.K13.k13_five_at_base
