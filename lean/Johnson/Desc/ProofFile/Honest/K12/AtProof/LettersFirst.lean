-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/LettersFirst.lean: the index-mask member of the last
chain's proximity test and its sender, at the filling onlineProverPartsInUse (K1/Law/WSideAtFill.lean),
at any index type: one job term on both sides, and the sender's half is what the search at the
first opening's place finds.

  mem_ext                 two members with one entry, one shape and one reader of rows are one
  first_member_is_own     at a message without main rows the member of K1.firstJob is the member
                          of the sender's job firstOfLot (FirstMemberSent.lean), at any lift
  first_member_any_size   so the sizes S reach no field of that member
  k1LotOf                 K1's lot as the filling lays it
  first_lot_head          that lot's first half is the sender's, by rfl
  first_lot_mem           that lot is a lot of the filling
  wLot_place              W's lot stands at W's place
  lots_at_first_place     every lot of the filling has no half at the first opening's place, or
                          K1's halves
  first_found             the search at that place, in the prover that onlineProverFromPublicFiles returns, finds the
                          sender's half
  firstMemberRows, jobW_first_member   the first member of jobW, by rfl
  first_member_is_sent    where jobRealW returns at secondW's letters and the message has no main
                          row: its first member is memK1 of the sender's job, at the input of the
                          sender's half

By what. rowsR_no_main (SendersW.lean): a message without main rows reads no data. So where the
job K1.firstJob and the sender's job differ, in their data, nothing is read. The reader of the
index and the sizes fall with it: the member is all coins.

Limits.
- hm, that the message has no main row, is a premise here; it is paid under the head at the full
  size: AtFullSide/K12/LettersAtHead.lean.
- That the carried stretch holds the sender's coins is not here.
- X := Unit and LongLots.plain: the one filling.
- first_found is conditional on onlineProverFromPublicFiles's return at the filling.
- That a half plays is not said. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.FirstMemberSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (FileDescription KindName Place)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest.K12.Light (ManyJob Mem firstsOf)
open Johnson.Prover.Send (shapeAt)

/-- Two members with one entry, one shape and one reader of rows are one. -/
theorem mem_ext {W X : Type} {a b : Mem W X} (hs : a.sent = b.sent) (hh : a.shape = b.shape)
    (hr : a.rows = b.rows) : a = b := by
  cases a
  cases b
  dsimp only at hs hh hr
  subst hs
  subst hh
  subst hr
  rfl

/-- **At a message without main rows the index-mask member is the sender's own.** -/
theorem first_member_is_own {W X : Type} (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (Z : Pub)
    (G : Ground) (readers : W → Readers) (lift : W → K1.PlaceIn Inst) (at_ : Addr) (k : Nat)
    (fs : Option Nat × Option Nat) (hm : (shapeAt (firstParOf Z G) k).mainRows = 0) :
    memK1 (K1.firstJob S Z G : K1.SendJob Readers X) readers at_ k fs =
      memK1 (firstOfLot (X := X) o S Z G) lift at_ k fs := by
  refine mem_ext rfl rfl ?_
  funext w fr St
  exact congrArg (psOfRows (firstParOf Z G) k)
    (rowsR_no_main (firstParOf Z G) (K1.firstRide G.first) _ _ _ k hm)

/-- **The sizes reach no field of that member.** -/
theorem first_member_any_size {W X : Type} (S S' : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground)
    (readers : W → Readers) (at_ : Addr) (k : Nat) (fs : Option Nat × Option Nat)
    (hm : (shapeAt (firstParOf Z G) k).mainRows = 0) :
    memK1 (K1.firstJob S Z G : K1.SendJob Readers X) readers at_ k fs =
      memK1 (K1.firstJob S' Z G : K1.SendJob Readers X) readers at_ k fs := by
  refine mem_ext rfl rfl ?_
  funext w fr St
  exact congrArg (psOfRows (firstParOf Z G) k)
    (rowsR_no_main (firstParOf Z G) (K1.firstRide G.first) _ _ _ k hm)

variable {W₀ : Type}

/-- K1's lot, as the filling lays it. -/
abbrev k1LotOf (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit :=
  HLot.byPub I.weights (LongLots.plain o S O).k1

/-- **The first half of K1's lot is the sender's.** -/
theorem first_lot_head (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Z : Pub) (G : Ground) :
    ∃ rest, (k1LotOf I o S O).halves Z G =
      K1.placeHalf (inOf (lettersW I Z)) (firstOfLot o S Z G) :: rest :=
  ⟨_, rfl⟩

/-- K1's lot is a lot of the filling. -/
theorem first_lot_mem (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    k1LotOf I o S O ∈ (onlineProverPartsInUse I o S O).lots :=
  List.mem_cons_self ..

/-- W's lot stands at W's place. -/
theorem wLot_place {X : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments) (Z : Pub)
    (G : Ground) : ∀ x ∈ (wLotAt (X := X) I o O).halves Z G, x.place = ⟨1, none, 4, .K1⟩ := by
  intro x hx
  rw [wLotAt_halves] at hx
  cases hm : OnBytes.linMessageW Z.first.lin with
  | none =>
    rw [hm] at hx
    cases hx
  | some msg =>
    rw [hm] at hx
    obtain rfl := List.mem_singleton.1 hx
    rfl

/-- **Every lot of the filling has no half at the first opening's place, or K1's halves.** No
premise. -/
theorem lots_at_first_place (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      (∀ g ∈ M.halves Z G, g.place ≠ ⟨1, some 0, 1, .K1⟩) ∨
      M.halves Z G = (k1LotOf I o S O).halves Z G := by
  intro M hM
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    by_cases k : q.2 = .K1
    · have e' : q = (HLot.byPub I.weights (LongLots.plain o S O).k1, .K1) :=
        List.inj_on_of_nodup_map widerPairs_nodup hq (List.Mem.head _) k
      rw [e']
      exact .inr rfl
    · refine .inl fun g hg e => ?_
      have hk := (FirstFill.widerKinds I o S O Z G).all q hq g hg
      rw [e] at hk
      exact k hk.symm
  · refine .inl fun g hg e => ?_
    have hk := closeLotAt_kinds I S Z G g hg
    rw [e] at hk
    have hk' : KindName.K1 = KindName.K10 := hk
    cases hk'
  · refine .inl fun g hg e => ?_
    have hk := proxLotAt_kinds I S Z G g hg
    rw [e] at hk
    have hk' : KindName.K1 = KindName.K12 := hk
    cases hk'
  · refine .inl fun g hg e => ?_
    rw [wLot_place I o O Z G g hg] at e
    cases e

/-- **The search at the first opening's place finds the sender's half.** -/
theorem first_found {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A) :
    A.H.first.find? (fun g => g.place == ⟨1, some 0, 1, .K1⟩) =
      some (K1.placeHalf (inOf (lettersW I A.Z)) (firstOfLot o S A.Z A.G)) := by
  obtain ⟨rest, e⟩ := first_lot_head I o S O A.Z A.G
  refine atPure_first_find hA (first_lot_mem I o S O) (lots_at_first_place I o S O A.Z A.G) ?_
  rw [e]
  exact List.find?_cons_of_pos (beq_self_eq_true _)

/-- The first rows of the blocks of jobW's first member. -/
def firstMemberRows (PI PW : VerifiableInference.Desc.K1.Par) (sO : OnBytes.OracleShape) :
    Option Nat × Option Nat :=
  (firstsOf (shapesW PI PW sO)).getD 0 (none, none)

/-- jobW's first member. -/
theorem jobW_first_member {W X Xi : Type} (q : VerifiableInference.Desc.K12.P12)
    (door : W → Front X → T12) (JI : K1.SendJob Readers X) (JW : K1.SendJob (K1.PlaceIn Xi) X)
    (A : ProofFile.Honest.K14.SendPub) (readers : W → Readers) (wit : W → K1.PlaceIn Xi)
    (ask : W → ProofFile.Honest.K14.Ask) (n₁ : Nat) :
    (jobW q door JI JW A readers wit ask n₁).mems[0]? =
      some (memK1 JI readers senderI (JI.P.sent.size - 1) (firstMemberRows JI.P JW.P
        ((ProofFile.Honest.K14.jobOmega ⟨A.P, n₁ + A.atPoint⟩).Q.sent.getD 0 default).shape)) := rfl

/-- **ONE JOB TERM AT THE INDEX-MASK MEMBER.** Where jobRealW returns at secondW's letters and the
message has no main row: the first member is memK1 of the sender's job, and K1's lot has that job's
half first, at the same input. -/
theorem first_member_is_sent (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (Fd : FileDescription Inst) (enter : Fd.S₃ → Except String T12) (Z : Pub) (G : Ground)
    {M : ManyJob (Local W₀ IndexCommitterCoins Inst Cells) Unit}
    (hM : jobRealW S Fd enter O.pile (K1.lotNo o Z) (lettersW I Z) (fun w => I.weights Z w.w₀)
      (fun P w => randAt P w.rc) Z G = some M)
    (hm : (shapeAt (firstParOf Z G) ((firstParOf Z G).sent.size - 1)).mainRows = 0) :
    ∃ fs, M.mems[0]? = some (memK1 (firstOfLot o S Z G) (inOf (lettersW I Z)) senderI
        ((firstParOf Z G).sent.size - 1) fs) ∧
      ∃ rest, (k1LotOf I o S O).halves Z G =
        K1.placeHalf (inOf (lettersW I Z)) (firstOfLot o S Z G) :: rest := by
  unfold jobRealW at hM
  obtain ⟨F, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hM
  exact ⟨_, (jobW_first_member _ _ _ _ _ _ _ _ _).trans (congrArg some
    (first_member_is_own o S Z G (lettersW I Z) (inOf (lettersW I Z)) senderI _ _ hm)),
    first_lot_head I o S O Z G⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.mem_ext
#print axioms ProofFile.Honest.K12.AtProof.first_member_is_own
#print axioms ProofFile.Honest.K12.AtProof.first_member_any_size
#print axioms ProofFile.Honest.K12.AtProof.first_lot_head
#print axioms ProofFile.Honest.K12.AtProof.first_lot_mem
#print axioms ProofFile.Honest.K12.AtProof.wLot_place
#print axioms ProofFile.Honest.K12.AtProof.lots_at_first_place
#print axioms ProofFile.Honest.K12.AtProof.first_found
#print axioms ProofFile.Honest.K12.AtProof.jobW_first_member
#print axioms ProofFile.Honest.K12.AtProof.first_member_is_sent
