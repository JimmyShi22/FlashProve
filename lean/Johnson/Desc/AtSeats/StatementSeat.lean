-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/StatementSeat.lean: AT THE
PROOF FILE's SEAT EVERY SUB-PROTOCOL OF THE FIRST CHAIN KEEPS A RELATION ON THE STATEMENT THAT MEETS
StKeeps; at FitStays: every ledger stays in order; so every ledger is in order at every reached
state.

  seatKeeps_by, seatBack_by   the two structures of Johnson/IMR/SeatKeeps.lean, at ByS R.
  descPure_by      so, by descPure_flat: every sub-protocol of the flat list whose own test on the
                   list of rounds passes keeps ByS R.
  descPure_ledgers   the instance.
  s0_first, startS_facts   THE START, AT EVERY PUBLIC PART OF AN INSTANCE, with no premise on the
                   request: no message, no pending row, between two links: in both arms of
                   ProofFile.startS (the first state with the request's words; the blank state).
  descPure_reach_ledgers   THE FIELD ON THE LEDGERS: its one premise left: every sub-protocol's own
                   test on the list of rounds passes.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.
-/
import Johnson.IMR.SeatKeeps
import Johnson.IMR.RecRun
import Johnson.Desc.K13.Law.StatementSeated
import Johnson.Desc.K13.Keeps
import Johnson.Desc.K13.Law.LedgersReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K13.Law (StKeeps atFinish_keeps stKeeps_fit FitStays LedgersFit
  reach_ledgers_plan)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Pub)

variable {R : Statement → Statement → Prop}

theorem seatKeeps_by (K : StKeeps R) : SeatKeeps (ByS R) where
  refl := by_refl K
  trans := by_trans K
  frames := fun _ h => framesOf_by K h
  k1First := fun q gp _ => firstAtS_by K q gp
  k1Later := fun q gp l p m a _ => laterAt_by K q gp l p m a
  reads := fun h => whole_by K (readsQuietAt_quiet h)
  k3 := fun c r X cs' sh' a _ h => whole_by K (theStated_quiet c r X cs' sh' a h)
  k4 := fun p => whole_by K (blockAtC_quiet p)
  k5 := fun W l g bf _ h => whole_by K (k5AtN_quiet W l g bf h)
  k6 := fun h => whole_by K (seatedClaims_quiet h)
  k7 := fun W l => whole_by K (k7Of_quiet W l)
  k8 := fun p => whole_by K (k8Whole_quiet p)
  k11 := fun P => whole_by K (headMerge11_quiet P)
  closeOf := closeOf_by K
  batch := fun p _ hf => batchW_by K p hf
  k2 := fun p _ => k2_by K p
  front := headFrontQ_by K
  openQ := fun P _ => headOpenQ_by K P
  finFront := finishFrontQ_by K
  finBehind := finishBehindQ_by K

theorem seatBack_by (K : StKeeps R) : SeatBack (ByS R) where
  k12 := fun _ _ => ⟨atFinish_keeps K _, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M3 := fun p => ⟨K13.atM3_keeps K.ground.quiet p, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩
  k13M4 := fun p P _ => ⟨K13.atM4_keeps K.ground.quiet p _ (K1.Rel.sendAtS_keeps K.ground P),
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- **AT THE PROOF FILE's SEAT, THE WHOLE FIRST CHAIN.** -/
theorem descPure_by (K : StKeeps R) {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ b ∈ c.blocksInOrder, b.planOk = true → Decides (ByS R) b :=
  descPure_flat (seatKeeps_by K) (seatBack_by K) (fun _ _ => trivial) h

/-- **Every ledger stays in order, at every sub-protocol of the first chain.** -/
theorem descPure_ledgers {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ b ∈ c.blocksInOrder, b.planOk = true → Decides (ByS FitStays) b :=
  descPure_by stKeeps_fit h

/-! ## The start -/

/-- The public part's first state is the literal "nothing has happened yet". -/
theorem s0_first {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    Z.s₀ = S.firstRecord Z.first.codes Z.first.shape Z.first.layout := by
  have k := pub_start h
  unfold S.startP at k
  split at k
  · exact (Option.some.inj k).symm
  · cases k

/-- **The first chain's first state, at every public part of an instance.** -/
theorem startS_facts {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    (ProofFile.startS Z p).out.pending = [] ∧ (ProofFile.startS Z p).st.oracles = #[] ∧
      (ProofFile.startS Z p).here = .between := by
  unfold ProofFile.startS
  dsimp only
  split
  · rw [s0_first h]
    exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- **THE FIELD ON THE LEDGERS, AT THE PROOF FILE's SEAT**: at every reached state of the first
chain every ledger is in order. -/
theorem descPure_reach_ledgers {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ((∀ b ∈ c.blocksInOrder, b.planOk = true) → ∀ (k : ℕ) (a : ProofFile.InstPub × S),
          Reach 0 c.blocksInOrder (ProofFile.startS Z) k a → LedgersFit a.2.st) := by
  obtain ⟨Z, A, B, c, hZ, e, k⟩ := descPure_ledgers h
  exact ⟨Z, A, B, c, hZ, e, fun hp _ _ hr =>
    reach_ledgers_plan (fun s : S => s.st) (fun z => (startS_facts hZ z).2.1) hp k hr⟩

#print axioms seatKeeps_by
#print axioms seatBack_by
#print axioms descPure_by
#print axioms descPure_ledgers
#print axioms startS_facts
#print axioms descPure_reach_ledgers

end Meaning.K2
