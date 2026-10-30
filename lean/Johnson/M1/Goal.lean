-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- the rule's four premises at our rows, at a return of the maker.
/-
Johnson/M1/Goal.lean: a return of the maker (`onlineProverFromPublicFiles`) opens the description that it returns, at its
own public part and ground. So, in the goals' scope where the gate accepts, at a return of the maker
at any filling, the four premises that the rule asks row by row hold at every row of our two lots, at
the return's own book. The second of the four holds under the public test on the book, which stays a
hypothesis of that clause. No property of the protocol is claimed here.
-/
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.SendSim.Seat.ReadsAtLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat

variable {W₀ Rc Tr X₀ X' : Type}

/-- **A return of the maker can be opened, at its own public part and ground.** -/
theorem open_of_return {pol lay KL : ByteArray} {Fl : OnlineProverParts W₀ Rc Tr X₀ X'}
    {R : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (h : onlineProverFromPublicFiles OnBytes.secondHashFunction pol lay KL Fl = .ok R) :
    ∃ (Bs : ProofFile.PureBase) (base : List (Block First.S ProofFile.Cl))
      (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      IM.Open OnBytes.secondHashFunction pol lay KL R.F R.Z Bs base c A B ∧ Bs.G₀ = R.G := by
  obtain ⟨hZ, hG, hF, -⟩ := atPure_ok h
  obtain ⟨Z', Bs, base, c, A, B, O⟩ := IM.seat_open hF
  have e : Z' = R.Z := Except.ok.inj (O.pub.symm.trans hZ)
  subst e
  exact ⟨Bs, base, c, A, B, O, Option.some.inj (O.blank.symm.trans hG)⟩

/-- **The four premises that the rule asks of a row**, at a return of the maker. The second holds under
the public test on the book. -/
def RowOwes {V W X Pb : Type} (R : OnlineProverWithDescription W₀ Rc Tr X₀ X') (pre₀ : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face V W Pb) (ord : List Place) (chain ft : Nat)
    (T : W → Thread R.B R.F.S₁ R.F.Cl V W X Pb) (Sd : W → Nat → Coins R.B → Mid W X → Prop)
    (fs : List (Fall R.F.S₁)) (r : Unlettered V W X Pb) : Prop :=
  R.F.first.blocksInOrder.any (fun b => b.place == r.place) = true ∧
    ((∀ e ∈ R.B.ahead, e.once = true → lotsMine R.Z R.G e.owner = true →
        lotsOkB R.Z R.G R.B ord e.owner = true) →
      ∀ σ, (r.lay T Sd R.F.first.blocksInOrder).side R.F.first.blocksInOrder fs = some σ →
        ∃ A₁ B₁, Good pre₀ φ σ R.B ord chain ft A₁ B₁ (r.lay T Sd R.F.first.blocksInOrder).On
          (r.lay T Sd R.F.first.blocksInOrder).bud) ∧
    (∀ σ, (r.lay T Sd R.F.first.blocksInOrder).side R.F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      R.F.first.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number →
      ∀ ρ : ProofFile.Honest.Draws, ρ.due R.F = true →
      (r.lay T Sd R.F.first.blocksInOrder).bud u.number ((ρ.first.drop n).take u.rounds.length)
        (asksFrom (treeAsks R.F ρ 0) (u.rounds.map (·.2.length))
          (((rowsOfChain R.F.first.blocksInOrder).take n).map (·.2.length)).sum)) ∧
    ∀ w b len, OnFromS (T w) (Sd w) (r.lay T Sd R.F.first.blocksInOrder) b len

/-- **The rule's four premises at every row of our two lots, at a return of the maker**, at its own
public part, ground and book, at every reader, numbers and data. -/
theorem rows_at_return {V W X Xi Pb : Type} {P : VerifierAndGoals.PublicFiles}
    {pre₀ : List (Nat × Nat × List Fmt.DeclaredRound)} {Fl : OnlineProverParts W₀ Rc Tr X₀ X'}
    {R : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL Fl = .ok R)
    (φ : Face V W Pb) (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (ord : List Place) (chain ft : Nat)
    (T : W → Thread R.B R.F.S₁ R.F.Cl V W X Pb) (Sd : W → Nat → Coins R.B → Mid W X → Prop)
    (fs : List (Fall R.F.S₁)) :
    ∀ r ∈ rowsOfLots R.Z R.G (sendLots (V := V) (X := X) (Pb := Pb) wit no D),
      RowOwes R pre₀ φ ord chain ft T Sd fs r := by
  obtain ⟨Bs, base, c, A, B, O, hG⟩ := open_of_return h
  unfold RowOwes
  rw [← hG]
  exact handIn_of_live hS hL O φ wit no D R.B ord chain ft T Sd fs

end Johnson.M1

#print axioms Johnson.M1.open_of_return
#print axioms Johnson.M1.rows_at_return
