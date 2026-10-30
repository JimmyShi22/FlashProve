-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FiveAtBorder.lean: the statements that a sub-protocol owes at
its border, as one structure. A border is the point before a sub-protocol of a chain's blocksInOrder list. A
thread is the structure of parameters of one chain's invariant (Honest/Thread/Thr.lean). `Said` is a
second condition beside the invariant (Honest/Thread/Said.lean). `fall` is a test that excuses the
sub-protocol's own step (Honest/Thread/Pays.lean). `J` is a condition on the verifier's state that
is carried only where nothing stopped and no fall spoke (Honest/Thread/ShapeJ.lean).

  `FiveAtBorder`    `PlaysS`, `BehindS`, `ExchangeS`, `RidesPastS`, `AcceptedS` at one border
  `FiveAtBorderJ`   the same four, `AcceptedJ` for the fifth, and `NextJ`
  `owesS_of_five`, `yesS_of_five`, `owesS_of_fiveJ`   what they give at every border
All of these hold for nothing at a `Said` or a thread whose invariant holds of nothing.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **The five statements at border number `b`.** A definition, meant as a hypothesis. -/
structure FiveAtBorder (T : Thread Bk S Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (b : Nat) : Prop where
  /-- the sender plays -/
  plays : PlaysS T Said b
  /-- behind the accepting step: the form, the riders, what the step keeps -/
  behind : BehindS T Said b
  /-- behind the accepting step: the items that the row owes -/
  exchange : ExchangeS T Said b
  /-- what stays open past the sub-protocol stays true -/
  ridesPast : RidesPastS T Said b
  /-- the sub-protocol's own step accepts, outside `fall` and the stops -/
  accepted : AcceptedS T Said fall b

/-- **The same with `J` in hand at the fifth, and `J` one border on.** A definition, meant as a
hypothesis. -/
structure FiveAtBorderJ (T : Thread Bk S Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (J : Nat → S → Prop) (fall : Nat → S → List Fmt.Drawn → Option String) (b : Nat) : Prop where
  plays : PlaysS T Said b
  behind : BehindS T Said b
  exchange : ExchangeS T Said b
  ridesPast : RidesPastS T Said b
  /-- the sub-protocol's own step accepts, with `J` in hand -/
  accepted : AcceptedJ T Said J fall b
  /-- `J` holds at the next border, where nothing stopped and no fall spoke -/
  next : NextJ T Said J fall b

variable {T : Thread Bk S Cl V W X Pb} {Said : Nat → Coins Bk → Mid W X → Prop}
  {fall : Nat → S → List Fmt.Drawn → Option String}

theorem owesS_of_five (h : ∀ b, b < T.bs.length → FiveAtBorder T Said fall b) : OwesS T Said :=
  fun b hb => ⟨(h b hb).plays, (h b hb).behind, (h b hb).exchange, (h b hb).ridesPast⟩

theorem yesS_of_five (h : ∀ b, b < T.bs.length → FiveAtBorder T Said fall b) : YesS T Said fall :=
  fun b hb => (h b hb).accepted

theorem owesS_of_fiveJ {J : Nat → S → Prop}
    (h : ∀ b, b < T.bs.length → FiveAtBorderJ T Said J fall b) : OwesS T Said :=
  fun b hb => ⟨(h b hb).plays, (h b hb).behind, (h b hb).exchange, (h b hb).ridesPast⟩

/-- The plain form gives the form with `J`, at any `J` that is carried. -/
theorem fiveJ_of_five {J : Nat → S → Prop} {b : Nat} (h : FiveAtBorder T Said fall b)
    (n : NextJ T Said J fall b) : FiveAtBorderJ T Said J fall b :=
  ⟨h.plays, h.behind, h.exchange, h.ridesPast, acceptedJ_of T Said J h.accepted, n⟩

/-- At `J` true everywhere the two forms are one. -/
theorem five_of_fiveJ_true {b : Nat} (h : FiveAtBorderJ T Said (fun _ _ => True) fall b) :
    FiveAtBorder T Said fall b :=
  ⟨h.plays, h.behind, h.exchange, h.ridesPast,
    fun blk hblk k s m E ds y cols hA hd hst hf hM =>
      h.accepted blk hblk k s m E ds y cols hA trivial hd hst hf hM⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.owesS_of_five
#print axioms ProofFile.Honest.yesS_of_five
#print axioms ProofFile.Honest.owesS_of_fiveJ
#print axioms ProofFile.Honest.fiveJ_of_five
#print axioms ProofFile.Honest.five_of_fiveJ_true
