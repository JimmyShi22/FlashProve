-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoRidesAt.lean

What is here. Law/WoRides.lean's statement called at the library's own parameters of the first
chain's thread (`lettersAt`, Honest/Thread/FirstAt.lean): a check that the call has the right
types there, and the threads' debt RidesPastAtS at `Item.wo m` at a member that leaves those four.
Statements with their proofs, by unfolding and a call.

  `k4WoTableBack_at`: at these parameters the thread's sentence at the item is the library's
      `woAt`: the converse of `k4WoTable_at` (Law/WoAt.lean).
  `rw13_quiet`: the library's reader of the pile of pending rows reads of the state the statement
      and the book alone.
  `k4_ridesPastAtS_wo_at`: RidesPastAtS T Said b (Item.wo m).

Limits. CONDITIONAL: on h, and on hK: that, wherever the thread's sentence and what has been said
hold in front, the thread's parameter keeps at the member number b leaves the statement, the book,
«out» and what is left for the pending row. hK IS SHOWN OF NO MEMBER HERE. It is not meant for a
member that turns the statement or the book: for such a member Law/WoRides.lean's wider hypothesis
`K4WoSame` is the form (Law/WoRidesGrown.lean). Member by member: Law/WoPast.lean,
Law/WoPastBehind.lean and Law/WoRidesLook.lean. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH
ALONE, as Law/WoAt.lean has it; that h holds of any files is not shown here: the side library
AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). h1 · h2 (the two lesser statements) are equations on two states. hK speaks of the
thread's parameter keeps, and one that never holds meets it emptily: of h together with hK at a
parameter that holds of a step of a run no example is known to us. IT IS A LAW, NOT A PART: through
h it rests on modules under Johnson/Goal/ (a walk stops at 16 there): no file that defines a part
may build on it. Nothing on soundness, on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.WoAt
import Johnson.Desc.ProofFile.Honest.K4.Law.WoRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open ProofFile.Honest.FirstThread (Script WtF lettersAt)
open VerifiableInference.Desc (Strs Chain)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MgData)
open P5J (AtMgA TS CellsM)
open Johnson.Desc.First.Walk.Law (leftOf)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- The library's reader reads of the state the statement and the book alone. -/
theorem rw13_quiet (z : ProofFile.InstPub) (s s' : TS) (h1 : s'.st = s.st) (h2 : s'.book = s.book) :
    h.𝔇.rw13 (z, s') = h.𝔇.rw13 (z, s) := by
  funext w'
  unfold MgData.rw13 VerifiableInference.Desc.K13.Law.rwBook
  dsimp only
  rw [h1, h2]

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **`K4WoTableBack` at the library's own parameters.** CONDITIONAL: on h. -/
theorem k4WoTableBack_at (m : Nat) :
    K4WoTableBack (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      (Item.wo m) h.𝔇.d1 h.𝔇.rw13 m :=
  ⟨fun _ _ _ _ hw => hw⟩

/-- **`RidesPastAtS` AT THE PENDING ROW's ITEM, AT A MEMBER THAT LEAVES THE FOUR.** CONDITIONAL: on
h and hK. -/
theorem k4_ridesPastAtS_wo_at
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (b m : Nat)
    (hK : ∀ k s m E s',
      ThrS (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
        Said b k s m E → keeps b s s' →
      s'.st = s.st ∧ s'.book = s.book ∧ s'.out = s.out ∧ leftOf s' = leftOf s) :
    RidesPastAtS (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      Said b (Item.wo m) :=
  k4_ridesPastAtS_wo Said
    (k4WoTable_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps m)
    (k4WoTableBack_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps m)
    fun k s m E s' v hT hKp =>
      woSame_quiet (rw13_quiet h) (hK k s m E s' hT hKp).1 (hK k s m E s' hT hKp).2.1
        (hK k s m E s' hT hKp).2.2.1 (hK k s m E s' hT hKp).2.2.2 v

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.rw13_quiet
#print axioms ProofFile.Honest.K4.k4WoTableBack_at
#print axioms ProofFile.Honest.K4.k4_ridesPastAtS_wo_at
