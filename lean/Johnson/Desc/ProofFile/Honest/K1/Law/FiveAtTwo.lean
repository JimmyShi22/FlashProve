-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FiveAtTwo.lean: `BehindS` AND `RidesPastS` AT THE KIND K1's
OPENING (number 2 of the first chain's flat list), AT ProofFile's `lettersHead`.

  `k1_riders_two`, `k1_riders_two_control`, `place_two`   by Lean's kernel
  `k1_ridesPastS_two`               under what the letter `Kp` gives at the place
  `k1_keeps_two`                    the kind's clause behind the member's step
  `k1_behindS_two`, `k1_ridesPastS_two_I`   at `fHeadJ`, the riders `csHead`, `b₀ = 339`

Limits. Nothing shows that the member accepts. Nothing on any property. Full size, the format's
second hash function.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FormAtTwo
import Johnson.Desc.ProofFile.Honest.K1.Law.BehindAtFifty
import Johnson.Desc.ProofFile.Honest.Thread.PileFirst
import Johnson.Desc.ProofFile.Honest.Thread.HeadPlaceAt
import Johnson.IMR.FirstSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Strs Place KindName)
open VerifiableInference.Desc.First (S Item kindsBeforeBatching)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (StepYes)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- K1's opening's place. -/
abbrev placeTwo : Place := { chain := 1, link := some 0, piece := 1, kind := .K1 }

/-- **Of the items that the opening neither shuts nor owes, which may ride.** -/
def k1RiderTwo : Item → Bool
  | .unmarked | .pinW | .pile => true
  | .constr _ q => P5J.parts4.contains q
  | _ => false

set_option maxRecDepth 1000000 in
/-- **THE RIDERS AT NUMBER 2**, by Lean's kernel. -/
theorem k1_riders_two : ((fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) 2).all fun i =>
      (FirstRows.rows P5J.At.links P5J.At.ps 2).shuts.contains i ||
      (FirstRows.rows P5J.At.links P5J.At.ps 2).owes.contains i || k1RiderTwo i) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The control: with `pile` struck from the list the test says no, so the test can fail. -/
theorem k1_riders_two_control : ((fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) 2).all fun i =>
      (FirstRows.rows P5J.At.links P5J.At.ps 2).shuts.contains i ||
      (FirstRows.rows P5J.At.links P5J.At.ps 2).owes.contains i ||
      (k1RiderTwo i && i != .pile)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **THE PLACE AT NUMBER 2**, by Lean's kernel. -/
theorem place_two : P5J.At.ps[2]? = some placeTwo := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **WHAT RIDES PAST THE OPENING RIDES.** -/
theorem k1_ridesPastS_two (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hK : ∀ s s', Kp placeTwo s s' →
      ∃ m, (K1FirstKeeps s m ∧ K1Out s m) ∧ keepsOpenedR 0 m s') :
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 2 := by
  have hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 2 s s' →
      ∃ m, (K1FirstKeeps s m ∧ K1Out s m) ∧ keepsOpenedR 0 m s' :=
    fun s s' a => hK s s' ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w place_two s s').1 a)
  refine ridesPastS_shares _ _ fun i hi h1 h2 => ?_
  have ht : k1RiderTwo i = true := by
    have t := List.all_eq_true.1 k1_riders_two i hi
    simp only [Bool.or_eq_true, List.contains_iff_mem] at t
    rcases t with (t | t) | t
    · exact absurd t h1
    · exact absurd t h2
    · exact t
  refine ridesPastAtS_of _ _ ?_
  cases i with
  | unmarked =>
    exact ridesPastAt_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w fun s s' a => by
      obtain ⟨m, -, k2⟩ := hk s s' a
      exact k2.1.1
  | pinW => exact ridesPastAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _
  | pile =>
    exact ridesPastAt_pile_two h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      (by rw [head_len h]; decide) fun s s' a => hk s s' a
  | constr m q =>
    simp only [k1RiderTwo, List.contains_iff_mem, P5J.parts4, List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact fun _ _ _ _ _ _ _ _ _ h0 => h0
    · exact fun _ _ _ _ _ _ _ _ _ h0 => h0
    · exact fun _ _ _ _ _ _ _ _ _ h0 => h0
    · exact fun _ _ _ _ _ _ _ _ _ h0 => h0
  | _ => cases ht

variable (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  {ν : Nat} {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}

include h in
/-- **THE CLAUSE BEHIND THE OPENING's STEP**: K1's half, then the frame's. -/
theorem k1_keeps_two {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[2]? = some blk) {s s' : TS}
    (hy : StepYes 0 blk s s') :
    blk.place = placeTwo ∧ ∃ m, (K1FirstKeeps s m ∧ K1Out s m) ∧ keepsOpenedR 0 m s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, e1, e2, L, hL, b', hb', ep, hj⟩ :=
    IM.first_sits h.scope h.reads O 0 (by decide) .K1 rfl
  have hb1 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by decide) 0] at hb1
  have hb2 : cF.blocksInOrder[2]? = some b := hb1
  obtain rfl : b = blk := Option.some.inj (hb2.symm.trans hb)
  have hb3 : cF.blocksInOrder[14 * 0 + 0 + 2]? = some b := hb
  refine ⟨head_place_hear h (l := 0) (i := 0) (k := .K1) (by decide) rfl hb3, ?_⟩
  exact keeps_joined_openedR hj 0
      (fun s m => K1FirstKeeps s m ∧ K1Out s m)
      (fun _ _ y _ => k1_first_half ⟨L, hL, hb'⟩ ep y) s s' hy

/-- **BEHIND THE OPENING: THE FORM, THE RIDERS, THE CLAUSE.** -/
theorem k1_behindS_two (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    BehindS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said 2 := by
  refine behindS_of_keeps_and _ Said
    (R₀ := fun c v s => 339 ≤ c → s.out.reply = some v.x.asked)
    (head_rides_and h H Q test carryX item n₁ n₂ 339 Vd _ _ w) ?_ ?_ ?_ ?_
  · intro blk hblk k s m E ds y cols s' hA hd hS
    have hform := k1_form_two h H Q test carryX item n₁ n₂ 339 Vd _ _ w Said hblk hA hS
    refine ⟨hform, (head_keeps h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w place_two s s').2 ?_⟩
    have y0 : StepYes 0 blk s s' := stepYes_of_stepped _ hd hS
    refine ⟨⟨⟨⟨⟨(fHead_K1_first Zp cF G take P11 p12 P13 (p := placeTwo) rfl rfl s s').2
        (k1_keeps_two h hblk y0).2,
      formsBehind_of_form h H Q test carryX item n₁ n₂ 339 Vd _ _ w place_two hform⟩, ?_⟩,
      trivial⟩, trivial⟩, trivial⟩
    intro l' _ hc
    have : (1 : Nat) = 6 ∨ (1 : Nat) = 7 := hc
    omega
  · intro blk hblk k s m E ds y cols s' hA hd hS hc
    have : 339 ≤ 2 + 1 := hc
    omega
  · intro c hc h1 h2
    have hs := csHead_span hc
    have := (h1 : c.lo ≤ 2)
    exfalso
    rcases hs with ⟨a, -⟩ | ⟨g, -, a, -⟩ | ⟨g, -, a, -⟩ | ⟨g, -, a, -⟩ <;> omega
  · intro c hc e
    have hs := csHead_span hc
    have e' : c.lo = 3 := e
    exfalso
    rcases hs with ⟨a, -⟩ | ⟨g, -, a, -⟩ | ⟨g, -, a, -⟩ | ⟨g, -, a, -⟩ <;> omega

/-- **WHAT RIDES PAST THE OPENING RIDES, AT THE TERM's CLAUSE.** -/
theorem k1_ridesPastS_two_I (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said 2 :=
  k1_ridesPastS_two h H Q test carryX item n₁ n₂ b₀ Vd Rd _ w Said fun s s' a =>
    (fHead_K1_first Zp cF G take P11 p12 P13 (p := placeTwo) rfl rfl s s').1 a.1.1.1.1.1

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_riders_two
#print axioms ProofFile.Honest.K1.k1_riders_two_control
#print axioms ProofFile.Honest.K1.place_two
#print axioms ProofFile.Honest.K1.k1_ridesPastS_two
#print axioms ProofFile.Honest.K1.k1_keeps_two
#print axioms ProofFile.Honest.K1.k1_behindS_two
#print axioms ProofFile.Honest.K1.k1_ridesPastS_two_I
