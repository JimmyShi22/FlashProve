-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/RidesAtStep.lean.
WHAT IT IS NOT. NO DEBT IS SHOWN: the last statement is CONDITIONAL ON FOUR NAMED PREMISES, one for
each item that the sub-protocol makes: its share of ExchangeS; none is paid here. All three
statements are conditional on the library's hypothesis P5J.AtMgA; the two shares on that alone. That
the thread holds at any run is shown nowhere; that the verifier accepts is the debt's own premise
(Stepped): nothing here shows it. ExchangeAtS and ExchangeS are definitions
(Honest/Thread/SharesS.lean, PaysS.lean): premises' forms: none of the library's goals. NO NEW
MATHEMATICS: the lemmas' lines with one fact taken from another place. (Of the hypothesis the
library has a member under four premises on the three public files: P5J.head_exists_at_name,
Johnson/P5J/HeadExistsAtName.lean; nothing here calls that.) The full size, the format's second
hash function, border 341 alone. Nothing on soundness, on completeness or on what a proof hides.
WHAT IT IS. THE SUB-PROTOCOL "the output head's own rounds": THE ITEMS THAT ITS ROW READS AND LEAVES
ARE IN HAND AGAIN BEHIND ITS ACCEPTING STEP, AT EVERY LETTER Kp AND WITHOUT THE DEBT BehindS.
  k6_exchange_pin'       the share at pin 24 0: k6_exchange_pin without hB and hKp'
  k6_exchange_small'     the share at constr 24 small: k6_exchange_small without hB
  k6_exchangeS_of_four'  ExchangeS at 341 from the four shares that are not paid here:
                         k6_exchangeS_of_four without hB and hKp'
WHY. Honest/K6/Law/RidesPast.lean's k6_exchange_pin, k6_exchange_small and k6_exchangeS_of_four ask
hB (the debt BehindS at the border) and hKp' (Kp plK6 s s' → K6Keeps s s'). BOTH ARE IDLE THERE IN
SUBSTANCE: exchangeAtS_again (Honest/Thread/SharesS.lean) takes of hB its third clause alone, "the
thread's keeps at 341"; for constr 24 small that clause is thrown away; for pin 24 0 it goes through
head_keeps and hKp' to K6Keeps s s', AND AT THAT PAIR THE MEMBER HAS STEPPED: K6Keeps follows from
the member's form and its accepting step alone (k6_keeps_of_member_step,
Johnson/Desc/K6/Honest/Law/KeepsMember.lean). So the three hold at every letter Kp and without
BehindS: by exchangeAtS_stepped (Honest/Thread/SharesStepped.lean): an item that is open at a
border, and whose sentence rides past every pair of states AT WHICH THE MEMBER HAS STEPPED, is in
hand again behind. The elder three stand as they are.
TYPED AFTER: k6_exchange_pin' has the lines of k6_ridesPast_pin, k6_exchangeS_of_four' those of
k6_exchangeS_of_four (Honest/K6/Law/RidesPast.lean); the member and its step as in k6_form_keeps
(Honest/K6/Law/Behind.lean).
OF THE FOLDER Johnson/Goal/ it imports no module by name.
It imports Honest/K6/Law/RidesPast.lean, Honest/Thread/SharesStepped.lean and what these import.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.RidesPast
import Johnson.Desc.ProofFile.Honest.Thread.SharesStepped

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps k6_keeps_of_member_step)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **THE PINS OF WHAT THE HEAD's SEGMENT HAS SENT FIRST ARE IN HAND AGAIN BEHIND THE MEMBER**, at
every letter Kp: `k6_exchange_pin` without hB and hKp'. CONDITIONAL: the hypothesis h. -/
theorem k6_exchange_pin' :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (Item.pin 24 0) := by
  refine exchangeAtS_stepped _ Said (opened_341 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).1
    fun blk hblk k s m E ds y cols s' v _ _ hS h0 => ?_
  obtain ⟨b, hfl, M⟩ := P4.k6_member_at_mg h.toAtMg
  obtain rfl : blk = b := Option.some.inj (hblk.symm.trans hfl)
  have hstep : blk.step 0 s (roundsOf y.1) cols = .ok (s', cols.length) := hS.2
  have K : K6Keeps s s' := k6_keeps_of_member_step M hstep
  have h1 : ∀ a ∈ (P5J.At.N Zp cF).sent 24 0,
      ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay) a.1 a.2
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k m s)
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E) v := h0
  show ∀ a ∈ (P5J.At.N Zp cF).sent 24 0,
      ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay) a.1 a.2
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k m s')
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add y.1)) v
  intro a ha
  exact k6_pin_rides K a.1 a.2 _ _ _ _ v (h1 a ha)

/-- **"THE WITNESS's CELLS ARE SMALL" IS IN HAND AGAIN BEHIND THE MEMBER**: `k6_exchange_small`
without hB. CONDITIONAL: the hypothesis h. At the threads the item reads neither the verifier's
state nor what the strings gain. -/
theorem k6_exchange_small' :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (Item.constr 24 .small) :=
  exchangeAtS_stepped _ Said (opened_341 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).2
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 => h0

/-- **ALL THAT THE ROW AT 341 OWES, FROM THE FOUR ITEMS THAT THE SUB-PROTOCOL MAKES**:
`k6_exchangeS_of_four` without hB and hKp': at every letter Kp. CONDITIONAL: the hypothesis h; AND
FOUR NAMED PREMISES, one for each item that is not paid in this file: its share of `ExchangeS`. -/
theorem k6_exchangeS_of_four'
    (hOwn : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      341 (Item.formsT 24 4 "own"))
    (hPlanes : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      341 (Item.formsT 24 3 "planes"))
    (hJoin : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      341 (Item.formsT 24 4 "join"))
    (hWeights : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      341 (Item.formsT 24 4 "weights")) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 := by
  refine (exchangeS_iff _ Said).2 fun i hi => ?_
  rw [owes_341 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w] at hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hOwn
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hPlanes
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hJoin
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hWeights
  rcases List.mem_cons.1 hi with rfl | hi
  · exact k6_exchange_pin' h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
  rcases List.mem_cons.1 hi with rfl | hi
  · exact k6_exchange_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
  rcases List.mem_cons.1 hi with rfl | hi
  · exact k6_exchange_small' h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
  cases hi

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_exchange_pin'
#print axioms ProofFile.Honest.K6.k6_exchange_small'
#print axioms ProofFile.Honest.K6.k6_exchangeS_of_four'
