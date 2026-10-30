-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadLift.lean: at the first chain's invariant at the full size
(`lettersHead`, FirstHead.lean), seven conditions on a sub-protocol carry over from the arguments
`Vd` and `Rd` to arguments `Vd'` and `Rd'` that imply them. No definition.

`Vd` is the condition on the run's input, `Rd` the part of `rides` that is an argument. Both stand
in the invariant `Thr` and in nothing else that the seven conditions read, and in all seven the
invariant is a hypothesis. So a stronger `Vd` or `Rd` makes each of them easier to prove.

  1  `head_thr_weaker`, `head_thrS_weaker`   the invariant at `Vd'`, `Rd'` gives the invariant at
     `Vd`, `Rd`
  2  `head_playsS_lift`, `head_exchangeS_lift`, `head_exchangeAtS_lift`, `head_laysAtS_lift`,
     `head_ridesPastS_lift`, `head_ridesPastAtS_lift`, `head_acceptedS_lift`   each condition at
     `Vd`, `Rd` gives the same condition at `Vd'`, `Rd'`

The use. Whoever has proved one of the seven at its own `Vd` and `Rd`, for example at conditions
that always hold, has it at the arguments of the gathering (Honest/Thread/GatherAboveT.lean).

Beside it. Four files under Honest/Thread/ that are not in the sealed library: RidersBeside.lean has
the like for `rides` at every thread, for four of the seven and for `BehindS`. RidersBesideHead.lean
has it at `lettersHead` for a list of clauses that is made longer. KeepsFree.lean and KeepsMono.lean
treat the argument `Kp`. And Honest/Thread/SaidMono.lean treats the family `Said`.

Limits.
  * `BehindS` is not among the seven. Its end holds `rides` after the step, so a stronger `Rd` makes
    it harder to prove. `behindS_more` (RidersBeside.lean) says what more is needed. A stronger `Vd`
    alone would not block it; this file does not carry it over even then.
  * The other arguments of `lettersHead` are the same on both sides.
  * `Vd` restricts the run's input and `Rd` the state at each border. At a `Vd'` that `w` does not
    meet, `PlaysS` and the six other conditions on a sub-protocol hold at `Vd'` and say nothing; at
    a border b where `Rd' b w` holds at no state, those at b do.
  * `hV` and `hR` are variables of the file (`include hV hR`). They are hypotheses of all nine
    lemmas, though they stand on no line of a statement: whoever quotes a lemma says "under `hV` and
    `hR`".
  * Conditional lemmas. Nothing here shows that one of the seven holds at any sub-protocol, or that
    the invariant holds at any state of a run.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Vd' : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd' : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (hV : ∀ v, Vd' v → Vd v) (hR : ∀ b v s, Rd' b v s → Rd b v s)
include hV hR

/-! ## 1 The invariant -/

/-- The invariant at the stronger arguments gives the invariant at the weaker. -/
theorem head_thr_weaker {b : Nat} {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hA : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd' Rd' Kp w).thread b k s m E) :
    Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E := by
  unfold Thr at hA ⊢
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hA
  have r6 : (b₀ ≤ b → s.out.reply = some m.st.input.x.asked) ∧ Rd' b m.st.input s := a6
  have r7 : m.st.input = w ∧ Vd' m.st.input := a7
  exact ⟨a1, a2, a3, a4, a5, ⟨r6.1, hR _ _ _ r6.2⟩, ⟨r7.1, hV _ r7.2⟩⟩

variable (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- The same for the invariant together with `Said`. -/
theorem head_thrS_weaker {b : Nat} {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hA : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd' Rd' Kp w).thread Said b k s m E) :
    ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E :=
  ⟨head_thr_weaker h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Vd' Rd' hV hR hA.1, hA.2⟩

/-! ## 2 The seven conditions -/

/-- `PlaysS`. -/
theorem head_playsS_lift {b : Nat}
    (hc : PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b) :
    PlaysS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd' Rd' Kp w).thread Said b :=
  fun blk hblk k s m E ds l hA hd hs hl => hc blk hblk k s m E ds l
    (head_thrS_weaker h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Vd' Rd' hV hR Said hA) hd hs hl

/-- `ExchangeS`. -/
theorem head_exchangeS_lift {b : Nat}
    (hc : ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd' Rd' Kp w).thread Said b :=
  fun blk hblk k s m E ds y cols s' hA hd hS => hc blk hblk k s m E ds y cols s'
    (head_thrS_weaker h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Vd' Rd' hV hR Said hA) hd hS

/-- `ExchangeAtS`. -/
theorem head_exchangeAtS_lift {b : Nat} {i : Item}
    (hc : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b i) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd' Rd' Kp w).thread Said b i :=
  fun blk hblk k s m E ds y cols s' hA hd hS => hc blk hblk k s m E ds y cols s'
    (head_thrS_weaker h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Vd' Rd' hV hR Said hA) hd hS

/-- `LaysAtS`. -/
theorem head_laysAtS_lift {b : Nat} {c : RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS}
    (hc : LaysAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b c) :
    LaysAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd' Rd' Kp w).thread Said b c :=
  fun blk hblk k s m E ds y cols s' hA hd hS => hc blk hblk k s m E ds y cols s'
    (head_thrS_weaker h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Vd' Rd' hV hR Said hA) hd hS

/-- `RidesPastS`. -/
theorem head_ridesPastS_lift {b : Nat}
    (hc : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b) :
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd' Rd' Kp w).thread Said b :=
  fun k s m E s' ps i v hA hk hi h1 h2 hm => hc k s m E s' ps i v
    (head_thrS_weaker h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Vd' Rd' hV hR Said hA) hk hi h1 h2
    hm

/-- `RidesPastAtS`. -/
theorem head_ridesPastAtS_lift {b : Nat} {i : Item}
    (hc : RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b i) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd' Rd' Kp w).thread Said b i :=
  fun k s m E s' ps v hA hk hm => hc k s m E s' ps v
    (head_thrS_weaker h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Vd' Rd' hV hR Said hA) hk hm

/-- `AcceptedS`. -/
theorem head_acceptedS_lift {fall : Nat → TS → List Fmt.Drawn → Option String} {b : Nat}
    (hc : AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall b) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd' Rd' Kp w).thread Said fall b :=
  fun blk hblk k s m E ds y cols hA hd hs hf hM => hc blk hblk k s m E ds y cols
    (head_thrS_weaker h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Vd' Rd' hV hR Said hA) hd hs hf hM

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_thr_weaker
#print axioms ProofFile.Honest.FirstThread.head_thrS_weaker
#print axioms ProofFile.Honest.FirstThread.head_playsS_lift
#print axioms ProofFile.Honest.FirstThread.head_exchangeS_lift
#print axioms ProofFile.Honest.FirstThread.head_exchangeAtS_lift
#print axioms ProofFile.Honest.FirstThread.head_laysAtS_lift
#print axioms ProofFile.Honest.FirstThread.head_ridesPastS_lift
#print axioms ProofFile.Honest.FirstThread.head_ridesPastAtS_lift
#print axioms ProofFile.Honest.FirstThread.head_acceptedS_lift
