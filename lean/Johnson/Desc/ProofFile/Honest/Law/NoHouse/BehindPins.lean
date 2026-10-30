-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/BehindPins.lean: THE SEGMENT's PINS RIDE PAST A STEP THAT
LEAVES THE STATEMENT, AT THE THREADS' LETTERS AT THE LIBRARY's HEAD. At the honest letters a pin
says `ansJT` (Honest/Thread/Ans.lean), which reads the verifier's state through the reader of
samples alone; at the head that reader is the library's `smpNamed`
(Johnson/Desc/Sound/SmpNamed.lean; `P5J.At.smp`), which reads the statement alone
(`smpNamed_stays`). So where s'.st = s.st a pin says of the one state what it says of the other.
With it `noHouse_behind_all` (Honest/Law/NoHouse/BehindAll.lean) loses its premise hctx: the
library's `Rb` behind the member has the statement as it was.

WHAT THIS IS. Lemmas on definitions of ours at the library's own terms; and a call. THE FULL SIZE
ALONE, and the format's second hash function alone. None of the library's goals.

  `head_pin_rides`, `head_pins_ride`, `noHouse_behind_eight`

WHAT STAYS A PREMISE OF THE LAST, AND WHOSE: EIGHT. hn: no half of the prover's stands at a place of
the kind frame. hg: the falls' writers (`FallGuards`). htest: whoever lays the thread's fall and the
item's test from one text. hKp: the filler of the thread's letter Kp. hRd, hb₀, said, rides: the
threads' letters.

MET FOR NOTHING. As `NoHouse`. The library's head has a member at the name under four premises on
the public files (`P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of
our files calls it; no member of the head TOGETHER WITH the thread's sentence is shown. Limits.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place Block Link)
open VerifiableInference.Desc.First (Item pinsOf)
open VerifiableInference.Desc.Sound (MsgT smpNamed_stays)
open VerifiableInference.Desc.K9 (Where)
open VerifiableInference.Desc.LinkJoin (batchAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **One pin rides where the statement stays.** -/
theorem head_pin_rides (v : Local W₀ Rc ProofFile.Inst Tr) (j t : Nat) (a : ProofFile.InstPub × TS) (s' : TS)
    (y : Strs) (u : WtF) (hst : s'.st = a.2.st)
    (h0 : ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg v).pin j t a y u) :
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg v).pin j t (a.1, s') y u := by
  rw [head_pin] at h0 ⊢
  refine ansJT_congr (P5J.At.cs Zp) (P5J.At.arr Zp) (fun z _ _ => ?_) h0
  exact smpNamed_stays (P5J.At.cs Zp) (P5J.At.seats Zp) a (a.1, s') z.1 z.2
    (by show _ = _; rw [hst]) (by show _ = _; rw [hst])

/-- **The segment's pins ride.** -/
theorem head_pins_ride (v : Local W₀ Rc ProofFile.Inst Tr) (m : Nat) (i : Item)
    (a : ProofFile.InstPub × TS) (s' : TS) (y : Strs) (u : WtF) (hi : i ∈ pinsOf m)
    (hst : s'.st = a.2.st)
    (h0 : Item.holds (P5J.At.N Zp cF)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg v) i a y u) :
    Item.holds (P5J.At.N Zp cF)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg v) i (a.1, s') y u := by
  have hi' : i = .pin m 0 ∨ i = .pin m 1 ∨ i = .pin m 2 := by
    simpa [pinsOf] using hi
  rcases hi' with rfl | rfl | rfl
  all_goals
    intro z hz
    exact head_pin_rides h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w v z.1 z.2 a s' y u hst
      (h0 z hz)

/-- **«LINK m: BEHIND THE BATCHING»: THE RECORD AT THE REAL MEMBER, EIGHT PREMISES LEFT.** -/
theorem noHouse_behind_eight
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {m : Nat} {Lk : Link TS ProofFile.Cl}
    {p9 : Where} {Q9 : VerifiableInference.Desc.First.Close.Par} {b₃ b₅ : Block TS ProofFile.Cl}
    (hm : m < 25) (St : h.Sits m Lk p9 Q9 b₃ b₅)
    (hn : (H.first.find? fun g => g.place == Lk.behindB.place) = none)
    (hg : FallGuards 0 Lk.behindB (fall (batchAt fullLinks P5J.At.ps m + 1)))
    (htest : ∀ s, fall (batchAt fullLinks P5J.At.ps m + 1) s [] = none → test m s = none)
    (hKp : ∀ s s', keepsBehind s s' → Kp Lk.behindB.place s s')
    (hRd : ∀ v s s', Rd (batchAt fullLinks P5J.At.ps m + 1) v s → Lk.runBehind s = .ok s' →
      Rd (batchAt fullLinks P5J.At.ps m + 1 + 1) v s')
    (hb₀ : b₀ ≠ batchAt fullLinks P5J.At.ps m + 1 + 1)
    (said : ∀ k μ, Said (batchAt fullLinks P5J.At.ps m + 1) k μ →
      Said (batchAt fullLinks P5J.At.ps m + 1 + 1) k μ)
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (batchAt fullLinks P5J.At.ps m + 1)) :
    NoHouse (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall
      (batchAt fullLinks P5J.At.ps m + 1) Lk.behindB :=
  noHouse_behind_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said fall hm St hn hg htest
    (fun v i a s' y u hi hy h0 =>
      head_pins_ride h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w v m i a s' y u hi
        (after_state Lk (after_share_head h hm St.lk St.seg) a.2 s' hy).1.st h0)
    hKp hRd hb₀ said rides

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_pin_rides
#print axioms ProofFile.Honest.FirstThread.head_pins_ride
#print axioms ProofFile.Honest.FirstThread.noHouse_behind_eight
