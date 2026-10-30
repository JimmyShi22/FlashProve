-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/BehindKp.lean: «LINK m: BEHIND THE BATCHING» AT THE
LIBRARY's HEAD, WITH THE LETTER Kp LAID BY THE KIND. `noHouse_behind_eight`
(Honest/Law/NoHouse/BehindPins.lean) keeps the premise hKp: the thread's letter Kp at the member's
place follows from `keepsBehind`. Where Kp is laid by the place's kind (`kpBy f`,
Honest/Thread/KeepsBy.lean) and the kind frame's clause is `keepsFrame`
(Honest/Law/NoHouse/KeepsFrame.lean), that premise is an equation by the place (`behind_kp`). SEVEN
PREMISES STAY, AND THAT LAYING (hf).

WHAT THIS IS. A lemma on definitions of ours at the library's own terms, and a call. THE FULL SIZE
ALONE, and the format's second hash function alone. None of the library's goals.

  `behind_kp`, `noHouse_behind_seven`

WHAT STAYS A PREMISE OF THE LAST, AND WHOSE: SEVEN, AND ONE EQUATION ON A LETTER. hn: no half of the
prover's stands at a place of the kind frame. hg: the falls' writers (`FallGuards`). htest: whoever
lays the thread's fall and the item's test from one text. hRd, hb₀, said, rides: the threads'
letters. THE EIGHTH, hf, STANDS IN hKp's STEAD: the family f has `keepsFrame` at the kind frame: an
equation that holds by unfolding once the family is a written term: until then it is a premise like
the others.

MET FOR NOTHING. As `NoHouse`. The library's head has a member at the name under four premises on
the public files (the seal's `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of
our files calls it; no member of the head TOGETHER WITH the thread's sentence is shown. Limits.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindPins
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.KeepsFrame
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place Block Link KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K9 (Where)
open VerifiableInference.Desc.LinkJoin (batchAt hearN)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **hKp, where the letter is laid by the kind and the kind frame's clause is `keepsFrame`.** -/
theorem behind_kp {m : Nat} (hm : m < 25) {Lk : Link TS ProofFile.Cl} {p9 : Where}
    {Q9 : VerifiableInference.Desc.First.Close.Par} {b₃ b₅ : Block TS ProofFile.Cl}
    (St : h.Sits m Lk p9 Q9 b₃ b₅) (f : KindName → Place → TS → TS → Prop) (take : Nat → Bool)
    (hf : f KindName.frame = keepsFrame P5J.At.links take) (s s' : TS)
    (hk : keepsBehind s s') : kpBy f Lk.behindB.place s s' := by
  refine (kpBy_at f (κ := KindName.frame) rfl s s').2 ?_
  rw [hf]
  refine (keepsFrame_behind P5J.At.links take (l := m) ?_ ?_ s s').2 hk
  · show some Lk.number = some m
    rw [behind_num_head h hm St.lk]
  · show Lk.hear.length + 2 = hearN fullLinks m + 2
    unfold hearN
    rw [St.sort, St.seg.hear]
    rfl

section
variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (f : KindName → Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **«LINK m: BEHIND THE BATCHING»: THE RECORD AT THE REAL MEMBER, SEVEN PREMISES LEFT**, and hf:
the family's clause at the kind frame. -/
theorem noHouse_behind_seven
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {m : Nat} {Lk : Link TS ProofFile.Cl}
    {p9 : Where} {Q9 : VerifiableInference.Desc.First.Close.Par} {b₃ b₅ : Block TS ProofFile.Cl}
    (hm : m < 25) (St : h.Sits m Lk p9 Q9 b₃ b₅) (take : Nat → Bool)
    (hf : f KindName.frame = keepsFrame P5J.At.links take)
    (hn : (H.first.find? fun g => g.place == Lk.behindB.place) = none)
    (hg : FallGuards 0 Lk.behindB (fall (batchAt fullLinks P5J.At.ps m + 1)))
    (htest : ∀ s, fall (batchAt fullLinks P5J.At.ps m + 1) s [] = none → test m s = none)
    (hRd : ∀ v s s', Rd (batchAt fullLinks P5J.At.ps m + 1) v s → Lk.runBehind s = .ok s' →
      Rd (batchAt fullLinks P5J.At.ps m + 1 + 1) v s')
    (hb₀ : b₀ ≠ batchAt fullLinks P5J.At.ps m + 1 + 1)
    (said : ∀ k μ, Said (batchAt fullLinks P5J.At.ps m + 1) k μ →
      Said (batchAt fullLinks P5J.At.ps m + 1 + 1) k μ)
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
      (batchAt fullLinks P5J.At.ps m + 1)) :
    NoHouse (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said fall
      (batchAt fullLinks P5J.At.ps m + 1) Lk.behindB :=
  noHouse_behind_eight h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w Said fall hm St hn hg
    htest (behind_kp h hm St f take hf) hRd hb₀ said rides

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.behind_kp
#print axioms ProofFile.Honest.FirstThread.noHouse_behind_seven
