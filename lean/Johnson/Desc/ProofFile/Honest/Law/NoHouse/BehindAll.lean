-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/BehindAll.lean: «LINK m: BEHIND THE BATCHING» AT THE
LIBRARY's HEAD, WITH THE FOUR EVALUATIONS PAID. `noHouse_behind_head`
(Honest/Law/NoHouse/BehindHead.lean) keeps thirteen premises. Four are facts on written lists: the
link's own number (here `behind_num_head`: the library's `IM.k9_of`, `LPFK9.link_of_lk`); the
table's row and open set at the member's number (`head_behind`,
Honest/Law/Rule/OpenForms.lean: by Lean's kernel): there the context is the segment's pins. And the
clause of keeps at the member's place need only FOLLOW FROM `keepsBehind`
(Honest/Law/NoHouse/BehindKeeps.lean), which `after_keeps` pays. NINE PREMISES STAY.

WHAT THIS IS. A conditional lemma on definitions of ours at the library's own terms: a call of
`noHouse_behind_head`. THE FULL SIZE ALONE, and the format's second hash function alone. None of the
library's goals.

  `behind_num_head`, `noHouse_behind_all`

WHAT STAYS A PREMISE. hn: no half of the prover's stands at a place of the kind frame.
hg: `FallGuards`. htest: whoever lays the thread's fall and the item's test
from one text. hctx: the segment's pins ride past a yes. hKp: the filler of the thread's letter Kp:
at this place it follows from `keepsBehind`. hRd, hb₀, said, rides: the threads' letters.

MET FOR NOTHING. As `NoHouse`. The library's head has a member at the name under four premises on
the public files (the seal's `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); none of
our files calls it; no member of the head TOGETHER WITH the thread's sentence is shown. Limits.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindHead
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindRows
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenForms
import Johnson.IMR.LinkSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place Block Link)
open VerifiableInference.Desc.First (Item pinsOf)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K9 (Where)
open VerifiableInference.Desc.LinkJoin (batchAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS fullLinks)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- The link that the head's data name at m bears the number m. -/
theorem behind_num_head {m : Nat} (hm : m < 25) {Lk : Link TS ProofFile.Cl}
    (hlk : h.𝔇.lk m = some Lk) : Lk.number = m := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, hall⟩ := IM.k9_of h.scope h.reads O
  obtain ⟨Lk', p, w, T, e1, -, -, -, -, -, -, -, -, -, n3, -⟩ := hall m hm
  obtain rfl : Lk' = Lk := Option.some.inj (e1.symm.trans (LPFK9.link_of_lk h O m Lk hlk))
  exact n3

section
variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **«LINK m: BEHIND THE BATCHING»: THE RECORD AT THE REAL MEMBER, NINE PREMISES LEFT.** -/
theorem noHouse_behind_all
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {m : Nat} {Lk : Link TS ProofFile.Cl}
    {p9 : Where} {Q9 : VerifiableInference.Desc.First.Close.Par} {b₃ b₅ : Block TS ProofFile.Cl}
    (hm : m < 25) (St : h.Sits m Lk p9 Q9 b₃ b₅)
    (hn : (H.first.find? fun g => g.place == Lk.behindB.place) = none)
    (hg : FallGuards 0 Lk.behindB (fall (batchAt fullLinks P5J.At.ps m + 1)))
    (htest : ∀ s, fall (batchAt fullLinks P5J.At.ps m + 1) s [] = none → test m s = none)
    (hctx : ∀ v i a s' y u, i ∈ pinsOf m → Lk.runBehind a.2 = .ok s' →
      Item.holds (P5J.At.N Zp cF)
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg v) i a y u →
      Item.holds (P5J.At.N Zp cF)
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg v) i (a.1, s') y u)
    (hKp : ∀ s s', keepsBehind s s' → Kp Lk.behindB.place s s')
    (hRd : ∀ v s s', Rd (batchAt fullLinks P5J.At.ps m + 1) v s → Lk.runBehind s = .ok s' →
      Rd (batchAt fullLinks P5J.At.ps m + 1 + 1) v s')
    (hb₀ : b₀ ≠ batchAt fullLinks P5J.At.ps m + 1 + 1)
    (said : ∀ k μ, Said (batchAt fullLinks P5J.At.ps m + 1) k μ →
      Said (batchAt fullLinks P5J.At.ps m + 1 + 1) k μ)
    (rides : RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (batchAt fullLinks P5J.At.ps m + 1)) :
    NoHouse (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall
      (batchAt fullLinks P5J.At.ps m + 1) Lk.behindB := by
  obtain ⟨e1, e2, e3⟩ := head_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm
  exact noHouse_behind_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said fall hm St
    (behind_num_head h hm St.lk) hn e1 e2 e3 hg htest hctx
    (fun s s' h0 hy => hKp s s' (after_keeps Lk (after_share_head h hm St.lk St.seg) s s'
      (rows_share_head h hm St.lk St.seg) h0 hy))
    hRd hb₀ said rides

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.behind_num_head
#print axioms ProofFile.Honest.FirstThread.noHouse_behind_all
