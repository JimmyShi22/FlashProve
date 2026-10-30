-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/HalfHead.lean: CONDITIONAL.

What is here. TOWARDS TWO HYPOTHESES OF `k4_accepted_dear` (Law/DearTop.lean), half AND hf, AT THE
MEMBER OF THE FEED-FORWARD LAYERS' ROUNDS, under h : AtMgA and `LaidK4`: what K4's own lot holds at
the member's place; and hf at the falls by the member's number. (1) K4's lot's honest side holds, as
its first half at the member's place, `k4Half` at the public data `k4PubAt`, at the ground
`ProofFile.blankBy ProofFile.pureRoad.links Zp`: NOTHING ELSE IS ASKED: that `k4PubOf` returns and that the test
`k4TableFits` accepts the public data stand under h and `LaidK4` (`k4Pub_head`, Law/FrontCount.lean
· `tableFits_member`, Law/TableFitsMember.lean, where `k4PubAt` is defined). It is the premise hg,
"what my own list holds at the place", of the frame's laws on which half is found at a place
(`firstOf_find`, Honest/FirstFind.lean; `atPure_first_find_kind`, Honest/FirstFindKind.lean; not
imported here). (2) hf holds at the falls by the member's number (`fallsBy`,
Honest/Law/FallFree.lean) of every list of falls that holds `k4Fall (k4PubAt cF k x)`. Statements
and proofs: calls of Law/LotFind.lean.

  `lot_half_head`   **the lot's first half at the member's place**, at a ground whose list holds x.
  `lot_half_ground`   the same at the ground that `LaidK4` names.
  `hf_head`   **hf at the falls by the member's number.**

Not shown here. That K4's lot stands in any prover's list of lots; that no other lot has a half at
the place; that a prover's ground is `ProofFile.blankBy ProofFile.pureRoad.links Zp`: so half itself, which
speaks of a prover's list, is not concluded. hm: that K4's own fall stands in any list of falls.
THAT h CAN HOLD: the side library AtFullSide proves, with no hypothesis, that h has a member at one
place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say
what it is worth). `LaidK4` ASKS NOTHING BEYOND h: `laid_head` (Law/SeatedHead.lean) has it at the
library's `atK4_full`, at each group below 12. hx is a field of it (lot), at the ground that is made
of the public part. THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction` alone. Beneath `lot_half_head`
stand comparisons by Lean's own kernel: the test `k4TableFits` is accepted through
`tableFits_member`, whose file's head says where its uses of kernel_rfl stand; that `k4PubOf`
returns stands, through `k4Pub_head`, on `k4_front_closed` (Law/FrontClosed.lean: `decide +kernel`).
No independent checker that its writers know of has replayed them. A LAW, NOT A
PART: no file that defines a part of the proof file's description may import this one. WHAT THIS
FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at every
module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose name
begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…: it
stopped at 36 modules under Johnson/Goal/ and at 5 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 41 is not counted: all the numbers are floors.

Kin. No twin is known to its writers. `k4HLot_find` and `coin_of_fallOf` (Law/LotFind.lean) are the
two laws at any public data; here their hypotheses are paid under h and `LaidK4`. `half_atPure`
(Law/HalfAtPure.lean) goes on from `lot_half_head` to the hypothesis half at the prover that the
frame's maker returns.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TableFitsMember
import Johnson.Desc.ProofFile.Honest.K4.Law.LotFind
import Johnson.Desc.ProofFile.Honest.Law.FallFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place} {W₀ Rc Tr X' : Type}

/-- CONDITIONAL: on h, `LaidK4` and hx. **THE LOT's FIRST HALF AT THE MEMBER's PLACE.** -/
theorem lot_half_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard) {G : ProofFile.Ground}
    (hx : x ∈ ProofFile.k4From Zp G G.built.toList 0 none) :
    ((k4HLot (Rc := Rc) (X := X') cells weights look).halves Zp G).find?
      (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights k4Tokens (look Zp G) (k4PubAt cF k x)) := by
  rw [← pubAt_place Lh]
  exact k4HLot_find cells weights look hx (k4Pub_head h Lh) (tableFits_member h Lh)

/-- The same at the ground that `LaidK4` names: the one that is made of the public part. -/
theorem lot_half_ground (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard) :
    ∃ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧
      ((k4HLot (Rc := Rc) (X := X') cells weights look).halves Zp G₀).find?
        (fun z => z.place == IM.k4Place g) =
        some (k4Half cells weights k4Tokens (look Zp G₀) (k4PubAt cF k x)) := by
  obtain ⟨G₀, hG, hx⟩ := Lh.lot
  exact ⟨G₀, hG, lot_half_head h Lh cells weights look hx⟩

/-- CONDITIONAL: on `LaidK4` and hm. **hf AT THE FALLS BY THE MEMBER's NUMBER.** -/
theorem hf_head {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk) {fs : List (Fall TS)}
    (hm : k4Fall (k4PubAt cF k x) ∈ fs) :
    ∀ s ds, fallsBy fs cF.blocksInOrder k s ds = none → k4CoinZero (k4PubAt cF k x) ds = none := by
  intro s ds hn
  unfold fallsBy at hn
  rw [Lh.member] at hn
  refine coin_of_fallOf hm (s := s) ?_
  rw [pubAt_place Lh, ← IM.alone_place Lh.laid]
  exact hn

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.lot_half_head
#print axioms ProofFile.Honest.K4.lot_half_ground
#print axioms ProofFile.Honest.K4.hf_head
