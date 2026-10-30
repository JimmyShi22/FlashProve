-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/LookAtHead.lean: CONDITIONAL.

What is here. THE TWO SENTENCES ON THE PARAMETER `look` OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(`LookIsK3`, Law/LookPtsHead.lean; `LookIsK3Wide`, Law/LookOpenHead.lean) HOLD AT THE TEXT
`k4LookAt` (Honest/K4/Look.lean), AT THE MEMBER's OWN PUBLIC DATA, FROM h : AtMgA AND `LaidK4`
ALONE: at every list of challenges `k4LookAt` agrees with the text `lookOfK3` of the writers of the
sub-protocol K3 (lookups) in the fields zx, zk, e, shape, zb0 and zb1. By reading, not by a
statement: the two equations beneath it (`lookBase_head`, `pubShape_head`, Law/LookBaseHead.lean)
are the two hypotheses on which `k4LookAt` stands by its own file's head. One statement: a call of
`lookAt_isK3` (Law/LookAtFill.lean) with `lookBase_head` (Law/LookBaseHead.lean). What it is for:
that `lookAt_isK3` and `lookBase_head` fit each other is held by Lean here.

Not shown here. SIX FIELDS' TEXTS ALONE: the two whole structures differ (`lookOf_ne`,
Law/LookAtFill.lean). That these fields are those of the verifier's hearing is other files'
(`lookPts_head`, Law/LookPtsHead.lean; `openSame_head`, Law/LookOpenHead.lean), where the thread
stands. THAT ANY PROVER's HALF IS LAID OVER `k4LookAt` is not shown here. `LaidK4` follows from h at
each of the twelve groups (`laid_head`, Law/SeatedHead.lean, with the library's `atK4_full`). THAT h
CAN HOLD: the side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). `LaidK4` ASKS NOTHING BEYOND h: `laid_head` (Law/SeatedHead.lean) has it at the library's
`atK4_full`, at each group below 12. THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction` alone: NOTHING AT
A SMALLER SET OF PUBLIC FILES: there Honest/K4/LookSeat.lean has a test with code. Beneath it stand
comparisons by Lean's own kernel, as Law/LookAtFill.lean's head says of `lookAt_isK3`; no
independent checker has replayed them. THE FILES OF THE AUTHORS OF THE KIND "lookup" ARE READING
COPIES FOR US BY THEIR OWN WORD. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one: as Law/LookFitsFill.lean says of itself. Transitive imports: those
of Law/LookAtFill.lean and Law/LookBaseHead.lean: not counted. No property is claimed.

  `k4LookAt_head`   **`LookIsK3Wide` and `LookIsK3` at `k4LookAt`, from h and `LaidK4`.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.LookAtFill
import Johnson.Desc.ProofFile.Honest.K4.Law.LookBaseHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h and Lh. **THE TWO SENTENCES ON `look` AT `k4LookAt`.** ξ: an instance; the
text of the writers of the sub-protocol K3 (lookups) does not read it. -/
theorem k4LookAt_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) (ξ : ProofFile.Inst) :
    LookIsK3Wide k4LookAt (k4PubAt cF k x) Zp cF g ξ ∧
      LookIsK3 k4LookAt (k4PubAt cF k x) Zp cF g ξ :=
  lookAt_isK3 h Lh ξ (lookBase_head h Lh)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4LookAt_head
