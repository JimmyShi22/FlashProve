-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/LaidAtGroup.lean: CONDITIONAL.

What is here. UNDER h, `LaidK4` (Law/SeatedHead.lean) HAS A MEMBER AT EACH OF THE TWELVE GROUPS OF
LAYERS: at the member number 28 g + 4 and the segment 2 g of the first chain there are parameters x
and a block blk with `LaidK4 Zp cF (28 * g + 4) (2 * g) g x blk`. `laid_head` (Law/SeatedHead.lean)
has, from a row of the table of places (`AtK4`), `LaidK4` at some group; the library's `atK4_full`
(Johnson/Road/K4/K04Tied.lean) has that row at each group. Here the two are joined, and the group
that comes out is the group that went in: two calls and one line of arithmetic.

  `laid_at`   **h and g < 12 give `LaidK4` at the group g.**

What it is for. Nearly every law of this folder stands under h and `LaidK4`: with this, whoever has
h has both.

Not shown here. h: the library's hypothesis `P5J.AtMgA` on the public files: the side library
AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what
it is worth). Beside g < 12, h is this statement's only hypothesis. Nothing on any other hypothesis
of a law that takes h and `LaidK4`. THE FULL SIZE ALONE, and the format's second hash function alone. A LAW,
NOT A PART: it stands over Law/SeatedHead.lean, whose closure reaches modules under Johnson/Goal/:
no file that defines a part of the proof file's description may stand over this one.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.SeatedHead
open OnBytes.Maker (WholeD)
open OnBytes.Road.K4 (atK4_full)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **h AND g < 12 GIVE `LaidK4` AT THE GROUP g.** CONDITIONAL: on h. -/
theorem laid_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12) :
    ∃ x blk, LaidK4 Zp cF (28 * g + 4) (2 * g) g x blk := by
  obtain ⟨g', x, blk, L⟩ := laid_head h (atK4_full g hg)
  obtain rfl : g' = g := by
    have e := L.num
    omega
  exact ⟨x, blk, L⟩

end ProofFile.Honest.K4.SeatedHead

#print axioms ProofFile.Honest.K4.SeatedHead.laid_at
