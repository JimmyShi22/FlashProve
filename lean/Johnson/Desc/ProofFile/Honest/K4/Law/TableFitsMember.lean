-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/TableFitsMember.lean: CONDITIONAL: on h and `LaidK4`.

What is here. THE PUBLIC DATA OF K4's MEMBER AT A GROUP OF LAYERS, AND THAT THE FIRST OF THE FOUR
PUBLIC TESTS ON THE PARTS OF THE FEED-FORWARD LAYERS' OWN ROUNDS (`k4TableFits`,
Honest/K4/Part.lean) IS TRUE AT THEM, under the library's hypothesis on the public files (h:
`P5J.AtMgA`) and `LaidK4` (Law/SeatedHead.lean). Its use: K4's lot lays a half at a place only where
that test accepts (`lot_half_head`, Law/HalfHead.lean). A definition, and statements with their
proofs.

  `k4PubAt`   the public data that `k4PubOf` returns at the member's parameters, under h and
      `LaidK4`.
  `pubAt_is`, `pubAt_place`   they are `k4PubAtX`'s (Law/FitsX.lean); their place is the member's.
  `tableFits_head`, `tableFits_member`   **the test on the table is true under h.**

How. Eight of the test's eleven clauses hold at every public data (Law/TableFitsFree.lean,
Law/TableFitsRows.lean); that K4 covers the plan: the library's `covers_of_lines`
(Johnson/Road/K4/RefInScope.lean) at its `PubLines`; the group in the list of tails and each
borrowed matrix's owner: a closed fact (`freeOwners`, Johnson/Road/K4/C/Free/FreeOwners.lean)
through the door under the head (`twins_head_all`, Johnson/Road/K4/C/PublicLight.lean).

Not shown here. THAT h CAN HOLD: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). BESIDE h: hg and hG (the group has a plan) in `tableFits_head`;
`LaidK4` in the three others. The three other public tests: Law/FitsMember.lean. THE TEST IS WEAK
WHERE IT CANNOT FAIL: eight of its eleven clauses are true at every public data. COUNTS AND PUBLIC
NUMBERS ALONE: nothing on what a half sends. THE FULL SIZE ALONE, and the format's second hash
function alone (`OnBytes.secondHashFunction`). Beneath it stand uses of kernel_rfl, comparisons by Lean's own
kernel, in the facts of Johnson/Road/K4/C/Free/ that it calls and in what these share
(Johnson/Road/K4/RowHead/ClosedAt.lean, Johnson/Road/K4/RowHead/ClosedTies.lean): not counted here;
no independent checker has replayed them. A LAW, NOT A PART: no file that defines a part of the
proof file's description may import this one. WHAT THIS FILE's IMPORTS REACH, by a program's walk
from import to import that stops, unopened, at every module under Johnson/Goal/, Johnson/D/,
Johnson/Bridge/ or ThirdParty/, at every module whose name begins Cb.Bridge, and at the names
RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…: it stopped at 36 modules under
Johnson/Goal/ and at 5 under Johnson/Bridge/; it saw 46 modules whose names hold RecCompile, none
under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of the three names. What lies
behind the 41 is not counted: all the numbers are floors. Nothing on soundness, on completeness or
on any other property.

Kin. No twin is known to its writers. `fits_member` (Law/FitsMember.lean) has all four tests at
these data, from two of them; it calls `tableFits_member`.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontCount
import Johnson.Desc.ProofFile.Honest.K4.Law.FitsX
import Johnson.Desc.ProofFile.Honest.K4.Law.TableFitsRows
import Johnson.Road.K4.C.PublicLight
import Johnson.Road.K4.C.Free.FreeOwners
import Johnson.Road.K4.RefInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Road.K4 (refPub_in_scope covers_of_lines)
open OnBytes.Road.K4.C (twins_head_all)
open OnBytes.Road.K4.C.Free (ownersAt freeOwners)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- **The public data that `k4PubOf` returns at the member's parameters, UNDER h AND `LaidK4`**
(`k4Pub_head`, Law/FrontCount.lean). The definition asks neither: it copies five fields of x.2, lays
twice the group as the segment, and counts the rounds in front off the chain's flat list
(`roundsTo`); it reads no public part, and not x.1. `k4PubOf` counts them off the public part's
table, and returns nothing where that table has no such step. -/
def k4PubAt (cF : Chain TS ProofFile.Cl) (k : ℕ) (x : Bool × Par) : K4Pub :=
  { P := x.2.P, hp := x.2.hp, g := x.2.g, link := x.2.link, piece := x.2.piece,
    r0 := roundsTo cF.blocksInOrder k, seg := 2 * x.2.g }

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on `LaidK4`. **THE LINK**: the member's public data are `k4PubAtX`. -/
theorem pubAt_is {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk) :
    k4PubAt cF k x = k4PubAtX (P5J.At.X Zp) x.2.hp g (roundsTo cF.blocksInOrder k) := by
  unfold k4PubAt k4PubAtX
  rw [Lh.P, Lh.grp, Lh.link, Lh.piece]

/-- The public data's place is the member's. -/
theorem pubAt_place {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk) : k4Place (k4PubAt cF k x) = IM.k4Place g := by
  show (⟨1, some x.2.link, x.2.piece, .K4⟩ : Place) = IM.k4Place g
  rw [Lh.link, Lh.piece]

/-- CONDITIONAL on h. **THE TEST ON THE TABLE IS TRUE UNDER h**, at each group and its plan. -/
theorem tableFits_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) (r0 : ℕ) :
    k4TableFits (k4PubAtX (P5J.At.X Zp) hp g r0) = true := by
  obtain ⟨s0, HL, -⟩ := (refPub_in_scope h.scope h.reads h.pubOne hg).lines hp hG
  have L := HL (P5J.At.X Zp).layers.tokv
  have hll : 1 < (Verify.layerShape (P5J.At.X Zp).P).ll := by
    rw [← L.Z.lL]
    decide
  have hc : OnBytes.Desc.First.K4.covers (k4PubAtX (P5J.At.X Zp) hp g r0).P = true :=
    covers_of_lines L.hy L.S hll L.hrd L.hN
  have o := twins_head_all h ownersAt freeOwners hg hG
  unfold ownersAt at o
  rw [Bool.and_eq_true] at o
  exact tableFits_three hc o.1 o.2

/-- CONDITIONAL on h and `LaidK4`. **AT THE MEMBER's OWN PUBLIC DATA.** -/
theorem tableFits_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) :
    k4TableFits (k4PubAt cF k x) = true := by
  rw [pubAt_is Lh]
  exact tableFits_head h Lh.lt Lh.hp _

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4PubAt
#print axioms ProofFile.Honest.K4.pubAt_is
#print axioms ProofFile.Honest.K4.pubAt_place
#print axioms ProofFile.Honest.K4.tableFits_head
#print axioms ProofFile.Honest.K4.tableFits_member
