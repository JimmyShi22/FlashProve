-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FitsMember.lean: CONDITIONAL. Statements with their proofs.

What is here: THE PUBLIC TEST ON THE PARTS OF THE FEED-FORWARD LAYERS' OWN ROUNDS (`k4Fits`,
Honest/K4/Part.lean; the sub-protocol K4), ALL FOUR OF ITS TESTS, AT THE MEMBER's OWN PUBLIC DATA,
under the library's hypothesis on the public files (h: `P5J.AtMgA`) and `LaidK4`
(Law/SeatedHead.lean). THE TEST ON THE TABLE (`k4TableFits`) IS TRUE THERE, WITH NO FURTHER
HYPOTHESIS: `tableFits_member` (Law/TableFitsMember.lean; called here). `fits_member`: `k4Fits` IS
TRUE THERE at every value fo of what the lookup has sampled that passes the test on its sizes
(`k4LookFits`) and at every request that passes the test on the tokens (`k4TokensFit`): of the four
tests the table's is had with no further hypothesis, the makers' from the test on the lookup's
sizes. That is the field fits of `K4Seated`, at these data, from the two other tests.
How. The table, in Law/TableFitsMember.lean: eight of its eleven clauses hold at every public data
(Law/TableFitsFree.lean, Law/TableFitsRows.lean); that K4 covers the plan: the library's
`covers_of_lines` (Johnson/Road/K4/RefInScope.lean) at its `PubLines`; the group in the list of
tails and each borrowed matrix's owner: a closed fact (`freeOwners`,
Johnson/Road/K4/C/Free/FreeOwners.lean) through the door under the head (`twins_head_all`,
Johnson/Road/K4/C/PublicLight.lean). The makers: `makersFit_member`; the link to the member's data:
`pubAt_is` (Law/TableFitsMember.lean).

Not shown here. That h can hold: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). BESIDE h: `LaidK4`, which h gives at each group (`laid_at`,
Law/LaidAtGroup.lean). Of h together with `LaidK4`, hL and hT at a run's own values no example is
known to us. THE FULL SIZE ALONE, and the format's second hash function alone. That `k4LookFits` holds at
what a run's lookup samples, and `k4TokensFit` at a run's request: hypotheses here (for the second,
at the honest side's reader of the request: `hTk_of`, Law/TokensSeat.lean; Law/TokensHead.lean
speaks of the tokens in the verifier's state, not of these). THE TEST IS WEAK WHERE IT CANNOT FAIL:
eight of the table's eleven clauses and five of the makers' fifteen are true at every public data.
WHAT THE TEST DOES NOT SEE: at the small synthetic plan, with the number of column bits of the
weights' layout one higher, all eighteen clauses of `k4Fits` still say true (Law/FitsXBends.lean).
IT SAYS NOTHING ON WHAT ANY PART SENDS: counts, returns, shapes and sizes. Beneath it stand uses of
kernel_rfl, comparisons by Lean's own kernel: one in each of the eight facts of
Johnson/Road/K4/C/Free/ that it calls, and seven that these share
(Johnson/Road/K4/RowHead/ClosedAt.lean, ClosedTies.lean), five of them with the parameter file's
eight free numbers as a variable. No independent checker has replayed them. Its imports reach files
under Johnson/Goal/: a program's walk from import to import, which reads import lines alone and
stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at
71 modules under Johnson/Goal/: a floor (with h; with Johnson/Road/K4/RefInScope.lean): A LAW, NOT A
PART: no file that defines a part of the proof file's description may import this one. Nothing on
soundness, on completeness or on any other property.
No property is claimed.

  `fits_member`   **the public test, whole**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TableFitsMember
import Johnson.Desc.ProofFile.Honest.K4.Law.MakersFitMember
import Johnson.Desc.ProofFile.Honest.K4.Law.TableFitsRows
import Johnson.Road.K4.C.Free.FreeOwners

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (refPub_in_scope covers_of_lines)
open OnBytes.Road.K4.C (twins_head_all)
open OnBytes.Road.K4.C.Free (ownersAt freeOwners)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h, `LaidK4`, hL and hT. **THE PUBLIC TEST, WHOLE, AT THE MEMBER's OWN PUBLIC
DATA.** -/
theorem fits_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {fo : Forest.Heard}
    {tokv : Array Nat} (hL : k4LookFits (k4PubAt cF k x) fo = true)
    (hT : k4TokensFit (k4PubAt cF k x) tokv = true) : k4Fits (k4PubAt cF k x) fo tokv = true := by
  unfold k4Fits
  rw [tableFits_member h Lh, hL, hT, makersFit_member h Lh hL]
  rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.fits_member
