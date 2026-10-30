-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/MakersFitMember.lean: CONDITIONAL. Statements with their
proofs.

What is here: THE CLAUSE ON THE MAKERS (`k4MakersFit`, Honest/K4/Part.lean: the last of the four
public tests on the parts of the feed-forward layers' own rounds, the sub-protocol K4) AT THE
MEMBER's OWN PUBLIC DATA, and that the test on the lookup's sizes has a member.
The link is `pubAt_is` (Law/TableFitsMember.lean; called here): under `LaidK4` (Law/SeatedHead.lean)
the public data at the member's parameters (`k4PubAt`, in that file: what `k4PubOf` returns there by
`k4Pub_head`, Law/FrontCount.lean) ARE `k4PubAtX` (Law/FitsX.lean) at the library's own public
parameters, the member's plan, its group and the rounds counted in front: field by field.
`lookFits_zero`: at every public data whose lookup has room for the long point (la ≤ dT) the test
`k4LookFits` is true at the value `k4ZeroLook` (Law/FitsX.lean). `lookFits_head`: so under h.
`makersFit_member`: under h and `LaidK4`: `k4LookFits` at fo gives `k4MakersFit` at fo, AT THE
MEMBER's DATA. `makersFit_zero_member`: at `k4ZeroLook` both tests are true there, with no further
hypothesis.

Not shown here. That h can hold: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). BESIDE h: hg and hG (the group has a plan) in `lookFits_head`;
`LaidK4`, which h gives at each group (`laid_at`, Law/LaidAtGroup.lean), in `makersFit_zero_member`;
`LaidK4` and hL in `makersFit_member`. THE FULL SIZE ALONE, and the format's second hash function alone.
That `k4LookFits` holds at what a run's lookup samples: `k4ZeroLook` is a value of the right sizes,
tied to no run. The test `k4TableFits` is not here. RETURNS, SHAPES AND SIZES AT THE ZERO INPUT:
nothing on what any maker's table is worth. Beneath it stand uses of kernel_rfl, comparisons by
Lean's own kernel: one in each of the seven facts of Johnson/Road/K4/C/Free/ that it calls, and
seven that these share (Johnson/Road/K4/RowHead/ClosedAt.lean, ClosedTies.lean), five of them with
the parameter file's eight free numbers as a variable. No independent checker has replayed them. Its
imports reach files under Johnson/Goal/: a program's walk from import to import, which reads import
lines alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/, Johnson/Bridge/ and
Cb/Bridge*, stopped at 71 modules under Johnson/Goal/: a floor (with h; with Law/DearTop.lean): A
LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
Nothing on soundness, on completeness or on any other property.
No property is claimed.

  `lookFits_zero`, `lookFits_head`   the test on the lookup's sizes has a member
  `makersFit_member`, `makersFit_zero_member`   **at the member**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MakersFitHead
import Johnson.Desc.ProofFile.Honest.K4.Law.DearTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4.C (light_head)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on hla. **The test on the lookup's sizes is true at `k4ZeroLook`.** -/
theorem lookFits_zero (Q : K4Pub) (hla : Q.P.y.h.la ≤ Q.P.y.fo.dT) :
    k4LookFits Q (k4ZeroLook Q.P) = true := by
  unfold k4LookFits
  dsimp only
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, decide_eq_true hla⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold OnBytes.Desc.First.K4.shapeFits k4ZeroLook
    simp
  · unfold k4ZeroLook
    simp
  · unfold k4ZeroLook
    simp
  · unfold k4ZeroLook
    simp
  · rw [List.all_eq_true]
    intro c hc
    have hc' := List.mem_range.1 hc
    unfold k4ZeroLook
    simp [Array.getD, hc']

/-- CONDITIONAL on h. So at the library's own public parameters, at each group and its plan. -/
theorem lookFits_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    {hp : HPlan2} (hG : (P5J.At.X Zp).G[g]? = some hp) (r0 : ℕ) :
    k4LookFits (k4PubAtX (P5J.At.X Zp) hp g r0) (k4ZeroLook (P5J.At.X Zp).layers) = true :=
  lookFits_zero (k4PubAtX (P5J.At.X Zp) hp g r0) (light_head h hg hG).2.1

/-- CONDITIONAL on h, `LaidK4` and hL. **THE CLAUSE ON THE MAKERS AT THE MEMBER's OWN PUBLIC DATA.**
-/
theorem makersFit_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {fo : Forest.Heard}
    (hL : k4LookFits (k4PubAt cF k x) fo = true) : k4MakersFit (k4PubAt cF k x) fo = true := by
  rw [pubAt_is Lh] at hL ⊢
  exact makersFit_head h Lh.lt Lh.hp _ hL

/-- CONDITIONAL on h and `LaidK4`. At `k4ZeroLook` both tests are true at the member's data. -/
theorem makersFit_zero_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) :
    k4LookFits (k4PubAt cF k x) (k4ZeroLook (P5J.At.X Zp).layers) = true ∧
      k4MakersFit (k4PubAt cF k x) (k4ZeroLook (P5J.At.X Zp).layers) = true := by
  have hL : k4LookFits (k4PubAt cF k x) (k4ZeroLook (P5J.At.X Zp).layers) = true := by
    rw [pubAt_is Lh]
    exact lookFits_head h Lh.lt Lh.hp _
  exact ⟨hL, makersFit_member h Lh hL⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.lookFits_zero
#print axioms ProofFile.Honest.K4.lookFits_head
#print axioms ProofFile.Honest.K4.makersFit_member
#print axioms ProofFile.Honest.K4.makersFit_zero_member
