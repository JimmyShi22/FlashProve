-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/FullHead.lean: CONDITIONAL.

Not shown here. THAT h : AtMgA CAN HOLD: The side library AtFullSide proves, with no hypothesis,
that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). `lam_head` has h as
its only hypothesis. `fullAt_stand` takes no h: its hypotheses are Z (a stand), eY and eS (the
public data at which the stand's hearing runs have the layout and the scales of the public
parameters: at a stand the hearing runs at the public data with the state's tokens laid in, which
turns neither) and eL (four layers in a group: `lam_head` has it under h). THE FULL SIZE ALONE, and
the format's second hash function alone. Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 22 modules under Johnson/Goal/ and at 5 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 27 is not counted: all the numbers are floors. They come with
h, with Law/SeatedHead.lean and with Johnson/Road/K4/RowLightOfHead.lean. `lam_head` calls
`Meaning.P34.pub34_all`, a statement of a file under Johnson/Goal/.

The hypothesis `FullAt` (Johnson/Road/K4/W/IdnOfField.lean) behind the step from a stand, and the
one public fact under h that it wants. K4 is the sub-protocol of the feed-forward layers' own
rounds. Statements with their proofs: calls.

  `lam_head`   under h the public parameters have four layers in a group: the library's
      `Meaning.P34.pub34_all` and `laySizes_of_layout` (Johnson/Road/K4/PlanSizes.lean), as
      Johnson/Road/K4/RowLightOfHead.lean calls them.
  `fullAt_stand`   **general in the thread: `FullAt X Q.g (layerShape X.P) DF o`** behind the step
      from a stand (`K4Stand`, Law/SlotsTrue.lean): the step's own hearing is that return.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedHead
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsTrue
import Johnson.Road.K4.RowLightOfHead
import Johnson.Road.K4.W.FullOfHear

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4.W (FullAt fullAt_of_hear)
open OnBytes.Maker (WholeD)
open Inst.Model.All (DF)
open VerifiableInference.Desc (Chain Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **Four layers in a group, at the library's own public parameters.** CONDITIONAL: on h. -/
theorem lam_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) : (P5J.At.X Zp).y.Lam = 4 := by
  have hX : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok (P5J.At.X Zp) := h.pubOne
  obtain ⟨⟨hy, _, _, _, Zd, _, _, _, _, _, _, _⟩, _⟩ :=
    Meaning.P34.pub34_all h.scope h.reads hX OnBytes.Road.gl_numerals
  have hy' : Layer.layout (Verify.layerShape (P5J.At.X Zp).P) (P5J.At.X Zp).P.polCalls =
      .ok (P5J.At.X Zp).layers.y := hy
  have L := OnBytes.Road.K4.laySizes_of_layout hy'
  have ell : (Verify.layerShape (P5J.At.X Zp).P).ll = 2 := by
    rw [← Zd.lL]
    rfl
  show (P5J.At.X Zp).layers.y.Lam = 4
  rw [L.Lam, ell]
  norm_num

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X' Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X' Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X'} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X'}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- **`FullAt` BEHIND THE STEP FROM A STAND.** General in the thread. CONDITIONAL: on Z, eY, eS and
eL. -/
theorem fullAt_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    {X : Verify.Public} (eY : Q.P.y = X.y) (eS : Q.P.sc = X.layers.sc) (eL : X.y.Lam = 4) :
    FullAt X Q.g (Verify.layerShape X.P) DF o := by
  obtain ⟨_, _, fo, _, _, _, _, hh, _⟩ := step_tape Z.seat Z.sits Z.stepped Z.seg Z.heard
  exact fullAt_of_hear (P := { Q.P with tokv := s.tokv }) hh eY eS eL

end

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.lam_head
#print axioms ProofFile.Honest.K4.W.fullAt_stand
