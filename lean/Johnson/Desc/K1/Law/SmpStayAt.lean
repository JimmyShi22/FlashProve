-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SmpStayAt.lean: which blocks and functions leave the codes and the sampled
messages (SmpStay, SmpStay.lean), said out: corollaries of the laws "this block keeps every relation
that the ground's plain functions keep" at groundKeeps_smpStay: the kind K1's three blocks at the
first chain's record; the kind K13's joined blocks there; a sending over the verifier program's own
functions (sendP); the eight functions of the page of the linear claim's shared rounds (K14).
So past each of them a sealed message stays sealed (Sealed.stays) and a held sample stays
(held_block, SmpHeldAt.lean).

Main names: sendAtS_smpStay, commitAtS_smpStay, firstAtS_smpStay; atM3_smpStay, atM4_smpStay;
sendP_smpStay; page_smpStay.

What is not claimed. Nothing on a block of another kind. K14's are the page's functions, not the
blocks that call them. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.SmpStay
import Johnson.Desc.K1.KeepsAtS
import Johnson.Desc.K13.Keeps
import Johnson.Desc.K14.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (GroundKeeps By)
open VerifiableInference.Desc.Keeps (Decides)

variable {L Cl : Type}

theorem sendAtS_smpStay (P : Par) :
    Decides (By SmpStay fun s : S => s.st) (sendAtS (Cl := Cl) P) :=
  Rel.sendAtS_keeps groundKeeps_smpStay P

theorem commitAtS_smpStay (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Decides (By SmpStay fun s : S => s.st) (commitAtS (Cl := Cl) P link moment arrays) :=
  Rel.commitAtS_keeps groundKeeps_smpStay P link moment arrays

theorem firstAtS_smpStay (q : Params.First) (gp : GPar) :
    Decides (By SmpStay fun s : S => s.st) (firstSegmentOpening (Cl := Cl) q gp) :=
  Rel.firstAtS_keeps groundKeeps_smpStay q gp

theorem atM3_smpStay (p : K13.Where) :
    Decides (By SmpStay fun s : S => s.st) (K13.atM3 (Cl := Cl) p) :=
  K13.atM3_keeps groundKeeps_smpStay.quiet p

theorem atM4_smpStay (p : K13.Where) (commitW : Block S Cl)
    (hW : Decides (By SmpStay fun s : S => s.st) commitW) :
    Decides (By SmpStay fun s : S => s.st) (K13.atM4 p commitW) :=
  K13.atM4_keeps groundKeeps_smpStay.quiet p commitW hW

/-- A sending over the verifier program's own functions, at either value of its flag, whatever the
announcements. -/
theorem sendP_smpStay (p : GPar) (own : Bool) (d : DState L) (sent : Array OracleNotice)
    (r₁ r₂ : Fmt.RoundView) (y : Array Nat × List E × List E × Nat × DState L)
    (h : sendP groundG p own d sent r₁ r₂ = some y) : SmpStay d.st y.2.2.2.2.st :=
  sendP_keeps groundKeeps_smpStay p own d sent r₁ r₂ y h

end VerifiableInference.Desc.K1

namespace Desc.K14
open OnBytes OnBytes.Params Desc.Plain VerifiableInference.Desc VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (SmpStay groundKeeps_smpStay)

/-- Each of the eight functions of Johnson/Desc/K14/Text.lean that return a state. -/
theorem page_smpStay (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (ids : Array Nat) :
    (linPoint p d rs = some d' → SmpStay d.st d'.st) ∧
    (laysRec p d rs = some d' → SmpStay d.st d'.st) ∧
    (loc p d rs gs = some d' → SmpStay d.st d'.st) ∧
    (joins p d rs = some d' → SmpStay d.st d'.st) ∧
    (linZeta d rs = some d' → SmpStay d.st d'.st) ∧
    (split p d rs = some d' → SmpStay d.st d'.st) ∧
    (behindU p d ids = some d' → SmpStay d.st d'.st) ∧
    (behindOmega p d ids = some d' → SmpStay d.st d'.st) :=
  ⟨linPoint_keeps groundKeeps_smpStay p d d' rs, laysRec_keeps groundKeeps_smpStay p d d' rs,
   loc_keeps groundKeeps_smpStay p d d' rs gs, joins_keeps groundKeeps_smpStay p d d' rs,
   linZeta_keeps groundKeeps_smpStay d d' rs, split_keeps groundKeeps_smpStay p d d' rs,
   behindU_keeps groundKeeps_smpStay p d d' ids, behindOmega_keeps groundKeeps_smpStay p d d' ids⟩


end Desc.K14
