-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeySmpStay2.lean: K14's
EIGHT BLOCKS' SHARE OF «THE SAMPLE ROWS STAY»: each of the eight blocks of the linear claim's shared
rounds (Desc.K14.blocks), of its own yes, leaves every SAMPLED message of the statement at its
number, with its shape, its mark and its sample rows (SmpStay: Johnson/Desc/K1/Law/SmpStay.lean): so
the sending kind's own sample row in the record (SeedIs) RIDES THROUGH ALL EIGHT, later sendings
among them (SeedIs.stays: K1/Law/SealStays.lean).
BY ONE CALL: Desc.K14.blocks_keep (Johnson/Desc/K14/BlocksKeep.lean: the eight blocks keep EVERY
relation that the ground's plain functions keep: general in R)
AT R := SmpStay WITH
groundKeeps_smpStay.
KIN, NOT CALLED HERE: Johnson/Desc/Sound/SamplesAtK14.lean (namespace Desc.K14.Law.Fence):
keepsSmp_k14: any of the eight: KeepsSmp d d' (shape ·
mark · sample rows of EVERY elder message stand): a stronger relation, proved there effect by
effect; it stands over BookAtK14 | K12/Coin/SamplesThrough.
OBJECT: b.decide, b ∈ [b1, …, b8] · held b · USER: l1hi_at6's premise h3 (pin 3's row from border 3
to border 6: Johnson/RunOne/KeyOn2Step.lean); whoever walks SeedIs along the shared chain · LETTERS:
Q b1 … b8; b.
  k14_smpStay     the eight, of their own decisions
  seedIs_rides    at a block as the maker holds it (held b; b.decide = bᵢ.decide): SeedIs in front
    gives SeedIs behind, at the same number, seed and answer
What is not claimed. Nothing on the shared chain's other blocks (the front; the proximity tests; the
end). NO MEMBER OF ANY PROMISE. Nothing on soundness.

-/
import Johnson.RunOne.KeyRowsSeat
import Johnson.Desc.K14.BlocksKeep
import Johnson.Desc.K1.Law.SealStays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Plain VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (SeedIs SmpStay groundKeeps_smpStay)
open _root_.Desc.K14 (P14 blocks)

/-- **The eight blocks, each of its own decision**: the general theorem at R := SmpStay. -/
theorem k14_smpStay (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit) (hbl : blocks Q = some [b1,
    b2, b3, b4, b5, b6, b7, b8])
    (b : Block St₂ Unit) (hmem : b ∈ [b1, b2, b3, b4, b5, b6, b7, b8]) (d d' : St₂) (rs : List
        Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : b.decide d rs gs = .ok d') : SmpStay d.st d'.st :=
  _root_.Desc.K14.blocks_keep groundKeeps_smpStay Q _ hbl b hmem d rs gs d' h

/-- **The sending kind's row rides through a block as the maker holds it.** -/
theorem seedIs_rides {Pr Cl : Type} (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit) (hbl :
    blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (b₀ : Block St₂ Unit) (hmem : b₀ ∈ [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St₂ Cl) (hd :
        b.decide = b₀.decide)
    (z z' : Pr × St₂) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h : (held b : Block
               (Pr × St₂) Cl).decide z rs gs = .ok z')
    (cs : Codes) (s : OracleShape) (o : Nat) (ρ : (Fin (Johnson.Pack.bitsZ cs s) → OnBytes.Slice.GE)
        × OnBytes.Slice.GEˣ) (y : OnBytes.Slice.GE)
    (H : SeedIs cs s z.2.st o ρ y) : SeedIs cs s z'.2.st o ρ y :=
  H.stays (k14_smpStay Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b₀ hmem z.2 z'.2 rs gs (hd ▸ (held_decide b z
      rs gs z' h).2))

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.k14_smpStay
#print axioms Johnson.RunOne.KeyRows23.seedIs_rides
