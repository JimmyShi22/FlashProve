-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Rows2Public.lean: THE KEY FILE, THE SHARED CHAIN: TWO PUBLIC FACTS THAT THE CALLS OF ITS ROWS WANT, each from what the seat hands.
  eight_said      where the description's test on the plan says yes, the kind's blocks at the shared chain's parameters are eight, by name: TWO CALLS: blocks_said (KeyPublicAtSeat.lean) and Desc.K14.Law.eight (Johnson/Desc/K14/Law/SplitGiven.lean).
  split_in_scope  in the goals' scope the sized key's shape splits (shape_full; then the kernel at the written shape).
Limits. Public facts alone. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyPublicAtSeat
import Johnson.Desc.K14.Law.SplitGiven

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₂ open₃)
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)

/-- **The kind's blocks are eight.** -/
theorem eight_said (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hp : (Fk X N P).planOk = true) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, _root_.Desc.K14.blocks (p14At X P) = some [b1, b2, b3, b4, b5, b6, b7, b8] := by
  obtain ⟨l, hl⟩ := blocks_said X N P hp
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := _root_.Desc.K14.Law.eight _ l hl
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, hl⟩

theorem splitNeeded_full : keyFull.once.shape.sharedSplitNeeded = true := by decide +kernel

/-- **In scope the shape splits.** -/
theorem split_in_scope {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol X₀) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) :
    (p14At X P).S.sharedSplitNeeded = true := by
  have e : (p14At X P).S = keyFull.once.shape := shape_full hZ hP hm hX hp
  rw [e]
  exact splitNeeded_full

end LPFD

#print axioms LPFD.eight_said
#print axioms LPFD.split_in_scope
