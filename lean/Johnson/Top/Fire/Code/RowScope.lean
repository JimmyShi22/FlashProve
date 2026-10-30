-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowScope.lean (OVER THE ONE BUILD ON WHICH THIS GROUP OF FILES IS WRITTEN; CALLED OUT OF KeyMemberAtSeat.lean | KeyPublicAtSeat.lean: plan10 ·
  cond10_in_scope · public10_in_scope · lengths_full · first_blocksOk | shared_blocksOk;
  last_of_seal | cutDs_held are called out of the general RowStretch.lean:
  so nothing of K13 lies beneath):
  THE KEY FILE's ROWS
  1.0 | 1.1, LEVEL 8: THE PAYERS' JOINTS: what the two rows' public premises ARE in the goals'
  scope, each by A CALL of a theorem that lies, and a handful of closed facts by the kernel at the
  written key (Lk6.AtPlan.keyFull), each with a plant beside it.
OBJECT: par10 X | par11 X (Row10At.lean | Row11.lean: K1's numbers at the key file's first two
  places) · USER: Row10Eight.lean | Row11Eight.lean · LETTERS: Zp · X₀ · cfg · m · X · N · P.
  par10_is | par11_is  by rfl: these numbers ARE parIdx X | parMsg X (KeySendAtDesc.lean)
  trees_reads          Par.trees reads the codes and the parts alone
  CLOSED, BY THE KERNEL: trees_idx_full | trees_msg_full (one tree a place) · THE PLANTS:
    trees_plant · shape_plant
  IN SCOPE: codes_key · lengths_key (lengths_full) · asks10 | asks11 (KeySendScope.lean's
    asks_in_scope) · plan11_of (msg_pays at the block's own test, from planOk_blocks) ·
    cond11 (KeySendGood.lean's cond_of) · trees10 | trees11 · shape10
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row11Seven
import Johnson.Top.Fire.Code.RowStretch
import Johnson.Top.Fire.Code.KeyMemberAtSeat
import Johnson.RunOne.KeySendScope
import Johnson.RunOne.KeyFillSame
import Johnson.RunOne.KeySeatScope
import Johnson.Desc.Sound.BoundsAtCap
import Johnson.Desc.Sound.ToldCount
import Johnson.Desc.PlanPasses
import Johnson.Desc.Sound.StageCut

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
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃
    seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)

open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece Sealed shapeAt shapesOf sampledAt
    errPort seedMaps seedEntry Tie planOkOwn)
open Johnson.Pack (portOmZ)
open Johnson.RunOne.KeySendErr (shareB belowB)
open Johnson.RunOne.KeyRows23 (baseK tieS_fam readerOf readerIn words_zero seatAt)
open VerifiableInference.Desc.Key.Fill (ShapesApart symsW six)
open Johnson.RunOne.KeySendGood (SendAsks asks_in_scope cond_of parIdx parMsg fullIdx fullMsg idx_at
    msg_at idx_pays msg_pays pays_bare rounds_idx rounds_msg seed_kind)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Lk6.AtPlan (keyFull)

theorem par10_is (X : Source) : par10 X = parIdx X := rfl
theorem par11_is (X : Source) : par11 X = parMsg X := rfl

/-- Par.trees reads the codes and the parts alone. -/
theorem trees_reads (Q Q' : Par) (hc : Q.codes = Q'.codes) (hp : Q.parts = Q'.parts) : Q.trees =
    Q'.trees := by
  unfold Par.trees Par.sent
  rw [hc, hp]

/-! ## Closed facts at the written key, by the kernel -/

theorem trees_idx_full : fullIdx.trees.length = 1 := by decide +kernel
theorem trees_msg_full : fullMsg.trees.length = 1 := by decide +kernel

/-- Plants: the same tests say no at a turned value. -/
theorem trees_plant : decide (fullIdx.trees.length = 2) = false := by decide +kernel
theorem shape_plant : decide (keyFull.once.input.shape = Johnson.Top.H.shMul) = false :=
    by decide +kernel

/-! ## From the tests on the plan alone -/

theorem plan11_of {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (hp : (Fk X N P).planOk = true)
    : planOkOwn (par11 X) = true :=
  (pays_bare _ Johnson.RunOne.KeyKeeps.st₁ _ (msg_pays _ _ _) ((Keeps.planOk_blocks (Fk X N P) hp).1
      _ (List.mem_of_getElem? (msg_at X N P)))).plan

/-! ## In scope -/

section
variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
variable {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP :
            ReadOf Zp.pol X₀) {cfg : ByteArray}
  {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp :
      (Fk X N P).planOk = true)
include hZ hP hm hX hp

/-- **(iv) «codes = csKey», typed.** -/
theorem codes_key : (oneAt X).codes = Johnson.Top.H.csKey := (five_in_scope hZ hP hm hX
    hp).2.2.2.2.trans Johnson.RunOne.KeyLetters.codes_full

theorem asks10 : SendAsks 129 (par10 X) (fun _ => 6130) := (asks_in_scope hZ hP hm hX hp).1
theorem asks11 : SendAsks 129 (par11 X) (fun _ => 3131959) := (asks_in_scope hZ hP hm hX hp).2.1

theorem lengths_key : (oneAt X).codes.lengthsOk = true := by
  rw [codes_key hZ hP hm hX hp]
  exact lengths_full

theorem cond11 : condPort (par11 X) (fun _ => 3131959) = true :=
  cond_of _ _ (plan11_of hp) (lengths_key hZ hP hm hX hp) (asks11 hZ hP hm hX hp).meets

theorem trees10 : (par10 X).trees.length = 1 := by
  obtain ⟨-, -, -, hi, hc⟩ := five_in_scope hZ hP hm hX hp
  rw [trees_reads (par10 X) fullIdx hc
      (by show [(_, #[X.Y.k.oneTime.indexMasks])] = _; rw [hi]; rfl)]
  exact trees_idx_full

/-- The first place's one message's shape is the library's shIdx. -/
theorem shape10 : (oneAt X).indexMasks.shape = Johnson.Top.H.shIdx := by
  rw [(five_in_scope hZ hP hm hX hp).2.2.2.1]
  exact Johnson.RunOne.KeyLetters.idx_shape_full

theorem trees11 : (par11 X).trees.length = 1 := by
  obtain ⟨-, hr, -, -, hc⟩ := five_in_scope hZ hP hm hX hp
  rw [trees_reads (par11 X) fullMsg hc
      (by show [(_, Wf.messageOf X.Y.k.oneTime.ranges)] = _; rw [hr]; rfl)]
  exact trees_msg_full

end

end LPFD

#print axioms LPFD.par10_is
#print axioms LPFD.par11_is
#print axioms LPFD.trees_reads
#print axioms LPFD.trees_idx_full
#print axioms LPFD.trees_msg_full
#print axioms LPFD.trees_plant
#print axioms LPFD.shape_plant
#print axioms LPFD.plan11_of
#print axioms LPFD.codes_key
#print axioms LPFD.asks10
#print axioms LPFD.asks11
#print axioms LPFD.lengths_key
#print axioms LPFD.cond11
#print axioms LPFD.trees10
#print axioms LPFD.shape10
#print axioms LPFD.trees11
