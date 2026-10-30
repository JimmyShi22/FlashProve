-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyAt32Letters.lean: THE KEY FILE: THREE PREMISES OF THE THREE JOINS pays_29 | pays_210 | pays_32, IN SCOPE, AT THE FILLING's OWN TERMS (RunOne/KeyRowsAtFk.lean:90: K₁ := plan₁ (oneAt X) · a₀ := (oneAt X).given.plan.samples): hnum₁ (rows 2.9 | 2.10) · ha (row 3.2) · AND hfit (row 3.2; also guard_32_at_all | aSide₂_at_all and at_32 ask it; so does aSide₃_at_all, which is not in this library).
(oI · hidx · hoI · hnI at 3.2: by k1_facts_32: NOT HERE.)
OBJECT: premises of pays_29 | pays_210 | pays_32 · USER: whoever calls these at the name · LETTERS: none but the scope's; B in the last three.
  num₁_of              PROVED: 1 ≤ stages · 0 ∈ ks · 2 ∈ ks ⟹ hnum₁'s text at K₁ := plan₁ one and ks: by planOk₁
  num₁_29 | num₁_210   PROVED, IN SCOPE: hnum₁ TO THE SIGN at ks := [0, 2, 4, 5] | [0, 2, 4]
  samples_32           PROVED, IN SCOPE: (oneAt X).given.plan.samples ≠ 0: by samples_in_scope (it is 1)
  fits_of_recBack      PROVED, IN SCOPE: recBack x = some r → x.key.fits (shapeAt X).fold.index = true
  fits_of_freeAt₃ | fits_of_freeAt₂   PROVED, IN SCOPE: WHERE THE READING's LETTER recOf IS recBack (the name's own: baseAt … recBack): the promise's FIRST clause (Free₃.record | Free₂.record : FreeAt) ⟹ hfit TO THE SIGN.
WHY NOT «OFF THE HISTORY»: Hist₁'s start asks nothing of the instance (st₁ : a.2 = F.start₁ a.1, at EVERY x): so no history yields a fact on x's key. BUT THE PROMISE DOES: FreeAt says that the reading finds the key file's stored data behind the instance; at recOf := recBack that is «x = keyInstanceOfOutOfDomainSample r», and fits_in_scope has the fit at every keyInstanceOfOutOfDomainSample r. SO hfit IS A PROJECTION OF On₃ … 2 a (where «unmarked» holds), NOT A TEST MORE.
KIN: instK_of_recBack (private) is recBack_spec (Top/Fire/Code/Rows2TiesB.lean:56) to the letter: not imported: that file stands over rows 2.1 | 2.4 | 2.7's whole cone.
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.KeyAtName
import Johnson.Top.Fire.Code.KeyPublicAtSeat
import Johnson.RunOne.KeyAtFkMore
import Johnson.RunOne.KeySamples
import Johnson.RunOne.KeyScopeNums

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
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)

open VerifiableInference.Desc.Key.Fill (six OmAt)
open Johnson.RunOne.KeyRows23 (atSix)
open Johnson.RunOne.KeyRows1 (plan₁)
open Johnson.RunOne.KeyRows23 (planOk₁ shapeAt P₂ P₃)

theorem num₁_of (one : OnBytes.Params.OneTime) (hst : 1 ≤ one.ranges.stages.length) (ks : List ℕ) (h0 : 0 ∈ ks) (h2 : 2 ∈ ks) :
    ∀ k ∈ [0, 2], ∀ o, (plan₁ one).orc k = some o → ∀ j, (plan₁ one).num o = some j → j ∈ ks := by
  intro k hk o ho j hj
  obtain ⟨o', ho', hn'⟩ := planOk₁ one hst k hk
  obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
  obtain rfl : k = j := Option.some.inj (hn'.symm.trans hj)
  rcases (by simpa using hk : k = 0 ∨ k = 2) with rfl | rfl
  · exact h0
  · exact h2

private theorem instK_of_recBack (x : Xi) (r : RecFull) (h : recBack x = some r) : VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r = x := by
  unfold recBack at h
  split at h
  · rename_i hx
    cases h
    exact Classical.choose_spec hx
  · cases h

section
variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}

theorem samples_32 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) : (oneAt X).given.plan.samples ≠ 0 := by
  have h : (oneAt X).given.plan.samples = 1 := Johnson.RunOne.KeySendGood.samples_in_scope hZ hP hm hX hp
  rw [h]
  decide

theorem stages_32 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) : 1 ≤ (oneAt X).ranges.stages.length := by
  rw [(five_in_scope hZ hP hm hX hp).2.1, Johnson.RunOne.KeyLetters.stages_full]
  decide

theorem num₁_29 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) :
    ∀ k ∈ [0, 2], ∀ o, (plan₁ (oneAt X)).orc k = some o → ∀ j, (plan₁ (oneAt X)).num o = some j → j ∈ [0, 2, 4, 5] :=
  num₁_of (oneAt X) (stages_32 hZ hP hm hX hp) [0, 2, 4, 5] (by decide) (by decide)

theorem num₁_210 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) :
    ∀ k ∈ [0, 2], ∀ o, (plan₁ (oneAt X)).orc k = some o → ∀ j, (plan₁ (oneAt X)).num o = some j → j ∈ [0, 2, 4] :=
  num₁_of (oneAt X) (stages_32 hZ hP hm hX hp) [0, 2, 4] (by decide) (by decide)

theorem fits_of_recBack (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) (x : Xi) (r : RecFull) (h : recBack x = some r) :
    x.key.fits (shapeAt X).fold.index = true := by
  have hf := fits_in_scope hZ hP hm hX hp r
  rw [instK_of_recBack x r h, (one_full hZ hP hm hX hp).2.1] at hf
  rw [shape_full hZ hP hm hX hp]
  exact hf

variable {Cells M Smp : Type} (B : BaseSt Cells M Smp RecFull)

/-- **hfit at the last chain: a projection of the promise's first clause.** -/
theorem fits_of_freeAt₃ (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) (hB : B.recOf = recBack) (coll : Strs → RecFull → Prop)
    (z : P₃ × St₃) (y : Strs) (h : FreeAt B.h₃ coll z y) : z.1.1.key.fits (shapeAt X).fold.index = true := by
  obtain ⟨r, hr, -⟩ := h
  exact fits_of_recBack hZ hP hm hX hp z.1.1 r (by rw [← hB]; exact hr)

/-- The like at the shared chain. -/
theorem fits_of_freeAt₂ (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) (hB : B.recOf = recBack) (coll : Strs → RecFull → Prop)
    (z : P₂ × St₂) (y : Strs) (h : FreeAt B.h₂ coll z y) : z.1.1.key.fits (shapeAt X).fold.index = true := by
  obtain ⟨r, hr, -⟩ := h
  exact fits_of_recBack hZ hP hm hX hp z.1.1 r (by rw [← hB]; exact hr)

end

end LPFD

#print axioms LPFD.num₁_of
#print axioms LPFD.samples_32
#print axioms LPFD.stages_32
#print axioms LPFD.num₁_29
#print axioms LPFD.num₁_210
#print axioms LPFD.fits_of_recBack
#print axioms LPFD.fits_of_freeAt₃
#print axioms LPFD.fits_of_freeAt₂
