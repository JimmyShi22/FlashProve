-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/VCAVDet.lean: the value of the verifier with a record at the verifier's side
(`VCAV`, Johnson/TypedOracleCompiler/RecCompile/CmsAnsSide.lean) at a family F of typed oracle functions: where the
key holds a proof string for Test, one entry with a proof string for Link, and the proof holds one
for the session: the conjunction of the test on the number of the stored copy, the two seeds' tests
and the three arms' values at F. Where one of the three strings is missing: false. General in the
wire records and the other letters. `VRAV_det`: so the value of the verifier at the key (root,
record), at EVERY key and EVERY proof: `VRAV` hands `VCAV` a key with just one entry and the place
0.
-/
import Johnson.TypedOracleCompiler.RecCompile.FrontRootAnsSide
import Rom.Cache

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch.Cms
open Rom _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} {lam : ℕ} {L : LHV X} {Bd : Type} {aT : RoundSplits L.test.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (carrierV L Bd aT aL)) (S : SeedV lam W.K L Bd aT aL)
  (cA : L.Ans → List (Dig lam)) (r₀ : L.Rec) (p : Params)
  (F : Fam (typedOracleFamily lam W.K (carrierV L Bd aT aL)))

/-- (J) **The value of `VCAV` where all three strings are there.** -/
theorem VCAV_det (cm : Dig lam) (rcd : L.Rec) (πT : OneProtocolProof lam (batTV L aT)) (cmj : Dig lam)
    (recj : L.Rec) (πL : OneProtocolProof lam (batLV L aL)) (x : X) (n : ℕ) (πB : OneProtocolProof lam L.bat) :
    (VCAV W S cA r₀ p ⟨cm, rcd, some πT, [(cmj, recj, some πL)]⟩ x ⟨0, n, some πB⟩).det F =
      (S.num n πB.plains && (seedIsV W S cm rcd.1).det F && (seedIsV W S cmj recj.1).det F &&
        (vTAV W cA p cm rcd πT).det F && (vLAV W cA p cm cmj rcd recj πL).det F &&
        (vBAV W cA r₀ p cmj x recj πB).det F) := by
  show ((seedIsV W S cm rcd.1).bind fun s0 =>
      (seedIsV W S cmj recj.1).bind fun sj =>
      (vTAV W cA p cm rcd πT).bind fun a =>
      (vLAV W cA p cm cmj rcd recj πL).bind fun b =>
      (vBAV W cA r₀ p cmj x recj πB).bind fun c =>
      OComp.pure (S.num n πB.plains && s0 && sj && a && b && c)).det F = _
  simp only [OComp.det_bind]
  rfl

/-- No string for Test: false. -/
theorem VCAV_det_noT (cm : Dig lam) (rcd : L.Rec)
    (links : List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLV L aL)))) (x : X) (π : PrfCV lam L) :
    (VCAV W S cA r₀ p ⟨cm, rcd, none, links⟩ x π).det F = false := rfl

/-- No string for Link at the one entry: false. -/
theorem VCAV_det_noL (cm : Dig lam) (rcd : L.Rec) (πT : Option (OneProtocolProof lam (batTV L aT)))
    (cmj : Dig lam) (recj : L.Rec) (x : X) (n : ℕ) (πB : Option (OneProtocolProof lam L.bat)) :
    (VCAV W S cA r₀ p ⟨cm, rcd, πT, [(cmj, recj, none)]⟩ x ⟨0, n, πB⟩).det F = false := by
  cases πT <;> rfl

/-- No string for the session: false. -/
theorem VCAV_det_noB (cm : Dig lam) (rcd : L.Rec) (πT : Option (OneProtocolProof lam (batTV L aT)))
    (links : List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLV L aL)))) (x : X) (leaf n : ℕ) :
    (VCAV W S cA r₀ p ⟨cm, rcd, πT, links⟩ x ⟨leaf, n, none⟩).det F = false := by
  unfold VCAV
  split <;> first | rfl | simp_all

/-- **The value of `VRAV`, at every key and every proof.** -/
theorem VRAV_det (k : KeyRootV lam L) (x : X) (π : PrfRootV lam L aT aL) :
    (VRAV W S cA r₀ p k x π).det F =
      match π.piT, π.link.2.2, π.piB with
      | some πT, some πL, some πB =>
        (S.num π.copy πB.plains && (seedIsV W S k.cm k.rcd.1).det F &&
          (seedIsV W S π.link.1 π.link.2.1.1).det F && (vTAV W cA p k.cm k.rcd πT).det F &&
          (vLAV W cA p k.cm π.link.1 k.rcd π.link.2.1 πL).det F &&
          (vBAV W cA r₀ p π.link.1 x π.link.2.1 πB).det F)
      | _, _, _ => false := by
  obtain ⟨cm, rcd⟩ := k
  obtain ⟨copy, piT, ⟨cmj, recj, piL⟩, piB⟩ := π
  cases piT with
  | none => exact VCAV_det_noT W S cA r₀ p F cm rcd _ x _
  | some πT =>
    cases piL with
    | none => exact VCAV_det_noL W S cA r₀ p F cm rcd (some πT) cmj recj x copy piB
    | some πL =>
      cases piB with
      | none => exact VCAV_det_noB W S cA r₀ p F cm rcd (some πT) _ x 0 copy
      | some πB => exact VCAV_det W S cA r₀ p F cm rcd πT cmj recj πL x copy πB

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.VRAV_det
#print axioms TypedOracleCompiler.Compile.Batch.Cms.VCAV_det
#print axioms TypedOracleCompiler.Compile.Batch.Cms.VCAV_det_noT
#print axioms TypedOracleCompiler.Compile.Batch.Cms.VCAV_det_noL
#print axioms TypedOracleCompiler.Compile.Batch.Cms.VCAV_det_noB
