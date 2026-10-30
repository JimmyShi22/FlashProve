-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/KeySeeds2910.lean: THE OOD SAMPLE's ROW (K1.SeedIs) AT THE MEMBERS OF THE TWO GROUPS THAT THE KEY FILE's SHARED CHAIN TESTS (rows 2.9 and 2.10 of the tables), IN THE VERIFIER's STATE IN FRONT OF EACH TEST: IN SCOPE, OFF THE CHAIN's HISTORY: in the letters in which the proximity test's kind's files ask for it. Statements with proofs: calls alone. IT PAYS NO FIELD OF THE TABLES.
THE MATHEMATICS IS OTHER FILES': u_row and omega_rows (Johnson/Top/Fire/Code/KeyOn2L1Hi.lean). HERE: these two called · their two public premises (the sending kind's condition condPort at the shared chain's two sendings) paid by Johnson/RunOne/KeyCondThree.lean · the first chain's list paid by head_flat · the shapes spelled as entries of the tables' list of six.
OBJECT. a.2.st at a state a that the shared chain has reached at a border from 6 on. USER. The proximity test's kind's files' bundle on the state at rows 2.9 | 2.10.
PREMISES. The scope's four · of the seat's accepting run: the later places and the place's numbers are made of the same m; the tests planOk and wantedOk accept · the history · AND ONE MORE: hfit: the instance's key fits the fold's index shape: u_row and omega_rows ask it.

  hC2_scope: u_row's premise hC2, to the letter, at the radius 8342420.
  seeds₂_scope: at every border from 6 on: message 0 bears an OOD sample of the fourth entry's shape, message 2 of the fifth's, message 3 of the sixth's.
  s9_scope, s10_scope: the two pairs that are asked for, at borders 9 and 10.
Limits. Empty where nothing is reached: no state reached at border 9 or 10 is shown by anybody. One size. Nothing on soundness, nothing on hiding.

-/
import Johnson.Top.Fire.Code.KeyOn2L1Hi
import Johnson.RunOne.KeyCondThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace Johnson.RunOne.Law.KeySeeds2910
open LPFD
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

open OnBytes.Params (OneTime Setting)
open Johnson.RunOne.KeyRows1
open Johnson.RunOne.KeyRows23 (CellOnly)

open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Johnson.RunOne.KeyRows23 (atSix)

open Johnson.RunOne.Law.StepSideGaps (gaps_of)
open Johnson.RunOne.Law.StepSideAtFk (H₀ H₁)

open Johnson.RunOne.KeyRows23
open VerifiableInference.Desc.Key.Fill (six)
open VerifiableInference.Desc.K1 (SeedIs condPort shapesOf shapeAt sampledAt SmpStay
    groundKeeps_smpStay)
open Lk6.AtPlan (keyFull)
open _root_.Desc.K14 (parK1 withU withOmega)
open Johnson.RunOne.KeyWalk (hist₂_rel begin_smp)

open Johnson.Top.H (csKey)

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- u_row's premise hC2. -/
theorem hC2_scope {Zp : VerifierAndGoals.PublicFiles} {Z : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) :
    condPort (parK1 (p14At X P) 2 "o_u and the first mask" sentUKey) (fun _ => 8342420) = true := by
  rw [Johnson.RunOne.KeyMsg.p14At_eta_scope hZ hP hm hX]
  exact Johnson.RunOne.KeyMsg.cond_u_full

/-- **The three rows, at every border from 6 on.** -/
theorem seeds₂_scope {Zp : VerifierAndGoals.PublicFiles} {Z : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true)
    (hN : rangesNumbers m = .ok N) (D : WholeD) (j : ℕ) (a : P₂ × St₂)
    (h : Hist₂ (Fk X N P) D (6 + j) a) (hfit : a.1.1.key.fits (shapeAt X).fold.index = true) :
    (∃ ρ yv, SeedIs csKey (six.get (⟨3, by decide⟩ : Fin six.length)).1 a.2.st 0 ρ yv) ∧
      (∃ ρ yv, SeedIs csKey (six.get (⟨4, by decide⟩ : Fin six.length)).1 a.2.st 2 ρ yv) ∧
      ∃ ρ yv, SeedIs csKey (six.get (⟨5, by decide⟩ : Fin six.length)).1 a.2.st 3 ρ yv := by
  obtain ⟨c₁, k₁, q₁⟩ := head_flat (Fk X N P).first
  have h3 : Hist₂ (Fk X N P) D (3 + (3 + j)) a := by
    have e : 3 + (3 + j) = 6 + j := by omega
    rw [e]
    exact h
  have hu := u_row X N P c₁ k₁ D q₁ hZ hP hm hX hL hp hw hN _ (hC2_scope hZ hP hm hX) (3 + j) a h3 hfit
  have ho := omega_rows X N P c₁ k₁ D q₁ hZ hP hm hX hL hp hw hN _
    (Johnson.RunOne.KeyMsg.cond_omega_six_scope hZ hP hm hX) j a h hfit
  exact ⟨hu, ho.1, ho.2⟩

/-- In front of the test on G_u. -/
theorem s9_scope {Y : Type} {Zp : VerifierAndGoals.PublicFiles} {Z : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true)
    (hN : rangesNumbers m = .ok N) (D : WholeD) (a : (P₂ × St₂) × Y)
    (h : Hist₂ (Fk X N P) D 9 a.1) (hfit : a.1.1.1.key.fits (shapeAt X).fold.index = true) :
    (∃ ρ yv, SeedIs csKey (six.get (⟨3, by decide⟩ : Fin six.length)).1 a.1.2.st 0 ρ yv) ∧
      ∃ ρ yv, SeedIs csKey (six.get (⟨5, by decide⟩ : Fin six.length)).1 a.1.2.st 3 ρ yv :=
  let H := seeds₂_scope hZ hP hm hX hL hp hw hN D 3 a.1 h hfit
  ⟨H.1, H.2.2⟩

/-- In front of the test on G_omega. -/
theorem s10_scope {Y : Type} {Zp : VerifierAndGoals.PublicFiles} {Z : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true)
    (hN : rangesNumbers m = .ok N) (D : WholeD) (a : (P₂ × St₂) × Y)
    (h : Hist₂ (Fk X N P) D 10 a.1) (hfit : a.1.1.1.key.fits (shapeAt X).fold.index = true) :
    (∃ ρ yv, SeedIs csKey (six.get (⟨4, by decide⟩ : Fin six.length)).1 a.1.2.st 2 ρ yv) ∧
      ∃ ρ yv, SeedIs csKey (six.get (⟨5, by decide⟩ : Fin six.length)).1 a.1.2.st 3 ρ yv :=
  (seeds₂_scope hZ hP hm hX hL hp hw hN D 4 a.1 h hfit).2

end Johnson.RunOne.Law.KeySeeds2910

#print axioms Johnson.RunOne.Law.KeySeeds2910.hC2_scope
#print axioms Johnson.RunOne.Law.KeySeeds2910.seeds₂_scope
#print axioms Johnson.RunOne.Law.KeySeeds2910.s9_scope
#print axioms Johnson.RunOne.Law.KeySeeds2910.s10_scope
