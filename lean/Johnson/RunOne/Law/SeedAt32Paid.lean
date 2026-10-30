-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/SeedAt32Paid.lean: THEOREMS. THE PREMISE hΩ OF
Johnson/RunOne/Law/SeedAt32.lean PAID BY CALLS: at the shared chain's end Omega's message holds the sending kind's row at an OOD seed
(VerifiableInference.Desc.K1.SeedIs); so Omega's copy does, from border 1 of the last chain on; so at_32 stands without hΩ.
A second file, so that SeedAt32.lean keeps its lighter imports.

Main names:
  oOmega_late        the tenth clause of the shared chain's book-keeping (LKFU.Shape23.shape₂): from border 6 on Omega's number is 2.
  oOmega_end         the same in scope, at a state that the shared chain reaches at border 12.
  omega_end          hΩ at a state that the shared chain reaches at border 12.
  seedIs_omega_3'    Omega's copy, at the written shape and the number wAt + 2, from border 1 of the last chain on.
  at_32'             border 2 of the last chain in the letters of the proximity test's files: all three OOD seeds.
Called: LPFD.omega_rows (Johnson/Top/Fire/Code/KeyOn2L1Hi.lean) and LPFD.aSide₂_at_all;
cond_omega_six_scope (Johnson/RunOne/KeyCondThree.lean). seeds₂_scope (Johnson/RunOne/Law/KeySeeds2910.lean) makes
the same two calls at every border from 6 on, at the numeral 2; «Omega's number is 2» is typed here alone.
IS IT EMPTY? They speak at every state that the chains reach. hfit («the instance's key fits the fold's index») IS A PREMISE ON THE PUBLIC
INSTANCE THAT omega_rows AND aSide₂_at_all BEAR: who pays it where these are called is not said here. hw₃: a clause of the border's invariant.
The scope's premises are shown together of nothing here. That an honest key file reaches any of these borders is not shown here.
What is not claimed. Which OOD seed. One size. Nothing on soundness.

-/
import Johnson.RunOne.Law.SeedAt32
import Johnson.Top.Fire.Code.KeyOn2L1Hi
import Johnson.RunOne.KeyCondThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.SeedAt32
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Xi)
open VerifiableInference.Desc.K1 (SeedIs)
open VerifiableInference.Desc.Key.Fill (six)
open Johnson.Top.H (csKey)
open Johnson.RunOne.KeyRows1 (plan₁ wAt)
open Johnson.RunOne.KeyRows23 (Fk oneAt St₂ St₃ nOwn shapeAt)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open LPFD (Hist₂ Hist₃)

/-- **From border 6 of the shared chain on Omega's number is 2**: the tenth clause of the book-keeping. -/
theorem oOmega_late (S : LinShape) (a k : ℕ) (d : St₂) (hk : 6 ≤ k) (h : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a k d) = true) :
    d.loc.oOmega = 2 := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, c10, -⟩ := h
  have hk' : ¬ k ≤ 5 := by omega
  simp [hk'] at c10
  exact c10.1

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
variable {Zp : VerifierAndGoals.PublicFiles} {Z : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}

/-- **At the shared chain's end Omega's number is 2**, in scope. -/
theorem oOmega_end (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
    (D : WholeD) (a₂ : (Xi × FirstState) × St₂) (h : Hist₂ (Fk X N P) D 12 a₂)
    (hfit : a₂.1.1.key.fits (shapeAt X).fold.index = true) : a₂.2.loc.oOmega = 2 := by
  obtain ⟨c₁, k₁, q₁⟩ : ∃ c₁ k₁, (Fk X N P).first.blocksInOrder = c₁ :: k₁ := ⟨_, _, rfl⟩
  exact oOmega_late _ _ 12 _ (by decide)
    (LPFD.aSide₂_at_all X N P c₁ k₁ D q₁ hZ hP hm hX hL hp hw hN 12 a₂ (by decide) h hfit).shape

/-- **hΩ, at the shared chain's end.** -/
theorem omega_end (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
    (D : WholeD) (a₂ : (Xi × FirstState) × St₂) (h : Hist₂ (Fk X N P) D 12 a₂)
    (hfit : a₂.1.1.key.fits (shapeAt X).fold.index = true) :
    ∃ ρ y, SeedIs csKey (six.get i4).1 a₂.2.st a₂.2.loc.oOmega ρ y := by
  obtain ⟨c₁, k₁, q₁⟩ : ∃ c₁ k₁, (Fk X N P).first.blocksInOrder = c₁ :: k₁ := ⟨_, _, rfl⟩
  have e : a₂.2.loc.oOmega = 2 := oOmega_end hZ hP hm hX hL hp hw hN D a₂ h hfit
  have g4 : (six.get i4).1 = Johnson.Top.H.shO := rfl
  rw [e, g4]
  exact (LPFD.omega_rows X N P c₁ k₁ D q₁ hZ hP hm hX hL hp hw hN _ (Johnson.RunOne.KeyMsg.cond_omega_six_scope hZ hP hm hX) 6 a₂ h hfit).1

/-- **Omega's copy holds the sending kind's row at an OOD seed**, from border 1 of the last chain on. -/
theorem seedIs_omega_3' (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
    (D : WholeD) (j : ℕ) (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D (1 + j) a)
    (hfit : a.1.1.key.fits (shapeAt X).fold.index = true) :
    ∃ ρ y, SeedIs csKey (six.get i4).1 a.2.st (wAt (oneAt X) + 2) ρ y :=
  seedIs_omega_3 hZ hP hm hX hp hN D j a h
    (omega_end hZ hP hm hX hL hp hw hN D ((a.1.1, a.1.2.1), a.1.2.2)
      ((LPFD.lengths_in_scope hZ hP hm hX hp hw).2.1 ▸ LPFD.hist₃_handed (Fk X N P) D _ a h) hfit)

/-- **Border 2 of the last chain, in the letters of the proximity test's files: all three OOD seeds.** hw₃: a clause of the border's invariant
(shapeB₃). hfit: see the head. -/
theorem at_32' (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
    (D : WholeD) (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D 2 a)
    (hw₃ : (plan₁ (oneAt X)).orc 2 = some a.2.loc.w) (hfit : a.1.1.key.fits (shapeAt X).fold.index = true) :
    a.2.st.codes = csKey ∧
      (∀ oI, (plan₁ (oneAt X)).orc 0 = some oI → (∃ ρ yv, SeedIs csKey (six.get i0).1 a.2.st oI ρ yv) ∧ oI ≠ nOwn a.2) ∧
      (∃ ρ yv, Johnson.RunOne.KeyMsg.SeedOk csKey (six.get i2).1 a.2.st a.2.loc.w ρ yv) ∧
      (∃ ρ yv, SeedIs csKey (six.get i4).1 a.2.st (nOwn a.2) ρ yv) ∧
      (plan₁ (oneAt X)).num a.2.loc.w = some 2 ∧ Means.OpenKinds a.2.st :=
  at_32 hZ hP hm hX hp hN D a h hw₃
    (omega_end hZ hP hm hX hL hp hw hN D ((a.1.1, a.1.2.1), a.1.2.2)
      ((LPFD.lengths_in_scope hZ hP hm hX hp hw).2.1 ▸ LPFD.hist₃_handed (Fk X N P) D _ a h) hfit)

end Johnson.RunOne.Law.SeedAt32

#print axioms Johnson.RunOne.Law.SeedAt32.oOmega_late
#print axioms Johnson.RunOne.Law.SeedAt32.oOmega_end
#print axioms Johnson.RunOne.Law.SeedAt32.omega_end
#print axioms Johnson.RunOne.Law.SeedAt32.seedIs_omega_3'
#print axioms Johnson.RunOne.Law.SeedAt32.at_32'
