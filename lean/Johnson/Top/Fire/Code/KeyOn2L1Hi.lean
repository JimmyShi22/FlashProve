-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyOn2L1Hi.lean: THE PREMISE L1hi OF on₂_of_tests
  (Johnson/RunOne/KeyOn2Tests.lean), OFF THE SHARED CHAIN's HISTORY, IN SCOPE: at the chain's own
  pins 3 | 4 | 5 the sending kind's own row of the OOD sample (SeedIs) lies in the own statement of
  every state that the shared chain reaches at a border at which the pin is open.
OTHER FILES HAVE THE LIKE AT PIECES' YESES, AT BORDERS 3 | 6 (l1hi_at3_scope | l1hi_at6_scope,
  Johnson/RunOne/KeyOn2Scope.lean): HERE: OFF THE HISTORY Hist₂, AT EVERY BORDER: BY CALLS:
  Reached.last at borders 3 | 6 · seedIs_send2 | seedIs_send5 (KeySeedIs2.lean:
  behind the held sendings' own yes) and THE CLOSED FACTS (len2 · smp2 · tieS2 · len5 · smp50 ·
  smp51 · tieS50 · tieS51 · withU_key · p14At_key) · shared_2 | shared_5 · sends_at_blocks
  · roundsFit_noDigest · hist₂_rel at SmpStay (the sampled messages stay along the shared
  chain) · the count of messages by aSide₂_at_all.
  count₂            the book-keeping's second clause: how many messages stand at borders 3 | 6
  u_row             PROVED: Hist₂ … (3 + j) a ⟹ ∃ ρ y, SeedIs csKey shU a.2.st 0 ρ y
  omega_rows        PROVED: Hist₂ … (6 + j) a ⟹ the like at shO, message 2, and at shSp, message 3
  pins_open         KERNEL FACT: pin 3 is open only from border 3 on; pins 4 | 5 only from 6 on (k ≤
    12)
  l1hi_of_hist    PROVED: on₂_of_tests' L1hi to the letter, k ≤ 12
TWO PUBLIC PREMISES STAY: hC2 | hC5: the sending law's condition on the plan (condPort) at K14's
  two places: binders_key PAYS THEM AT THE WRITTEN VALUES
  (Johnson/Goal/Numbers/SeatBinders.lean): NO SECOND PAYER IS TYPED HERE.
OBJECT: on₂_of_tests' L1hi · USER: of l1hi_of_hist: none in this library; of u_row | omega_rows:
  Johnson/RunOne/Law/KeySeeds2910.lean, Johnson/RunOne/Law/SeedAt32Paid.lean · LETTERS: rad2 rad5.
  EMPTY WHERE NOTHING IS REACHED. IT FIXES THE RELEASE's ONE CONFIGURATION (keyFull). Nothing on
  soundness.
-/
import Johnson.Top.Fire.Code.KeyASide2All
import Johnson.RunOne.KeyOn2Scope
import Johnson.RunOne.KeySeedIs2
import Johnson.RunOne.KeyWalkAny

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

/-- The book-keeping's second clause. -/
theorem count₂ (S : OnBytes.Params.LinShape) (a k : ℕ) (d : St₂) (h : LKFU.Shape23.ok
    (LKFU.Shape23.shape₂ S a k d) = true) :
    (k = 3 → d.st.oracles.size = 2) ∧ (k = 6 → d.st.oracles.size = 4) := by
  simp only [LKFU.Shape23.ok, LKFU.Shape23.shape₂, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at h
  obtain ⟨-, c2, -⟩ := h
  constructor
  · rintro rfl
    simpa using c2
  · rintro rfl
    simpa using c2

/-- Which own pins are open where. -/
theorem pins_open : ∀ k, k < 13 → (3 ∈ pinned (open₂ k) → 3 ≤ k) ∧ (4 ∈ pinned (open₂ k) → 6 ≤ k) ∧
    (5 ∈ pinned (open₂ k) → 6 ≤ k) := by
  decide +kernel

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made}
variable (D : WholeD)

/-- **o_u's row, at every border from 3 on.** -/
theorem u_row (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
    (rad2 : ℕ → ℕ) (hC2 : condPort (parK1 (p14At X P) 2 "o_u and the first mask" sentUKey) rad2 =
        true)
    (j : ℕ) (a : P₂ × St₂) (h : Hist₂ (Fk X N P) D (3 + j) a) (hfit : a.1.1.key.fits (shapeAt
        X).fold.index = true) :
    ∃ ρ y, SeedIs Johnson.Top.H.csKey Johnson.Top.H.shU a.2.st 0 ρ y := by
  obtain ⟨a3, h3, e3, hs⟩ := hist₂_rel groundKeeps_smpStay begin_smp D 3 j a h
  have T := aSide₂_at_all X N P c₁ k₁ D q₁ hZ hP hm hX hL hp hw hN 3 a3 (by decide) h3
      (by rw [e3]; exact hfit)
  have n2 : (show St₂ from a3.2).st.oracles.size = 2 := (count₂ _ _ 3 _ T.shape).1 rfl
  obtain ⟨a', b, rs, cols, -, hb, hd, hf⟩ := Reached.last (k := 2) h3
  rw [List.getElem?_map] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  obtain rfl : b₀ = seat b2 := Option.some.inj (hb₀.symm.trans (shared_2 X N P b1 b2 b3 b4 b5 b6 b7
      b8 h8))
  obtain ⟨sentU, hU, e2, -⟩ := sends_at_blocks _ b1 b2 b3 b4 b5 b6 b7 b8 h8
  have hkey : X.chains.made.sized.key = keyFull := Johnson.RunOne.KeyRows23.key_of_scope hZ hP hm hX
  have hf' : roundsFit b2.rounds rs = true := hf
  rw [e2] at hf'
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 (roundsFit_length _ _ hf')
  rw [p14At_key hkey P] at h8 hC2 hU hf'
  obtain rfl : sentU = sentUKey := Option.some.inj (hU.symm.trans withU_key)
  have hlen : (shapesOf (parK1 (p14Key (beforeSharedPoint P)) 2 "o_u and the first mask"
      sentUKey)).length = 2 := len2
  have H := seedIs_send2 (Pr := P₂) (p14Key (beforeSharedPoint P)) b1 b2 b3 b4 b5 b6 b7 b8 h8 (seat
      b2 : Block St₂ Key.Claim) rfl sentUKey withU_key rad2 hC2
    a' a3 (noDigest r₁) (noDigest r₂) _ hd ((roundsFit_noDigest _ [r₁, r₂]).trans hf') ⟨0,
        by rw [hlen]; decide⟩ smp2
  have H2 : ∃ ρ y, SeedIs Johnson.Top.H.csKey (shapeAt (parK1 (p14Key (beforeSharedPoint P)) 2
      "o_u and the first mask" sentUKey) ⟨0, by rw [hlen]; decide⟩)
      (show St₂ from a3.2).st ((show St₂ from a3.2).st.oracles.size - (shapesOf (parK1 (p14Key
          (beforeSharedPoint P)) 2 "o_u and the first mask" sentUKey)).length + 0) ρ y := H
  rw [show shapeAt (parK1 (p14Key (beforeSharedPoint P)) 2 "o_u and the first mask" sentUKey) ⟨0,
      by rw [hlen]; decide⟩ = Johnson.Top.H.shU from tieS2, n2, hlen] at H2
  obtain ⟨ρ, y, hy⟩ := H2
  exact ⟨ρ, y, hy.stays hs⟩

/-- **Omega's and the split's rows, at every border from 6 on.** -/
theorem omega_rows (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
    (rad5 : ℕ → ℕ) (hC5 : condPort (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X
        P).S)) rad5 = true)
    (j : ℕ) (a : P₂ × St₂) (h : Hist₂ (Fk X N P) D (6 + j) a) (hfit : a.1.1.key.fits (shapeAt
        X).fold.index = true) :
    (∃ ρ y, SeedIs Johnson.Top.H.csKey Johnson.Top.H.shO a.2.st 2 ρ y) ∧ ∃ ρ y, SeedIs
        Johnson.Top.H.csKey Johnson.Top.H.shSp a.2.st 3 ρ y := by
  obtain ⟨a6, h6, e6, hs⟩ := hist₂_rel groundKeeps_smpStay begin_smp D 6 j a h
  have T := aSide₂_at_all X N P c₁ k₁ D q₁ hZ hP hm hX hL hp hw hN 6 a6 (by decide) h6
      (by rw [e6]; exact hfit)
  have n4 : (show St₂ from a6.2).st.oracles.size = 4 := (count₂ _ _ 6 _ T.shape).2 rfl
  obtain ⟨a', b, rs, cols, -, hb, hd, hf⟩ := Reached.last (k := 5) h6
  rw [List.getElem?_map] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  obtain rfl : b₀ = seat b5 := Option.some.inj (hb₀.symm.trans (shared_5 X N P b1 b2 b3 b4 b5 b6 b7
      b8 h8))
  obtain ⟨-, -, -, e5⟩ := sends_at_blocks _ b1 b2 b3 b4 b5 b6 b7 b8 h8
  have hkey : X.chains.made.sized.key = keyFull := Johnson.RunOne.KeyRows23.key_of_scope hZ hP hm hX
  have hf' : roundsFit b5.rounds rs = true := hf
  rw [e5] at hf'
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 (roundsFit_length _ _ hf')
  rw [p14At_key hkey P] at h8 hC5 hf'
  have hlen : (shapesOf (parK1 (p14Key (beforeSharedPoint P)) 5 "o_omega and o_sp" (withOmega
      (p14Key (beforeSharedPoint P)).S))).length = 2 := len5
  have hfit5 := (roundsFit_noDigest _ [r₁, r₂]).trans hf'
  have H0 := seedIs_send5 (Pr := P₂) (p14Key (beforeSharedPoint P)) b1 b2 b3 b4 b5 b6 b7 b8 h8 (seat
      b5 : Block St₂ Key.Claim) rfl rad5 hC5
    a' a6 (noDigest r₁) (noDigest r₂) _ hd hfit5 ⟨0, by rw [hlen]; decide⟩ smp50
  have H1 := seedIs_send5 (Pr := P₂) (p14Key (beforeSharedPoint P)) b1 b2 b3 b4 b5 b6 b7 b8 h8 (seat
      b5 : Block St₂ Key.Claim) rfl rad5 hC5
    a' a6 (noDigest r₁) (noDigest r₂) _ hd hfit5 ⟨1, by rw [hlen]; decide⟩ smp51
  have G0 : ∃ ρ y, SeedIs Johnson.Top.H.csKey (shapeAt (parK1 (p14Key (beforeSharedPoint P)) 5
      "o_omega and o_sp" (withOmega (p14Key (beforeSharedPoint P)).S)) ⟨0, by rw [hlen]; decide⟩)
      (show St₂ from a6.2).st ((show St₂ from a6.2).st.oracles.size - (shapesOf (parK1 (p14Key
          (beforeSharedPoint P)) 5 "o_omega and o_sp" (withOmega (p14Key (beforeSharedPoint
          P)).S))).length + 0) ρ y := H0
  have G1 : ∃ ρ y, SeedIs Johnson.Top.H.csKey (shapeAt (parK1 (p14Key (beforeSharedPoint P)) 5
      "o_omega and o_sp" (withOmega (p14Key (beforeSharedPoint P)).S)) ⟨1, by rw [hlen]; decide⟩)
      (show St₂ from a6.2).st ((show St₂ from a6.2).st.oracles.size - (shapesOf (parK1 (p14Key
          (beforeSharedPoint P)) 5 "o_omega and o_sp" (withOmega (p14Key (beforeSharedPoint
          P)).S))).length + 1) ρ y := H1
  rw [show shapeAt (parK1 (p14Key (beforeSharedPoint P)) 5 "o_omega and o_sp" (withOmega (p14Key
      (beforeSharedPoint P)).S)) ⟨0, by rw [hlen]; decide⟩ = Johnson.Top.H.shO from tieS50, n4,
      hlen] at G0
  rw [show shapeAt (parK1 (p14Key (beforeSharedPoint P)) 5 "o_omega and o_sp" (withOmega (p14Key
      (beforeSharedPoint P)).S)) ⟨1, by rw [hlen]; decide⟩ = Johnson.Top.H.shSp from tieS51, n4,
      hlen] at G1
  obtain ⟨ρ, y, hy⟩ := G0
  obtain ⟨ρ', y', hy'⟩ := G1
  exact ⟨⟨ρ, y, hy.stays hs⟩, ρ', y', hy'.stays hs⟩

/-- **L1hi off the shared chain's history.** -/
theorem l1hi_of_hist (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
    (rad2 rad5 : ℕ → ℕ) (hC2 : condPort (parK1 (p14At X P) 2 "o_u and the first mask" sentUKey) rad2
        = true)
    (hC5 : condPort (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S)) rad5 = true)
    (k : ℕ) (hk : k ≤ 12) (a : P₂ × St₂) (h : Hist₂ (Fk X N P) D k a) (hfit : a.1.1.key.fits
        (shapeAt X).fold.index = true) :
    ∀ i : Fin six.length, numSix i ∈ pinned (open₂ k) → ¬ numSix i < 3 →
      ∃ o ρ y, orc₂ (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1 a.2.st o ρ y :=
          by
  obtain ⟨p3, p4, p5⟩ := pins_open k (by omega)
  rintro ⟨i, hlt⟩ hi hn
  have hi' : i ∈ pinned (open₂ k) := hi
  have hn' : ¬ i < 3 := hn
  have h6 : i < 6 := hlt
  obtain rfl | rfl | rfl : i = 3 ∨ i = 4 ∨ i = 5 := by omega
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (p3 hi')
    obtain ⟨ρ, y, hy⟩ := u_row X N P c₁ k₁ D q₁ hZ hP hm hX hL hp hw hN rad2 hC2 j a h hfit
    exact ⟨0, ρ, y, rfl, hy⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (p4 hi')
    obtain ⟨ρ, y, hy⟩ := (omega_rows X N P c₁ k₁ D q₁ hZ hP hm hX hL hp hw hN rad5 hC5 j a h hfit).1
    exact ⟨2, ρ, y, rfl, hy⟩
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (p5 hi')
    obtain ⟨ρ, y, hy⟩ := (omega_rows X N P c₁ k₁ D q₁ hZ hP hm hX hL hp hw hN rad5 hC5 j a h hfit).2
    exact ⟨3, ρ, y, rfl, hy⟩

end

end LPFD

#print axioms LPFD.count₂
#print axioms LPFD.pins_open
#print axioms LPFD.u_row
#print axioms LPFD.omega_rows
#print axioms LPFD.l1hi_of_hist
