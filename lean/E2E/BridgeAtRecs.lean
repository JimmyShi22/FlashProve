-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/BridgeAtRecs.lean: A VALUE OF THE LETTERS OF THE SCHEME's HONEST SIDE
(`OnBytes.WholeKey.AtRecs`, Johnson/WholeKey/Premises.lean) whose three honest provers are
`proversOf hT hL Fm`; and, at that value, what the statement of index privacy asks of these letters
AS FAR AS IT READS THE SESSION's PROVER. General in the object, the two other provers and the
family.

  `RestOf hT hL`: the letters of `AtRecs` that do not read the session's prover: a structure of
    data.
  `coinEnum Fm`, **`coinEnum_ok`**: an enumeration of the family's coins that lists each once (the
    library's `Enum.ofNum_ok`): the clause `kB` of `CoinsFit`.
  `atRecsOf hT hL Fm R rvB pvB startB`: the value. The decisions of the session's prover's abort set
    are classical; its coins' enumeration is `coinEnum Fm`.
  **`runVals_of`**: `RunVals (atRecsOf …) ok` AS A STRUCTURE: the clauses on the key file's prover
    and the link's are premises in that structure's own words; the session's from a law on the plain
    parts at the family.
  `okB_of`: the clause `okB` of `CoinsFit`: the run values that the coins give are of the right
    form: from the same of rvB.

Limits. Data and three small facts: nothing on hiding, soundness or acceptance. Of `CoinsFit` two
clauses of nineteen are treated here (E2E/BridgeCoins.lean proves twelve, the first of these two
among them); the others read the wiring, the lengths, the enumerations of committer's randomness,
salts and runs' coins, the other two provers' coins, and startB. `RestOf` is filled by nobody here.


-/
import E2E.BridgePrivacy
import Iop.WireOK

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Bridge
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {L : HolographicProtocol I X}

/-- **The letters of `AtRecs` that do not read the session's prover.** -/
structure RestOf (lam : ℕ) (Bd : Type) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape)
    (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
    (hL : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed))) where
  dcT : ∀ w x ρ, Decidable (ρ ∈ hT.withheld w x)
  dcL : ∀ w x ρ, Decidable (ρ ∈ hL.withheld w x)
  b₀ : Bd
  capT : ℕ → ℕ
  capL : ℕ → ℕ
  capB : ℕ → ℕ
  M : ℕ
  nm : ℕ → ℕ
  RV : Type
  okV : RV → Prop
  rvT : hT.Coin → RV
  rvL : hL.Coin → RV
  startT : RV → ℕ → Bool → Bits → Bits
  startL : RV → ℕ → Bool → Bits → Bits
  pvT : Plains L.offline.shape → RV
  pvL : Plains L.link.shape → RV
  rtail : ℕ → Bits
  nR : ℕ
  nK : ℕ
  nJ : ℕ
  fill : Bits
  ri : Enum L.EncodingRandomness
  sl : Enum (ℕ → Bits)
  kT : Enum hT.Coin
  kL : Enum hL.Coin
  coT : Enum (Coins lam (typedOracleCarrier L Bd aT aL))
  coL : Enum (Coins lam (typedOracleCarrier L Bd aT aL))
  coB : Enum (Coins lam (typedOracleCarrier L Bd aT aL))

variable {lam : ℕ} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
  (hL : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)))
  (Fm : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed))

/-- An enumeration of the family's coins. -/
def coinEnum : Enum Fm.Coin := Enum.ofNum Fm.Coin (Fintype.equivFin Fm.Coin)

/-- **It lists each coin once.** -/
theorem coinEnum_ok : (coinEnum Fm).OK := Enum.ofNum_ok Fm.Coin (Fintype.equivFin Fm.Coin)

variable (R : RestOf lam Bd aT aL hT hL) (rvB : Fm.Coin → R.RV)
  (pvB : Plains L.onlineBatch.loc.shape → R.RV) (startB : R.RV → ℕ → Bool → Bits → Bits)

open Classical in
/-- **The letters of the scheme's honest side at `proversOf hT hL Fm`.** -/
def atRecsOf : AtRecs lam L Bd aT aL where
  Hs := proversOf hT hL Fm
  dc := ⟨R.dcT, R.dcL, fun _ _ _ => propDecidable _⟩
  b₀ := R.b₀
  capT := R.capT
  capL := R.capL
  capB := R.capB
  M := R.M
  nm := R.nm
  RV := R.RV
  okV := R.okV
  rvT := R.rvT
  rvL := R.rvL
  rvB := rvB
  startT := R.startT
  startL := R.startL
  startB := startB
  pvT := R.pvT
  pvL := R.pvL
  pvB := pvB
  rtail := R.rtail
  nR := R.nR
  nK := R.nK
  nJ := R.nJ
  fill := R.fill
  ri := R.ri
  sl := R.sl
  kT := R.kT
  kL := R.kL
  kB := coinEnum Fm
  coT := R.coT
  coL := R.coL
  coB := R.coB

/-- Its three provers are `proversOf hT hL Fm`: by definition. -/
theorem atRecsOf_Hs : (atRecsOf hT hL Fm R rvB pvB startB).Hs = proversOf hT hL Fm := rfl

/-- **`RunVals` as a structure.** -/
theorem runVals_of (ok : I → Prop)
    (hTv : ∀ i r e κ ρ, ok i → ρ ∉ hT.withheld (i, r, e) (L.recOf i r e) →
      R.pvT ((hT.strat (i, r, e) (L.recOf i r e) κ).run ρ).1.plains = R.rvT κ)
    (hLv : ∀ i u u' κ ρ, ok i →
      ρ ∉ hL.withheld (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2) →
      R.pvL ((hL.strat (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2) κ).run ρ).1.plains =
        R.rvL κ)
    (hBv : ∀ i r e n x κ ρ,
      pvB ((Fm.strat n (i, r, e) (x, L.recOf i r e) κ).run ρ).1.plains = rvB κ) :
    RunVals (atRecsOf hT hL Fm R rvB pvB startB) ok where
  T := hTv
  Lk := hLv
  B := fun i r e n x κ ρ _ _ => hBv i r e n x κ ρ

/-- The clause `kB` of `CoinsFit` at the value. -/
theorem kB_of : (atRecsOf hT hL Fm R rvB pvB startB).kB.OK := coinEnum_ok Fm

/-- The clause `okB` of `CoinsFit` at the value. -/
theorem okB_of (h : ∀ κ, R.okV (rvB κ)) :
    ∀ κ, (atRecsOf hT hL Fm R rvB pvB startB).okV ((atRecsOf hT hL Fm R rvB pvB startB).rvB κ) := h

end AtPublicFiles.Bridge

#print axioms AtPublicFiles.Bridge.coinEnum_ok
#print axioms AtPublicFiles.Bridge.atRecsOf_Hs
#print axioms AtPublicFiles.Bridge.runVals_of
#print axioms AtPublicFiles.Bridge.kB_of
#print axioms AtPublicFiles.Bridge.okB_of
