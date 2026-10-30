-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineGoodAt.lean: the goal at a row of the offline prover's first chain, as one sentence, and how
it plugs into the field `good` of `Owed` (Honest/Owed.lean) at the muted rows.

  `GoodAt`            a row's fields at the letters that the muted rows ask
  `Good.narrow`       `Good` at a stronger On and a stronger bud: both are premises of `exact` and
                      `fresh` alone
  `muted_of_goodAt`   from `GoodAt` at a row's side to `goodAt` at the muted row with the field beside

`A` and `B` are false here, so `plays` and `acc` are vacuous: the form that the muted rows ask, and it
says nothing on a run. Nothing on any property.
-/
import E2E.OfflineSides
import E2E.KeyProtocolOverDescription
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open AtPublicFiles.KeyFile (KeyInst)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open AtPublicFiles.AtFiles (keyFileDescription)

section General
variable {S Cl V W Y Pb : Type}

/-- **`Good` at a stronger On and a stronger bud.** -/
theorem Good.narrow {pre : List (Nat × Nat × List Fmt.DeclaredRound)} {φ : Face V W Pb}
    {σ : Side S Cl V W Y Pb} {Bk : ProverCoinCounts} {ord : List Place} {chain firstTree : Nat}
    {A B : Coins Bk → S → Mid W Y → Env → Prop}
    {On On' : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop}
    {bud bud' : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (hO : ∀ u ca m front, On' u ca m front → On u ca m front)
    (hB : ∀ n ds asks, bud' n ds asks → bud n ds asks)
    (g : Good pre φ σ Bk ord chain firstTree A B On bud) :
    Good pre φ σ Bk ord chain firstTree A B On' bud' :=
  { fits := g.fits
    plays := g.plays
    acc := g.acc
    exact := fun u hu ca m front ds asks h1 h2 h3 h4 h5 =>
      g.exact u hu ca m front ds asks (hO _ _ _ _ h1) h2 h3 h4 (hB _ _ _ h5)
    fresh := fun u hu p sp ca m ds asks h1 h2 =>
      g.fresh u hu p sp ca m ds asks h1 (hB _ _ _ h2) }

end General

section Value
variable {W₀ Rc Pb : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)

/-- A row's fields, as one sentence. -/
abbrev GoodAt (K₀ : KeyPub) (σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl
      (Local W₀ Rc KeyInst Unit) (Local W₀ Rc KeyInst Unit) Unit Pb)
    (On : (u : Member (Local W₀ Rc KeyInst Unit) (Local W₀ Rc KeyInst Unit) Unit Pb) →
      CsAll u.part.carries → Mid (Local W₀ Rc KeyInst Unit) Unit → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Prop :=
  ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc KeyInst Unit) (Local W₀ Rc KeyInst Unit) Pb) (chain firstTree : Nat),
    Good pre φ σ (keyBook K₀) (orderOf (keyFileDescription Xs N Pl)) chain firstTree (fun _ _ _ _ => False)
      (fun _ _ _ _ => False) On bud

/-- **From `GoodAt` at a row's side to what `Owed.good` asks of the muted row**, in the first chain. -/
theorem muted_of_goodAt {K₀ : KeyPub}
    (L : Lettered (keyBook K₀) (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc KeyInst Unit)
      (Local W₀ Rc KeyInst Unit) Unit KeyInst)
    (fs : List (Fall (keyFileDescription Xs N Pl).S₁))
    (h : ∀ σ, L.side (keyFileDescription Xs N Pl).first.blocksInOrder fs = some σ → GoodAt Xs N Pl K₀ σ L.On L.bud) :
    (L.mute.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
      (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
      (orderOf (keyFileDescription Xs N Pl)) 0 0 fs :=
  goodAt_mute fun σ hσ => ⟨_, _, h σ hσ _ _ _ _⟩

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.Good.narrow
#print axioms AtPublicFiles.OfflineRows.muted_of_goodAt
