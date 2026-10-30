-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/MgGCAtBase.lean: THE PREMISES ON THE FILLING's LETTERS OF
THE TIE AT THE FIRST SEGMENT's OPENING (`first_tiedR_at9`, TiesAt9.lean), PAID AT THE
COMPOSED FILLING OVER ITS CLOSED BASE `mgAll 𝔇 mgBase`, AT EVERY 𝔇: so it says AT WHICH TERMS the
tie's letters dk, nsOf, dg and First.FillSent's data stand. Statements with their proofs: each by
the composed meaning's own lemma on its public tests (PubAllAt.lean) or the table "no sentence is
meant" (First.saysNone, AllSaid.lean, laid in MgBase.lean). `mgGC_base`: `MgGC 𝔇.N (mgAll 𝔇 mgBase)
  𝔇.pubD.nsOf 𝔇.pubD.d3 dg`: dk := `K3Data.of X 𝔇.sent`; nsOf m := the built segment m's number of
  slots; dg: WHERE `k3SortAt 𝔇.pubD.d3.X 0 2 = some dg` (one test on the public parameters).
  `unheard_base`, `unheardP_base`: hUn, hUP. `sent_base`, `trees_base`, `sentP_base`,
  `treesP_base`: hSent, hTrees, hSP, hTP: at `sentDataAt 𝔇.shape 𝔇.N 𝔇.links (flatPlacesOf 𝔇.links
  true) 𝔇.built`.
It says which terms the fields are. Nothing on any sub-protocol. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.MoreAtOpening
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S Pub)
open VerifiableInference.Desc.First.FillSent (sentDataAt sentIsB treesAreB)
open VerifiableInference.Desc.First.Look (k3SortAt)
open VerifiableInference.Desc.Sound (MgData mgAll mgBase mgAll_pub mgAll_pubP_said)
open VerifiableInference.Desc.K13.Law (MgGC madeSix)

theorem madeSix_said : ∀ q ∈ madeSix, (First.saysNone q).isSome = true := by decide

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

/-- **`MgGC` at the composed filling over its closed base.** -/
theorem mgGC_base (dg : Bool) (hdg : k3SortAt 𝔇.pubD.d3.X 0 2 = some dg) :
    MgGC 𝔇.N (mgAll 𝔇 mgBase) 𝔇.pubD.nsOf 𝔇.pubD.d3 dg where
  noneSent := fun _ => rfl
  ledger := fun _ => rfl
  freeAbove := fun _ => rfl
  linkFresh := fun _ => rfl
  lookIn := fun x => First.pubAll_lookIn 𝔇.pubD _ 0 2 dg hdg x
  quiet := fun q hq x => mgAll_pubP_said 𝔇 q x (madeSix_said q hq)

theorem unheard_base (x : P × S) : (mgAll 𝔇 mgBase).pub .unheard x = First.unheardB x.2 := rfl

theorem unheardP_base (x : P × S) : (mgAll 𝔇 mgBase).pubP .unheard x :=
  mgAll_pubP_said 𝔇 _ x (by decide)

theorem sent_base (x : P × S) : (mgAll 𝔇 mgBase).pub sentItem0 x =
    sentIsB (sentDataAt 𝔇.shape 𝔇.N 𝔇.links (First.flatPlacesOf 𝔇.links true) 𝔇.built) 0 x.2 := by
  rw [mgAll_pub]
  exact First.pubAll_more_sentIs 𝔇.pubD _ 0 x

theorem trees_base (x : P × S) : (mgAll 𝔇 mgBase).pub treesItem0 x =
    treesAreB (sentDataAt 𝔇.shape 𝔇.N 𝔇.links (First.flatPlacesOf 𝔇.links true) 𝔇.built) 0 x.2 := by
  rw [mgAll_pub]
  exact First.pubAll_more_treesAre 𝔇.pubD _ 0 x

theorem sentP_base (x : P × S) : (mgAll 𝔇 mgBase).pubP sentItem0 x :=
  mgAll_pubP_said 𝔇 _ x (by decide)

theorem treesP_base (x : P × S) : (mgAll 𝔇 mgBase).pubP treesItem0 x :=
  mgAll_pubP_said 𝔇 _ x (by decide)

end

end HashBuild
