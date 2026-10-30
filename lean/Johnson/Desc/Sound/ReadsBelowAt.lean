-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsBelowAt.lean: AT THE FIRST CHAIN's TABLE's FILLED MEANING (meaningSig, Johnson/Desc/Sound/BordersFill.lean): THE CONDITION UNDER WHICH THE FIRST CHAIN's WHOLE LAST PROMISE RIDES ALONG THE TWO LATER CHAINS (LettersReadBelow,
Johnson/Desc/Sound/OcRides.lean) COMES DOWN TO ONE TEST ON THE PLAN's NUMBERS. Small lemmas.

  lettersReadBelow_sig: at meaningSig: "decodes" reads the stored table alone, "shown" and "no collision" of a tenant that tenant's tree alone (ReadsTreeAt.lean): BY MAKE. LEFT: every tenant whose pin is open at the first chain's last border sits in a
    tree below lo: sampledBelow: a test with code.
  ocEnd_readsBelow_sig: so ocEnd at meaningSig reads below lo.
  pin₁_col_sig: the slot's pins at tiedMeaning over meaningSig read their tenant's tree alone: the premise (P) of PointMake.lean and RidesMake.lean.

Limits. The codes, the members, arr, the samples' reader, the decoder are letters. sampledBelow has run at no plan.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ReadsTreeAt
import Johnson.Desc.Sound.OcRides
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start openSets sampledIn)

/-- A TEST ON THE PLAN's NUMBERS: every tenant whose pin is open (O) sits in a tree below lo. -/
def sampledBelow (lo : ℕ) (N₁ : Numbers) (O : List Item) : Bool :=
  (sampledIn N₁ O).all fun x => decide (x.1 < lo)

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
  (Mg : Meaning P (Wit Cells Tok MsgT))

/-- **The condition on the first table's letters, at the filled meaning, from one test.** -/
theorem lettersReadBelow_sig (lo : ℕ) (N₁ : Numbers) (O : List Item)
    (h : sampledBelow lo N₁ O = true) :
    LettersReadBelow lo N₁ (meaningSig cs G arr smp ms decT Mg) O :=
  ⟨fun a y y' hc hp => decodesOf_cell decT a y y' hc hp,
    fun j t y y' hc hp => shownJT_col cs G ms j t y y' hc hp,
    fun j t a y y' hc hp => noCollJT_col cs G smp ms j t a y y' hc hp,
    fun x hx => of_decide_eq_true (List.all_eq_true.1 h x hx)⟩

/-- So the first chain's last promise, at the filled meaning, reads below lo. -/
theorem ocEnd_readsBelow_sig {A : Type} (get : A → P × First.S) (lo : ℕ) (N₁ : Numbers)
    (links : List ModelPart) (ps : List Place)
    (h : sampledBelow lo N₁ ((openSets links ps (start links))[ps.length]?.getD []) = true) :
    OcReadsBelow lo (ocEnd get N₁ (meaningSig cs G arr smp ms decT Mg) links ps) :=
  ocEndReadsBelow A P _ get lo N₁ _ links ps (lettersReadBelow_sig cs G arr smp ms decT Mg lo N₁ _ h)

/-- The slot's pins, at the tied meaning over the filled one, read their tenant's tree alone. -/
theorem pin₁_col_sig {A S₂ : Type} (get : A → P × First.S) (MgS : MeaningS S₂ A (Wit Cells Tok MsgT))
    (j t : ℕ) (q : A) (y y' : Strs) (w : Wit Cells Tok MsgT) (hc : ∀ z, y'.col j z = y.col j z)
    (hp : (tiedMeaning get (meaningSig cs G arr smp ms decT Mg) MgS).pin₁ j t q y w) :
    (tiedMeaning get (meaningSig cs G arr smp ms decT Mg) MgS).pin₁ j t q y' w :=
  pinJT_col cs G arr smp ms j t (get q) y y' w hc hp

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.lettersReadBelow_sig
#print axioms VerifiableInference.Desc.Sound.ocEnd_readsBelow_sig
#print axioms VerifiableInference.Desc.Sound.pin₁_col_sig
