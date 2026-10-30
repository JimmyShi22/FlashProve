-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsBelowEq.lean: "THE FIRST CHAIN's LAST PROMISE AND THE SLOT's PINS READ THE ORACLES BELOW lo ALONE", GENERAL IN THE FIRST TABLE's MEANING Mg₁: FROM FOUR EQUATIONS ON ITS FIELDS. Three theorems.
WHY. Johnson/Desc/Sound/ReadsBelowAt.lean says these at Mg₁ := meaningSig …: one filling. The first table's meaning that counts is a composed term with many layers over that filling. A law that is typed at meaningSig … cannot be called there; a law that takes Mg₁ as a letter wants the two facts from what the composed term gives BY ITS MAKE: four equations (each an rfl line there): decodes = decodesOf decT · shown = shownJT cs G ms · noColl = noCollJT cs G smp ms · pin = pinJT cs G arr smp ms.
  lettersReadBelow_eq: the first three, and one test on the planner's numbers (sampledBelow), give LettersReadBelow lo N₁ Mg₁ O.
  ocEnd_readsBelow_eq: so OcReadsBelow lo (ocEnd get N₁ Mg₁ links ps).
  pin₁_col_eq: the fourth gives: at tiedMeaning get Mg₁ MgS the slot's pin of a tenant reads that tenant's tree alone.
So no clause on "reads below" need be added to the structure JointSays (its first field IS the fourth equation).

Limits. Rewritings. Nothing on what the fields say.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ReadsBelowAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start openSets sampledIn)

variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
  (Mg₁ : Meaning P (Wit Cells Tok MsgT))

/-- **The condition on the first table's letters, from three equations and one test.** -/
theorem lettersReadBelow_eq (hd : Mg₁.decodes = decodesOf decT) (hs : Mg₁.shown = shownJT cs G ms)
    (hn : Mg₁.noColl = noCollJT cs G smp ms) (lo : ℕ) (N₁ : Numbers) (O : List Item)
    (h : sampledBelow lo N₁ O = true) : LettersReadBelow lo N₁ Mg₁ O := by
  refine ⟨?_, ?_, ?_, fun x hx => of_decide_eq_true (List.all_eq_true.1 h x hx)⟩
  · rw [hd]
    exact fun a y y' hc hp => decodesOf_cell decT a y y' hc hp
  · rw [hs]
    exact fun j t y y' hc hp => shownJT_col cs G ms j t y y' hc hp
  · rw [hn]
    exact fun j t a y y' hc hp => noCollJT_col cs G smp ms j t a y y' hc hp

/-- So the first chain's last promise reads below lo. -/
theorem ocEnd_readsBelow_eq (hd : Mg₁.decodes = decodesOf decT) (hs : Mg₁.shown = shownJT cs G ms)
    (hn : Mg₁.noColl = noCollJT cs G smp ms) {A : Type} (get : A → P × First.S) (lo : ℕ)
    (N₁ : Numbers) (links : List ModelPart) (ps : List Place)
    (h : sampledBelow lo N₁ ((openSets links ps (start links))[ps.length]?.getD []) = true) :
    OcReadsBelow lo (ocEnd get N₁ Mg₁ links ps) :=
  ocEndReadsBelow A P _ get lo N₁ _ links ps
    (lettersReadBelow_eq cs G smp ms decT Mg₁ hd hs hn lo N₁ _ h)

/-- **The slot's pins read their tenant's tree alone.** -/
theorem pin₁_col_eq (hp : Mg₁.pin = pinJT cs G arr smp ms) {A S₂ : Type} (get : A → P × First.S)
    (MgS : MeaningS S₂ A (Wit Cells Tok MsgT)) (j t : ℕ) (q : A) (y y' : Strs)
    (w : Wit Cells Tok MsgT) (hc : ∀ z, y'.col j z = y.col j z)
    (h : (tiedMeaning get Mg₁ MgS).pin₁ j t q y w) : (tiedMeaning get Mg₁ MgS).pin₁ j t q y' w := by
  have h' : Mg₁.pin j t (get q) y w := h
  show Mg₁.pin j t (get q) y' w
  rw [hp] at h' ⊢
  exact pinJT_col cs G arr smp ms j t (get q) y y' w hc h'

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.lettersReadBelow_eq
#print axioms VerifiableInference.Desc.Sound.ocEnd_readsBelow_eq
#print axioms VerifiableInference.Desc.Sound.pin₁_col_eq
