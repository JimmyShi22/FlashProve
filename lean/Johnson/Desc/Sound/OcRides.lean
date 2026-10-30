-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/OcRides.lean: "THE SLOT's OWN CONDITION IS CARRIED", which the rules for the shared chain ask of every block (Johnson/Desc/Sound/BordersSharedQ.lean: SharedJoin's last
premise) and the last chain's promise holds at every border (Johnson/Desc/Last/BordersLast.lean: onL), BROUGHT DOWN TO THREE THINGS. Definitions, three statements written as
def … : Prop, and their proofs. Over TieEnd.lean: general in the first chain's record.

While Oc was a letter the premise was a premise on a letter. With Oc filled (ocEnd, Johnson/Desc/Sound/TieEnd.lean: the first chain's WHOLE promise at its last border) it is a debt: that
promise still holds at the oracles BEHIND each block of the two later chains.
  OcReadsBelow lo Oc: Oc reads the oracles through the stored table and the trees below lo alone.
  OcRides: a condition that reads so rides past every piece whose stretch begins at a tree from lo on and which leaves what was handed to the chain as it is. By the facts on
    the strings (Johnson/Desc/Sound/StringsStay.lean: cellStays, colStays; SendLaw.lean: out_behind): CALLED. General in the chain's record (get: what was handed, in it).
  LettersReadBelow lo N₁ Mg₁ O: THE CONDITION ON THE FIRST TABLE's LETTERS: "decodes" reads the stored table alone; "shown" and "no collision" of a tenant read that tenant's tree alone; the
    tenants whose pins are open (O) sit in trees below lo.
  OcEndReadsBelow: under it ocEnd reads below lo.   OcEndRides: the two, joined.

WHO PAYS WHAT IS LEFT. "It leaves what was handed": the lift's make (other files hold it as a lemma on the seat, by report). "The stretch begins from lo on": the tiling, with the chain's
base. LettersReadBelow AT THE FILLED MEANING (Johnson/Desc/Sound/BordersFill.lean): three small lemmas on the library's notions (by a reading of the definitions; untyped) and one
test on the plan's numbers. AT A LETTER Mg₁ IT CANNOT BE PROVED: a letter may read any tree.

Limits. Rules under letters.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TieEnd
import Johnson.Desc.Sound.StringsStay
import Johnson.Desc.Sound.SendLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start onAt openSets sampledIn)

/-- A condition reads the oracles through the stored table and the trees below lo alone. -/
def OcReadsBelow {P₁ : Type} (lo : ℕ) (Oc : P₁ → Strs → Prop) : Prop :=
  ∀ (p : P₁) (y y' : Strs), (∀ x, y'.cell x = y.cell x) → (∀ j x, j < lo → y'.col j x = y.col j x) →
    Oc p y → Oc p y'

/-- **Such a condition rides past a piece that sends later trees and leaves what was handed.** -/
def OcRides : Prop :=
  ∀ (A P₁ Cl Wt : Type) (C : CK) (Fr : Frame) (get : A → P₁) (lo : ℕ) (Oc : P₁ → Strs → Prop)
    (x : Piece C Fr A Cl Wt),
    OcReadsBelow lo Oc → lo ≤ x.base →
    (∀ a τ b, x.ior.red.out a τ = some b → get b.1 = get a.1) →
    ∀ a τ b, Oc (get a.1) (strsOf Fr a.2) → x.ior.red.out a τ = some b → Oc (get b.1) (strsOf Fr b.2)

/-- The condition on the first table's letters. O: the items that are open at the first chain's last border. -/
def LettersReadBelow {P W : Type} (lo : ℕ) (N₁ : Numbers) (Mg₁ : Meaning P W) (O : List Item) : Prop :=
  (∀ a (y y' : Strs), (∀ x, y'.cell x = y.cell x) → Mg₁.decodes a y → Mg₁.decodes a y') ∧
    (∀ j t (y y' : Strs), (∀ x, y'.col j x = y.col j x) → Mg₁.shown j t y → Mg₁.shown j t y') ∧
    (∀ j t a (y y' : Strs), (∀ x, y'.col j x = y.col j x) → Mg₁.noColl j t a y → Mg₁.noColl j t a y') ∧
    ∀ x ∈ sampledIn N₁ O, x.1 < lo

/-- **The first chain's last promise reads below lo.** -/
def OcEndReadsBelow : Prop :=
  ∀ (A P W : Type) (get : A → P × First.S) (lo : ℕ) (N₁ : Numbers) (Mg₁ : Meaning P W) (links : List ModelPart)
    (ps : List Place),
    LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD []) →
    OcReadsBelow lo (ocEnd get N₁ Mg₁ links ps)

/-- **ocEnd rides.** -/
def OcEndRides : Prop :=
  ∀ (A A₁ P Cl W : Type) (C : CK) (Fr : Frame) (handed : A → A₁) (get : A₁ → P × First.S) (lo : ℕ)
    (N₁ : Numbers) (Mg₁ : Meaning P W) (links : List ModelPart) (ps : List Place) (x : Piece C Fr A Cl W),
    LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD []) →
    lo ≤ x.base →
    (∀ a τ b, x.ior.red.out a τ = some b → handed b.1 = handed a.1) →
    ∀ a τ b, ocEnd get N₁ Mg₁ links ps (handed a.1) (strsOf Fr a.2) → x.ior.red.out a τ = some b →
      ocEnd get N₁ Mg₁ links ps (handed b.1) (strsOf Fr b.2)

theorem ocRides : OcRides := by
  intro A P₁ Cl Wt C Fr get lo Oc x hR hlo hK a τ b hO hb
  rw [hK a τ b hb, out_behind x a b τ hb]
  exact hR (get a.1) (strsOf Fr a.2) (strsOf Fr (behind C Fr x.base x.ds a.2 τ))
    (fun z => cellStays C Fr x.base x.ds a.2 τ z)
    (fun j z hj => colStays C Fr x.base x.ds a.2 τ j z (Nat.lt_of_lt_of_le hj hlo)) hO

theorem ocEndReadsBelow : OcEndReadsBelow := by
  intro A P W get lo N₁ Mg₁ links ps hL p y y' hc hcol h
  obtain ⟨hd, hs, hn, hlt⟩ := hL
  refine ⟨hd (get p) y y' hc h.1, h.2.imp id fun h' => ⟨h'.1, h'.2.1, fun x hx => ?_, h'.2.2.2⟩⟩
  exact ⟨hs _ _ y y' (fun z => hcol _ z (hlt x hx)) (h'.2.2.1 x hx).1,
    hn _ _ (get p) y y' (fun z => hcol _ z (hlt x hx)) (h'.2.2.1 x hx).2⟩

theorem ocEndRides : OcEndRides := by
  intro A A₁ P Cl W C Fr handed get lo N₁ Mg₁ links ps x hL hlo hK
  exact ocRides A A₁ Cl W C Fr handed lo _ x
    (ocEndReadsBelow A₁ P W get lo N₁ Mg₁ links ps hL) hlo hK

-- A CONTROL: a condition that reads a later tree does not read below (so OcReadsBelow can fail)
example : ¬ OcReadsBelow (P₁ := Unit) 1 (fun _ y => y.col 1 0 = []) := by
  intro h
  have := h () ⟨fun _ => none, fun _ _ => []⟩ ⟨fun _ => none, fun j _ => if j = 1 then [0] else []⟩
    (fun _ => rfl) (fun j _ hj => by
      have : j ≠ 1 := by omega
      simp [this]) rfl
  simp at this

#check @OcRides
#check @OcEndReadsBelow
#check @OcEndRides

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.ocRides
#print axioms VerifiableInference.Desc.Sound.ocEndReadsBelow
#print axioms VerifiableInference.Desc.Sound.ocEndRides
