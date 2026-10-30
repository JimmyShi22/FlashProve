-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameStringsRide.lean: THE STRINGS' HALF AT ONE STATE OF THE VERIFIER, AT THE
COMPOSED MEANING (`mgAll 𝔇 Mg`, Johnson/Desc/Sound/MgAll.lean): `StringsRide`
(FrameRides.lean): its four fields, all under "the committed table's cells, and every column of a
tree below base, are as they were" (`Stays`).

What is said.
  `lowItem_of_lowAt`: an item of the list O names in its pins only trees below base, where every
    tenant whose pin is open in O sits in such a tree (`LowAt`, FramePromiseRides.lean).
  `CarryStays 𝔇 base`: the premise on the parameter 𝔇.cr1: at one state, the carried word's sentence
    goes back over `Stays`.
  `OpenFit X O' Op`: three facts on every item that is open behind: it stands in the list O' (the
    computed list in front or the one behind: whichever its payer has); it has no part of a segment
    of its own; it is no part of a segment's relation that `ownAt X` names.
  `stringsRide_mgAll`: **`StringsRide N (mgAll 𝔇 Mg) base O Op` from `LowAt N O base`,
    `LowAt N O' base`, `OpenFit X O' Op` and `CarryStays`.** "decodes": outright. "shown",
    "noColl": under `LowAt N O base` alone. "items": `fieldsBack_same` (FrameFieldsBack.lean)
    through `items_of_fields` (FrameItemsBack.lean).
  `stringsRide_three`: the first three fields need `LowAt` alone: said apart, as a conjunction.

Limits. `LowAt` and `OpenFit` are facts on the plan's numbers and the table: owed. `CarryStays` is a
premise on a parameter that is a letter: owed by whoever fills 𝔇.cr1; THAT ANY REAL
FILLING HAS IT IS NOT SHOWN HERE. No soundness statement.

-/
import Johnson.Top.H0.Walk.FramePromiseRides
import Johnson.Top.H0.Walk.FrameRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item Meaning Numbers sampledIn)

/-- An item of O names in its pins only trees below base. -/
theorem lowItem_of_lowAt {N : Numbers} {O : List Item} {base : Nat} (hl : LowAt N O base)
    {i : Item} (hi : i ∈ O) : lowItem N (fun j => j < base) i := by
  have key : ∀ x, (x ∈ match i with
      | .pin m t => N.sent m t
      | .pinKept m => N.keptOf m
      | .pinI => [N.index]
      | .pinV => [N.w]
      | _ => []) → x.1 < base := fun x hx => hl x (List.mem_flatMap.2 ⟨i, hi, hx⟩)
  cases i with
  | pin m t => exact fun x hx => key x hx
  | pinKept m => exact fun x hx => key x hx
  | pinI => exact key _ List.mem_cons_self
  | pinV => exact key _ List.mem_cons_self
  | _ => trivial

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (VerifiableInference.Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **The premise on 𝔇.cr1**: at one state it goes back over `Stays`. -/
def CarryStays (base : Nat) : Prop :=
  ∀ m a y y' w, Stays base y y' → 𝔇.cr1 m a y' w → 𝔇.cr1 m a y w

/-- Three facts on every item that is open behind. -/
def OpenFit (X : OnBytes.Model.Verify.Public) (O : List Item) (Op : Item → Prop) : Prop :=
  ∀ i, Op i → i ∈ O ∧ i.part = none ∧ notOwn (ownAt X) i

/-- The first three fields: under `LowAt` alone. -/
theorem stringsRide_three {N : Numbers} {O : List Item} {base : Nat} (hl : LowAt N O base) :
    (∀ a y y', Stays base y y' → (mgAll 𝔇 Mg).decodes a y → (mgAll 𝔇 Mg).decodes a y') ∧
      (∀ x y y', Stays base y y' → x ∈ sampledIn N O → (mgAll 𝔇 Mg).shown x.1 x.2 y →
        (mgAll 𝔇 Mg).shown x.1 x.2 y') ∧
      ∀ a x y y', Stays base y y' → x ∈ sampledIn N O → (mgAll 𝔇 Mg).noColl x.1 x.2 a y →
        (mgAll 𝔇 Mg).noColl x.1 x.2 a y' :=
  ⟨fun a y y' hy h => decodes_rides 𝔇 Mg (rel := fun s t => t = s) base
      (fun _ _ _ _ e h => by rw [e]; exact h) a.1 a.2 a.2 y y' rfl hy h,
    fun x _ _ hy hx h => shown_rides 𝔇 Mg (hl x hx) hy h,
    fun a x _ _ hy hx h => noColl_rides 𝔇 Mg (p := a.1) (s := a.2) (t := a.2) (hl x hx) hy
      (fun _ _ _ z hz => ⟨z, hz, rfl⟩) h⟩

/-- **THE STRINGS' HALF AT THE COMPOSED MEANING.** -/
theorem stringsRide_mgAll {N : Numbers} {O O' : List Item} {Op : Item → Prop} {base : Nat}
    (hl : LowAt N O base) (hl' : LowAt N O' base) (hO : OpenFit X O' Op)
    (hc : CarryStays 𝔇 base) :
    StringsRide N (mgAll 𝔇 Mg) base O Op where
  decodes := (stringsRide_three 𝔇 Mg hl).1
  shown := (stringsRide_three 𝔇 Mg hl).2.1
  noColl := (stringsRide_three 𝔇 Mg hl).2.2
  items a y y' w i hy hop h := by
    have H := fieldsBack_same 𝔇 Mg (fun s t => t = s) (fun _ _ e => e) base (fun _ _ => True)
      (fun m a y b y' w hr hb => by
        obtain rfl : b = a := Prod.ext hr.1 hr.2.1
        exact hc m b y y' w hr.2.2.1 hb)
    exact items_of_fields (N := N) (Op := Op) (ownAt X) (fun j => j < base) H
      (fun i hi => ⟨(hO i hi).2.1, (hO i hi).2.2, lowItem_of_lowAt hl' (hO i hi).1⟩)
      a.1 a.2 a.2 y y' w i rfl hy trivial hop h

end

#print axioms lowItem_of_lowAt
#print axioms stringsRide_three
#print axioms stringsRide_mgAll

end Johnson.Desc.First.Walk.Tied
