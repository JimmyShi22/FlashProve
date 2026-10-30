-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/PinsGoBack.lean: THE PINS GO BACK: what a rider past a block asks at the items
"pin", "pinKept", "pinI" and "pinV" of the table of joints (`Item.holds`,
Johnson/Desc/First/Borders.lean), where the letter "pin" is filled as another file fills it
(`pinJT`, Johnson/Desc/Sound/MeaningSig.lean). KIND-FREE: no block, no piece. Statements as
definitions of a Prop, and their proofs.
Main names:
  `OwedPinBack`, `pin_back`: at ONE seat (j, t) and one pair of records a, a' and of strings y, y':
    the seat's tree's column is as it was, and the sample of each member of ms that sits there is
    left: a pin at (a', y') is a pin at (a, y). One call of `pinsStay`
    (Johnson/Desc/K13/Law/SigPins.lean).
  `IsPin i`: the item is one of the four.
  `OwedPinArms`, `pin_arms`: **the four arms at once, in the form of the user's binder**: O: the
    items that are open; i ∈ O is one of the four; every tenant of `sampledIn N O` has its tree
    below base; the strings are kept below base; the samples of the members at these tenants are
    left: `i.holds N Mg x' y' w → i.holds N Mg x y w`, at every Mg whose "pin" is
    `pinJT cs G arr smp ms`.
  `tenants_in`: an open pin's tenants are among `sampledIn N O`.
What is not claimed. That a block's yes leaves the samples (`SmpLeft`, MgK1.lean): a premise, at
one pair of records. That the strings are kept below base: the piece's. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.SigPins
import Johnson.Desc.K13.Law.AtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Item Meaning Numbers sampledIn)
open VerifiableInference.Desc.Sound (MsgT Sending Mem SitsAt pinJT)
open VerifiableInference.Desc.K13.Law (OldKept pinsStay)

/-- **OWED.** At one seat: the column kept, the members' samples left: the pin goes back. -/
def OwedPinBack : Prop :=
  ∀ {A Xi Cells Tok : Type} (cs : Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (j t : ℕ) (a a' : A) (y y' : Strs) (w : Desc.Wit Cells Tok MsgT),
    OldKept j y y' → (∀ m ∈ ms, SitsAt m j t → smp a' m.1 m.2 = smp a m.1 m.2) →
    pinJT cs G arr smp ms j t a' y' w → pinJT cs G arr smp ms j t a y w

theorem pin_back : OwedPinBack := by
  intro A Xi Cells Tok cs G arr smp ms j t a a' y y' w hK hS h
  exact ((pinsStay cs G arr smp ms j t a a' y y' hK.2 hS).2.2 w).2 h

/-- The item is one of the four pins on sampled tenants. -/
def IsPin : Item → Prop
  | .pin _ _ => True
  | .pinKept _ => True
  | .pinI => True
  | .pinV => True
  | _ => False

/-- An open pin's tenants are among the sampled tenants whose pin is open. -/
theorem tenants_in (N : Numbers) (O : List Item) (i : Item) (hi : i ∈ O) (u : ℕ × ℕ)
    (hu : u ∈ (match i with
      | .pin m t => N.sent m t
      | .pinKept m => N.keptOf m
      | .pinI => [N.index]
      | .pinV => [N.w]
      | _ => [])) : u ∈ sampledIn N O :=
  List.mem_flatMap.2 ⟨i, hi, hu⟩

/-- **OWED.** The four arms, in the form of the user's binder. -/
def OwedPinArms : Prop :=
  ∀ {Pp Xi Cells Tok : Type} (cs : Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (N : Numbers) (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)),
    Mg.pin = pinJT cs G arr smp ms →
    ∀ (O : List Item) (base : ℕ) (x x' : Pp × S) (y y' : Strs) (w : Desc.Wit Cells Tok MsgT),
    (∀ u ∈ sampledIn N O, u.1 < base) → (∀ j, j < base → OldKept j y y') →
    (∀ u ∈ sampledIn N O, ∀ m ∈ ms, SitsAt m u.1 u.2 → smp x' m.1 m.2 = smp x m.1 m.2) →
    ∀ i ∈ O, IsPin i → i.holds N Mg x' y' w → i.holds N Mg x y w

theorem pin_arms : OwedPinArms := by
  intro Pp Xi Cells Tok cs G arr smp ms N Mg hMg O base x x' y y' w hb hK hS i hi hp h
  have one : ∀ u ∈ sampledIn N O, Mg.pin u.1 u.2 x' y' w → Mg.pin u.1 u.2 x y w := by
    intro u hu hpin
    rw [hMg] at hpin ⊢
    exact pin_back cs G arr smp ms u.1 u.2 x x' y y' w (hK u.1 (hb u hu)) (hS u hu) hpin
  cases i with
  | pin m t => exact fun u hu => one u (tenants_in N O _ hi u hu) (h u hu)
  | pinKept m => exact fun u hu => one u (tenants_in N O _ hi u hu) (h u hu)
  | pinI => exact one N.index (tenants_in N O _ hi _ (List.mem_singleton.2 rfl)) h
  | pinV => exact one N.w (tenants_in N O _ hi _ (List.mem_singleton.2 rfl)) h
  | _ => exact absurd hp (fun c => c)

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.pin_back
#print axioms VerifiableInference.Desc.K1.pin_arms
