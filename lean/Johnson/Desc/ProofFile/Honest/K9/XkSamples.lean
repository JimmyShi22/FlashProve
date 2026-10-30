-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/XkSamples.lean: FOR "THE FORM BEHIND" AT K9's THREE MEMBERS: THE PROMISE's Bool
`samplesHeld` ("the verifier's state still holds the sample of every tenant whose pin is open") IS HANDED ON BY EVERY
YES OF THE SEATED BLOCK's STEP, AT ALL 25 SEGMENTS. No thread, no prover, no string is in this file. Statements and
proofs ON THE VERIFIER's TEXT; no goal is stated.
  `pins_bat`, `pins_eq`, `pins_shut`   the written table's open sets behind and in front of each of the 75 members
      hold the same pins of the four sorts that `sampledIn` reads, in the same order: three evaluations by Lean's
      kernel at the library's written list (`IM.linksW`, `IM.placesW`)
  `held_of_pins`   so: where every `Mg.held j t` that says yes in front says yes behind, `samplesHeld` behind follows
      from `samplesHeld` in front; N and Mg are letters
  **`samples_behind_bat`** (under the head and `SeatedFree`), **`samples_behind_eq`**, **`samples_behind_shut`** (at
      `SeatedClose`: no head)   at a meaning Mg whose `held` is the library's `smpHeld` at the state's statement and
      book (hH: the library's `mgAll_held` says so of the composed meaning, by rfl): a yes of the step from s to s',
      `samplesHeld N Mg ‹open at b› (z, s) = true` ⊢ `samplesHeld N Mg ‹open at b + 1› (z, s') = true`. The state's
      half: at the batching and at "the segment is shut" statement and book are as they were (the library's `Rb`:
      `LinkShare.two`, `rb_putLink`); at "the one equation" the library's `eq_held`. NO PREMISE ON THE STATE STAYS
      BESIDE `samplesHeld` IN FRONT
WHAT IS NOT CLAIMED. That a yes is there. `samplesHeld` at any state. hH at any meaning. pubP. No member. It imports
Honest/K9/XkClose.lean for that file's imports and calls none of its theorems; XkAtHead.lean reaches XkClose.lean
through it. The three `pins_…` and `held_of_pins`: called here alone; the three `samples_behind_…` by
Honest/K9/XkAtHead.lean. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.XkClose
import Johnson.Desc.First.BordersKeep
import Johnson.Desc.First.Link.Law.OracleRides
import Johnson.Desc.First.Link.Law.DoorBlind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (Rb held_rides rb_putLink eq_held)

set_option maxRecDepth 1000000 in
/-- The same pins are open behind and in front of the batching. -/
theorem pins_bat : ∀ l < 25, (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 2 + 1)).filter Item.isPin =
    (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 2)).filter Item.isPin := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The like at "the one equation". -/
theorem pins_eq : ∀ l < 25, (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 4 + 0 + 1)).filter Item.isPin =
    (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 4 + 0)).filter Item.isPin := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The like at "the segment is shut". -/
theorem pins_shut : ∀ l < 25, (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 4 + 2 + 1)).filter Item.isPin =
    (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 4 + 2)).filter Item.isPin := by decide +kernel

/-- From the same pins and "held" handed on. -/
theorem held_of_pins {P W : Type} (N : Numbers) (Mg : Meaning P W) {O O' : List Item}
    (hp : O'.filter Item.isPin = O.filter Item.isPin) {a a' : P × S}
    (hh : ∀ j t, Mg.held j t a = true → Mg.held j t a' = true) (hs : samplesHeld N Mg O a = true) :
    samplesHeld N Mg O' a' = true := by
  unfold samplesHeld at hs ⊢
  rw [sampledIn_of_filter N O O' hp]
  rw [List.all_eq_true] at hs ⊢
  exact fun y hy => hh y.1 y.2 (hs y hy)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **`samplesHeld` behind the batching's yes.** -/
theorem samples_behind_bat (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp l kk Lk p w) {P W : Type} (N : Numbers) (Mg : Meaning P W)
    (hH : Mg.held = fun j t (a : P × S) => smpHeld a.2.st a.2.book j t) (z : P) (ft : ℕ) {s s' : S}
    (hy : IM.Yes ft (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) s s')
    (hs : samplesHeld N Mg (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 2)) (z, s) = true) :
    samplesHeld N Mg (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 2 + 1)) (z, s') = true := by
  obtain ⟨rs, cols, n, hstep⟩ := hy
  have R : Rb s s' := ((linkShare_seated h hl Sd).two.1 ft s rs cols s' n hstep).1
  refine held_of_pins N Mg (pins_bat l hl) (fun j t e => ?_) hs
  rw [hH] at e ⊢
  exact held_rides s s' R j t e

/-- **`samplesHeld` behind the yes of "the one equation".** -/
theorem samples_behind_eq {c : Chain S Claim} {Zq : ProofFile.Pub} {l : ℕ} (hl : l < 25) {Lk : Link S Claim}
    {p : Desc.K9.Where} {Q : Close.Par} {bE bS : Block S Claim} (H : SeatedClose c Zq l Lk p Q bE bS)
    {P W : Type} (N : Numbers) (Mg : Meaning P W)
    (hH : Mg.held = fun j t (a : P × S) => smpHeld a.2.st a.2.book j t) (z : P) (ft : ℕ) {s s' : S}
    (hy : IM.Yes ft bE s s')
    (hs : samplesHeld N Mg (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 4 + 0)) (z, s) = true) :
    samplesHeld N Mg (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 4 + 0 + 1)) (z, s') = true := by
  obtain ⟨rs, cols, n, hstep⟩ := IM.Yes.under (LPFK9.HandsAt.eq_under p Q _ rfl)
    (IM.Yes.under (IM.alone_underR H.aloneE) hy)
  refine held_of_pins N Mg (pins_eq l hl) (fun j t e => ?_) hs
  rw [hH] at e ⊢
  have e2 := eq_held p _ (fun _ _ _ _ _ e' => e') _ _ _ _ _ n hstep j t
  exact e2.trans e

/-- **`samplesHeld` behind the yes of "the segment is shut".** -/
theorem samples_behind_shut {c : Chain S Claim} {Zq : ProofFile.Pub} {l : ℕ} (hl : l < 25) {Lk : Link S Claim}
    {p : Desc.K9.Where} {Q : Close.Par} {bE bS : Block S Claim} (H : SeatedClose c Zq l Lk p Q bE bS)
    {P W : Type} (N : Numbers) (Mg : Meaning P W)
    (hH : Mg.held = fun j t (a : P × S) => smpHeld a.2.st a.2.book j t) (z : P) (ft : ℕ) {s s' : S}
    (hy : IM.Yes ft bS s s')
    (hs : samplesHeld N Mg (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 4 + 2)) (z, s) = true) :
    samplesHeld N Mg (IM.openAt IM.linksW IM.placesW (14 * l + IM.nAt l + 4 + 2 + 1)) (z, s') = true := by
  obtain ⟨rs, cols, n, hstep⟩ := hy
  obtain ⟨L, hL, rfl⟩ := (H.shutKeeps ft s s' rs cols n hstep).laid
  have R : Rb s (s.putLink (Desc.K9.closed L L.check.frame)) := rb_putLink s L _ hL rfl
  refine held_of_pins N Mg (pins_shut l hl) (fun j t e => ?_) hs
  rw [hH] at e ⊢
  exact held_rides s _ R j t e

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.pins_bat
#print axioms ProofFile.Honest.K9.pins_eq
#print axioms ProofFile.Honest.K9.pins_shut
#print axioms ProofFile.Honest.K9.held_of_pins
#print axioms ProofFile.Honest.K9.samples_behind_bat
#print axioms ProofFile.Honest.K9.samples_behind_eq
#print axioms ProofFile.Honest.K9.samples_behind_shut
