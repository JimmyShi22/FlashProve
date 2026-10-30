-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/SigDecodes.lean: "THE STORED TABLE DECODES" RIDES, AND THE STORED TABLE's PIN
GOES BACK, OVER EVERY STEP THAT LEAVES THE PUBLIC PART. One definition and statements with their
proofs. It names no table of joints.
Why. The table of joints' letters "decodes" and "pinW" are filled by other files
(`decodesOf decT`, `pinWOf decT`: Johnson/Desc/Sound/MeaningSig.lean). Both read the stored table's
cells and, through the letter decT, the pair of the public part and the chain's record. Each block
owes that the first rides over its step and that the second goes back. Over a step that turns the
record that is true only of a decT that does not read what the step turns.
  `DecBlind decT`: THE PREMISE ON decT: it reads the public part alone, not the chain's record.
  `decBlind_of_pub`: ITS MEMBERS: every decT of the form "f at the cells and the public part". THE
    decT THAT IS MEANT IS OF THAT FORM BY ITS MAKE (`decTop`, Johnson/Desc/Sound/DecTop.lean: the
    top statements' decoder at the stored table's string and at the key file's record, which is
    read off the public part): `decBlind_of_pub _` has that type by unfolding. NOT CALLED HERE AT
    `decTop`: that file is not imported.
  `decodes_rides_blind`, `pinW_back_blind`: kind-free: over two pairs with one public part and two
    strings with one reader of the cells.
  `decodes_M3`, `pinWBack_M3`, `decodes_M4`, `pinWBack_M4`: at kind K13's block and at W's
    commitment: the clauses `Others3.decodes`, `Others3.pinWBack`, `Others4.decodes`,
    `Others4.pinWBack` (Johnson/Desc/K13/Law/FillFromSentences.lean) TO THE LETTER at a filling Mg
    whose `Mg.decodes` is `decodesOf decT` and whose `Mg.pinW` is `pinWOf decT` by the make. At any
    other step h whose first part is "the public part stays": the two kind-free lemmas at h.1.
What is not claimed. That the filling of record lays a decT that is blind. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.Sound.MeaningSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT decodesOf pinWOf)

section
variable {Pp Cells Tok : Type}

/-- **The premise on decT**: it reads the public part alone, not the chain's record. -/
def DecBlind (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) : Prop :=
  ∀ cell z s s', decT cell (z, s') = decT cell (z, s)

/-- Its members: every decT that is made of a function of the cells and the public part. -/
theorem decBlind_of_pub (f : (ℕ → Option (ℕ × List UInt64)) → Pp → Option Cells) :
    DecBlind (fun cell (p : Pp × S) => f cell p.1) := fun _ _ _ _ => rfl

variable {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}

/-- At two pairs with one public part a blind decT gives one thing. -/
theorem DecBlind.same (h : DecBlind decT) {x x' : Pp × S} (e : x'.1 = x.1)
    (cell : ℕ → Option (ℕ × List UInt64)) : decT cell x' = decT cell x := by
  obtain ⟨z, s⟩ := x
  obtain ⟨z', s'⟩ := x'
  obtain rfl : z' = z := e
  exact h cell z' s s'

/-- **"decodes" rides**, kind-free. -/
theorem decodes_rides_blind (h : DecBlind decT) {x x' : Pp × S} (e : x'.1 = x.1) {y y' : Strs}
    (hc : y'.cell = y.cell) (hd : decodesOf decT x y) : decodesOf decT x' y' := by
  unfold decodesOf at hd ⊢
  rw [hc, h.same e]
  exact hd

/-- **"pinW" goes back**, kind-free. -/
theorem pinW_back_blind (h : DecBlind decT) {x x' : Pp × S} (e : x'.1 = x.1) {y y' : Strs}
    (hc : y'.cell = y.cell) {w : Desc.Wit Cells Tok MsgT} (hp : pinWOf decT x' y' w) :
    pinWOf decT x y w := by
  unfold pinWOf at hp ⊢
  rw [hc, h.same e] at hp
  exact hp

variable {Cl : Type} {P : Where} {P' : K1.Par}

/-- `Others3.decodes`. -/
theorem decodes_M3 (h : DecBlind decT) :
    ∀ x x' y y', StepM3 Cl P x x' → y'.cell = y.cell → decodesOf decT x y → decodesOf decT x' y' :=
  fun _ _ _ _ hs hc hd => decodes_rides_blind h hs.1 hc hd

/-- `Others3.pinWBack`. -/
theorem pinWBack_M3 (h : DecBlind decT) :
    ∀ x x' y y' (w : Desc.Wit Cells Tok MsgT), StepM3 Cl P x x' → y'.cell = y.cell →
      pinWOf decT x' y' w → pinWOf decT x y w :=
  fun _ _ _ _ _ hs hc hp => pinW_back_blind h hs.1 hc hp

/-- `Others4.decodes`. -/
theorem decodes_M4 (h : DecBlind decT) :
    ∀ x x' y y', StepM4 Cl P P' x x' → y'.cell = y.cell → decodesOf decT x y →
      decodesOf decT x' y' :=
  fun _ _ _ _ hs hc hd => decodes_rides_blind h hs.1 hc hd

/-- `Others4.pinWBack`. -/
theorem pinWBack_M4 (h : DecBlind decT) :
    ∀ x x' y y' (w : Desc.Wit Cells Tok MsgT), StepM4 Cl P P' x x' → y'.cell = y.cell →
      pinWOf decT x' y' w → pinWOf decT x y w :=
  fun _ _ _ _ _ hs hc hp => pinW_back_blind h hs.1 hc hp

end

end VerifiableInference.Desc.K13.Law
