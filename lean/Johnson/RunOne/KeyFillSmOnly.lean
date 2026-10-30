-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyFillSmOnly.lean: THE LOCAL PREMISE ON THE TABLES' ONE READING, BaseSt.SmOnly (Johnson/RunOne/KeySmOnly.lean: the letter sm reads of a message's record its shape, whether it is sampled, and its sample's rows: nothing else), HOLDS AT THE FILLING.
  rowIsK_only   the sending kind's tie rowIsK reads of the record sampled and sampleRows alone
  smOnly        SmOnly at baseFam, where the letter rowIs reads these two alone
  smOnlyK       SmOnly at baseK
(smReadsK | smGroupsK of Johnson/RunOne/KeyFillSeed.lean follow from it by smReads_of_only | smGroups_of_only (Johnson/RunOne/KeySmOnly.lean); they stay as they are.)
OBJECT: BaseSt.SmOnly (Johnson/RunOne/KeySmOnly.lean) · USER: the rows that turn the statement's messages (the four proximity tests' rows) · LETTERS: cs l num at_ decT recOf orc₁. Nothing on soundness.
-/
import Johnson.RunOne.KeyFillSeed
import Johnson.RunOne.KeySmOnly

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))

theorem rowIsK_only (i : Fin l.length) (o : ℕ) (x x' : OnBytes.Oracle) (h1 : x'.sampled = x.sampled) (h2 : x'.sampleRows = x.sampleRows) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) :
    rowIsK cs l i o x' ρ v ↔ rowIsK cs l i o x ρ v := by
  unfold rowIsK
  rw [h1, h2]

variable (num : Fin l.length → ℕ) (at_ : Where)
  (rowIs : ∀ i : Fin l.length, ℕ → OnBytes.Oracle → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)
  {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)

/-- **SmOnly at the filling, where the letter rowIs reads sampled and sampleRows alone.** -/
theorem smOnly (hR : ∀ i o (x x' : OnBytes.Oracle), x'.sampled = x.sampled → x'.sampleRows = x.sampleRows → ∀ ρ v, rowIs i o x' ρ v ↔ rowIs i o x ρ v) :
    (baseFam cs l num at_ rowIs decT recOf orc₁).SmOnly :=
  fun c o x x' e1 e2 e3 => smFam_congr cs l rowIs c o x x' e1 fun i ρ v => hR i o x x' e2 e3 ρ v

/-- **SmOnly at the tables' one reading with the sample's tie filled.** -/
theorem smOnlyK : (baseK cs l num at_ decT recOf orc₁).SmOnly :=
  smOnly cs l num at_ (rowIsK cs l) decT recOf orc₁ fun i o x x' e2 e3 ρ v => rowIsK_only cs l i o x x' e2 e3 ρ v

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.rowIsK_only
#print axioms Johnson.RunOne.KeyRows23.smOnly
#print axioms Johnson.RunOne.KeyRows23.smOnlyK
