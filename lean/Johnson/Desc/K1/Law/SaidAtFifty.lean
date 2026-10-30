-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SaidAtFifty.lean: one fact more on the
closed list `mwMore` (DoorAtPlus13.lean), by evaluation in Lean's kernel, asked for K01_law's
turned binder hBase: every public item that stands in the open public set BEHIND one
of K1's fifty later places, `left` and `leftOn` apart, is `hasRow` (`p1Item`) or an item of which
the table `First.saysNone` (Johnson/Desc/First/AllSaid.lean) says "no sentence beside the test".
  `saidB`          the test on an item
  `saidSetB`       the test on the open public set at a border; `said_of`: what its accept says
  `said_mw`        [kernel] at the border behind each of the fifty
  `said_plus13`    the same at the wider meaning's own list, where `Mg₀.more` is the empty one
  `baseP_plus13`   **the one field of `BaseK1`, second form, written out**, at M := the wider
                   meaning's list and MgP := the pending claim's layer over Mg₀. PREMISE hS: Mg₀'s
                   `pubP` holds wherever `saysNone` names a part (at the base meaning `mgBase`,
                   Johnson/Desc/Sound/MgBase.lean: by its make)
  `saidTests_fail`   [kernel] the test can fail: with `saysNone` alone (without `p1Item`, and with
                   `leftOn` not set apart) it refuses behind segment 0's reads
WHICH LIST. The open public set (`First.pubSets`), of which the promise asks `pubP`; the items that
are tied to open items (`First.pubOfItems`) are not in it.
The recursion limit is raised in this file (maxRecDepth 1000000), as in FormsAtFifty.lean:
for the elaboration of the kernel's evaluations alone.
What is not claimed. That the table is right. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.DoorFactsAtPlus13
import Johnson.Desc.First.AllSaid
import Johnson.Desc.K1.Law.CallsB

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf pubSets
  saysNone)
open VerifiableInference.Desc.First.FillP1 (p1Item)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13)
open VerifiableInference.Desc.K13.Law (plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open IM (k1Ix)

/-- `left` or `leftOn`. -/
def leftish : Pub → Bool
  | .left _ => true
  | .leftOn _ => true
  | _ => false

/-- The test on an item. -/
def saidB (q : Pub) : Bool := leftish q || p1Item q || (saysNone q).isSome

/-- Every item of the open public set at border k passes c. -/
def saidSetB (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) (c : Pub → Bool) : Bool :=
  ((pubSets M links ps)[k]?.getD []).all c

theorem said_of {M : More} {links : List ModelPart} {ps : List Place} {k : ℕ}
    (h : saidSetB M links ps k saidB = true) (q : Pub) (hq : q ∈ (pubSets M links ps)[k]?.getD [])
    (h1 : ∀ m, q ≠ .left m) (h2 : ∀ m, q ≠ .leftOn m) :
    p1Item q = true ∨ (saysNone q).isSome = true := by
  have h0 : (leftish q || p1Item q || (saysNone q).isSome) = true := List.all_eq_true.1 h q hq
  have hl : leftish q = false := by
    cases q with
    | left m => exact absurd rfl (h1 m)
    | leftOn m => exact absurd rfl (h2 m)
    | _ => rfl
  rw [hl, Bool.false_or, Bool.or_eq_true] at h0
  exact h0

theorem said_mw : ((List.range 25).all fun l => [false, true].all fun d =>
    saidSetB mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2 + 1)
      saidB) = true := by
  decide +kernel

/-- **The test can fail**: `saysNone` alone refuses behind segment 0's reads. -/
theorem saidTests_fail :
    saidSetB mwMore linksFull (flatPlacesOf linksFull true) (14 * 0 + k1Ix 0 false + 2 + 1)
      (fun q => (saysNone q).isSome) = false := by
  decide +kernel

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X) (dk : K12Data)
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **At the wider meaning's own list.** -/
theorem said_plus13 (h : Mg₀.more = {}) : ∀ l, l < 25 → ∀ d : Bool, ∀ q,
    q ∈ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
      (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] →
    (∀ m, q ≠ .left m) → (∀ m, q ≠ .leftOn m) →
    p1Item q = true ∨ (saysNone q).isSome = true := by
  intro l hl d q hq h1 h2
  rw [plus13_more_closed Dm dk Mg₀ h] at hq
  exact said_of (List.all_eq_true.1 (List.all_eq_true.1 said_mw l (List.mem_range.2 hl)) d
    (by cases d <;> simp)) q hq h1 h2

/-- **`BaseK1.pubP`, second form, to the letter.** -/
theorem baseP_plus13 (h : Mg₀.more = {})
    (hS : ∀ q a, (saysNone q).isSome = true → Mg₀.pubP q a) : ∀ l, l < 25 → ∀ d : Bool,
    ∀ q ∈ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
      (flatPlacesOf linksFull true))[noL l d + 1]?.getD [], isLeft q = false →
    ∀ a, (First.FillP1.fillP1 Dm.d1 Dm.rw13 Dm.A1 Dm.cr1 Mg₀).pubP q a := by
  intro l hl d q hq hq0 a
  have h1 : ∀ m, q ≠ .left m := fun m e => by rw [e] at hq0; cases hq0
  have h2 : ∀ m, q ≠ .leftOn m := fun m e => by rw [e] at hq0; cases hq0
  cases hp : p1Item q with
  | true => exact First.FillP1.fillP1_pubP_own _ _ _ _ _ q hp a
  | false =>
    rw [First.FillP1.fillP1_pubP_else _ _ _ _ _ q hp a]
    rcases said_plus13 Dm dk Mg₀ h l hl d q hq h1 h2 with e | e
    · rw [hp] at e
      cases e
    · exact hS q a e

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.baseP_plus13
#print axioms VerifiableInference.Desc.K1.said_mw
#print axioms VerifiableInference.Desc.K1.saidTests_fail
#print axioms VerifiableInference.Desc.K1.said_plus13
