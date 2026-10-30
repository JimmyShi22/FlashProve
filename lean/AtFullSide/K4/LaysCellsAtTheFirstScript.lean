-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K4/LaysCellsAtTheFirstScript.lean: CONDITIONAL: on the head at the return, on the maker's
return at the base filling and, at the segments 1 to 24, on closingReturns: the code switch's public
test closingOk says yes at each of the plan's switches. THE FULL SIZE ALONE.

What is here. THE BASE PROVER's SCRIPT (firstScriptAt, AtFullSide/K1/FirstScript.lean) LAYS THE
FILLING OFF THE PLANES: the form LaysCells (Honest/K5/Law/LaysCells.lean) at each of the 25 segments,
at the filling's own readers, at «no challenge has been heard», at every N. It is what
k4_exchange_all_items (Honest/K4/Law/W/ExchangeAllItems.lean) asks of the Script at the segments 2 g
and 2 (g - 1).

  laysCells_at_opening    segment 0, at the seat of the opening, at every set of inputs
  laysCells_at_switches   segments 1 to 24, at the seat over the code switches' sendings, at every set
                          of inputs that pass the description's okStart
  lays_cells              at the valid inputs of the first thread, at every l below 25: some seat

By what. Calls alone: laysFilling_opening_any (AtFullSide/K1/LaysAtEveryList.lean),
laysFilling_switches (AtFullSide/K1/LaysAtSwitches.lean), laysCells_of_laysFilling
(Honest/K5/Law/LaysCells.lean); of the three hypotheses of laysFilling_switches two are paid here:
switch_handed_at_maker_closed (AtFullSide/K5/SwitchesLendAtMakerClosed.lean) and publicOk_at_head
(Honest/K5/Law/PublicOkPaid.lean).

Not shown here. AT THE BASE MAKER's RETURN, AT `IndexCommitterCoins`: NOT AT THE ONLINE MAKER's RETURN
(`onlineFilling`, E2E/TheHonestProver.lean, is this filling read through `OnlineProverParts.through`): the crossing
is not here. closingReturns: a premise here; closing_returns_at_base (AtFullSide/K4/ClosingAtBase.lean)
pays it from h and hA by the code switch's closing_at_head (Honest/K2/Law/ClosingAtHead.lean),
beneath which lie 25 closed facts by Lean's kernel, replayed from compiled files and never built.
 That any input is valid. It says what the Script's messages hold as a
function of the readers of the input: nothing on what the readers hold. Main rows alone; nothing at
a plane's array. The laws called are no part of laws.14. Nothing on soundness, on completeness, on
hiding or on any other property.
No property is claimed.
-/
import AtFullSide.K1.LaysAtEveryList
import AtFullSide.K5.SwitchesLendAtMakerClosed
import AtFullSide.K4.SignsLetters
import Johnson.Desc.ProofFile.Honest.K5.Law.LaysCells
import Johnson.Desc.ProofFile.Honest.K5.Law.PublicOkPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K4.Signs
open ProofFile ProofFile.Honest
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.K1 (LocB firstSeat laysFilling_opening_any laysFilling_switches)
open ProofFile.Honest.K5 (LaysCells laysCells_of_laysFilling)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes.HonestTrace (Sz)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- CONDITIONAL on h and hA. **THE SCRIPT LAYS THE FILLING OFF THE PLANES AT SEGMENT 0**, at the seat
of the opening, at every set of inputs and every N. -/
theorem laysCells_at_opening (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (inputs : LocB FullSizeMatrix → Prop) (N : ℕ) :
    LaysCells h.head (theScript h) Sz.ref inputs N (readersAt A)
      (firstSeat h.head.𝔇.sent.shape 0) (fun _ => 0) 0 :=
  laysCells_of_laysFilling (laysFilling_opening_any h.head hA inputs N)

/-- CONDITIONAL on h, hA, closingReturns and inputsStart. **THE SCRIPT LAYS THE FILLING OFF THE PLANES
AT EVERY SEGMENT FROM 1 TO 24**, at the seat over the code switches' sendings, at every N. -/
theorem laysCells_at_switches (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (closingReturns : ∀ p ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take p.link) p = true)
    (inputs : LocB FullSizeMatrix → Prop)
    (inputsStart : ∀ v, inputs v → h.description.okStart v.x = true) (N : ℕ)
    {l : ℕ} (h1 : 1 ≤ l) (h25 : l < 25) :
    LaysCells h.head (theScript h) Sz.ref inputs N (readersAt A) (K2.switchSeat A.Z A.G)
      (fun _ => 0) l :=
  laysCells_of_laysFilling (laysFilling_switches h.head hA inputs N
    (AtFullSide.K5.switch_handed_at_maker_closed h.head hA) closingReturns
    (fun p hp w hw => K5.publicOk_at_head h.head (atPure_ok hA).2.1 (inputsStart w hw) p hp) h1 h25)

/-- CONDITIONAL on h, hA and closingReturns. (1) **THE SCRIPT LAYS THE FILLING OFF THE PLANES AT EVERY
SEGMENT, AT THE VALID INPUTS OF THE FIRST THREAD.** N: any number. -/
theorem lays_cells (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFilling = .ok A)
    (closingReturns : ∀ p ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take p.link) p = true)
    {l : ℕ} (hl : l < 25) (N : ℕ) :
    ∃ seat : MsgAddr → Option (ℕ × ℕ),
      LaysCells h.head (theScript h) Sz.ref (validInput h) N (readersAt A) seat (fun _ => 0) l := by
  rcases Nat.eq_zero_or_pos l with rfl | h1
  · exact ⟨_, laysCells_at_opening h hA (validInput h) N⟩
  · exact ⟨_, laysCells_at_switches h hA closingReturns (validInput h) (fun _ hv => hv.1) N h1 hl⟩

end AtFullSide.K4.Signs

#print axioms AtFullSide.K4.Signs.laysCells_at_opening
#print axioms AtFullSide.K4.Signs.laysCells_at_switches
#print axioms AtFullSide.K4.Signs.lays_cells
