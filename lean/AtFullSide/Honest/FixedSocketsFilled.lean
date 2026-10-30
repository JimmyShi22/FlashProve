-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/FixedSocketsFilled.lean: THREE FIELDS OF `TheThreadsHalf` (TheOneObject.lean of
this folder), IN THAT STRUCTURE's OWN FIELD TYPES, at every value of its two open letters: `fix₂`
and `fix₃` (each tree available at a border of the shared, of the second chain is fixed by the
challenges heard there) and `takenAre` (each tree in the second chain's list of taken trees is
declared as taken over). Statements with their proofs; no definition.

Main names. `fix₂_filled`: with no premise. `fix₃_filled`: from the maker's return alone: the second
clause of `fixed_fields_at_the_letters` (AtFullSide/K14/AtTheLetters.lean). `takenAre_filled`: with
no premise. At the file's end a check by Lean's elaborator that the three have the fields' types.

Limits. Public sentences on the letters fixed and taken: no run, no coin. O, P: the structure's two
open letters; P holds propositions, and that a value of P exists is not shown here. The full size,
and the hash function `OnBytes.secondHashFunction`, alone.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import AtFullSide.Honest.TheOneObject
import AtFullSide.K14.AtTheLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixFilling)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Committed AtPublicFiles.TheFalls
open OnBytes.Slice (frS)
open VerifierAndGoals (PublicFiles readFiles)
open ProofFile.Honest.Small (sentIn_front treesTo_roots decls_split lists_of_shaped)

/- The three instances that the structure's own file gives by hand. -/
local instance (priority := high) nonemptyPadZ_fixedSockets : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_fixedSockets : Nonempty RunValue :=
  ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_fixedSockets : Inhabited RunValue :=
  ⟨fun _ => 0⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {O : TheLetters.OpenShared A}
  (P : TheLetters.OpenLast h O)

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **The field fix₂.** The law on the three sentences together takes a value of what ready returns,
which this sentence does not read: so its share of that law's proof is repeated here. -/
theorem fix₂_filled (O : TheLetters.OpenShared A) : Socket.fix₂ h (TheLetters.shared h O) := by
  obtain ⟨-, s2, -⟩ := planOk_all (head_planOk h.head)
  intro b _ j hj
  show (TheLetters.later (h := h) O).fixed (.own j) ≤ _
  rw [AtFullSide.K14.shared_fixed_is h (TheLetters.later (h := h) O) rfl j,
    decls_split h.description.shared.blocksInOrder b]
  refine sentIn_front _ _ j ?_
  rw [← treesTo_roots h.description.shared.blocksInOrder (fun x hx => lists_of_shaped (s2 x hx).2) b]
  exact hj

/-- **The field fix₃.** -/
theorem fix₃_filled (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) :
    ∀ r : TiedRun h hr, Socket.fix₃ h (TheLetters.first h) (TheLetters.reads h)
      (lastParts h (TheLetters.first h) (TheLetters.last h P)) r.R :=
  fun r => (AtFullSide.K14.fixed_fields_at_the_letters h made P r.R).2.1

/-- **The field takenAre.** -/
theorem takenAre_filled :
    Socket.takenAre (lastParts h (TheLetters.first h) (TheLetters.last h P)) := by
  intro σ hσ
  rcases HonestTraceRun.LaterTrees.takenLast_declared h σ hσ with ⟨j, rfl, -⟩ | ⟨j, rfl, -⟩
  · exact ⟨0, j, rfl⟩
  · exact ⟨1, j, rfl⟩

/-- A check by Lean's elaborator that the three have the fields' types: a value of the structure
with these three fields laid anew by the three statements. It takes a value T for the other fields:
so it shows nothing of the others, and is no payment. -/
example (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (T : TheThreadsHalf h hr) : TheThreadsHalf h hr :=
  { T with
    fix₂ := fix₂_filled h T.open₂
    fix₃ := fix₃_filled h hr T.open₃ made
    takenAre := takenAre_filled h T.open₃ }

end AtFullSide.Honest

#print axioms AtFullSide.Honest.fix₂_filled
#print axioms AtFullSide.Honest.fix₃_filled
#print axioms AtFullSide.Honest.takenAre_filled
