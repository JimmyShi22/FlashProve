-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAt/SmallRun.lean: WHAT THE COMPOSED MEANING's FIELD "forms" SAYS AT THE RUN
"small" (Johnson/Desc/Sound/MgAll.lean). Statements and proofs. Over the composing's own
files alone.
  `reader_small`: where the chain has a link m: the readers of segment m, asked for the forms of the
    run "K8.equations" at any piece, answer with the reader of the single equations
    (`K9.smallReader`).
  `formsQA_small`: where segment m has the sort sub, and the table's map of names at that sort sends
    (5 + o, "small") to just [(4 + o, "K8.equations")]: the field "forms" at (m, 5 + o, "small")
    gives `formsQA` at (4 + o, "K8.equations"): the clause for a run whose forms may name what is
    ahead.
  `runs_small`: that map at the three sorts: o = 0 at a feed-forward and at an attention segment,
    o = 1 at the head's.
On the premise on the sort: beyond the list of sorts the map of names is empty (`runsAt`), and the
field at the run "small" holds of every state and witness (`forms_idle`): there it could give
`formsQA` only if that held of every state and witness. That it does not is not shown here.
Nothing on soundness.

-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.Sound.MgAt.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning runsOf)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- The readers of a segment that has a link read the single equations by `K9.smallReader`. -/
theorem reader_small (m : ℕ) (l : Link First.S Claim) (hl : 𝔇.lk m = some l) (b : ℕ)
    (s : First.S) : (𝔇.Rd m).forms b "K8.equations" s = K9.smallReader s := by
  unfold MgData.Rd
  rw [K9.readersAt_some 𝔇.lk X _ m l hl]
  exact K9.forms_small (K9.holesAt X _ m l) l b s

/-- The map of names at the run "small", at the three sorts. -/
theorem runs_small :
    runsOf .layers (5 + 0) "small" = [(4 + 0, "K8.equations")] ∧
    runsOf .attention (5 + 0) "small" = [(4 + 0, "K8.equations")] ∧
    runsOf .head (5 + 1) "small" = [(4 + 1, "K8.equations")] := by decide

/-- **From the field "forms" at the run "small" to the clause on the single equations.** -/
theorem formsQA_small (m o : ℕ) (sub : ModelPart) (hsub : 𝔇.links[m]? = some sub)
    (hr : runsOf sub (5 + o) "small" = [(4 + o, "K8.equations")]) (z : P) (s : First.S)
    (y : Strs) (w : Wit (CellsQ rows cols) Tok MsgT)
    (h : (mgAll 𝔇 Mg).forms m (5 + o) "small" (z, s) y w) :
    formsQA (𝔇.N.sent m) (𝔇.N.group m) (𝔇.Rd m) (4 + o) "K8.equations" s
      (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w) := by
  rw [mgAll_forms] at h
  have hm : ((4 + o, "K8.equations") : ℕ × String) ∈ 𝔇.runs m (5 + o) "small" := by
    unfold MgData.runs
    rw [runsAt_of 𝔇.links m sub hsub, hr]
    exact List.mem_singleton.2 rfl
  have h1 := h.1 _ hm
  have ha : 𝔇.ah (4 + o) "K8.equations" = true := rfl
  rw [if_pos ha] at h1
  exact h1

/-- Beyond the list of sorts the field at the run "small" holds of itself. -/
theorem forms_idle (m k : ℕ) (hm : 𝔇.links[m]? = none) (z : P) (s : First.S) (y : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) : (mgAll 𝔇 Mg).forms m k "small" (z, s) y w := by
  rw [mgAll_forms]
  refine ⟨fun p hp => ?_, fun h => ?_⟩
  · unfold MgData.runs runsAt at hp
    rw [hm] at hp
    cases hp
  · exact absurd h (by decide)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.reader_small
#print axioms VerifiableInference.Desc.Sound.runs_small
#print axioms VerifiableInference.Desc.Sound.formsQA_small
#print axioms VerifiableInference.Desc.Sound.forms_idle
