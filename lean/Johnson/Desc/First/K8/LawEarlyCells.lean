-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawEarlyCells.lean: THE APPROXIMATE RANGE PROOF (KIND K8; IN THE FILES BESIDE
THIS ONE: THE SMALLNESS TEST) AT THE TABLE OF JOINTS: A TABLE OF CELLS THAT IS A FUNCTION OF THE
MEMBERS' TYPED MESSAGES AND AGREES WITH THE ITEM "tie"'S OWN TABLE AT EVERY EARLY CELL.

Why. The law of the sub-protocol in which the verifier samples the matrix, at two tables
(`k08_rowT`, Johnson/Desc/First/K8/LawTable.lean; `k08_goodInT_cap`,
Johnson/Desc/First/K8/LawGoodCapT.lean), has the premise hE: a table entE out of the members' typed
messages agrees with the witness's table entW at every early cell (a cell of an array that the
sampled matrix multiplies). At the table of joints entW is `cellsAt cs arr ms N m (z, s)`
(Johnson/Desc/Sound/CellsAt.lean). Here entE is made, and hE is shown, from the congruence
`cellsAt_congr_msgs` (Johnson/Desc/First/K8/LawBlockIn.lean).
  `msgNow_of_named`: under the test `Named.namedB` the array of every early cell has a message now.
    Two calls: `early_iff_named` (Johnson/Desc/First/K8/LawEarly.lean), `Named.namedB_at`
    (Johnson/Desc/First/K8/LawNamed.lean).
  `entOfMsgs`: THE TABLE, AS A TERM: at typed messages M that are some witness's: `cellsAt` at a
    witness that has them, taken by choice; at all other M: 0.
  `entOfMsgs_eq`: **where every early cell's array has a message now and `CellsIn` holds there: at
    every witness and every early cell `entOfMsgs` at the witness's typed messages is `cellsAt` at
    the witness**: hE to the letter, at entW := `cellsAt cs arr ms N m (z, s)` and tl0 := the part
    tl of the verifier's state s.
  `exists_entE`: the same as "there is a table".
Statements and proofs.
Limits. `CellsIn` is a premise at every early cell's array: shown at no verifier's state and at no
plan; all limits of LawBlockIn.lean stand: it can hold on nothing, and then both tables are 0
there. `entOfMsgs` has no code: it is made by choice. `cellsAt_of_msgs` (LawBlockIn.lean) writes the
same value out array by array. Outside the early cells nothing is said of it. Nothing on soundness.

-/
import Johnson.Desc.First.K8.LawBlockIn
import Johnson.Desc.First.K8.LawEarly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound Johnson.Pack
open OnBytes.Tie.Pv.Tail (early)

/-- Under the test on the names the array of every early cell has a message now. -/
theorem msgNow_of_named {p : Par} {st : Statement} {book : TreeBook} {tl : HTailF2} {L : LinkCtx}
    (h : Named.namedB p st book tl L = true) {t r c : ℕ} (he : early tl (.cell t r c) = true) :
    ∃ o, Named.msgNow L t = some o := by
  obtain ⟨o, _, ho, _⟩ := Named.namedB_at h ((early_iff_named tl t r c).1 he)
  exact ⟨o, ho⟩

section
variable {P : Type} (Cells Tok : Type) (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ) (z : P)
  (s : S)

open Classical in
/-- **The table out of the typed messages.** -/
noncomputable def entOfMsgs (M : (sigOf cs l).Msg) (t r c : ℕ) : Cb.Gl.E :=
  if h : ∃ w : Wit Cells Tok MsgT, msgsOf cs l seat' arr w = M then
    cellsAt cs arr ms N m (z, s) h.choose t r c
  else 0

variable {Cells Tok}

/-- **hE, to the letter.** -/
theorem entOfMsgs_eq {L : LinkCtx} {F : Fork} {tl : HTailF2} (hL : s.link? = some L)
    (hF : s.fork? = some F) (ht : s.tl? = some tl)
    (h : ∀ t r c, early tl (.cell t r c) = true →
      ∃ o, Named.msgNow L t = some o ∧ CellsIn cs l seat' ms N m s t o) :
    ∀ (w : Wit Cells Tok MsgT) (t r c : ℕ), early tl (.cell t r c) = true →
      entOfMsgs Cells Tok cs l seat' arr ms N m z s (msgsOf cs l seat' arr w) t r c =
        cellsAt cs arr ms N m (z, s) w t r c := by
  intro w t r c he
  obtain ⟨o, ho, C⟩ := h t r c he
  have hM : ∃ w' : Wit Cells Tok MsgT, msgsOf cs l seat' arr w' = msgsOf cs l seat' arr w :=
    ⟨w, rfl⟩
  unfold entOfMsgs
  rw [dif_pos hM]
  exact cellsAt_congr_msgs cs l seat' arr ms N m z s hL hF ht ho C _ w hM.choose_spec r c

/-- The same as "there is a table". -/
theorem exists_entE {L : LinkCtx} {F : Fork} {tl : HTailF2} (hL : s.link? = some L)
    (hF : s.fork? = some F) (ht : s.tl? = some tl)
    (h : ∀ t r c, early tl (.cell t r c) = true →
      ∃ o, Named.msgNow L t = some o ∧ CellsIn cs l seat' ms N m s t o) :
    ∃ entE : (sigOf cs l).Msg → ℕ → ℕ → ℕ → Cb.Gl.E,
      ∀ (w : Wit Cells Tok MsgT) (t r c : ℕ), early tl (.cell t r c) = true →
        entE (msgsOf cs l seat' arr w) t r c = cellsAt cs arr ms N m (z, s) w t r c :=
  ⟨entOfMsgs Cells Tok cs l seat' arr ms N m z s,
    entOfMsgs_eq cs l seat' arr ms N m z s hL hF ht h⟩

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.msgNow_of_named
#print axioms VerifiableInference.Desc.First.K8.entOfMsgs_eq
#print axioms VerifiableInference.Desc.First.K8.exists_entE
