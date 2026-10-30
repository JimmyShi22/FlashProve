-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecK4.lean: kind K4's block at the first chain's record (blockAtS,
Johnson/Desc/First/K4/AtS.lean) writes neither the statement nor a copy of the frame of the links:
it is Quiet (Johnson/Goal/Meaning/RecQuiet.lean): its decide, its two runs of claims ("front",
"back") and its run behind the batching ("free-slot").

The block is typed at a part (what S holds inside a layers' link; the debt of rows; the tokens) and
lifted. At the part it writes through its seat's three layings alone: the ledger F, what was heard
  (own), the debt: never the link L. SameL p x: the part x has the link of the part p, and owes no
  rows where p owes none.
  k4_steps, k4_runs, k4_after: the block at the part keeps SameL.
  setPart_quiet: laid back into S, a part with the same link gives a Quiet record.
  k4_quiet: Whole Quiet (blockAtS p). k4_rec, k4_grows: so Whole (RecRel cs sh) and Whole (GrowsBy
  fun s => s.st).
Not claimed: anything on another kind's blocks.
OBJECT: the makers' blocks and steps that are named above. USERS: through whole_rec |
recRel_of_quiet the walk (Johnson/Goal/Meaning/RecWalk.lean: recAll_border, at the letters cs and
sh); through whole_grows | groundKeeps_grows the owed premise of Johnson/Desc/StatementGrows.lean
(ChainKeeps (GrowsBy st) c). Neither calls them yet. Which maker stands at which place of a seated
text is not said here.
-/
import Johnson.Goal.Meaning.RecQuiet
import Johnson.Desc.First.K4.LedgerKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole)
open OnBytes.Desc.First.K4 (blockAtS block seatOwn part? setPart decide_ok freeSlot_same runOf)

/-- The part x has the link of the part p, and owes no rows where p owes none. -/
def SameL (p x : OnBytes.Desc.First.K4.Part) : Prop :=
  x.1.L = p.1.L ∧ (p.2.1 = none → x.2.1 = none)

theorem k4_steps (p : OnBytes.Desc.First.K4.Par) : (block seatOwn p).Steps SameL := by
  intro s rs gs s' h
  obtain ⟨_, _, _, fo, o, F, _, _, h6⟩ := decide_ok seatOwn h
  rw [h6]
  exact ⟨rfl, fun _ => rfl⟩

theorem runOf_sameL {name : String}
    {f : Layer.Own → Fork → Option (Array Aff × Fork)} {s s' : OnBytes.Desc.First.K4.Part}
    {cl : List Aff} (h : runOf seatOwn name f s = .ok (cl, s')) : SameL s s' := by
  unfold runOf at h
  obtain ⟨o, _, h⟩ := bindE h
  obtain ⟨x, _, h⟩ := bindE h
  cases h
  exact ⟨rfl, fun w => w⟩

theorem k4_runs (p : OnBytes.Desc.First.K4.Par) : (block seatOwn p).RunsStep SameL := by
  intro c hc n s cl s' h
  rcases List.mem_cons.1 hc with rfl | hc
  · exact runOf_sameL h
  · rcases List.mem_cons.1 hc with rfl | hc
    · exact runOf_sameL h
    · cases hc

theorem k4_after (p : OnBytes.Desc.First.K4.Par) : (block seatOwn p).AfterStep SameL := by
  intro c hc s s' h
  rcases List.mem_cons.1 hc with rfl | hc
  · rw [freeSlot_same seatOwn h]
    exact ⟨rfl, fun w => w⟩
  · cases hc

/-- Laid back into S, a part with the same link gives a Quiet record. -/
theorem setPart_quiet (t : S) (p x : OnBytes.Desc.First.K4.Part) (hp : part? t = some p)
    (e : SameL p x) : Quiet t (setPart t x) := by
  unfold part? at hp
  split at hp
  · rename_i a ha
    cases hp
    have e' : x.1.L = a.L := e.1
    refine ⟨⟨rfl, fun f hf => ?_, rfl, rfl⟩, ?_, fun w => ?_, fun _ e => e⟩
    · unfold framesIn at hf ⊢
      rw [ha]
      simpa [setPart, e'] using hf
    · simp [ctxW, ctxOf, openOf, armOf, S.link?, setPart, ha, e']
    · have k : x.2.1 = none := e.2 (by simp [w])
      simp [S.noneWaits, setPart, k]
  · cases hp

/-- **K4's block at the record is Quiet.** -/
theorem k4_quiet (p : OnBytes.Desc.First.K4.Par) : Whole Quiet (blockAtS p) :=
  whole_of_steps (stepsLiftPart part? setPart _ (k4_steps p) setPart_quiet)
    (runsLiftPart part? setPart _ (k4_runs p) setPart_quiet)
    (afterLiftPart part? setPart _ (k4_after p) setPart_quiet)

theorem k4_rec {cs : Codes} {sh : ReqShape} (p : OnBytes.Desc.First.K4.Par) :
    Whole (RecRel cs sh) (blockAtS p) := whole_rec (k4_quiet p)

theorem k4_grows (p : OnBytes.Desc.First.K4.Par) :
    Whole (ChainEnd.GrowsBy fun s : S => s.st) (blockAtS p) := whole_grows (k4_quiet p)

#print axioms k4_quiet
#print axioms k4_rec
#print axioms k4_grows

end Meaning.K2
