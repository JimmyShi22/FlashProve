-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/PlayLaw.lean: K9's PART, PLAYED: AT EVERY STAND AND EVERY CHALLENGE THAT THE ROUND
CAN DRAW. Statements and proofs on the frame's own player (`play`, Honest/Frame.lean) at K9's part (`batPart`,
Honest/K9/Part.lean), which sends nothing. No goal is stated.
  `bat_items`      the round that K9's entry states cuts no item but roots
  `draws_one`      a list of challenges that K9's one round can draw (`drawsFit`) is ONE challenge, of ONE element, no
      position, no matrix entry and no sealed digest
  **`bat_play`**    the part's one step, played alone from any stand m at any challenge d: it returns; the one round
      as played shows no item and no table; behind it the state has heard d and is otherwise as it was, d stands among
      the challenges that the stops may read, and the round ⟨[], d⟩ among the rounds shown
  `bat_reads`      K9's one round reads no column
General in the name, the address, what the second stop may read, and the coins (there are none).
No member here: the toy's `#guard` lines run the player (Honest/K9/Toy.lean). Called by Honest/K9/GoodLaw.lean,
ThrPlays.lean, ThrYes.lean and ThrBehind.lean.
WHAT IS NOT CLAIMED. Anything on the verifier's answer. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference VerifiableInference.Desc

variable {V W X : Type}

/-- K9's round cuts no item but roots. -/
theorem bat_items (p : Desc.K9.Where) :
    (({ entry := Desc.K9.entry p } : Fmt.DeclaredRound).items.filter (· != .root)) = [] := by
  simp only [Fmt.DeclaredRound.items, Fmt.Entry.cut, Desc.K9.entry]; decide

/-- What K9's one round can draw. -/
theorem draws_one (p : Desc.K9.Where) (ds : List Fmt.Drawn)
    (h : drawsFit [{ entry := Desc.K9.entry p }] ds = true) : ∃ tr, ds = [⟨[tr], [], [], none⟩] := by
  match ds, h with
  | [⟨el, po, tri, dg⟩], h =>
    simp only [drawsFit, drawFit, Bool.and_eq_true, Bool.and_true, beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, _⟩, _⟩, _⟩, h8⟩ := h
    have e1 : el.length = 1 := h1
    have e2 : po.length = 0 := h2
    have e3 : tri.length = 0 := h3
    have e8 : dg = none := by
      rcases h8 with h8 | h8
      · cases dg with
        | none => rfl
        | some _ => exact nomatch h8
      · have h9 : Fmt.kindOf "BAT-sigma" = some .sealed := h8
        exact absurd h9 (by decide)
    match el, e1 with
    | [tr], _ =>
      rw [List.length_eq_zero_iff.1 e2, List.length_eq_zero_iff.1 e3, e8]
      exact ⟨tr, rfl⟩
  | [], h => exact nomatch h
  | _ :: _ :: _, h =>
    simp only [drawsFit, Bool.and_false] at h
    exact nomatch h

/-- **The part's one step, played alone.** -/
theorem bat_play (p : Desc.K9.Where) (name : String) (a : Addr) (v : Option V)
    (c : (batPart : Part V W X).Coins) (d : Fmt.Drawn) (m : Mid W X) :
    play ((batPart : Part V W X).steps name a [({ entry := Desc.K9.entry p }, [])] v c) [d] [] m =
      .ok ([⟨name, a.place, a.part, true, [], [], d⟩],
        ⟨{ m.st.hears d with own := (m.st.hears d).own }, m.loc ++ [d], m.seen ++ [⟨[], d⟩], m.opened⟩) := by
  have hfit : (⟨[], []⟩ : Sending).fits { entry := Desc.K9.entry p } [] = true := by
    unfold Sending.fits
    rw [bat_items p]
    rfl
  cases v <;>
    simp [Part.steps, batPart, play, Step.tell, Step.hear, Step.stop, hfit, Except.bind, Except.map]

/-- K9's one round reads no column. -/
theorem bat_reads (p : Desc.K9.Where) (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (ds : List Fmt.Drawn) :
    readsOf chain ft stored tree [{ entry := Desc.K9.entry p }] ds = [] := by
  match ds with
  | [] => rfl
  | _ :: _ => rfl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.bat_items
#print axioms ProofFile.Honest.K9.draws_one
#print axioms ProofFile.Honest.K9.bat_play
#print axioms ProofFile.Honest.K9.bat_reads
