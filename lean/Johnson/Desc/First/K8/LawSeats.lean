-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawSeats.lean: THE SMALLNESS TEST, ITS FIRST HALF: "FIXED BEFORE THE DRAW":
THE TEST ON THE PLAN TIED TO THE MESSAGES THAT THE CALLER READS.

Johnson/Desc/First/K8/LawBefore.lean has, at the plan: every message that the kind's block names in
`before` is sent strictly in front of the round of the draw. What a caller of the proved block owes
to spend that (`CallerAt`) gives each of the caller's oracle messages a number, AND THAT NUMBER IS
FREE DATA THERE: no law ties it to the message of the file. At the letters of
Johnson/Desc/First/K8/LawAtFrame.lean it is not free: a member's word is read off the frame's
strings AT THE TREE THAT seat' NAMES, so the number to give it is that tree's.
  `rootsIn`, `sendRound_lt`, `rootsIn_take_mono`: on numbers: the message number n is among the
    trees that the rounds up to the one that sends it send.
  `named_below`: from the file's one test on the plan: every message that the block names has a
    number below the number of trees that the first chain's rounds in front of the block's round
    send.
  `frameCallerAt`: a value of `CallerAt` at the caller over the frame's own oracle messages: a
    member's number := the number of the tree off which its word is read. ONE PREMISE: every such
    tree is named by the block.
  `seats_below`: so the premise of `frameReads` on the seats (every named tree is sent in front of
    the block's stretch), under which its words pass the block unturned, is PAID by the file's one
    test on the plan, where the stretch's base is that number of trees.
Definitions, statements and proofs.
Limits. A tree's number is taken through the file; the block's field `before` counts in the first
chain's order of sending: the two agree because a description's first chain's trees come first
(`FileDescription.oracleAt`, Johnson/Desc/Msg.lean): read, not proved here. THAT THE STRETCH'S BASE IS THAT
NUMBER OF TREES is the tiling's to say. `frameCallerAt` takes ALL members as read (`dep` := all).
STILL OWED: that the arrays which the matrix multiplies LIE IN the tenants that seat' names (Θ and
rdm are letters); whose sample's answers the round between carries.

-/
import Johnson.Desc.First.K8.LawAtFrame
import Johnson.Desc.First.K8.LawPlaced

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- The number of trees that a list of declared rounds sends. -/
def rootsIn (ds : List Fmt.DeclaredRound) : Nat := (ds.map (·.entry.roots)).sum

/-- The message number n is among those that the rounds up to the one that sends it send. -/
theorem sendRound_lt : ∀ (ds : List Fmt.DeclaredRound) (n i : Nat), sendRound ds n = some i →
    n < rootsIn (ds.take (i + 1))
  | [], _, _, h => by simp [sendRound] at h
  | r :: l, n, i, h => by
    unfold sendRound at h
    by_cases hn : n < r.entry.roots
    · rw [if_pos hn] at h
      obtain rfl : 0 = i := by simpa using h
      simpa [rootsIn] using hn
    · rw [if_neg hn] at h
      cases hs : sendRound l (n - r.entry.roots) with
      | none => simp [hs] at h
      | some j =>
        rw [hs] at h
        obtain rfl : j + 1 = i := by simpa using h
        have h1 := sendRound_lt l _ j hs
        simp only [List.take_succ_cons, rootsIn, List.map_cons, List.sum_cons] at h1 ⊢
        omega

theorem rootsIn_take_mono : ∀ (ds : List Fmt.DeclaredRound) (a b : Nat), a ≤ b →
    rootsIn (ds.take a) ≤ rootsIn (ds.take b)
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => by simp [rootsIn]
  | _ :: _, _ + 1, 0, h => absurd h (by omega)
  | r :: l, a + 1, b + 1, h => by
    have h1 := rootsIn_take_mono l a b (by omega)
    simp only [List.take_succ_cons, rootsIn, List.map_cons, List.sum_cons] at h1 ⊢
    omega

end VerifiableInference.Desc

namespace VerifiableInference.Desc.First.K8

/-- **From the file's one test on the plan**: every message that the kind's block names has a number
below the number of trees that the first chain's rounds in front of the block's round send. -/
theorem named_below {Xi : Type} (F : FileDescription Xi) {seat : Seat F.S₁} {p : Par} {b : Block F.S₁ F.Cl}
    (h : Like seat p b) (pre post : List (Block F.S₁ F.Cl))
    (hflat : F.first.blocksInOrder = pre ++ b :: post)
    (hF : F.planOk = true) (n : Nat) (hn : n ∈ p.matsIn ++ p.readsIn) :
    n < rootsIn (F.roundsDeclaredByBlocks.1.take (roundsIn pre)) := by
  obtain ⟨i, h1, h2⟩ := file_before_draw_like F h pre post hflat hF n hn
  exact lt_of_lt_of_le (sendRound_lt _ _ _ h1) (rootsIn_take_mono _ _ _ h2)

section
open Cb Cb.Pv.Tail OnBytes.Model KObj Johnson.Pack VerifiableInference.Desc.Sound

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ)
  (tl0 : HTailF2) (Θ : TLetters Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl0))
  (rdm : (sigOf cs l).Msg → Θ.M) (p : Par)

/-- **What a caller owes to spend the test on the plan, at the caller over the frame's own oracle
messages**: a member's number is THE NUMBER OF THE TREE OFF WHICH ITS WORD IS READ. One premise:
every such tree is named by the block. -/
def frameCallerAt (hnamed : ∀ i, (seat' i).1 ∈ p.matsIn ++ p.readsIn) :
    CallerAt p (tailCallerOf (OnBytes.Tie.Pv.Tail.sizeOf tl0) Θ (sigOf cs l) rdm) where
  dep := fun _ => True
  no := fun i => (seat' i).1
  sym_dep := fun m m' h => by
    have e : m = m' := funext fun a => h a trivial
    rw [e]
  tab_dep := fun m m' h => by
    have e : m = m' := funext fun a => h a trivial
    rw [e]
  named := fun i _ => hnamed i

/-- **So the premise of `frameReads` on the seats is paid by the file's one test on the plan**,
where the stretch's base is the number of trees that the first chain's rounds in front of it send.
-/
theorem seats_below {Xi : Type} (F : FileDescription Xi) {seat : Seat F.S₁} {b : Block F.S₁ F.Cl}
    (h : Like seat p b) (pre post : List (Block F.S₁ F.Cl))
    (hflat : F.first.blocksInOrder = pre ++ b :: post)
    (hF : F.planOk = true) (hnamed : ∀ i, (seat' i).1 ∈ p.matsIn ++ p.readsIn) (i : Fin l.length) :
    (seat' i).1 < rootsIn (F.roundsDeclaredByBlocks.1.take (roundsIn pre)) :=
  named_below F h pre post hflat hF _ (hnamed i)

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.frameCallerAt
#print axioms VerifiableInference.Desc.First.K8.seats_below
#print axioms VerifiableInference.Desc.First.K8.named_below
