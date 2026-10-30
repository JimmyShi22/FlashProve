-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/CrAre.lean: WHAT THE BATCHING's DRAW WILL TEST OF THE LEDGER AND OF THE SEGMENT's BOOK-KEEPING,
AS TWO READINGS, and the relation "an open segment behind has these two readings as they were in front". Definitions and small
lemmas.

  `cr F`        of a ledger: the column weights of every virtual row of every array; the coefficients on the slots; the
                constant; the number of claims added; the mark "the batching element is drawn"; the mark "the one equation has
                been made"
  `lnk L`       of a segment's book-keeping: the mark "the draw has run"; the list of arrays; the segment's number
  `cr_core`     a ledger that has the eleven fields of `Core` (Johnson/Desc/First/K4/RunsCore.lean) has the reading
  `cr_taken`    noting that an array's commitment is received leaves the reading
  **`KeepsCr s s'`**   where a ledger and book-keeping are open at s', they are open at s, with the same two readings
  `keeps_reflC`, `keeps_transC`, `keeps_of_casesC`, `keeps_sameC`, `keeps_putsC`   the tools

One of nine files (Honest/K9/CrAre.lean, CrFl, CrWalk, CrK4, CrK5, CrK6, CrSeated, CrVia, CrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves what the batching's draw will test of the
ledger (`cr`) and of the segment's book-keeping (`lnk`). The walk through each sub-protocol's text is the library's own walk for
the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files Slots*.lean beside it), carried over by program
to the reading `cr`, name by name, and righted by hand where the ground fact is another.

Limits. Nothing is said here of any sub-protocol. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.First.K4.RunsCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Core)
open VerifiableInference.Desc.First (S)

/-- What the batching's draw will test of a ledger. -/
def cr (F : Fork) : Array (Array (Array E)) × Array E × E × ℕ × Bool × Bool :=
  (F.trees.map fun X => X.rows.map (·.L), F.LS, F.c0, F.nClaim, F.thetaDrawnF, F.doorShutF)

/-- What it will test of a segment's book-keeping, but for the moments; and the segment's number. -/
def lnk (L : LinkCtx) : Bool × Tail2 × ℕ := (L.handed, L.list, L.link)

theorem cr_core {F G : Fork} (h : Core F G) : cr G = cr F := by
  unfold cr
  rw [h.trees, h.LS, h.c0, h.nClaim, h.thetaDrawnF, h.doorShutF]

/-- A change of one member of an array that a reader does not see. -/
theorem map_modify_same {α β : Type} (g : α → β) (f : α → α) (hf : ∀ x, g (f x) = g x) (a : Array α) (t : ℕ) :
    (a.modify t f).map g = a.map g := by
  refine Array.ext (by simp) fun i h1 h2 => ?_
  simp only [Array.getElem_map, Array.getElem_modify]
  split
  · exact hf _
  · rfl

/-- Noting that the chain has received an array's commitment. -/
theorem cr_taken (F : Fork) (t w : ℕ) : cr (F.rootTaken t w) = cr F := by
  have e : (F.rootTaken t w).trees.map (fun X => X.rows.map (·.L)) = F.trees.map fun X => X.rows.map (·.L) :=
    map_modify_same (fun X : HTree => X.rows.map (·.L)) (fun X => { X with root := some w }) (fun _ => rfl) F.trees t
  unfold cr
  rw [e]
  rfl

/-- **Where a ledger and book-keeping are open behind, they are open in front, with the same two readings.** -/
def KeepsCr (s s' : S) : Prop :=
  ∀ G' L', s'.fork? = some G' → s'.link? = some L' →
    ∃ G L, s.fork? = some G ∧ s.link? = some L ∧ lnk L = lnk L' ∧ cr G' = cr G

theorem keeps_reflC (s : S) : KeepsCr s s := fun G L hG hL => ⟨G, L, hG, hL, rfl, rfl⟩

theorem keeps_transC (a b c : S) (h : KeepsCr a b) (k : KeepsCr b c) : KeepsCr a c := by
  intro G'' L'' hG hL
  obtain ⟨G', L', g1, l1, e1, e2⟩ := k G'' L'' hG hL
  obtain ⟨G, L, g0, l0, e3, e4⟩ := h G' L' g1 l1
  exact ⟨G, L, g0, l0, e3.trans e1, e2.trans e4⟩

theorem keeps_of_casesC {s s' : S}
    (h : ∀ G' L', s'.fork? = some G' → s'.link? = some L' →
      ∃ G L, s.fork? = some G ∧ s.link? = some L ∧ lnk L = lnk L' ∧ cr G' = cr G) : KeepsCr s s' := h

/-- The two readings of the state are left. -/
theorem keeps_sameC {s s' : S} (hf : s'.fork? = s.fork?) (hl : s'.link?.map lnk = s.link?.map lnk) :
    KeepsCr s s' := by
  refine keeps_of_casesC fun G' L' hG hL => ?_
  rw [hL] at hl
  cases e : s.link? with
  | none =>
    rw [e] at hl
    exact nomatch hl
  | some L =>
    rw [e] at hl
    exact ⟨G', L, hf ▸ hG, rfl, (Option.some.inj hl).symm, rfl⟩

/-- A writing of book-keeping and of a ledger with the same readings. u: any state with s's two readings (what a kind
lays back beside them). -/
theorem keeps_putsC {s u : S} {L0 L : LinkCtx} {F0 F : Fork} (hL : s.link? = some L0) (hF : s.fork? = some F0)
    (uL : u.link? = some L0) (uF : u.fork? = some F0) (el : lnk L = lnk L0) (ef : cr F = cr F0) :
    KeepsCr s ((u.putLink L).putFork F) := by
  obtain ⟨r1, r2⟩ := reads_puts u L0 F0 uL uF L F
  refine keeps_of_casesC fun G' L' hG hL' => ⟨F0, L0, hF, hL, ?_, ?_⟩
  · rw [← Option.some.inj (r1.symm.trans hL'), el]
  · rw [← Option.some.inj (r2.symm.trans hG), ef]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.cr_core
#print axioms VerifiableInference.Desc.LinkJoin.map_modify_same
#print axioms VerifiableInference.Desc.LinkJoin.cr_taken
#print axioms VerifiableInference.Desc.LinkJoin.keeps_reflC
#print axioms VerifiableInference.Desc.LinkJoin.keeps_transC
#print axioms VerifiableInference.Desc.LinkJoin.keeps_of_casesC
#print axioms VerifiableInference.Desc.LinkJoin.keeps_sameC
#print axioms VerifiableInference.Desc.LinkJoin.keeps_putsC
