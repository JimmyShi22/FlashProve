-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TrAre.lean: THE LEDGER's ARRAYS, BUT FOR THE MARK "THE COMMITMENT IS RECEIVED", AS A READING,
and the relation "an open segment behind has this reading, and the book-keeping's, as they were in front". Definitions and small
lemmas.

  `tr F`        of a ledger: its arrays, each with the mark "the chain has received the array's commitment" struck
  `tr_core`     a ledger that has the eleven fields of `Core` (Johnson/Desc/First/K4/RunsCore.lean) has the reading
  `tr_taken`    noting that an array's commitment is received leaves the reading
  **`KeepsTr s s'`**   where a ledger and book-keeping are open at s', they are open at s, with the same readings `tr` and `lnk`
                       (Honest/K9/CrAre.lean)
  `keeps_reflT`, `keeps_transT`, `keeps_of_casesT`, `keeps_sameT`, `keeps_putsT`   the tools

One of nine files (Honest/K9/TrAre.lean, TrFl, TrWalk, TrK4, TrK5, TrK6, TrSeated, TrVia, TrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves the ledger's arrays, but for the mark
"the commitment is received" (`tr`), and what the batching's draw will test of the segment's book-keeping (`lnk`). They are the
nine files Honest/K9/CrAre.lean to CrLot.lean, carried over by program from the reading `cr` to the reading `tr`, name by name;
these in turn carry the library's own walk for the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files
Slots*.lean beside it).

Limits. Nothing is said here of any sub-protocol. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.CrAre

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Core)
open VerifiableInference.Desc.First (S)

/-- A ledger's arrays, each with the mark "the commitment is received" struck. -/
def tr (F : Fork) : Array HTree := F.trees.map fun X => { X with root := none }

theorem tr_core {F G : Fork} (h : Core F G) : tr G = tr F := by
  unfold tr
  rw [h.trees]

/-- Noting that the chain has received an array's commitment. -/
theorem tr_taken (F : Fork) (t w : ℕ) : tr (F.rootTaken t w) = tr F :=
  map_modify_same (fun X : HTree => ({ X with root := none } : HTree)) (fun X => { X with root := some w })
    (fun _ => rfl) F.trees t

/-- **Where a ledger and book-keeping are open behind, they are open in front, with the same two readings.** -/
def KeepsTr (s s' : S) : Prop :=
  ∀ G' L', s'.fork? = some G' → s'.link? = some L' →
    ∃ G L, s.fork? = some G ∧ s.link? = some L ∧ lnk L = lnk L' ∧ tr G' = tr G

theorem keeps_reflT (s : S) : KeepsTr s s := fun G L hG hL => ⟨G, L, hG, hL, rfl, rfl⟩

theorem keeps_transT (a b c : S) (h : KeepsTr a b) (k : KeepsTr b c) : KeepsTr a c := by
  intro G'' L'' hG hL
  obtain ⟨G', L', g1, l1, e1, e2⟩ := k G'' L'' hG hL
  obtain ⟨G, L, g0, l0, e3, e4⟩ := h G' L' g1 l1
  exact ⟨G, L, g0, l0, e3.trans e1, e2.trans e4⟩

theorem keeps_of_casesT {s s' : S}
    (h : ∀ G' L', s'.fork? = some G' → s'.link? = some L' →
      ∃ G L, s.fork? = some G ∧ s.link? = some L ∧ lnk L = lnk L' ∧ tr G' = tr G) : KeepsTr s s' := h

/-- The two readings of the state are left. -/
theorem keeps_sameT {s s' : S} (hf : s'.fork? = s.fork?) (hl : s'.link?.map lnk = s.link?.map lnk) :
    KeepsTr s s' := by
  refine keeps_of_casesT fun G' L' hG hL => ?_
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
theorem keeps_putsT {s u : S} {L0 L : LinkCtx} {F0 F : Fork} (hL : s.link? = some L0) (hF : s.fork? = some F0)
    (uL : u.link? = some L0) (uF : u.fork? = some F0) (el : lnk L = lnk L0) (ef : tr F = tr F0) :
    KeepsTr s ((u.putLink L).putFork F) := by
  obtain ⟨r1, r2⟩ := reads_puts u L0 F0 uL uF L F
  refine keeps_of_casesT fun G' L' hG hL' => ⟨F0, L0, hF, hL, ?_, ?_⟩
  · rw [← Option.some.inj (r1.symm.trans hL'), el]
  · rw [← Option.some.inj (r2.symm.trans hG), ef]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tr_core
#print axioms VerifiableInference.Desc.LinkJoin.tr_taken
#print axioms VerifiableInference.Desc.LinkJoin.keeps_reflT
#print axioms VerifiableInference.Desc.LinkJoin.keeps_transT
#print axioms VerifiableInference.Desc.LinkJoin.keeps_of_casesT
#print axioms VerifiableInference.Desc.LinkJoin.keeps_sameT
#print axioms VerifiableInference.Desc.LinkJoin.keeps_putsT
