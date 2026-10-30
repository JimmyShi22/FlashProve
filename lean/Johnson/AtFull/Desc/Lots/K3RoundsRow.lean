-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3RoundsRow.lean: THE LOT OF THE KIND "LOOKUP" (K3Lot.lot): ITS SECOND ROW:
EVERY BLOCK's DECLARED ROUNDS ARE THE TABLE's LIST AT THE WRITTEN NAME OF THE BLOCK's PLACE.
Joinings, and one light closed fact by the kernel.
  `rounds_rep`: the eight closed facts (K3RoundsC.lean, K3RoundsD.lean), by the link's sort.
  `k3_lists_written`: under the first row's hypotheses (`Reads Z`, K3Row.lean): each block stands
    at a lookup's place and has the list at `spotW i d`.
  `name_at_full`, `name_at`: the written name at a place (`ProofFile.Sk.Full.nameW`,
    Johnson/Desc/ProofFile/Law/Skel/Full/Names.lean) is `spotW i d` at the fifty places.
    `name_at_control`: with calls and digits exchanged: at none.
  `k3_lists_at`: **∀ b ∈ (K3Lot.lot Z).blocks G, Lst listAt (nameW b.place) b.rounds**: the row
    that `ProofFile.Sk.Full.rows_by_place` takes, at this lot.
  `k3_lists_public`, `k3_lists_scope`: the same under `ReadsEq Z` with the reader's return, and
    under `ReadsLeft Z` with the four common premises.
WHERE THE WEIGHT GOES: as at the first row: `Reads Z` is a premise; the calls' tables' cost stands
in the reader's return. WHICH WRITTEN NAMES: the hypotheses stand at Johnson.G.proofCodesWritten and
ReqLit.shapeFull, at Z.first (through `beforeW`).
Limits. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3RoundsLaw
import Johnson.AtFull.Desc.Lots.K3RoundsC
import Johnson.AtFull.Desc.Lots.K3RoundsD
import Johnson.AtFull.Desc.Lots.K3RowScope
import Johnson.Desc.ProofFile.Law.Skel.SkelLists
import Johnson.Desc.ProofFile.Law.Skel.Full.Names

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.Desc

theorem rounds_rep (i : Nat) (d : Bool) :
    (coreW (sortOf i) d).rounds = Johnson.AtFull.Rounds.listAt (repW (sortOf i) d) := by
  unfold sortOf
  split
  · cases d
    · exact rounds_c3
    · exact rounds_d3
  · split
    · cases d
      · exact rounds_c1
      · exact rounds_d1
    · split
      · cases d
        · exact rounds_c0
        · exact rounds_d0
      · cases d
        · exact rounds_c2
        · exact rounds_d2

/-- **EACH BLOCK: ITS PLACE, AND THE TABLE's LIST AT THE WRITTEN NAME.** -/
theorem k3_lists_written {Z : ProofFile.Pub} (R : Reads Z) (G : ProofFile.Ground)
    {b : Block First.S ProofFile.Cl} (hb : b ∈ (K3Lot.lot Z).blocks G) :
    ∃ i < 25, ∃ d, b.place = ⟨1, some i, pieceW i d, .K3⟩ ∧
      b.rounds = Johnson.AtFull.Rounds.listAt (spotW i d) := by
  obtain ⟨i, hi, d, hp, hr⟩ := block_at R G hb
  exact ⟨i, hi, d, hp, hr.trans ((rounds_rep i d).trans (lists_same hi d).symm)⟩

def nameB (f : Bool → Bool) (i : Nat) (d : Bool) : Bool :=
  ProofFile.Sk.Full.nameW ⟨1, some i, pieceW i d, .K3⟩ == spotW i (f d)

set_option maxRecDepth 1000000 in
theorem name_at_full :
    ((List.range 25).all fun i => [false, true].all fun d => nameB id i d) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with calls and digits exchanged: at none. -/
theorem name_at_control :
    ((List.range 25).any fun i => [false, true].any fun d => nameB not i d) = false := by
  decide +kernel

theorem name_at {i : Nat} (hi : i < 25) (d : Bool) :
    ProofFile.Sk.Full.nameW ⟨1, some i, pieceW i d, .K3⟩ = spotW i d :=
  beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 name_at_full i (List.mem_range.2 hi)) d
    (by cases d <;> simp))

/-- **THE LOT's SECOND ROW.** -/
theorem k3_lists_at {Z : ProofFile.Pub} (R : Reads Z) (G : ProofFile.Ground) :
    ∀ b ∈ (K3Lot.lot Z).blocks G,
      ProofFile.Sk.Lst Johnson.AtFull.Rounds.listAt (ProofFile.Sk.Full.nameW b.place) b.rounds := by
  intro b hb
  obtain ⟨i, hi, d, hp, hr⟩ := k3_lists_written R G hb
  rw [hp, name_at hi d]
  exact Or.inr hr

/-- The same where `publicOf` returned. -/
theorem k3_lists_public {Z : ProofFile.Pub} {pol KL : ByteArray} {lay : Option ByteArray}
    (h : publicOf pol KL lay = .ok Z.p.X) (R : ReadsEq Z) (G : ProofFile.Ground) :
    ∀ b ∈ (K3Lot.lot Z).blocks G,
      ProofFile.Sk.Lst Johnson.AtFull.Rounds.listAt (ProofFile.Sk.Full.nameW b.place) b.rounds :=
  k3_lists_at (reads_of_public h R) G

/-- The same under the four common premises. -/
theorem k3_lists_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G₀ : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (R : ReadsLeft Z) (G : ProofFile.Ground) :
    ∀ b ∈ (K3Lot.lot Z).blocks G,
      ProofFile.Sk.Lst Johnson.AtFull.Rounds.listAt (ProofFile.Sk.Full.nameW b.place) b.rounds :=
  k3_lists_public (public_of_plain hZ hG) (readsEq_of_scope hS hR (public_of_plain hZ hG) R) G

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.rounds_rep
#print axioms Johnson.AtFull.Lots.K3.k3_lists_written
#print axioms Johnson.AtFull.Lots.K3.name_at_full
#print axioms Johnson.AtFull.Lots.K3.name_at_control
#print axioms Johnson.AtFull.Lots.K3.name_at
#print axioms Johnson.AtFull.Lots.K3.k3_lists_at
#print axioms Johnson.AtFull.Lots.K3.k3_lists_public
#print axioms Johnson.AtFull.Lots.K3.k3_lists_scope
