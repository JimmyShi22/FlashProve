-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HasRowAtReads.lean: K01_law, rows
P.hasRow and G.wo at the reads' place's joined block (`k1Reads`, Johnson/IMR/K1Seat.lean: the
sending of the reads with the quiet step behind it). Two statements as Props by def, with their
proofs.

  `HasRowAtReads`, `WoBackAtReads`: the statements. `keepsRow_k1Quiet`, `keepsRow_k1Reads`: the
    quiet step and the joined block are members of `KeepsRow`.
  `hasRowAtReads`, `woBackAtReads`: **the proofs.**

Limits. As in HasRowAtLater.lean. K01_law is not proved by this. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.HasRowAtLater
import Johnson.IMR.K1Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Pub)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

/-- **ROW P.hasRow, at the reads' place.** -/
def HasRowAtReads : Prop :=
  ∀ (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ) (reads : Option (List ℕ)),
    KeepsHasRow (k1Reads Z G l X pr reads)

/-- **ROW G.wo, at the reads' place.** -/
def WoBackAtReads : Prop :=
  ∀ (Pp W : Type) (nR kC : ℕ) (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) (d : First.FillP1.PubData)
    (rw : Pp × S → W → First.FillP1.PileWit nR kC) (m : Nat) (x x' : Pp × S) (y y' : Strs) (w : W)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (k1Reads Z G l X pr reads).decide x.2 rs gs = .ok x'.2 →
      K13.Law.AgreeAt x.2.out.indexMasks (rw x' w) (rw x w) →
      First.FillP1.woAt d rw m x' y' w → First.FillP1.woAt d rw m x y w

/-- Where no block could be made the refuser stands, which never says yes. -/
theorem keepsRow_k1Quiet (G : ProofFile.Ground) (l : Nat) (X : LinkH) : KeepsRow (k1Quiet G l X) := by
  unfold k1Quiet
  dsimp only
  cases hq : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
  | none => exact fun s s' rs gs h => nomatch h
  | some q => exact keepsRow_readsQuietAt l X _ q hq

/-- **The reads' place's joined block.** -/
theorem keepsRow_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) : KeepsRow (k1Reads Z G l X pr reads) :=
  keepsRow_andThen _ _ _ (keepsRow_laterAt G.first (gpOf Z) l pr 1 reads) (keepsRow_k1Quiet G l X)

theorem hasRowAtReads : HasRowAtReads := fun Z G l X pr reads =>
  keepsHasRow_of (keepsRow_k1Reads Z G l X pr reads)

theorem woBackAtReads : WoBackAtReads :=
  fun _ _ _ _ Z G l X pr reads d rw m x x' y y' w rs gs h hA h0 =>
    wo_back (keepsRow_k1Reads Z G l X pr reads) d rw m x x' y y' w rs gs h hA h0

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.keepsRow_k1Quiet
#print axioms VerifiableInference.Desc.K1.keepsRow_k1Reads
#print axioms VerifiableInference.Desc.K1.hasRowAtReads
#print axioms VerifiableInference.Desc.K1.woBackAtReads
