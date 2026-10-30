-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofBack/Back.lean: the proof file's back at the full size: at what the planner and
`sendsOf` have made (m : `Johnson.G.OfPlan.Made`), UNDER EQUATIONS ON m, `Johnson.G.OfPlan.declPOf`
and `ProofFile.toldOf` return, at written values; also at `ProofFile.Law.blankM m`.

Statements.
  **`declPOf_written`**, **`toldOf_written`**: from EIGHT equations on m: (hz) the sized proof is
    the written one; (hp) the proof file's sendings are the written ones; (e0, e1, e2) the three
    chains' plans have the written rounds' entries as their rounds; (o0, o1, o2) each has as many
    entries as rounds. `declPOf m` returns the 136 written declared rounds along the written runs
    (Johnson/AtFull/ProofBack/DeclWritten.lean); `toldOf m` returns the three chains' trees with
    their tenants (Johnson/AtFull/ProofBack/Told.lean).
  `toldOf_of`: general: `toldOf`'s value from its three lines' values.
  `declPOf_blank`, `toldOf_blank`: `blankM` turns a field that neither routine reads: by `rfl`.
  **`declPOf_at_fields`**, **`toldOf_at_fields`**: the same two values at `blankM m`, from ELEVEN
    equations: (hz), (hp); (p0, p1, p2) m's three chains' plans are three plans A, B, C; and the six
    on A, B, C alone.

Limits. The full size alone. THE EQUATIONS ARE PREMISES: this file pays none of them. That a value m
is made at any public files is not said here. No closed fact of its own and so no negative test:
joinings of the folder's other four files. Nothing on soundness. On hiding nothing.

-/
import Johnson.AtFull.ProofBack.DeclWritten
import Johnson.AtFull.ProofBack.Told
import Johnson.Desc.ProofFile.Law.PlainIsMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofBack
open OnBytes OnBytes.Params Johnson.G Johnson.G.OfPlan Johnson.G.Runs Johnson.Unfolds
open VerifiableInference.PlanWritten (proofSizedFull declRecsFull)

variable {m : Made}

/-- **`declPOf m` returns the written declared rounds**, from eight equations on m. -/
theorem declPOf_written (hz : m.p.chains.made.sized.proof = proofSizedFull)
    (hp : m.proof = proofSendsFull)
    (e0 : m.p.chains.proof.first.given.plan.rounds = es0)
    (o0 : m.p.chains.proof.first.given.plan.entries.length -
      m.p.chains.proof.first.given.plan.rounds.length = 0)
    (e1 : m.p.chains.proof.shared.given.plan.rounds = es1)
    (o1 : m.p.chains.proof.shared.given.plan.entries.length -
      m.p.chains.proof.shared.given.plan.rounds.length = 0)
    (e2 : m.p.chains.proof.second.given.plan.rounds = es2)
    (o2 : m.p.chains.proof.second.given.plan.entries.length -
      m.p.chains.proof.second.given.plan.rounds.length = 0) :
    declPOf m = .ok (unrunG declRecsFull dryProofRunsFull0, unrunG declRecsFull dryProofRunsFull1,
      unrunG declRecsFull dryProofRunsFull2) := by
  unfold declPOf
  rw [hz, hp]
  exact fileOf_runs e0 o0 e1 o1 e2 o2

/-- `toldOf`'s value, from its three lines' values. -/
theorem toldOf_of {a b c : List ProofFile.Root}
    (h0 : ProofFile.toldChain "the tenants, first chain" m.proof.1
      m.p.chains.proof.first.given.plan [] none = .ok a)
    (h1 : ProofFile.toldChain "the tenants, shared chain" m.proof.2.1
      m.p.chains.proof.shared.given.plan
      (ownMasks m.proof.2.1.codes m.p.chains.made.sized.proof.batch.shape
        m.p.chains.proof.shared.given.plan.rounds)
      (m.p.chains.made.sized.proof.batch.shape.testOmega.head?.map fun st =>
        foldMaskNotice (ioppFoldShape st {})) = .ok b)
    (h2 : ProofFile.toldChain "the tenants, second chain" m.proof.2.2
      m.p.chains.proof.second.given.plan [] none = .ok c) :
    ProofFile.toldOf m = .ok (a, b, c) := by
  unfold ProofFile.toldOf
  simp only [h0, h1, h2, bind, Except.bind, pure, Except.pure]

/-- **`toldOf m` returns the three chains' trees with their tenants**, from the same eight. -/
theorem toldOf_written (hz : m.p.chains.made.sized.proof = proofSizedFull)
    (hp : m.proof = proofSendsFull)
    (e0 : m.p.chains.proof.first.given.plan.rounds = es0)
    (o0 : m.p.chains.proof.first.given.plan.entries.length -
      m.p.chains.proof.first.given.plan.rounds.length = 0)
    (e1 : m.p.chains.proof.shared.given.plan.rounds = es1)
    (o1 : m.p.chains.proof.shared.given.plan.entries.length -
      m.p.chains.proof.shared.given.plan.rounds.length = 0)
    (e2 : m.p.chains.proof.second.given.plan.rounds = es2)
    (o2 : m.p.chains.proof.second.given.plan.entries.length -
      m.p.chains.proof.second.given.plan.rounds.length = 0) :
    ProofFile.toldOf m =
      .ok (mineW tl0 extra0 none, mineW tl1 extra1 maskW, mineW tl2 extra2 none) := by
  refine toldOf_of ?_ ?_ ?_
  · rw [hp]
    exact told0 e0 o0 _
  · rw [hp, hz, e1]
    exact told1 e1 o1 _
  · rw [hp]
    exact told2 e2 o2 _

/-- `blankM` turns a field that `declPOf` does not read. -/
theorem declPOf_blank (m : Made) : declPOf (ProofFile.Law.blankM m) = declPOf m := rfl

/-- `blankM` turns a field that `toldOf` does not read. -/
theorem toldOf_blank (m : Made) : ProofFile.toldOf (ProofFile.Law.blankM m) = ProofFile.toldOf m := rfl

variable {A B C : Fmt.Plan}

/-- **`declPOf` at `blankM m`**, from five equations on m and six on the three plans. -/
theorem declPOf_at_fields (hz : m.p.chains.made.sized.proof = proofSizedFull)
    (hp : m.proof = proofSendsFull) (p0 : m.p.chains.proof.first.given.plan = A)
    (p1 : m.p.chains.proof.shared.given.plan = B) (p2 : m.p.chains.proof.second.given.plan = C)
    (e0 : A.rounds = es0) (o0 : A.entries.length - A.rounds.length = 0)
    (e1 : B.rounds = es1) (o1 : B.entries.length - B.rounds.length = 0)
    (e2 : C.rounds = es2) (o2 : C.entries.length - C.rounds.length = 0) :
    declPOf (ProofFile.Law.blankM m) =
      .ok (unrunG declRecsFull dryProofRunsFull0, unrunG declRecsFull dryProofRunsFull1,
        unrunG declRecsFull dryProofRunsFull2) := by
  subst p0 p1 p2
  rw [declPOf_blank]
  exact declPOf_written hz hp e0 o0 e1 o1 e2 o2

/-- **`toldOf` at `blankM m`**, from the same eleven. -/
theorem toldOf_at_fields (hz : m.p.chains.made.sized.proof = proofSizedFull)
    (hp : m.proof = proofSendsFull) (p0 : m.p.chains.proof.first.given.plan = A)
    (p1 : m.p.chains.proof.shared.given.plan = B) (p2 : m.p.chains.proof.second.given.plan = C)
    (e0 : A.rounds = es0) (o0 : A.entries.length - A.rounds.length = 0)
    (e1 : B.rounds = es1) (o1 : B.entries.length - B.rounds.length = 0)
    (e2 : C.rounds = es2) (o2 : C.entries.length - C.rounds.length = 0) :
    ProofFile.toldOf (ProofFile.Law.blankM m) =
      .ok (mineW tl0 extra0 none, mineW tl1 extra1 maskW, mineW tl2 extra2 none) := by
  subst p0 p1 p2
  rw [toldOf_blank]
  exact toldOf_written hz hp e0 o0 e1 o1 e2 o2

end Johnson.AtFull.ProofBack

#print axioms Johnson.AtFull.ProofBack.declPOf_written
#print axioms Johnson.AtFull.ProofBack.toldOf_of
#print axioms Johnson.AtFull.ProofBack.toldOf_written
#print axioms Johnson.AtFull.ProofBack.declPOf_blank
#print axioms Johnson.AtFull.ProofBack.toldOf_blank
#print axioms Johnson.AtFull.ProofBack.declPOf_at_fields
#print axioms Johnson.AtFull.ProofBack.toldOf_at_fields
