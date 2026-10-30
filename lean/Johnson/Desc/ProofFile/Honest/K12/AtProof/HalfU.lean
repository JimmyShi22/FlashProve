-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/HalfU.lean: the prover's side of the proximity test on G_u
of the proof file's shared chain, made of a public part and of two things that a filling of the
honest prover (`OnlineProverParts`, Johnson/Desc/ProofFile/Honest/AtPure.lean) holds already: its reader of the
index and its encoded index's columns. For the field `OnlineProverParts.shared`. Definitions with code, and one
statement on public letters.

  `randAt`       the index committer's values of the item that the shared chain's parameters name:
                 the reader by which the chain's six other sides read them
  `jobRealU`     the job: `jobLocU` (JobsLocU.lean) at the public part's own letters: the sendings'
                 public data (`sendPub`, Members.lean), the place's numbers (`four`, Places.lean),
                 what goes out with o_u (`sentOf`, NearAtHead.lean), the kind K14's eight
                 sub-protocols (`Desc.K14.blocks`); the stored columns are the filling's, as words;
                 the vector of o_u is the sending's own text at the challenges heard (its last
                 argument is none). Nothing where one of the public letters is not made
  `realU`, `halfU`   the job as a `TestJob`; its pair of parts at the test's place
  `sixAt`        the chain's six other sides: `K14.sixOf`
                 (Johnson/Desc/ProofFile/Honest/K14/Six.lean), called as `nowSharedBy` calls it
  `withHalfU`    a filling with the pair behind its shared chain's other sides (`withShared`,
                 Doors.lean)
  `realU_bare`   the job's place, members and word on the fresh table are the bare job's (`bareU`,
                 Bare.lean)

A second text. `sixAt` is the text of `nowSharedBy`
(Johnson/Desc/ProofFile/Honest/AtPureWiderAt.lean, which is in no booked state of the library yet):
the same body; what parts: its name, the name of its first argument, and `TableKey` written short.

Limits. Nothing is played here, and nothing says that a sub-protocol accepts what the pair sends.
The state on entry is `doorUF`'s (DoorsByShape.lean): where its fold fails it falls back, without a
warning, on a state that is not shown to be the verifier's. The job reads the stored table's columns
at "LOC"'s positions; these are computed from the index.
`withHalfU`'s reader wt is a free letter: nothing holds it against the reader with which the
filling's six other sides were made, nor against the filling's columns; with two readers the test's
rows are not the sender's. Where `four`, `sendPub` or `Desc.K14.blocks` gives nothing, `halfU` is
the empty list and `withHalfU` returns the filling's own sides, without a word; where the library's
`withU` refuses, `sentOf` is the empty array, without a word.
Beneath it, through Members.lean: Johnson/Desc/ProofFile/Honest/SharedChainProverSides.lean, which is booked but
in no sealed library yet. The test on G_u alone. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.JobsLocU
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Bare
import Johnson.Desc.ProofFile.Honest.K14.Six

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (TableKey)
open ProofFile.Honest.K12.Light (ManyJob jobLocU sentOf)

variable {W₀ Tr X : Type}

/-- The index committer's values of the item that the shared chain's parameters name. -/
def randAt (P : Desc.K14.P14) (rc : IndexCommitterCoins) : TableRand := ⟨(rc P.item).pad, (rc P.item).tail⟩

/-- **The job at the test on G_u, at a public part.** wt: the reader of the index. enc: the encoded
index's columns, by the statement's item and the position. -/
def jobRealU (wt : W₀ → Weights) (enc : W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) (Z : Pub) :
    Option (ManyJob (Common W₀ IndexCommitterCoins TableKey) Unit) :=
  (four Z).bind fun F => (sendPub Z).bind fun A => (Desc.K14.blocks A.P).map fun bs =>
    jobLocU A F.U (sentOf A.P.S) bs
      (fun w rc i x => (enc w rc i x).map (·.map OnBytes.Slice.ofF))
      (fun w => wt w.w₀) (fun w => randAt A.P w.rc) none

/-- The same as a `TestJob`. -/
def realU (wt : W₀ → Weights) (enc : W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) (Z : Pub) :
    Option (TestJob (Common W₀ IndexCommitterCoins TableKey) Unit) :=
  (jobRealU wt enc Z).map (·.toRun.toTest)

/-- **The pair of parts at the test's place**; no side where the job is not made. -/
def halfU (wt : W₀ → Weights) (enc : W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) (Z : Pub) :
    List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit) :=
  (realU wt enc Z).toList.map proverSideOfProximityTest

/-- The shared chain's six other sides, or an error message. -/
def sixAt (wt : W₀ → Weights) (Z : Pub) :
    Except String (List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit)) :=
  (due? "the shared chain's own parameters" (p14At Z)).bind fun P =>
  (due? "the shared chain's place in the description" (onlineSharedChain Z)).bind fun s =>
    K14.sixOf P s.chain.blocksInOrder wt fun rc : IndexCommitterCoins => ⟨(rc P.item).pad, (rc P.item).tail⟩

/-- **A filling with the pair behind its shared chain's other sides.** wt: the filling's reader of
the index; the columns are the filling's own. -/
def withHalfU (P : OnlineProverParts W₀ IndexCommitterCoins Tr Unit X) (wt : Pub → W₀ → Weights) : OnlineProverParts W₀ IndexCommitterCoins Tr Unit X :=
  withShared P fun Z => halfU (wt Z) (P.enc Z) Z

/-- **The job's place, members and word on the fresh table are the bare job's.** -/
theorem realU_bare (wt : W₀ → Weights) (enc : W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F))
    (Z : Pub) (J : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit) (h : realU wt enc Z = some J) :
    ∃ J₀ : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit, bareU Z = some J₀ ∧ J.p = J₀.p ∧
      J.members = J₀.members ∧ J.fresh = J₀.fresh := by
  unfold realU jobRealU at h
  unfold bareU
  cases hF : four Z with
  | none => rw [hF] at h; cases h
  | some F =>
    cases hA : sendPub Z with
    | none => rw [hF, hA] at h; cases h
    | some A =>
      cases hb : Desc.K14.blocks A.P with
      | none => rw [hF, hA] at h; simp [hb] at h
      | some bs =>
        rw [hF, hA] at h
        simp only [Option.bind_some, hb, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨_, rfl, rfl, rfl, rfl⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.randAt
#print axioms ProofFile.Honest.K12.AtProof.jobRealU
#print axioms ProofFile.Honest.K12.AtProof.realU
#print axioms ProofFile.Honest.K12.AtProof.halfU
#print axioms ProofFile.Honest.K12.AtProof.sixAt
#print axioms ProofFile.Honest.K12.AtProof.withHalfU
#print axioms ProofFile.Honest.K12.AtProof.realU_bare
