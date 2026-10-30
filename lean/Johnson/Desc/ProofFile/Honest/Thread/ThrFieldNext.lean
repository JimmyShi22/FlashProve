-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/ThrFieldNext.lean: the state of the prover's run (`Mid`,
Honest/Frame.lean) has a field `opened`: the columns opened so far. `Thread.Field`
(Honest/Thread/ThrField.lean) says what that field holds at a border of a thread. This file carries
it from a border to the next. No definition.

  1  `fieldFit_of_thr`   the three side conditions `FieldFit` of the law `FieldAt.step`
     (Honest/FieldLaw.lean) follow from the invariant `Thr`: two from its clause `Fit`, one from `Made`
  2  `Thread.field_next`   **the law at a thread**: from `Thr` and `Thread.Field` at border b, and
     `Thread.Moved` at the sub-protocol number b, `Thread.Field` holds at border b + 1, at the state
     after the play with the sub-protocol's columns taken in (`Mid.took`)
  3  `Thread.field_next_stepped`   the same from `Thread.Stepped`

It calls `drawsFit_length` (Honest/Law/Along.lean) and `declsTo_succ`
(Honest/Thread/MadeLaw.lean).

Limits.
  * The state at the next border is `y.2.took cols`, not `y.2`. `play` does not lengthen the field
    (`play_opened`, Honest/Gap.lean). A statement whose next state is `y.2` is not served.
  * `base` is a parameter. Nothing says what a run's own value is, or that `Thread.Field` holds at
    the first border.
  * Nothing here shows that the invariant holds at any state of a run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ThrField
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.ProofFile.Honest.FieldLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-! ## 1 The side conditions, from the invariant -/

variable (T : Thread Bk S Cl V W X Pb)

/-- The law's three side conditions hold where the invariant holds. -/
theorem fieldFit_of_thr {b : Nat} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    (hA : Thr T b k s m E) : FieldFit (declsTo T.bs b) T.front m E := by
  unfold Thr Thread.Fit Thread.Made at hA
  obtain ⟨-, hF, -, -, ⟨-, -, -, hT, -⟩, -, -⟩ := hA
  have hl := drawsFit_length _ _ hF
  rw [List.length_append] at hl
  unfold FieldFit
  refine ⟨?_, ?_, hT⟩
  · show T.ahead.length ≤ m.st.heard.length
    omega
  · rw [List.length_drop]
    show (declsTo T.bs b).length = m.st.heard.length - T.ahead.length
    omega

/-! ## 2 The law at a thread -/

/-- **`Thread.Field` is carried from a border to the next.** -/
theorem Thread.field_next {base : List OpenedColumn} {b : Nat} {blk : Block S Cl}
    (hblk : T.bs[b]? = some blk) {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hA : Thr T b k s m E) (hF : T.Field base b m E) (hM : T.Moved blk k m E ds y cols) :
    T.Field base (b + 1) (y.2.took cols) (E.add y.1) := by
  obtain ⟨hs, hl, hT⟩ := fieldFit_of_thr T hA
  obtain ⟨⟨l, -, hp⟩, hc⟩ := hM
  show FieldAt T.chain T.ft (declsTo T.bs (b + 1)) base T.front (y.2.took cols) (E.add y.1)
  rw [declsTo_succ hblk]
  exact FieldAt.step hF hT hs hl hp hc

/-- The same from an accepted step. -/
theorem Thread.field_next_stepped {base : List OpenedColumn} {b : Nat} {blk : Block S Cl}
    (hblk : T.bs[b]? = some blk) {k : Coins Bk} {s s' : S} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hA : Thr T b k s m E) (hF : T.Field base b m E)
    (hS : T.Stepped blk k s m E ds y cols s') :
    T.Field base (b + 1) (y.2.took cols) (E.add y.1) :=
  T.field_next hblk hA hF hS.1

end ProofFile.Honest

#print axioms ProofFile.Honest.fieldFit_of_thr
#print axioms ProofFile.Honest.Thread.field_next
#print axioms ProofFile.Honest.Thread.field_next_stepped
