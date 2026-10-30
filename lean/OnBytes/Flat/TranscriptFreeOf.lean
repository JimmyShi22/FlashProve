-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/TranscriptFreeOf.lean: `TranscriptFree` (OnBytes/Flat/LinksFreeHead.lean) holds: one of
the seven statements from which that file has that the check of the head at two requests states the
same rounds.

`HTailF2.transcript` (OnBytes/Model/Tail.lean) runs the messages of the smallness test: two tests on
the state of that test, the test on the order of the samples, the draw of the matrix, the commitment
to two arrays, the lookup on the digits; before the third and behind the last it reads the number of
the next free slot. The request reaches the state of the smallness test through one field, the list
of tables (`funs`). By the program's text no routine of `transcript` reads that field; the draw of
the matrix and the last line hand it on as it is. So at two states that are equal in all but that
list every routine is one and the same, by unfolding, and what is returned is equal in all but that
list.

Main theorems: `fixedBefore_funs` (the test on the order of the samples does not read the list),
`drawMatrixF_rel` (the draw of the matrix), `transcriptFree : TranscriptFree`.

Not claimed: the other six statements. Nothing on a run on a view. That the two lists of tables are
alike is a premise of `TranscriptFree` and is not used: the statement holds at any two lists. For
proofs only; no module of the program imports this file.


-/
import OnBytes.Flat.LinksFreeHead

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model

/-- The test on the order of the samples does not read the list of tables. -/
theorem fixedBefore_funs (tl : HTailF2) (f' : Array HFun) :
    ({ tl with funs := f' } : HTailF2).fixedBeforeTheMatrixF = tl.fixedBeforeTheMatrixF := rfl

/-- **The draw of the matrix** at two states of the smallness test that are equal in all but the
list of tables: from one state both fail, or both return, with one state left and values that are
equal in all but that list. -/
theorem drawMatrixF_rel (f f' : Array HFun) (tl : HTailF2) (hf : tl.funs = f) :
    cmpS.Rel (TailAlike f f') tl.drawMatrixF ({ tl with funs := f' } : HTailF2).drawMatrixF := by
  unfold HTailF2.drawMatrixF
  dsimp only
  refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
  exact cmpS.pure' ⟨hf, rfl⟩

/-- **The messages of the smallness test** at two states that are equal in all but the list of
tables. -/
theorem transcriptFree : TranscriptFree := by
  intro f f' tl tl' _ h
  obtain ⟨hf, e⟩ := h
  subst e
  unfold HTailF2.transcript HTailF2.transcriptF
  rw [fixedBefore_funs]
  dsimp only
  refine cmpL.bind_same same_cmpL (by keeps) fun _ => ?_
  refine cmpL.bind_same same_cmpL (by keeps) fun _ => ?_
  refine cmpL.bind_same same_cmpL (by keeps) fun _ => ?_
  refine cmpL.bind_same same_cmpL (by keeps) fun _ => ?_
  refine cmpL.bind' (S := TailAlike f f') (by keeps)
    (sub_rel (by keeps) (drawMatrixF_rel f f' tl hf)) fun t t' ht => ?_
  obtain ⟨ht, e⟩ := ht
  subst e
  dsimp only
  refine cmpL.bind_same same_cmpL (by keeps) fun _ => ?_
  refine cmpL.bind_same same_cmpL (by keeps) fun _ => ?_
  refine cmpL.bind_same same_cmpL (by keeps) fun _ => ?_
  exact cmpL.pure' ⟨ht, rfl⟩

end OnBytes.Flat
