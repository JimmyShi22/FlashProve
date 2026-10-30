-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TiedAtErr.lean: KIND-FREE: A TIE GOES UP IN THE ERRORS: what is tied to the table of joints at a piece (TiedAt, Johnson/Desc/Sound/ChainOfPromises.lean) is tied at the same piece with
greater errors: by goodIn_err (Johnson/Desc/Sound/GoodInErr.lean); the other seven clauses of TiedAt read no error. WHY: the maker's rests lay THE CAP at every piece (Err.cap 128), not a kind's own errors: a kind's law at its own errors reaches
the description's piece by this lemma and «the kind's errors are at most the cap».
  tiedAt_err
Nothing on soundness.
-/
import Johnson.Desc.Sound.ChainOfPromises
import Johnson.Desc.Sound.GoodInErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open _root_.Iop (Err)
open VerifiableInference.Desc.First (ModelPart Meaning Numbers)

/-- **A tie goes up in the errors.** -/
theorem tiedAt_err {A P Cl W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (k : ℕ) (q : Piece C Fr A Cl W)
    (ε : Err (uLT C q.ds)) (h : Err.le q.err ε) (t : TiedAt N Mg links ps get k q) :
    TiedAt N Mg links ps get k ({ q with err := ε } : Piece C Fr A Cl W) := by
  obtain ⟨o, o', R, R', g, t1, t2, t3, t4, t5, t6, t7⟩ := t
  exact ⟨o, o', R, R', goodIn_err q ε h o o' R R' g, t1, t2, t3, t4, t5, t6, t7⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.tiedAt_err
