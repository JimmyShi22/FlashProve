-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Eval/TwinAtOracle.lean: IT SERVES THE EVALUATION ALONE: NO THEOREM ON THE COMMITTER
IMPORTS IT. What is run of the committer (Johnson/Bind/Twin.lean) is `commit`: its text at the
format's own hash. What is proved of it speaks of the algorithm `twinID`
(Johnson/Bind/TwinAlgorithm.lean) at every hash function. Here the two meet at one hash function:
the one on bit strings that the format's realised oracle spells (`Run.oBits`, Run/OracleBits.lean).
  `commitO_oracle`: over the realised oracle the committer gives what it gives at the format's own
    hash.
  `evaluate_twinID_oBits`: the algorithm's value at that hash function is the ID that `commit`
    gives.
Both where `Fits S files` (Johnson/Bind/TwinDom.lean), of which the full size's shape and the small
stored example's are members. The three names live in the namespace `Bind.Twin`, beside what they
speak of, though the file serves the evaluation.
The chain from a run to the algorithm. The evaluating programs (with their steps; not all of them
are in this library) run the committer's steps at `Fmt.HF`, which is the format's own hash
(`Fmt.HF_eq`, Fmt/Rules5Fast.lean), and, for a whole table, at the fast encoder, which gives the
committer's own value at shapes with a ≤ 32 and l + r ≤ 2^a (`commitFastW_is_commitW`,
Johnson/Bind/TwinFastProof.lean). That value is `commit`'s, and by this file it is `twinID`'s at one
hash function. That a program with its prints computes the Lean term rests on a reading: no theorem
speaks of input and output; and on Lean's compiler and runtime, which the kernel does not check.
Calls alone: `commitW_dom`, `Fmt.HO_oracle`, `Fmt.size_H` (Fmt/Rules23Laws.lean),
`OnBytes.Tie.HO_oBits` (OnBytes/Tie/LinkPlain.lean), `evaluate_twinID`.
Limits. It ties what is run in Lean to a value of `twinID`, at the shape and table that ran. The
theorems on the committer stand at the full size's shape, where nothing has been run: the same Lean
definition, at another shape and table. Nothing on what the format's hash is,
nothing on an oracle that is sampled at random, and nothing on any program.

-/
import Johnson.Bind.TwinDom
import Johnson.Bind.TwinAlgorithm
import OnBytes.Tie.LinkPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

/-- The committer over an oracle that is a function, in the function's form of the hash. -/
theorem commitO_eq (O : ByteArray → ByteArray) (S : Shape) (files : List ByteArray) (T : Table) :
    commitO O S files T = commitW (m := Id) (Fmt.HO O) S files T := by
  have e : Fmt.HM (m := Id) O = Fmt.HO O := by
    funext number tree index start bytes
    exact Fmt.HM_id _ _ _ _ _ _
  unfold commitO
  rw [e]

/-- **Over the realised oracle the committer gives what it gives at the format's own hash.** -/
theorem commitO_oracle (S : Shape) (files : List ByteArray) (T : Table) (fits : Fits S files) :
    commitO Fmt.oracle S files T = commit S files T := by
  rw [commitO_eq]
  exact commitW_dom Fmt.formatHash (Fmt.HO Fmt.oracle) (fun n t i s b hd => Fmt.HO_oracle n t i s b hd)
    (fun n t i s b => Fmt.size_H n t i s b) S files T fits

/-- **The algorithm's value at the hash function that the realised oracle spells is the ID that is
run.** -/
theorem evaluate_twinID_oBits (S : Shape) (pol lay KL : ByteArray) (T : Table)
    (fits : Fits S [pol, lay, KL]) :
    (twinID S pol lay KL T).evaluate (_root_.Run.oBits ()) =
      _root_.Run.bytesToDig (commit S [pol, lay, KL] T).id := by
  rw [evaluate_twinID, commitO_eq, OnBytes.Tie.HO_oBits, ← commitO_eq,
    commitO_oracle S [pol, lay, KL] T fits]

end Bind.Twin

#print axioms Bind.Twin.commitO_eq
#print axioms Bind.Twin.commitO_oracle
#print axioms Bind.Twin.evaluate_twinID_oBits
