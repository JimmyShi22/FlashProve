-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchStand.lean: the closing of a segment (K10): three clauses of the fields stand of this
folder's records on the senders (`FreshBySwitch`, `FreshByShared`, `TieBySwitch`, `TieByShared`), at a stand of any thread in
front of which no round has been heard.

  `step_valid`     the prover's input is one of the thread's valid inputs
  `step_heard`     as many challenges have been heard as the blocks in front have rounds
  **`step_heard_le`**  so no fewer than the blocks in front of an earlier border have: the clauses "N ≤ …", "fx ≤ …", "front ≤ …", at
                   the numbers 0 + roundsTo bs b' that the laws on the first chain's script take

By the invariant's own clauses (`Thr`, Honest/Thread/Thr.lean); `drawsFit_length` (Honest/Law/Along.lean); `roundsTo_mono`
(Honest/Thread/ScriptFit.lean).

Limits. Implications from a stand. That a stand is reached is not said.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.Shown
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.ProofFile.Honest.Thread.ScriptFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block OpenedColumn)

variable {S' Cl V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S' Cl V W X Pb}
  {Said : Nat → Coins Bk → Mid W X → Prop} {b : Nat} {blk : Block S' Cl} {k : Coins Bk} {s : S'} {m : Mid W X}
  {En : Env} {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn} {s' : S'}

/-- The prover's input is one of the thread's valid inputs. -/
theorem step_valid (St : StepAt T Said b blk k s m En ds y cols s') : T.valid m.st.input := by
  have hT := St.thr.1
  unfold Thr at hT
  exact hT.2.2.2.2.2.2

/-- As many challenges have been heard as the blocks in front have rounds. -/
theorem step_heard (ha : T.ahead = []) (St : StepAt T Said b blk k s m En ds y cols s') :
    m.st.heard.length = roundsTo T.bs b := by
  have hT := St.thr.1
  unfold Thr at hT
  have hF : drawsFit (T.ahead ++ declsTo T.bs b) m.st.heard = true := hT.2.1
  rw [ha, List.nil_append] at hF
  exact drawsFit_length _ _ hF

/-- **No fewer than the blocks in front of an earlier border have.** -/
theorem step_heard_le (ha : T.ahead = []) (St : StepAt T Said b blk k s m En ds y cols s') {b' : Nat} (hb : b' ≤ b) :
    0 + roundsTo T.bs b' ≤ m.st.heard.length := by
  rw [step_heard ha St, Nat.zero_add]
  exact roundsTo_mono T.bs b' b hb

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.step_valid
#print axioms ProofFile.Honest.K10.step_heard
#print axioms ProofFile.Honest.K10.step_heard_le
