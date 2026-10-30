-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/CarriesFoK4.lean: THE THREE FRAME's LAWS OF K4's BLOCK IN THESE
LETTERS: `Block.Steps`, `Block.RunsStep`, `Block.AfterStep` (Johnson/Desc/Sound/FoldSteps.lean)
at the relation `CarriesFo S.fork? hd` (Johnson/Desc/First/LedgerAtFo.lean). Statements and proofs:
each is the law of Johnson/Desc/First/K4/CarriesAtS.lean or RunsAtC.lean, which are typed unfolded:
LEAN TAKES THE ONE FOR THE OTHER BY UNFOLDING ALONE. FRAME's LAWS: no error term; nothing on
soundness.

  `carried_iff`: `Carried hd s s'` is `CarriesFo S.fork? hd s s'`.
  `k4_stepsFo`, `k4_runsFo`, `k4_afterFo`: of `blockAtS p`, at every reading hd that reads nothing
    that K4 writes (`KeepsIn hd`). `k4C_stepsFo`, `k4C_runsFo`, `k4C_afterFo`: of `blockAtC p`.
  `k4_look`, `k4_digits`: `(blockAtS p).RunsStep (CarriesFo S.fork? hd)` at the two readings at
    which the premise `KindsCarry.k4` is wanted: `S.lookHeard?` and the digits'
    lookup's, written out (`fun s => s.tl?.bind (·.heard)`).

Limits. As CarriesAtS.lean's: NOTHING HERE SHOWS THAT ANY DECISION OR RUN OF THE BLOCK RETURNS
ANYWHERE. `KindsCarry` IS NOT IMPORTED: that `k4_look` and `k4_digits` have the type of its field k4
is by reading (Johnson/Desc/First/K9x/RunsOfKinds.lean [not in this library], line 94,
with its abbreviation CF, K9x/ReadingsAtK9.lean:78). Its own joint for the digits wants the reading
under the name `heardD`, a plain definition with this body (that file, :34): equal by unfolding
that one name, so `exact` should take `k4_digits` there; a rewriting at `heardD` will not see it. IT
STANDS ON SIX OTHER FILES, by its import of LedgerAtFo.lean:
Johnson/Desc/First/LedgerAtFo.lean, StateLedger.lean, Johnson/Desc/Sound/FoldSteps.lean,
FoldHeard.lean, FoldStepsProofs.lean and FoldHeardProofs.lean;
of these it names `Block.Steps`, `Block.RunsStep`, `Block.AfterStep` and `CarriesFo` alone.


-/
import Johnson.Desc.First.K4.RunsAtC
import Johnson.Desc.First.LedgerAtFo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block CarriesFo)
open VerifiableInference.Desc.First (S)

/-- The relation of CarriesAtS.lean is `CarriesFo` (LedgerAtFo.lean), unfolded. -/
theorem carried_iff (hd : S → Option Forest.Heard) (s s' : S) :
    Carried hd s s' ↔ CarriesFo S.fork? hd s s' := Iff.rfl

/-- The decision of K4's block at the carried record carries. -/
theorem k4_stepsFo {hd : S → Option Forest.Heard} (H : KeepsIn hd) (p : Par) :
    (blockAtS p).Steps (CarriesFo S.fork? hd) := k4_steps H p

/-- Every run of claims of K4's block at the carried record carries. -/
theorem k4_runsFo {hd : S → Option Forest.Heard} (H : KeepsIn hd) (p : Par) :
    (blockAtS p).RunsStep (CarriesFo S.fork? hd) := k4_runsStep H p

/-- Its run behind the batching carries. -/
theorem k4_afterFo {hd : S → Option Forest.Heard} (H : KeepsIn hd) (p : Par) :
    (blockAtS p).AfterStep (CarriesFo S.fork? hd) := k4_afterStep H p

/-- The typed block's decision carries. -/
theorem k4C_stepsFo {hd : S → Option Forest.Heard} (H : KeepsIn hd) (p : Par) :
    (blockAtC p).Steps (CarriesFo S.fork? hd) := k4C_steps H p

/-- Every run of claims of the typed block carries. -/
theorem k4C_runsFo {hd : S → Option Forest.Heard} (H : KeepsIn hd) (p : Par) :
    (blockAtC p).RunsStep (CarriesFo S.fork? hd) := k4C_runsStep H p

/-- The typed block's run behind the batching carries. -/
theorem k4C_afterFo {hd : S → Option Forest.Heard} (H : KeepsIn hd) (p : Par) :
    (blockAtC p).AfterStep (CarriesFo S.fork? hd) := k4C_afterStep H p

/-- **At what the lookup on the calls was heard to return.** -/
theorem k4_look : ∀ p, (blockAtS p).RunsStep (CarriesFo S.fork? S.lookHeard?) :=
  k4_runsFo keepsIn_look

/-- **At what the lookup on the digits was heard to return.** -/
theorem k4_digits : ∀ p, (blockAtS p).RunsStep (CarriesFo S.fork? fun s => s.tl?.bind (·.heard)) :=
  k4_runsFo keepsIn_digits

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.k4_look
#print axioms OnBytes.Desc.First.K4.k4_digits
#print axioms OnBytes.Desc.First.K4.k4_stepsFo
#print axioms OnBytes.Desc.First.K4.k4_afterFo
#print axioms OnBytes.Desc.First.K4.k4C_stepsFo
#print axioms OnBytes.Desc.First.K4.k4C_runsFo
#print axioms OnBytes.Desc.First.K4.k4C_afterFo
