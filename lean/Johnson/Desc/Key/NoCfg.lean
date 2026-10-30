-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/NoCfg.lean: which parts of the key file's description read the digest of the public
files. The planner's answer at another digest is `chainsAtCfg` of its answer (OnBytes/Tie/
ChainsAtCfg.lean: `chainsOf_at`). Here the description's source is carried to another digest
likewise (`Source.atCfg`), and every field of `descriptionFromSource` but the test on the file (`fileOk`) is shown to
be the same, by unfolding alone.

Main names.
  Source.atCfg X c: the source with the digest c in the place of its own: in the three chains'
    values as read (`keyAtCfg`) and in what the planner has made (`chainsAtCfg`).
  cfg_atCfg: the carried source does hold c where the digest stood.
  first_atCfg, shared_atCfg, second_atCfg: the three chains are the same blocks.
  plans_atCfg, tableDepth_atCfg, okStart_atCfg, start₁_atCfg, start₂_atCfg, start₃_atCfg, fin_atCfg:
    the declared rounds handed in, the table's depth, the test on the instance, the three starts and
    the last test are the same.
  desc_atCfg: so the description at another digest is the description with another `fileOk`.

Limits. Of `fileOk` nothing is shown: four of its clauses read the digest. Of the decision on three
views alone: how the views are made of a file, and what the transcript's hashing starts from, is not
here. That the source, N and P at another digest are what the makers return there is not shown here:
Johnson/Desc/Key/NoCfgAt.lean, under the three hypotheses of the library's `chainsOf_at`. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.Desc
import OnBytes.Tie.ChainsAtCfg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Tie

/-- The source with another digest in the place of its own. -/
def Source.atCfg (X : Source) (c : ByteArray) : Source :=
  { X with Y := { X.Y with k := keyAtCfg X.Y.k c }, chains := chainsAtCfg X.chains c }

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (c : ByteArray)

/-- The carried source does hold the other digest: in each chain's values as read, and in what the
planner has made. -/
theorem cfg_atCfg : (X.atCfg c).Y.k.oneTime.given.cfg = c ∧ (X.atCfg c).Y.k.shared.given.cfg = c ∧
    (X.atCfg c).Y.k.second.given.cfg = c ∧ (X.atCfg c).chains.made.configuration = c ∧
    (X.atCfg c).chains.key.oneTime.given.cfg = c :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem first_atCfg : (descriptionFromSource (X.atCfg c) N P).first = (descriptionFromSource X N P).first := rfl

theorem shared_atCfg : (descriptionFromSource (X.atCfg c) N P).shared = (descriptionFromSource X N P).shared := rfl

theorem second_atCfg : (descriptionFromSource (X.atCfg c) N P).second = (descriptionFromSource X N P).second := rfl

theorem plans_atCfg : (descriptionFromSource (X.atCfg c) N P).plans = (descriptionFromSource X N P).plans := rfl

theorem tableDepth_atCfg : (descriptionFromSource (X.atCfg c) N P).tableDepth = (descriptionFromSource X N P).tableDepth := rfl

theorem okStart_atCfg : (descriptionFromSource (X.atCfg c) N P).okStart = (descriptionFromSource X N P).okStart := rfl

theorem start₁_atCfg : (descriptionFromSource (X.atCfg c) N P).start₁ = (descriptionFromSource X N P).start₁ := rfl

theorem start₂_atCfg : (descriptionFromSource (X.atCfg c) N P).start₂ = (descriptionFromSource X N P).start₂ := rfl

theorem start₃_atCfg : (descriptionFromSource (X.atCfg c) N P).start₃ = (descriptionFromSource X N P).start₃ := rfl

theorem fin_atCfg : (descriptionFromSource (X.atCfg c) N P).fin = (descriptionFromSource X N P).fin := rfl

/-- **The description at another digest is the description with another test on the file.** -/
theorem desc_atCfg :
    descriptionFromSource (X.atCfg c) N P = { descriptionFromSource X N P with fileOk := (descriptionFromSource (X.atCfg c) N P).fileOk } := rfl

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.cfg_atCfg
#print axioms VerifiableInference.Desc.Key.first_atCfg
#print axioms VerifiableInference.Desc.Key.shared_atCfg
#print axioms VerifiableInference.Desc.Key.second_atCfg
#print axioms VerifiableInference.Desc.Key.plans_atCfg
#print axioms VerifiableInference.Desc.Key.tableDepth_atCfg
#print axioms VerifiableInference.Desc.Key.okStart_atCfg
#print axioms VerifiableInference.Desc.Key.start₁_atCfg
#print axioms VerifiableInference.Desc.Key.start₂_atCfg
#print axioms VerifiableInference.Desc.Key.start₃_atCfg
#print axioms VerifiableInference.Desc.Key.fin_atCfg
#print axioms VerifiableInference.Desc.Key.desc_atCfg
