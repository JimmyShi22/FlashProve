-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/StatementGrows.lean: "the statement grows" (Grows, Johnson/Desc/Grows.lean)
MEETS StKeeps (Johnson/Desc/K13/Law/StatementCalls.lean): a second instance beside FitStays.

  stKeeps_grows    the ground's routines (groundKeeps_grows); the beginning of a proximity test
                   (grows_begun); the one write of a pending row (it turns one message's ledger).
  atFinish_grows   so kind K12's sub-protocol at the first chain's end lets the statement grow.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K13.Law.StatementSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (By groundKeeps_grows)
open VerifiableInference.Desc.Keeps (Decides)

theorem stKeeps_grows : StKeeps Grows where
  ground := groundKeeps_grows
  begun := grows_begun
  row := fun lay im o n lin T r os' h => by
    obtain ⟨k, f, hf, rfl⟩ := Meaning.K2.pendingRowO_rowGrows lay lin im o n T.oracles r os' h
    exact grows_modOracle T k f hf

theorem atFinish_grows (p : K12.P12) :
    Decides (By Grows fun s : S => s.st) (K12.atFinish p) := atFinish_keeps stKeeps_grows p

end VerifiableInference.Desc.K13.Law
