-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/KeepsSeatStatement.lean: WHAT THE MERGE's MEMBER LEAVES OF THE TWO READINGS
THAT STEPS OF SEVERAL KINDS SHARE: `S.tl?` AND `S.fork?` (Johnson/Desc/First/State.lean): A
STATEMENT ALONE: a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and it is none of
the library's goals: it is a lemma's statement.

Why. `HeadMergeKeepsLater` (KeepsLaterStatement.lean of this folder) speaks of the head's own parts
a and a' in front and behind. A seat of another kind reads the state through `S.tl?` and `S.fork?`,
which at the head's link answer only where the link is opened.

  `HeadMergeKeepsSeat`   under the kind's clause on what its member's step leaves and turns
                         (`K11Keeps P s s'`, KeepsStatement.lean of this folder): `S.tl?` answers
                         the same behind as in front; `S.fork?` answers in front; and whatever it
                         answers in front, it answers behind a ledger that is later in both of the
                         library's forms (`Fo.Later`, OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean;
                         `PscRun.Later`, OnBytes/Tie/Pv/Psc/PscLater.lean)

Limits. The clause is a premise. Nothing on which values are laid. Nothing on any property.
-/
import Johnson.Desc.K11.Returns.KeepsLaterStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open OnBytes.Model (Fork)
open VerifiableInference.Desc.First (S)

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadMergeKeepsSeat : Prop :=
  ∀ (P : HeadMergeP) (s s' : S), K11Keeps P s s' →
    s'.tl? = s.tl? ∧ (∃ F : Fork, s.fork? = some F) ∧
      ∀ F : Fork, s.fork? = some F →
        ∃ F' : Fork, s'.fork? = some F' ∧ _root_.Fo.Later F F' ∧ OnBytes.PscRun.Later F F'

end Johnson.Desc.First.ForkMerge.Returns

#print axioms Johnson.Desc.First.ForkMerge.Returns.HeadMergeKeepsSeat
