-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ToldGroups.lean: THREE LISTS OF GROUPS, ONE FOR EACH OF THE KEY FILE's
CHAINS: for each written sending, for each of its oracle messages, the groups that it joins.
Definitions alone.
They are the right sides of the three closed facts on `Key.groupsAtLabel` at the written
sendings' labels (`groups_keySends0`, `1`, `2`, Johnson/AtFull/KeyBack/LabelsKey.lean), letter for
letter.
Limits. No theorem is here.

-/
import Johnson.AtFull.KeyBack.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack


def groupsA : List (List (List Nat)) := [[[300]], [[100]], [[101]], [[102]], [[103]], [[300]]]

def groupsB : List (List (List Nat)) :=
  [[[200]], [[250, 300], [250, 200]], [[201]], [[202]], [[203]], [[204]], [[251]], [[252]],
    [[253]]]

def groupsC : List (List (List Nat)) := [[[301]], [[302]], [[303]], [[304]]]

end Johnson.AtFull.KeyBack
