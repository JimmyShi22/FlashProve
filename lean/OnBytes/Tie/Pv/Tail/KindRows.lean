-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/KindRows.lean: a statement on the order of the links of a request's chain: which
place has a link of which kind, with which plan's routine.

A definition alone, of type Prop without free letters: nothing is proved here and nothing is
assumed. A later file proves it, as a theorem whose type is the statement's name.

`OfAPlan` with `linksOf_kinds` (OnBytes/Tie/Pv/Keeps/KeepsKinds.lean) says that every link of the
program's own list runs the routine of a layers' plan, of an attention plan or of the head's plan;
which place has which kind it leaves open. OnBytes/Tie/Pv/Keeps/LinksOrder.lean goes from a group to
its places; the statement here goes from a place to the kind. The planner is called place by place
(`Verify.linkRounds`, OnBytes/Model/VerifySubproofs.lean: by the place's remainder and quotient by 1
or 2). To lay a run against the plan at every link (`stepAt_kind`, in a
later file) the two orders must be one.

Main names:
  `Fo.BatRows.stepOf V` (OnBytes/Tie/Pv/Lookup/Ends/BatRows.lean; not defined here): 2 where the
    proof covers attention, else 1: as in `Verify.linkRounds`.
  `row_place_kind`: the link at place l of `Verify.linksOf V cov`: the head's at l = stepOf V *
    V.NGr; below that the layers' of group l / stepOf V where the remainder is 0, else the
    attention's of that group.

Limits: a statement alone; its proof is in a later file.


-/
import OnBytes.Model.VerifyLinks
import OnBytes.Tie.Pv.Lookup.Ends.BatRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.KindRows
open OnBytes OnBytes.Model OnBytes.Model.Stages
open Fo.BatRows (stepOf)

/-- Which place has which kind of link. Text: OnBytes/Model/StagesLinks.lean (listLinksH: for
each group g the link of its layers, directly followed by that of its attention where the proof
covers attention; last the head's; SubPlanH.link keeps the routine), VerifyLinks.lean (linksOf: the
plans that listLinksH is given). -/
def row_place_kind : Prop :=
  ∀ (V : Verify.Public) (cov : Head.Covered) (ls : Array LinkH), Verify.linksOf V cov = .ok ls →
    ∀ (l : Nat) (X : LinkH), ls[l]? = some X →
      (l = stepOf V * V.NGr ∧ X.run = (Verify.headPlanOf V cov).run) ∨
      (l < stepOf V * V.NGr ∧ l % stepOf V = 0 ∧ ∃ hp, V.G[l / stepOf V]? = some hp ∧
        X.run = (Verify.layersPlanOf V cov.tokv (l / stepOf V) hp).run) ∨
      (l < stepOf V * V.NGr ∧ l % stepOf V ≠ 0 ∧ ∃ a, V.A[l / stepOf V]? = some a ∧
        X.run = (Verify.attentionPlanOf a).run)

end OnBytes.Tie.Pv.Tail.KindRows
