-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/K5/AtOwn.lean: the head's example: a test at the attention's plan number g AS
publicOfO ITSELF LAYS IT INTO ITS VALUE at the stored full-size files: the plan that the twin of
the attention's maker returns, with the smallness test that attentionOwners returns laid into its
seam (publicOfO's own zipWith). Definitions alone.
  `atOwn g f`: the walk of `owners_W` (Johnson/AtFull/Public/Owners.lean), step for step (withPubC ·
    plansG · readLines · the twelve groupS · attentionOwners), with f at plan number g at its end.
  `k5Q3 a`: three of the four parts from which `k5LotB_of_Q` makes the lot's test at a plan
    (Johnson/Desc/First/Att/Row/K5LotNoPad.lean): 162 rounds · planOkOwn · claimsOkAtQ.

Limits. No program calls these: they stand in statements alone; what ties atOwn to publicOfO's
value is Johnson/AtFull/K5/OwnTie.lean. Nothing on soundness.
-/
import Johnson.AtFull.Public.Owners
import Johnson.Desc.First.Att.Row.K5RowPlans
import Johnson.Desc.First.Att.Row.K5DryNoPad

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K5
open OnBytes OnBytes.Model
open OnBytes.Road.K4.Trial.AttK7Owners (withPubC onOk PW ttR mqOf)
open VerifiableInference.Desc.First VerifiableInference.Desc.First.Att.P H2K5.Row

/-- The plans are made as publicOfO makes them, and f accepts at number g. -/
def atOwn (g : Nat) (f : Attention.Plan → Bool) : Bool :=
  withPubC fun L => onOk (Layer.plansG L) fun G =>
    onOk (Attention.readLines PW.polCallsA) fun l =>
      onOk ((List.range L.y.NGr).mapM (Attention.groupS ttR PW L.y L.sc (mqOf L.y) l)) fun ps =>
        onOk (Verify.attentionOwners L.y.h.p4 L.y.NGr
            (G.map fun O => (⟨O.tl, O.Fp, O.Tp⟩ : Verify.SubPlan))
            (ps.toArray.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩)) fun seenA =>
          ((ps.toArray.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } })
            seenA)[g]?).any f

/-- 162 rounds, the test on the plan's own numbers, and the claims' test less the padding keys'. -/
def k5Q3 (a : Attention.Plan) : Bool :=
  decide (nRounds a.own = 162) && planOkOwn a.own && claimsOkAtQ a

end Johnson.AtFull.K5
