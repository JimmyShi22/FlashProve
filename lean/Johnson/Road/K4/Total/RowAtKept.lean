-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/RowAtKept.lean: THE LAW "the pending row can be made of what K4's hearing
leaves" (Johnson/Road/K4/Total/RowReturns.lean) AT THE VERIFIER's STATE: behind a yes of K4's block
the public test hasRow (Johnson/Top/H0/Walk/FrameRow.lean: the frame's reader of the pending row
returns) says yes, under named premises. Statements and proofs.

  `hasRow_core`: at two states s, s' with Rest s s' (K4's yes turns neither the statement nor the
    number of the index masks' message): what is left at s' is w · w has w₀'s skeleton · wsPending
    returns at w₀ · the ledger AT s has an entry to take: then hasRow at s'.
  `hasRow_at_kept`: so behind a yes of K4's block (KeptAtS p s s', Johnson/Road/K4/KeptAtS.lean),
    the skeleton asked of whatever the state behind holds as heard.
  `hasRow_of_member`: the skeleton paid by hear_row_skel: THE MEMBER IS A SECOND RETURN OF THE
    HEARING at the same plan (the tokens may differ) of whose leavings wsPending makes a row.
No new argument: row_return, hear_row_skel, rowAt_some, leftOf_of_lay.
**Limits.** PREMISES OF hasRow_of_member, beside KeptAtS (paid by kept_atS at a yes): three
equations on the two values of the public parameters; the second hearing's return; THE MEMBER:
wsPending returns at its leavings: BY NO THEOREM HERE, and no run is cited here (rowB,
Johnson/Road/K4/Total/PlanRowDefs.lean, makes it a test with code); roomB at the state IN FRONT of
K4's block: message number indexMasks of the statement has a ledger with an entry to take: no table
of public items that is cited here says it; it is no invariant of the chain
(Johnson/Road/K4/Total/RoomFor.lean). The letters of hasRow are filled with p.P.wsLay and p.hp.NCL;
lin is free: that these are the letters at which the table asks the test is not said. It says that
the reader returns, not what the row says. Nothing on soundness. K04_law, the law of K4's block
itself, IS NOT PROVED. Met through Lean at no member.


-/
import Johnson.Road.K4.Total.RowProofs
import Johnson.Road.K4.Total.HearRowSkel
import Johnson.Road.K4.KeptAtS
import Johnson.Top.H0.Walk.FrameRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub Own)
open OnBytes.Params (LinShape)
open OnBytes.Road.K4 (KeptAtS)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk (leftLay)
open Johnson.Desc.First.Walk.Law (hasRow rowAt rowAt_some leftOf_of_lay)

/-- The test at a state s' that has s's statement and number of the index masks' message. -/
theorem hasRow_core {lay : WsLay} {n : Nat} {lin : LinShape} {s s' : S} {w w₀ : WsForkOut}
    (hleft : leftLay s' = some w) (hR : Rest s s') (hS : RowSkel w w₀)
    (hm : (wsPending lay w₀ n lin).toOption.isSome = true)
    (hroom : roomB s.out.indexMasks s.st.oracles = true) : hasRow lay n lin s' = true := by
  obtain ⟨⟨row, os⟩, hr⟩ := row_return lay s.out.indexMasks n lin s.st.oracles w w₀ hS hm hroom
  have e : rowAt lay n lin s' = some row :=
    rowAt_some.2 ⟨w, os, leftOf_of_lay hleft, by rw [hR.out, hR.st]; exact hr⟩
  unfold hasRow
  rw [e]
  rfl

/-- **Behind a yes of K4's block**, the skeleton asked of what the state behind holds as heard. -/
theorem hasRow_at_kept {p : Par} {s s' : S} {w₀ : WsForkOut} {lin : LinShape}
    (K : KeptAtS p s s') (hS : ∀ o, s'.own? = some o → RowSkel o.wo w₀)
    (hm : (wsPending p.P.wsLay w₀ p.hp.NCL lin).toOption.isSome = true)
    (hroom : roomB s.out.indexMasks s.st.oracles = true) :
    hasRow p.P.wsLay p.hp.NCL lin s' = true := by
  obtain ⟨_, _, o, _, _, _, _, _, hown, _, _, hleft, hR, _⟩ := K
  exact hasRow_core hleft hR (hS o hown) hm hroom

/-- **Behind a yes of K4's block**, the member a second return of the hearing at the same plan. -/
theorem hasRow_of_member {p : Par} {s s' : S} {lin : LinShape} {P₀ : Pub} {fo₀ : Forest.Heard}
    {F₀ G₀ : Fork} {t₀ u₀ : Tape} {o₀ : Own} (K : KeptAtS p s s') (hy : p.P.y = P₀.y)
    (hrd : p.P.rd = P₀.rd) (hl : p.P.wsLay = P₀.wsLay)
    (h₀ : hear engFl P₀ p.hp p.g fo₀ F₀ t₀ = some (o₀, G₀, u₀))
    (hm : (wsPending p.P.wsLay o₀.wo p.hp.NCL lin).toOption.isSome = true)
    (hroom : roomB s.out.indexMasks s.st.oracles = true) :
    hasRow p.P.wsLay p.hp.NCL lin s' = true := by
  obtain ⟨a, fo, o, G, _, _, _, _, _, _, _, hleft, hR, _, _, t, u, hh⟩ := K
  exact hasRow_core hleft hR
    (hear_row_skel { p.P with tokv := s.tokv } P₀ p.hp p.g fo fo₀ a.F G F₀ G₀ t u t₀ u₀ o o₀ hy hrd
      hl hh h₀) hm hroom

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.hasRow_core
#print axioms OnBytes.Desc.First.K4.Total.hasRow_at_kept
#print axioms OnBytes.Desc.First.K4.Total.hasRow_of_member
