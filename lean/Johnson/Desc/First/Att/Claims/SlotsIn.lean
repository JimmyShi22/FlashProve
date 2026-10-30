-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/SlotsIn.lean: kind K5: THE SLOTS' TWIN OF Claims/Covered.lean, ITS
GROUND: the predicate "every slot that a form names meets Ps", its closure under the forms'
operations, and the TWO RECORDS OF PREMISES under which the law on the runs "first" and "second" is
to be typed. The law itself IS NOT TYPED HERE: its statement stands as a definition of type Prop
(Spec.SlotsCovered).

Why. A table's public test beside "the forms of a run are worth 0" asks of every slot that a form
names that it is below the number of slots and filled. The kind's own runs lay nothing: so the
hearing must have filled it. Ps IS A LETTER: meant: "slot j is filled in the ledger behind the
hearing"; or: lo ≤ j < hi (with hear_fills,
Att/K05HearFills.lean [not in this library], that gives the first).

The predicate SlotsIn and its closure lemmas are not typed here: THEY ARE ANOTHER FILE's
(Johnson/Road/K4/Slots/SlotsIn.lean; namespace OnBytes.Desc.First.K4.Slots; general in the predicate).
They are exported into this namespace: aliases, no new declaration.

Main names:
  `SlotsIn Ps f` (that file's): every slot that f names meets Ps.
  `slotsIn_a`, `slotsIn_b`: a sumcheck of products' two end values of member b.
  `PtsSlots Ps g p`: what the claims read of what was heard (Pts, Att/Points.lean): from each number,
    along the stretch that the runs walk from it (Att/RunsP.lean), every slot meets Ps.
  `RowsSlots Ps p`: the rows that the sumchecks leave name such slots alone: RowsCov's seven fields
    (Claims/Covered.lean) at SlotsIn.
  `Spec.SlotsCovered`: THE LAW OWED, as a statement.
  `slotsIn_bites`: a control: the form "slot j" has not SlotsIn Ps where Ps j fails.
Limits. NEITHER RECORD IS SHOWN OF ANYTHING HERE. The key forms that "keys" hands on to the lookup's
join are not spoken of. EMPTY AT: Ps := fun _ => False: then SlotsIn says that the form names no
slot, and PtsSlots is false wherever a stretch has a member. IDLE AT: Ps := fun _ => True.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Covered
import Johnson.Road.K4.Slots.SlotsIn

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P.Runs (W JoinsP)

export OnBytes.Desc.First.K4.Slots (SlotsIn slotsIn_mono slotsIn_ofConst slotsIn_slot slotsIn_empty
  slotsIn_ent slotsIn_addMul slotsIn_scale slotsIn_add slotsIn_sub slotsIn_foldl slotsIn_foldl_mem)

variable {Ps : ℕ → Prop}

/-- The two end values of member b of a sumcheck of products with n members. -/
theorem slotsIn_a {s : P.SumP} {n b : ℕ} (h : ∀ i, i < 2 * n → Ps (s.ends + i)) (hb : b < n) :
    SlotsIn Ps (s.a b) := slotsIn_slot (h _ (by omega))
theorem slotsIn_b {s : P.SumP} {n b : ℕ} (h : ∀ i, i < 2 * n → Ps (s.ends + i)) (hb : b < n) :
    SlotsIn Ps (s.b b) := slotsIn_slot (h _ (by omega))

/-- **What the claims read of what was heard: along each number's stretch every slot meets Ps.** -/
structure PtsSlots (Ps : ℕ → Prop) (g : P.Geo) (p : P.Pts) : Prop where
  /-- a unit's plane values: three of a remainder unit's three; five of a softmax unit's seven -/
  planes : ∀ pc ∈ p.planes.toList, 3 ≤ pc.np ∧ ∀ i, i < pc.np → Ps (pc.s0 + i)
  /-- a softmax unit's seven scalars; its sumcheck's end values, two a piece -/
  scores : ∀ k ∈ p.scores.toList, (∀ i, i < 7 → Ps (k.s0 + i)) ∧
    ∀ i, i < 2 * k.pw.size → Ps (k.sc.ends + i)
  five : ∀ i, i < 5 → Ps (p.d.s5 + i)
  bits : ∀ i, i < g.lt → Ps (p.d.sIB + i)
  two : ∀ i, i < 2 → Ps (p.d.s5h + i)
  values : ∀ i, i < 2 → Ps (p.d.sCl + i)
  maxima : ∀ i, i < g.NP → Ps (p.x.sM6 + i)
  scE : ∀ i, i < 2 * g.NP → Ps (p.d.scE.ends + i)
  vpm : ∀ i, i < 2 * g.NP → Ps (p.d.vpm.ends + i)
  vpd : ∀ i, i < 2 * g.NP → Ps (p.d.vpd.ends + i)
  scF : ∀ i, i < 2 * g.NP → Ps (p.x.scF.ends + i)
  scd : ∀ i, i < g.Lam + g.NP * g.lt → Ps (p.x.scd.ends + i)
  scH : ∀ i, i < 2 * g.NP → Ps (p.x.scH.ends + i)

/-- **The rows that the sumchecks leave name such slots alone.** -/
structure RowsSlots (Ps : ℕ → Prop) (p : P.Pts) : Prop where
  units : ∀ k ∈ p.scores.toList, SlotsIn Ps k.sc.row
  scE : SlotsIn Ps p.d.scE.row
  vpm : SlotsIn Ps p.d.vpm.row
  vpd : SlotsIn Ps p.d.vpd.row
  scF : SlotsIn Ps p.x.scF.row
  scd : SlotsIn Ps p.x.scd.row
  scH : SlotsIn Ps p.x.scH.row

/-- **THE LAW OWED**: every form that "first" or "second" gathers names such slots alone. NOT PROVED
HERE. -/
def Spec.SlotsCovered : Prop :=
  ∀ (Ps : ℕ → Prop) (i : P.Runs.In) (K : ℕ) (l₁ l₂ : List Aff) (j : JoinsP), PtsSlots Ps i.g i.p →
    RowsSlots Ps i.p → P.Runs.firstRun i K = some (l₁, j) → P.Runs.secondRun i K = some l₂ →
    ∀ f ∈ l₁ ++ l₂, SlotsIn Ps f

/-- A control. -/
theorem slotsIn_bites {j : ℕ} (h : ¬ Ps j) : ¬ SlotsIn Ps (Aff.slot j) := fun hs =>
  h (hs (j, oneE) (by simp [Aff.slot]))

end K5Law

#print axioms K5Law.slotsIn_a
#print axioms K5Law.slotsIn_bites
