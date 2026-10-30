-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/DsTail.lean: K4's WRITTEN ROUNDS, ROW BY ROW OF K4's OWN TABLE OF ROUNDS, AS
DATA. K4's block declares its own table's rows, each as an entry (`entries` is `rounds` under
`entryOf`: Johnson/Desc/First/K4/Block.lean). Here: the written round of a row as a function of the
row (`rdOf`); that the written rounds `k4Ds p` (Johnson/Desc/First/K4/Ds.lean) are, at every place,
the table's rows under that function; and what such a round sends and draws, in the form that the
library's maps to typed rounds ask (`SendsDraws`, OnBytes/Slice/RoundsOf.lean). Definitions with
code, statements and proofs.

`Fit d x`: the written round x answers the row d of the table: name, kind, the two numbers of
draws; no position, no matrix entry; the word logN at most 64; its message is cut into d.sent
elements of the extension field and nothing else. `fit_sd`: then, if d draws no fewer elements than
it draws by the rule that never gives 0, x sends some number of elements and draws d.drawn elements
and nothing else. `Fit.allE`: every item of its message is an element of the extension field.
`kd n`, `rdOf d`: the kind that the format gives a round's name; the row's written round.
`rdtOf_entryOf`, `fit_rdOf`, `rdOf_items`: it is what `rdtOf` makes of the row's entry; it answers
the row; its message is d.sent elements. `k4Ds_eq`: AT EVERY PLACE `k4Ds p` is the list of the
table's rows' written rounds: by the definitions alone, under no premise and from no test's yes.
`k4Ds_allE`: so every message holds elements of the extension field alone.

Limits. This speaks of the rounds that K4's block DECLARES. That the made plan's entries at the
place are these is asked by the tests on the plan (they compare; they lay nothing in) and was shown
by the first form's runs alone (Block.lean's own Limits), not here. `entryOf` lays no proof of work:
at a parameter file that asks work of these rounds the declared rounds are not the plan's, and the
tests on the plan refuse. «Every place» takes in places that `covers` refuses, where the table is no
plan's list. Nothing on which scalar is which. The cut into the sixteen pieces of the record `TailR`
stands in Johnson/Road/K4/DsTailR.lean. Nothing on soundness.
-/
import Johnson.Desc.First.K4.Ds
import OnBytes.Slice.RoundsOf
import OnBytes.Flat.RoundsT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Slice OnBytes.Flat

/-! ### A written round against a row of the table -/

/-- The written round x answers the row d. -/
structure Fit (d : Rd) (x : RDT) : Prop where
  name : x.entry.name = d.name.name
  kind : Fmt.kindOf x.entry.name = some x.kind
  drawE : x.entry.drawE = d.drawn
  drawNZ : x.entry.drawNZ = d.notZero
  poss : x.entry.poss = 0
  trits : x.entry.trits = 0
  logN : x.entry.logN ≤ 64
  items : x.items = List.replicate d.sent .e

/-- None of the twelve names of `RoundName` is a sealing's or a seeds'. -/
theorem kind_of_name (n : RoundName) :
    Fmt.kindOf n.name = some .elems ∨ Fmt.kindOf n.name = some .join ∨
      Fmt.kindOf n.name = some .nothing := by
  cases n <;> decide

theorem Fit.kind_ok {d : Rd} {x : RDT} (h : Fit d x) : x.kind ≠ .sealed ∧ x.kind ≠ .seeds := by
  have hk := h.kind
  rw [h.name] at hk
  rcases kind_of_name d.name with e | e | e <;>
  · rw [e] at hk
    rw [← Option.some.inj hk]
    exact ⟨by decide, by decide⟩

/-- **What a written round draws**, where it answers a row that draws no fewer elements than it
draws by the rule that never gives 0: d.drawn elements and nothing else. It sends some number of
elements. -/
theorem fit_sd {d : Rd} {x : RDT} (h : Fit d x) (hz : d.notZero ≤ d.drawn) :
    ∃ ns a, SendsDraws (toRD x) ns d.drawn 0 a := by
  have hz' : x.entry.drawNZ ≤ x.entry.drawE := by
    rw [h.drawNZ, h.drawE]
    exact hz
  have s : SendsDraws (toRD x) (nS x.items) x.entry.drawE x.entry.poss x.entry.logN :=
    sendsDraws_of (d := toRD x) (r := ⟨x.entry, x.kind, x.items, []⟩) ⟨rfl, rfl, rfl⟩
      h.trits h.kind_ok.1 h.kind_ok.2 hz' h.logN
  rw [h.drawE, h.poss] at s
  exact ⟨_, _, s⟩

/-- Every item of such a round's message is an element of the extension field. -/
theorem Fit.allE {d : Rd} {x : RDT} (h : Fit d x) : ∀ it ∈ x.items, it = Fmt.Item.e := by
  intro it hi
  rw [h.items] at hi
  exact List.eq_of_mem_replicate hi

/-! ### A row's written round -/

/-- The kind that the format gives a round's name. -/
def kd (n : RoundName) : Fmt.Kind := (Fmt.kindOf n.name).getD .elems

theorem kindOf_kd (n : RoundName) : Fmt.kindOf n.name = some (kd n) := by
  unfold kd
  rcases kind_of_name n with e | e | e <;> rw [e] <;> rfl

/-- **A row's written round**: no tree is sent or opened, no stored table is opened. -/
def rdOf (d : Rd) : RDT := ⟨⟨entryOf d, kd d.name, (entryOf d).cut, [], []⟩, []⟩

/-- It is what `rdtOf` makes of the row's entry. -/
theorem rdtOf_entryOf (d : Rd) : rdtOf (entryOf d) = some (rdOf d) := by
  have hk : Fmt.kindOf (entryOf d).name = some (kd d.name) := kindOf_kd d.name
  simp [rdtOf, hk, rdOf]

/-- The cut of a row's own entry: as many elements of the extension field as the row sends. -/
theorem cut_entryOf (d : Rd) : (entryOf d).cut = List.replicate d.sent .e := by
  have h : (24 * d.sent - 24 * 0 - 32 * 0) / 24 = d.sent := by omega
  show List.replicate 0 Fmt.Item.answer ++ List.replicate 0 Fmt.Item.root ++
    List.replicate ((24 * d.sent - 24 * 0 - 32 * 0) / 24) Fmt.Item.e = _
  simp only [h, List.replicate_zero, List.nil_append]

/-- Its message is d.sent elements of the extension field. -/
theorem rdOf_items (d : Rd) : (rdOf d).items = List.replicate d.sent .e := cut_entryOf d

/-- It answers the row. -/
theorem fit_rdOf (d : Rd) : Fit d (rdOf d) :=
  ⟨rfl, kindOf_kd d.name, rfl, rfl, rfl, rfl, Nat.zero_le 64, cut_entryOf d⟩

/-! ### At a place -/

theorem mapM_rdOf : ∀ ds : List Rd, (ds.map entryOf).mapM rdtOf = some (ds.map rdOf)
  | [] => by simp
  | d :: ds => by
    rw [List.map_cons, List.mapM_cons]
    simp [rdtOf_entryOf, mapM_rdOf ds]

/-- **K4's written rounds are the table's rows' written rounds**, at every place. -/
theorem k4Ds_eq (p : Par) : k4Ds p = some ((rounds p.P p.hp p.g).map rdOf) :=
  mapM_rdOf (rounds p.P p.hp p.g)

/-- **At a place every message of K4's written rounds holds elements of the extension field
alone.** -/
theorem k4Ds_allE {p : Par} {xs : List RDT} (h : k4Ds p = some xs) :
    ∀ x ∈ xs, ∀ it ∈ x.items, it = Fmt.Item.e := by
  obtain rfl : (rounds p.P p.hp p.g).map rdOf = xs := Option.some.inj ((k4Ds_eq p).symm.trans h)
  intro x hx
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
  exact (fit_rdOf d).allE

end OnBytes.Desc.First.K4
