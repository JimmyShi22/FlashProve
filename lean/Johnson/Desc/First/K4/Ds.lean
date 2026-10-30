-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Ds.lean: K4's DECLARED ROUNDS AS THE LIBRARY's DATA OF WRITTEN ROUNDS (`RDT`,
OnBytes/Maker/Trees.lean): the list `ds` over which a stretch of a file's chain is read as typed
rounds (`Maps ds s'`, OnBytes/Flat/CarrySMaps.lean) and over which a block is a piece of a chain.
Definitions with code, and small theorems.

`rdtOf e`: a round that sends no tree, opens none and opens no stored table, from its entry of the
plan: its kind by the entry's name (`Fmt.kindOf`), the cut of its message by the entry's words
(`Fmt.Entry.cut`); nothing if the format has not the name. `k4Ds p`: K4's rounds at the place p so,
in their order.
`k4Ds_entries`: their entries are K4's own table's (`entries`), which are the entries of the block's
declared rounds (`k4Ds_rounds`). `k4Ds_bare`: none sends or opens a tree, none opens a stored table.
`rdtOf_round`: it is what the format's own `DeclaredRound.round` makes of the declared round, whatever
was sent earlier.

Not said: that these are the rounds of a real file's chain at the place (whoever cuts the chain
pays). Nothing on soundness.
-/
import Johnson.Desc.First.K4.Block
import OnBytes.Maker.Trees
import Fmt.Parsed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Maker

/-- A round without a tree and without an opening, from its entry of the plan. -/
def rdtOf (e : Fmt.Entry) : Option RDT :=
  (Fmt.kindOf e.name).map fun k => ⟨⟨e, k, e.cut, [], []⟩, []⟩

/-- **K4's rounds at a place, as the library's data of written rounds.** -/
def k4Ds (p : Par) : Option (List RDT) := (entries p.P p.hp p.g).mapM rdtOf

theorem rdtOf_entry {e : Fmt.Entry} {d : RDT} (h : rdtOf e = some d) :
    d.entry = e ∧ d.trees = [] ∧ d.opens = [] ∧ d.stored = [] ∧ d.items = e.cut := by
  unfold rdtOf at h
  cases hk : Fmt.kindOf e.name with
  | none => simp [hk] at h
  | some k =>
    rw [hk] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem mapM_rdtOf : ∀ (es : List Fmt.Entry) (ds : List RDT), es.mapM rdtOf = some ds →
    ds.map (·.entry) = es ∧ ∀ d ∈ ds, d.trees = [] ∧ d.opens = [] ∧ d.stored = []
  | [], ds, h => by
    obtain rfl : [] = ds := by simpa using h
    exact ⟨rfl, fun _ hd => absurd hd List.not_mem_nil⟩
  | e :: es, ds, h => by
    rw [List.mapM_cons] at h
    cases h1 : rdtOf e with
    | none => simp [h1] at h
    | some d =>
      cases h2 : es.mapM rdtOf with
      | none => simp [h1, h2] at h
      | some ds' =>
        obtain rfl : d :: ds' = ds := by simpa [h1, h2] using h
        obtain ⟨a1, a2, a3, a4, _⟩ := rdtOf_entry h1
        obtain ⟨b1, b2⟩ := mapM_rdtOf es ds' h2
        refine ⟨by rw [List.map_cons, a1, b1], fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨a2, a3, a4⟩
        · exact b2 x hx

/-- Their entries are K4's own table's. -/
theorem k4Ds_entries {p : Par} {ds : List RDT} (h : k4Ds p = some ds) :
    ds.map (·.entry) = entries p.P p.hp p.g := (mapM_rdtOf _ _ h).1

/-- These are the entries of the block's declared rounds, at any seat. -/
theorem k4Ds_rounds {T : Type} (L : Seat T) {p : Par} {ds : List RDT} (h : k4Ds p = some ds) :
    (block L p).rounds.map (·.entry) = ds.map (·.entry) := by
  rw [k4Ds_entries h]
  show ((entries p.P p.hp p.g).map fun e => ({ entry := e } : Fmt.DeclaredRound)).map (·.entry) = _
  rw [List.map_map]
  exact List.map_id _

/-- None sends or opens a tree; none opens a stored table. -/
theorem k4Ds_bare {p : Par} {ds : List RDT} (h : k4Ds p = some ds) :
    ∀ d ∈ ds, d.trees = [] ∧ d.opens = [] ∧ d.stored = [] := (mapM_rdtOf _ _ h).2

/-- It is what the format's own reading makes of the declared round. -/
theorem rdtOf_round (e : Fmt.Entry) (earlier : List (List ByteArray × ByteArray)) :
    (({ entry := e } : Fmt.DeclaredRound).round earlier).map
      (fun w => (⟨⟨w.entry, w.kind, w.items, [], []⟩, []⟩ : RDT)) = rdtOf e := by
  unfold Fmt.DeclaredRound.round rdtOf
  cases Fmt.kindOf e.name with
  | none => rfl
  | some k => rfl

end OnBytes.Desc.First.K4
