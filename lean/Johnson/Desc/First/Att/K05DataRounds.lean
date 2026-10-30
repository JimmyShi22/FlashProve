-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05DataRounds.lean: kind K5: three public premises of the kind's law at the
piece (K5Public.plain, entries, kinds: Johnson/Desc/First/Att/K05LawOne.lean), AT THE DATA OF A
FILE's ROUNDS, from the general rule on a description's data (`roundsOfData`,
Johnson/Desc/Sound/DataRounds.lean).

Why. The law has a letter ds: the data of the written rounds at the kind's stretch. At ds := the
kind's own list (`written p`) the three are theorems (`seam_plain`, `seam_entries`, `seam_kinds`,
Johnson/Desc/First/Att/K05Seam.lean). A description's data are made of the blocks' own declared
rounds: `roundsOfData` says so round by round (`RoundAsG`: the entry, the kind of its name, the
items, the number of trees, the stored tables). So at the stretch that stands against the kind's
declared rounds the three hold by make: no test need ask them.

Main names.
  `plain_of_as`: data d that stand against a declared round r of the kind (RoundAsG d r) are Plain.
  `public_of_as`: List.Forall₂ RoundAsG ds (rounds p) gives plain, entries and kinds at ds.
  `forall₂_cut`: of lists alone: a Forall₂ against a ++ m ++ c gives one against m, at the stretch
    of m's length behind a's.
  `k5_public_at_data`: F.data file = .ok D, and the first chain's declared rounds without the last
    are pre ++ rounds p ++ post: the three hold at the stretch of D.ds₁ of (rounds p).length rounds
    behind pre.length.

IS IT EMPTY HERE? `public_of_as` has a member at every p: ds := written p, where trees and stored
are empty as the kind's entries have no root (not typed here as a lemma). `k5_public_at_data`: THAT
ANY DESCRIPTION's declared rounds are pre ++ rounds p ++ post IS A PREMISE: by the text of
FileDescription.roundsDeclaredByBlocks (Johnson/Desc/Block.lean) they are the blocks' rounds in a row, so it holds wherever a
block of the first chain has rounds := rounds p and is not the last: NOT SHOWN HERE of any
description. That pre.length is the number that the rule of composition calls the piece's base is
not shown here. hD: that F.data returns at any description and file is not shown here; it is the
compile's own premise: where it refuses, the theorem is idle.
Limits. Nothing on the other ten public premises. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.DataRounds
import Johnson.Desc.First.Att.K05Seam

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop OnBytes OnBytes.Model OnBytes.Flat OnBytes.Maker Fo.Peel
open VerifiableInference.Desc (RoundAsG RoundsAre roundsOfData FileDescription)

/-- **One round**: data that stand against a declared round of the kind are Plain. -/
theorem plain_of_as (p : Par) {d : RDT} {r : Fmt.DeclaredRound} (hr : r ∈ rounds p)
    (h : RoundAsG d r) : Plain (toRD d) := by
  obtain ⟨he, hk, hi, _, _⟩ := h
  obtain ⟨a1, a2, a3, a4⟩ := rounds_ok p r.entry (List.mem_map_of_mem hr)
  have c := rounds_cut p r hr
  have hcut : r.items = List.replicate (r.entry.msg / 24) Fmt.Item.e := by
    show r.entry.cut = _
    unfold Fmt.Entry.cut
    rw [c.answers, c.roots]
    simp
  refine ⟨fun it hit => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hi' : it ∈ d.items := hit
    rw [hi, hcut] at hi'
    exact List.eq_of_mem_replicate hi'
  · show d.items.length = d.entry.msg / 24
    rw [hi, hcut, List.length_replicate, he]
  · show d.entry.poss = 0
    rw [he]; exact a1
  · show d.entry.logN = 0
    rw [he]; exact a2
  · show d.entry.trits = 0
    rw [he]; exact a3
  · show d.kind ≠ .sealed
    intro e
    rw [e] at hk
    rcases c.kind with h | h | h <;> rw [h] at hk <;> cases hk
  · show d.kind ≠ .seeds
    intro e
    rw [e] at hk
    rcases c.kind with h | h | h <;> rw [h] at hk <;> cases hk
  · show d.entry.drawNZ ≤ d.entry.drawE
    rw [he]; exact a4

/-- The three, against any list of declared rounds of the kind. -/
theorem public_of_as_in (p : Par) {ds : List RDT} {l : List Fmt.DeclaredRound}
    (h : List.Forall₂ RoundAsG ds l) : (∀ r ∈ l, r ∈ rounds p) →
    (∀ d ∈ ds, Plain (toRD d)) ∧ ds.map (·.entry) = l.map (·.entry) ∧
      ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind := by
  induction h with
  | nil => exact fun _ => ⟨fun _ hd => (by cases hd), rfl, fun _ hd => (by cases hd)⟩
  | @cons d r ds l hd _ ih =>
    intro hl
    obtain ⟨i1, i2, i3⟩ := ih fun r' hr' => hl r' (List.mem_cons_of_mem _ hr')
    have hr := hl r List.mem_cons_self
    refine ⟨fun d' hd' => ?_, ?_, fun d' hd' => ?_⟩
    · rcases List.mem_cons.1 hd' with rfl | h'
      · exact plain_of_as p hr hd
      · exact i1 d' h'
    · rw [List.map_cons, List.map_cons, i2, hd.1]
    · rcases List.mem_cons.1 hd' with rfl | h'
      · rw [hd.1]; exact hd.2.1
      · exact i3 d' h'

/-- **K5Public's plain, entries and kinds**, at data that stand round by round against the kind's
declared rounds. -/
theorem public_of_as (p : Par) {ds : List RDT} (h : List.Forall₂ RoundAsG ds (rounds p)) :
    (∀ d ∈ ds, Plain (toRD d)) ∧ ds.map (·.entry) = (rounds p).map (·.entry) ∧
      ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind :=
  public_of_as_in p h fun _ hr => hr

/-- Of lists alone: the stretch in the middle. -/
theorem forall₂_cut {α β : Type} {R : α → β → Prop} {l : List α} {a m c : List β}
    (h : List.Forall₂ R l (a ++ m ++ c)) :
    List.Forall₂ R ((l.drop a.length).take m.length) m := by
  have h2 := List.forall₂_take m.length (List.forall₂_drop a.length h)
  rw [List.append_assoc, List.drop_left, List.take_left] at h2
  exact h2

/-- **At a description's data**: where the first chain's declared rounds, without the sealing one,
are pre ++ the kind's ++ post. -/
theorem k5_public_at_data {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (hD : F.data file = .ok D) (p : Par) (pre post : List Fmt.DeclaredRound)
    (hdecl : F.roundsDeclaredByBlocks.1.dropLast = pre ++ rounds p ++ post) :
    (∀ d ∈ (D.ds₁.drop pre.length).take (rounds p).length, Plain (toRD d)) ∧
      ((D.ds₁.drop pre.length).take (rounds p).length).map (·.entry) =
        (rounds p).map (·.entry) ∧
      ∀ d ∈ (D.ds₁.drop pre.length).take (rounds p).length,
        Fmt.kindOf d.entry.name = some d.kind :=
  public_of_as p (forall₂_cut (hdecl ▸ (roundsOfData F file D hD).1))

#print axioms public_of_as
#print axioms k5_public_at_data

end VerifiableInference.Desc.First.Att.P
