-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OpenAtEnd.lean: THE TWO TESTS ON THE FIRST TABLE's LAST BORDER, AS THEOREMS FOR
EVERY LIST OF SEGMENTS: "(Eval) is laid" is open there AT EVERY DOOR; "W sits as the plan says" is
open there at every door that holds wSitsMore and whose row at the seal does not drop that name.
Statements with their proofs; no definition.

Why. The table's owner's laws at the shared chain's point, and row 0 of the last chain's table, take
from the first chain's last promise that (Eval) is laid and that W sits (hEL_at_ocEnd,
point_leadsB_at_ocEnd, point_leadsB_layers: h2, h3). Elsewhere the two tests are had by the kernel
at two written lists and at an empty door merged with wSitsMore (evalLaid_open,
Johnson/Desc/K13/Law/LaidToEnd.lean): each caller bears "the list is one of the two" and "the door
is empty", and at a composed meaning, whose door is not empty, the tests are to be run anew.

OBJECT   First.pubSets M links (First.flatPlaces true links true): the table's own text.
USER     h2 | h3 of the owner's three laws; h2 of rowZeroOwed_atJoint
         (Johnson/Flat/Last/RowZeroAtJoint.lean). evalLaid_open_all is called in
         Johnson/Flat/Last/RowZeroAtPlaces.lean and Johnson/Desc/K14/Law/LedgerFieldLaid.lean, among
         others.
LETTERS  M · links.
FIELD    leads3_last_chains_table · shared_joint_count (Johnson/Goal/Skeleton/ProofFile.lean).

  pubSetsBy_last       the last of the open public sets is the fold of the steps.
  mem_step_made | mem_step_kept   a step's two ways in.
  flat_tail            the list of places ends in W's sending (kind K1, piece 4) and the seal.
  open_of_made         an item that the row at W's sending makes and the row at the seal does not
                       drop is open at the last border.
  evalLaid_open_all    **h2 at every M and every links**: a door adds and drops NAMED items alone
                       (moreItem): it cannot drop one of the table's own.
  wSits_open_all       **h3** at A.merge wSitsMore, where A's row at the seal does not drop the
                       name.
What is not claimed. That links is a plan's, or the list a description's own places. several :=
true alone (there is a joining block). That the promise at the last border is earned. Nothing on
soundness.

-/
import Johnson.Desc.K13.Law.SitsDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (ModelPart Pub More PubRow pubSets pubSetsBy pubStep pubRowM pubRowOf
  pubStartM flatPlaces flatPlacesOf moreItem)

/-- The last of the open public sets is the fold of the steps. -/
theorem pubSetsBy_last (rows : Place → PubRow) : ∀ (ps : List Place) (Q : List Pub),
    (pubSetsBy rows ps Q)[ps.length]? = some (ps.foldl (fun Q p => pubStep Q (rows p)) Q)
  | [], _ => rfl
  | p :: ps, Q => by
    show (Q :: pubSetsBy rows ps (pubStep Q (rows p)))[ps.length + 1]? = _
    rw [List.getElem?_cons_succ]
    exact pubSetsBy_last rows ps _

/-- What a row makes is open behind. -/
theorem mem_step_made {Q : List Pub} {r : PubRow} {q : Pub} (h : q ∈ r.makes) :
    q ∈ pubStep Q r := by
  unfold pubStep
  by_cases hq : q ∈ Q.filter fun x => !r.drops.contains x
  · exact List.mem_append_left _ hq
  · refine List.mem_append_right _ (List.mem_filter.2 ⟨h, ?_⟩)
    show (!(List.contains (Q.filter fun x => !r.drops.contains x) q)) = true
    cases hc : List.contains (Q.filter fun x => !r.drops.contains x) q with
    | true => exact absurd (List.contains_iff_mem.1 hc) hq
    | false => rfl

/-- What is open in front and is not dropped is open behind. -/
theorem mem_step_kept {Q : List Pub} {r : PubRow} {q : Pub} (h : q ∈ Q) (hd : q ∉ r.drops) :
    q ∈ pubStep Q r := by
  unfold pubStep
  refine List.mem_append_left _ (List.mem_filter.2 ⟨h, ?_⟩)
  simpa using hd

/-- W's sending's place, and the seal's. -/
abbrev placeW : Place := { chain := 1, link := none, piece := 4, kind := .K1 }
abbrev placeSeal : Place := { chain := 1, link := none, piece := 5, kind := .frame }

/-- The list of places ends in W's sending and the seal. -/
theorem flat_tail (links : List ModelPart) :
    ∃ pre, flatPlaces true links true = pre ++ [placeW, placeSeal] := by
  refine ⟨First.frameAt none 0 :: (links.zipIdx.flatMap fun x => First.linkPlaces x.2 x.1) ++
    [{ chain := 1, link := none, piece := 1, kind := .K2 },
      { chain := 1, link := none, piece := 2, kind := .K12 },
      { chain := 1, link := none, piece := 3, kind := .K13 }], ?_⟩
  show flatPlacesOf links true = _
  unfold flatPlacesOf
  simp [First.addresses, First.backKinds, First.frameAt, List.zipIdx]

/-- **An item that the row at W's sending makes and the row at the seal does not drop is open at
the first chain's last border.** -/
theorem open_of_made (M : More) (links : List ModelPart) (q : Pub)
    (hm : q ∈ (pubRowM M links placeW).makes) (hd : q ∉ (pubRowM M links placeSeal).drops) :
    q ∈ (pubSets M links (flatPlaces true links true))[(flatPlaces true links
      true).length]?.getD [] := by
  obtain ⟨pre, hp⟩ := flat_tail links
  unfold pubSets
  rw [pubSetsBy_last, hp, List.foldl_append]
  exact mem_step_kept (mem_step_made hm) hd

/-- **h2 AT EVERY DOOR AND EVERY LIST OF SEGMENTS.** -/
theorem evalLaid_open_all (M : More) (links : List ModelPart) :
    Pub.evalLaid ∈ (pubSets M links (flatPlaces true links true))[(flatPlaces true links
      true).length]?.getD [] := by
  refine open_of_made M links _ (List.mem_append_left _ (List.mem_singleton.2 rfl)) ?_
  intro h
  rcases List.mem_append.1 h with h | h
  · cases h
  · obtain ⟨x, _, hx⟩ := List.mem_map.1 h
    cases hx

/-- **h3**, at a door that holds wSitsMore. -/
theorem wSits_open_all (A : More) (links : List ModelPart)
    (hA : ((none, "K13.wSits") : First.MoreName) ∉ (A.rows links placeSeal).drops) :
    wSitsItem ∈ (pubSets (A.merge wSitsMore) links (flatPlaces true links
      true))[(flatPlaces true links true).length]?.getD [] := by
  refine open_of_made _ links _ ?_ ?_
  · refine List.mem_append_right _ (List.mem_map.2 ⟨(none, "K13.wSits"), ?_, rfl⟩)
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  · intro h
    rcases List.mem_append.1 h with h | h
    · cases h
    · obtain ⟨x, hx, he⟩ := List.mem_map.1 h
      have hx' : x ∈ (A.rows links placeSeal).drops ++ (wSitsMore.rows links placeSeal).drops := hx
      have e : x = (none, "K13.wSits") := by
        obtain ⟨a, b⟩ := x
        have he' : Pub.more a b = Pub.more none "K13.wSits" := he
        cases he'
        rfl
      subst e
      rcases List.mem_append.1 hx' with h1 | h1
      · exact hA h1
      · cases h1

end VerifiableInference.Desc.K13.Law
