-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/XchAtBookKit.lean: the closing of a segment (K10): at the written book, the entries by which a part of the first
chain carries, each as owner, start and count, are a list that Lean's kernel can evaluate: the text of `segmentCarriesAt`
(Johnson/Desc/ProofFile/Honest/BookCarryKit.lean) on the digest of the written messages with each message's start.

  `viewE`, `Rw`, `tv`, `dg2`, `pickV`   an entry as three fields; a row of the digest with its start; the text on such rows
  `carries_view`     that text is `segmentCarriesAt`'s: at every list of messages
  `rsW`, `rows_written`   the rows of the written messages
  **`carried_view`**   at the book that the maker returns at the written description: the carrying entries at an address of the
                    first chain, as three fields, are the text at the written rows
  `at_view`          a member of such a view comes from an entry at the same number
  `find_key`         in a list whose keys are apart a member is what a search by its key finds

Limits. Owners, starts and counts alone; the names are in PaysByTriples.lean. Written values alone, at the full size.
-/
import AtFullSide.K10.PaysByDigest
import AtFullSide.K10.PaysBook
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10 AtFullSide.K14
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- An entry as owner, start, count. -/
def viewE (e : Ahead) : Addr × Due × Due := (e.owner, e.start, e.count)

/-- A row of the digest, with the message's start. -/
abbrev Rw : Type := Dg × Due

/-- A row as owner, start, count. -/
def tv (m : Rw) : Addr × Due × Due := (m.1.b.sender, m.2, m.1.b.count)

/-- What is read of a message, with its start. -/
def dg2 (m : SentMsg) : Rw := (dg m, m.start)

/-- The text of `segmentCarriesAt` on such rows. -/
def pickV (bf : Nat → Option (Addr × Addr)) (rs : List Rw) (a : Addr) : List Rw :=
  (rs.filter fun m => m.1.fresh && m.1.link.isSome).flatMap fun f =>
    match bf f.1.round, f.1.link with
    | some (p, q), some l =>
      (if p == a then rs.filter (fun m => !m.1.masks && (m.1.link.any fun j =>
          decide (j < l) || (j == l && !m.1.fresh))) else []) ++
      (if q == a then rs.filter (fun m => !m.1.masks && (m.1.link.any fun j =>
          decide (j ≤ l))) else [])
    | _, _ => []

/-- One filter's messages, carried and viewed. -/
theorem view_map (ms : List SentMsg) (F : Dg → Bool) (a : Addr) :
    ((ms.filter fun m => F (dg m)).map (·.carry a)).map viewE =
      ((ms.map dg2).filter fun m => F m.1).map tv := by
  rw [List.filter_map, List.map_map, List.map_map]
  rfl

/-- **The text on rows is `segmentCarriesAt`'s.** -/
theorem carries_view (here : List PlanB) (ms : List SentMsg) (a : Addr) :
    (segmentCarriesAt here ms a).map viewE = (pickV (behindFold here) (ms.map dg2) a).map tv := by
  unfold segmentCarriesAt pickV
  rw [List.map_flatMap, List.map_flatMap, List.filter_map, List.flatMap_map]
  refine flatMap_ext _ fun f _ => ?_
  show (match behindFold here f.round, linkOf f.label with
    | some (p, q), some l => _
    | _, _ => []).map viewE = (match behindFold here f.round, linkOf f.label with
    | some (p, q), some l => _
    | _, _ => []).map tv
  generalize behindFold here f.round = o₁
  generalize linkOf f.label = o₂
  rcases o₁ with _ | ⟨p, q⟩
  · rfl
  · rcases o₂ with _ | l
    · rfl
    · show ((if p == a then _ else []) ++ (if q == a then _ else [])).map viewE =
        ((if p == a then _ else []) ++ (if q == a then _ else [])).map tv
      rw [List.map_append, List.map_append]
      congr 1
      · split
        · exact view_map ms (fun m => !m.masks && (m.link.any fun j =>
            decide (j < l) || (j == l && !m.fresh))) a
        · rfl
      · split
        · exact view_map ms (fun m => !m.masks && (m.link.any fun j => decide (j ≤ l))) a
        · rfl

/-- The written messages' digest, each row with its start. -/
def rsW : List Rw := dgW.zip (sentFirstW.map (·.start))

theorem map_pair {α β γ : Type} (f : α → β) (g : α → γ) :
    ∀ l : List α, l.map (fun x => (f x, g x)) = (l.map f).zip (l.map g)
  | [] => rfl
  | x :: l => by
    simp only [List.map_cons, List.zip_cons_cons]
    rw [map_pair f g l]

theorem rows_written : sentFirstW.map dg2 = rsW := by
  unfold rsW
  rw [← digest_written]
  exact map_pair dg (·.start) sentFirstW

/-- **At the book that the maker returns at the written description the carrying entries at an address of the first chain are
the text at the written rows.** -/
theorem carried_view {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
                (mergesByName WP.first.blocksInOrder) = .ok B) {a : Addr} (ha : a.place ∈ WP.first.blocksInOrder.map (·.place)) :
    (K12.Light.carriedOf B a).map viewE = (pickV bfW rsW a).map tv := by
  obtain ⟨m0, hm, e⟩ := bookWhole_carries hB P2Law.ProofPlan.wp_placesOk ha
  obtain rfl : sentFirstW = m0 := Except.ok.inj (sentIn_first_written.symm.trans hm)
  have e' : K12.Light.carriedOf B a = segmentCarriesAt (planOf WP.first.blocksInOrder) sentFirstW a := e
  rw [e', carries_view, bf_written, rows_written]

/-- A member of a view comes from an entry at the same number. -/
theorem at_view {l : List Ahead} {v : Addr × Due × Due} {i : Nat} (h : (l.map viewE)[i]? = some v) :
    ∃ e, l[i]? = some e ∧ viewE e = v := by
  rw [List.getElem?_map] at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨e, he, rfl⟩

/-- In a list whose keys are apart a member is what a search by its key finds. -/
theorem find_key {α : Type} (k : α → Nat) : ∀ {l : List α} {x : α}, (l.map k).Nodup → x ∈ l →
    l.find? (fun y => k y == k x) = some x
  | [], _, _, hx => by cases hx
  | y :: l, x, hn, hx => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hx with rfl | h
    · simp
    · have hne : k y ≠ k x := fun e => hn.1 (e ▸ List.mem_map_of_mem h)
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact find_key k hn.2 h

end AtFullSide.K10

#print axioms AtFullSide.K10.view_map
#print axioms AtFullSide.K10.carries_view
#print axioms AtFullSide.K10.map_pair
#print axioms AtFullSide.K10.rows_written
#print axioms AtFullSide.K10.carried_view
#print axioms AtFullSide.K10.at_view
#print axioms AtFullSide.K10.find_key
