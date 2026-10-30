-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/Leaves/OneK7.lean: THE DRIVER's TABLE OF PLACES HOLDS JUST ONE PLACE OF THE KIND
K7, where its test on the list of parts (`linksOk`) says yes: the first place of the head's segment,
and the head is the last part and stands nowhere else.
  `fst_mem_of_zipIdx`, `mem_addresses`: what a member of a numbered list, and of `addresses`, is.
  `hear_K7`: among a segment's kinds in front of its batching K7 stands only in the head's, first.
  `head_last`: in a list whose members but the last are not the head, the head has the last number.
  `linkPlaces_K7`, `flatPlaces_K7`: a place of the kind K7 in the table is ⟨1, some i, 1, K7⟩ with
    the head at number i.
  **`flatPlaces_K7_one`**: two places of the kind K7 in the table are one.
  `linkPlaces_count`, `links_count`, **`flatPlaces_count`**: and that place stands at just one ENTRY
    of the table. `firstChain_count`: so just one entry of the first chain's flat list stands there.
  `cut_pins`: where that list is cut at such a block, none stands in front of the cut or behind it.
Limits. Facts on the driver's table of places (Johnson/Desc/First/Driver/Chain.lean), and on the
flat list's places by `flat_places`. Nothing on what a block decides.

-/
import Johnson.Desc.Plain.Leaves.HasK7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

theorem fst_mem_of_zipIdx {α : Type} (x : α) (i : Nat) : ∀ (l : List α) (n : Nat),
    (x, i) ∈ l.zipIdx n → x ∈ l
  | [], _, h => by cases h
  | a :: l, n, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with e | h
    · rw [(Prod.mk.inj e).1]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (fst_mem_of_zipIdx x i l (n + 1) h)

theorem mem_addresses {link : Option Nat} {ks : List KindName} {a : Place}
    (h : a ∈ addresses link ks) : ∃ k j, (k, j) ∈ ks.zipIdx ∧ a = ⟨1, link, j + 1, k⟩ := by
  unfold addresses at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  exact ⟨x.1, x.2, hx, rfl⟩

/-- Among a segment's kinds in front of its batching, K7 stands only in the head's, first. -/
theorem hear_K7 (sub : ModelPart) (first : Bool) (j : Nat)
    (h : (KindName.K7, j) ∈ (kindsBeforeBatching sub first).zipIdx) : sub = .head ∧ j = 0 := by
  cases sub <;> cases first <;> simp [kindsBeforeBatching, kindOfModelPart, List.zipIdx_cons] at h <;>
    exact ⟨rfl, h⟩

/-- In a list whose members but the last are not the head, the head has the last number. -/
theorem head_last : ∀ (l : List ModelPart) (n i : Nat), (∀ x ∈ l.dropLast, x ≠ ModelPart.head) →
    (ModelPart.head, i) ∈ l.zipIdx n → i + 1 = n + l.length
  | [], _, _, _, h => by cases h
  | [a], n, i, _, h => by
    rw [List.zipIdx_cons, List.zipIdx_nil] at h
    have e := List.mem_singleton.1 h
    rw [(Prod.mk.inj e).2]
    rfl
  | a :: b :: t, n, i, hd, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with e | h
    · exact absurd (Prod.mk.inj e).1.symm (hd a (by rw [List.dropLast_cons₂]; exact
        List.mem_cons_self))
    · have := head_last (b :: t) (n + 1) i
        (fun x hx => hd x (by rw [List.dropLast_cons₂]; exact List.mem_cons_of_mem _ hx)) h
      rw [this, List.length_cons, List.length_cons, List.length_cons]
      omega

theorem linkPlaces_K7 (l : Nat) (sub : ModelPart) (a : Place) (h : a ∈ linkPlaces l sub)
    (hk : a.kind = .K7) : sub = .head ∧ a = ⟨1, some l, 1, .K7⟩ := by
  unfold linkPlaces at h
  dsimp only at h
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h
  rcases h with (((rfl | h) | (rfl | rfl)) | h) | rfl
  · cases hk
  · obtain ⟨k, j, hkj, rfl⟩ := mem_addresses h
    obtain rfl : k = .K7 := hk
    obtain ⟨rfl, rfl⟩ := hear_K7 sub _ j hkj
    exact ⟨rfl, rfl⟩
  · cases hk
  · cases hk
  · unfold closeAddresses at h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    have hm := fst_mem_of_zipIdx x.1 x.2 closeKinds 0 hx
    have hk' : x.1 = .K7 := hk
    rw [hk'] at hm
    simp [closeKinds] at hm
  · cases hk

theorem flatPlaces_K7 (links : List ModelPart) (several : Bool) (a : Place)
    (h : a ∈ flatPlacesOf links several) (hk : a.kind = .K7) :
    ∃ i, (ModelPart.head, i) ∈ links.zipIdx ∧ a = ⟨1, some i, 1, .K7⟩ := by
  unfold flatPlacesOf at h
  simp only [List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil, or_false] at h
  rcases h with ((rfl | ⟨x, hx, h⟩) | h) | rfl
  · cases hk
  · obtain ⟨e, rfl⟩ := linkPlaces_K7 x.2 x.1 a h hk
    exact ⟨x.2, by rw [← e]; exact hx, rfl⟩
  · obtain ⟨k, j, hkj, rfl⟩ := mem_addresses h
    have hm := fst_mem_of_zipIdx k j _ 0 hkj
    obtain rfl : k = .K7 := hk
    cases several <;> simp [backKinds] at hm
  · cases hk

/-- **Two places of the kind K7 in the table are one.** -/
theorem flatPlaces_K7_one (links : List ModelPart) (several : Bool) (hl : linksOk links = true)
    (a b : Place) (ha : a ∈ flatPlacesOf links several) (hb : b ∈ flatPlacesOf links several)
    (hka : a.kind = .K7) (hkb : b.kind = .K7) : a = b := by
  obtain ⟨i, hi, rfl⟩ := flatPlaces_K7 links several a ha hka
  obtain ⟨j, hj, rfl⟩ := flatPlaces_K7 links several b hb hkb
  unfold linksOk at hl
  have hd : ∀ x ∈ links.dropLast, x ≠ ModelPart.head := by
    intro x hx
    have := List.all_eq_true.1 (Bool.and_eq_true_iff.1 hl).2 x hx
    simpa using this
  have e1 := head_last links 0 i hd hi
  have e2 := head_last links 0 j hd hj
  have : i = j := by omega
  rw [this]

/-- The test "the place's kind is K7". -/
def isK7 (a : Place) : Bool := a.kind == .K7

/-- A segment's places hold one of the kind K7 if it is the head's, else none. -/
theorem linkPlaces_count (l : Nat) (sub : ModelPart) :
    (linkPlaces l sub).countP isK7 = if sub = .head then 1 else 0 := by
  cases sub <;> cases h : (l == 0) <;>
    simp [linkPlaces, kindsBeforeBatching, kindOfModelPart, addresses, closeAddresses, closeKinds, frameAt, isK7, h,
      List.zipIdx_cons]

/-- The segments' places in a row hold one, where the head is last and stands nowhere else. -/
theorem links_count : ∀ (l : List ModelPart) (n : Nat), (∀ x ∈ l.dropLast, x ≠ ModelPart.head) →
    l.getLast? = some ModelPart.head →
    ((l.zipIdx n).flatMap fun x => linkPlaces x.2 x.1).countP isK7 = 1
  | [], _, _, h => by cases h
  | [a], n, _, h => by
    obtain rfl : a = ModelPart.head := by simpa using h
    rw [List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      linkPlaces_count]
    rfl
  | a :: b :: t, n, hd, h => by
    have ha : a ≠ ModelPart.head := hd a (by rw [List.dropLast_cons₂]; exact List.mem_cons_self)
    rw [List.zipIdx_cons, List.flatMap_cons, List.countP_append, linkPlaces_count, if_neg ha,
      Nat.zero_add]
    exact links_count (b :: t) (n + 1)
      (fun x hx => hd x (by rw [List.dropLast_cons₂]; exact List.mem_cons_of_mem _ hx))
      (by rw [List.getLast?_cons_cons] at h; exact h)

/-- **The table holds a place of the kind K7 at just one entry.** -/
theorem flatPlaces_count (links : List ModelPart) (several : Bool) (hl : linksOk links = true) :
    (flatPlacesOf links several).countP isK7 = 1 := by
  unfold linksOk at hl
  have h1 : links.getLast? = some ModelPart.head := eq_of_beq (Bool.and_eq_true_iff.1 hl).1
  have hd : ∀ x ∈ links.dropLast, x ≠ ModelPart.head := by
    intro x hx
    have := List.all_eq_true.1 (Bool.and_eq_true_iff.1 hl).2 x hx
    simpa using this
  have hb : (addresses none (backKinds several)).countP isK7 = 0 := by
    cases several <;> simp [addresses, backKinds, isK7, List.zipIdx_cons]
  unfold flatPlacesOf
  rw [List.countP_append, List.countP_append, List.countP_cons, links_count links 0 hd h1, hb]
  simp [frameAt, isK7]

variable {S Cl : Type}

/-- **The first chain's flat list holds a block at a place of the kind K7 at just one entry.** -/
theorem firstChain_count {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c : Chain S Cl}
    (h : firstChain H links several = some c) :
    c.blocksInOrder.countP (fun b => isK7 b.place) = 1 := by
  have e := flatPlaces_count links several (firstChain_linksOk h)
  rw [← flat_places H links several c h, List.countP_map] at e
  exact e

/-- Where a list holds one such entry and is cut at one: none stands in front of the cut or behind
it. -/
theorem cut_pins (l pre post : List (Block S Cl)) (blk : Block S Cl) (hcut : l = pre ++ blk :: post)
    (hk : blk.place.kind = .K7) (hc : l.countP (fun b => isK7 b.place) = 1) :
    (∀ c ∈ pre, c.place.kind ≠ .K7) ∧ ∀ c ∈ post, c.place.kind ≠ .K7 := by
  have hb : isK7 blk.place = true := by unfold isK7; rw [hk]; rfl
  rw [hcut, List.countP_append, List.countP_cons] at hc
  simp only [hb, if_true] at hc
  have h1 : pre.countP (fun b => isK7 b.place) = 0 := by omega
  have h2 : post.countP (fun b => isK7 b.place) = 0 := by omega
  refine ⟨fun c hc' e => ?_, fun c hc' e => ?_⟩
  · exact List.countP_eq_zero.1 h1 c hc' (by unfold isK7; rw [e]; rfl)
  · exact List.countP_eq_zero.1 h2 c hc' (by unfold isK7; rw [e]; rfl)

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.flatPlaces_K7_one
#print axioms VerifiableInference.Desc.First.flatPlaces_count
#print axioms VerifiableInference.Desc.First.firstChain_count
#print axioms VerifiableInference.Desc.First.cut_pins
