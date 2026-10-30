-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/LinksOnce.lean: THE LIST OF SEGMENTS THAT THE LOT OF THE KINDS K9 AND K10
WALKS (`ProofFile.k9Links (ProofFile.k9Stretches Z)`, Johnson/Desc/ProofFile/Lot/K9.lean): NO STRAY, NONE
TWICE. Lemmas on the description's maker's own text; no honest side's frame in them; none of the
library's goals. It imports no file of this folder.

  `count_le_flat`, `filter_le_flat`   two small ones on lists
  `where_in_links`  where `k9Where` yields numbers at l, `k9Links` lists l (a twin,
                   `links_of_where`, stands in Johnson/Desc/ProofFile/Honest/K10/LotLinks.lean,
                   which a tree may lack)
  `ownAt`, `own_is`   the lot's own blocks are, link by link of its list, `ownAt`: the closing's
                   three blocks, or one block that refuses
  `ownAt_k10`       among these is one of the kind K10, at that link
  `lot_in_all`      the lot, with its blocks, is among the opened seat's
  `link_once`       at a link of the list: it is one of the driver's links, and it is listed once
  `links_once`      under `IM.Open` (Johnson/IMR/SeatOpen.lean), AT EVERY OLDER HASH, WITH NO
                   PREMISE ON SCOPE: the list has no double, and its members are just the numbers
                   below the length of `ProofFile.subsOf Z`
  `links_scope`     in the goals' scope, at `OnBytes.secondHashFunction`: no double; just the l < 25

HOW. The opened seat has no fault (`IM.Open`'s field `sound`). So the block of the kind K10 that the
lot lays at a link of its list stands at a place of the shape (`IM.stands_in_shape`), which is one
of the driver's (`IM.shape_places`, `IM.k10_in_flat`, Johnson/IMR/LinkSeat.lean): no stray. And the
seat's test "the place is taken by more than one block" (`ProofFile.faultsOf`,
Johnson/Desc/ProofFile/Frames1.lean) counts the blocks at a place of the shape: a link that is
listed twice would lay two: none twice. The way forth: `IM.k9_alone`.

Limits. NOTHING ON THE ORDER OF THE LIST: no equation with `List.range`. IT SAYS: WHERE THE MAKER
HAS RETURNED, THE LIST IS CLEAN; not that the text of `k9Links` is. `IM.Open` is had where the
maker returns (`IM.seat_open`, Johnson/IMR/SeatOpen.lean); whether it returns anywhere is no
theorem (Johnson/IMR/K6Seat.lean's head). No member. Nothing on soundness, completeness or hiding
of the protocol.

-/
import Johnson.IMR.LinkSeat
import Johnson.IMR.PlacesScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10.YesFree
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-! ## Two small ones on lists; one on the lot's two texts -/

theorem count_le_flat {β : Type} (G : Nat → List β) (P : β → Bool) (l : Nat)
    (h : ∃ y ∈ G l, P y = true) : ∀ L : List Nat, L.count l ≤ ((L.flatMap G).filter P).length
  | [] => Nat.le_refl _
  | a :: L => by
    have ih := count_le_flat G P l h L
    rw [List.flatMap_cons, List.filter_append, List.length_append, List.count_cons]
    by_cases e : a = l
    · subst e
      obtain ⟨y, hy, hP⟩ := h
      have h1 : 0 < ((G a).filter P).length :=
        List.length_pos_of_mem (List.mem_filter.2 ⟨hy, hP⟩)
      simp only [beq_self_eq_true, if_true]
      omega
    · have e' : (a == l) = false := by simpa using e
      simp only [e', Bool.false_eq_true, if_false]
      omega

theorem filter_le_flat.{u, v} {α : Type u} {β : Type v} (f : α → List β) (P : β → Bool) (a : α) :
    ∀ M : List α, a ∈ M → ((f a).filter P).length ≤ ((M.flatMap f).filter P).length
  | b :: M, h => by
    rw [List.flatMap_cons, List.filter_append, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := filter_le_flat f P a M h
      omega

/-- Where `k9Where` yields numbers at l, `k9Links` lists l. -/
theorem where_in_links {xs : List (ProofFile.Spot × List Fmt.DeclaredRound × Nat)} {l : Nat}
    {p : VerifiableInference.Desc.K9.Where}
    (h : ProofFile.k9Where xs l = some p) : l ∈ ProofFile.k9Links xs := by
  unfold ProofFile.k9Where at h
  obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.1 h
  have hm := List.mem_of_find?_eq_some hx
  have hp := List.find?_some hx
  unfold ProofFile.k9Links
  refine List.mem_filterMap.2 ⟨x, hm, ?_⟩
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨h1, h2⟩)]
  exact eq_of_beq h3

/-! ## The lot's own blocks, link by link -/

/-- What the lot lays at a link of its list. -/
def ownAt (Z : ProofFile.Pub) (l : Nat) : List (Block S Unit) :=
  match (ProofFile.k9Where (ProofFile.k9Stretches Z) l).bind fun p =>
      (ProofFile.k10Par Z (ProofFile.k9Stretches Z) p).map fun P => (p, P) with
  | some (p, P) => VerifiableInference.Desc.K9.closeOf p P
  | none => [ProofFile.refuser s!"link {l}: the closing" ⟨1, some l, 0, .K10⟩ "K9's or K10's numbers"]

theorem own_is (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (ProofFile.k9Ninth Z).own G = (ProofFile.k9Links (ProofFile.k9Stretches Z)).flatMap (ownAt Z) := by
  unfold ProofFile.k9Ninth
  dsimp only
  rw [List.flatMap_map]
  rfl

/-- Among them is one of the kind K10, at that link. -/
theorem ownAt_k10 (Z : ProofFile.Pub) (l : Nat) :
    ∃ y ∈ ownAt Z l, ∃ q, y.place = ⟨1, some l, q, .K10⟩ := by
  unfold ownAt
  split
  · rename_i p P h
    obtain ⟨p', hp', e⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨P', hP', e⟩ := Option.map_eq_some_iff.1 e
    cases e
    obtain ⟨_, h2, _⟩ := IM.k9Where_fields hp'
    obtain ⟨q1, _⟩ := IM.k10Par_fields hP'
    refine ⟨VerifiableInference.Desc.K9.closing P, by simp [VerifiableInference.Desc.K9.closeOf],
      P.piece, ?_⟩
    show (⟨1, some P.link, P.piece, .K10⟩ : Place) = _
    rw [q1, h2]
  · exact ⟨_, List.mem_singleton.2 rfl, 0, rfl⟩

/-! ## No stray, none twice -/

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem lot_in_all (O : IM.Open o pol lay KL F Z Bs base c A B) :
    (ProofFile.k9Ninth Z, (ProofFile.k9Ninth Z).blocks Bs.G₀) ∈ Bs.all := by
  obtain ⟨_, _, _, hall⟩ := IM.base_made O.made
  rw [hall]
  refine List.mem_map.2 ⟨ProofFile.k9Ninth Z, ?_, rfl⟩
  show ProofFile.k9Ninth Z ∈ ProofFile.onlineFirstChainBlockTables Z
  unfold ProofFile.onlineFirstChainBlockTables
  simp

/-- At a link of the list: the link is one of the driver's, and it is listed once. -/
theorem link_once (O : IM.Open o pol lay KL F Z Bs base c A B) {l : Nat}
    (hl : l ∈ ProofFile.k9Links (ProofFile.k9Stretches Z)) :
    l < (ProofFile.subsOf Z).length ∧ (ProofFile.k9Links (ProofFile.k9Stretches Z)).count l ≤ 1 := by
  obtain ⟨hs, hsh, _, _⟩ := IM.base_made O.made
  obtain ⟨y, hy, q, hq⟩ := ownAt_k10 Z l
  have hin := lot_in_all O
  have hyo : y ∈ (ProofFile.k9Ninth Z).own Bs.G₀ := by
    rw [own_is]
    exact List.mem_flatMap.2 ⟨l, hl, hy⟩
  have hyb : (y.retype : Block S Cl) ∈ (ProofFile.k9Ninth Z).blocks Bs.G₀ :=
    List.mem_append_left _ (List.mem_map.2 ⟨y, hyo, rfl⟩)
  have hya : (y.retype : Block S Cl) ∈ Bs.all.flatMap fun x => x.2 :=
    List.mem_flatMap.2 ⟨_, hin, hyb⟩
  have hpl : (y.retype : Block S Cl).place = ⟨1, some l, q, .K10⟩ := hq
  obtain ⟨e, he, ee⟩ := IM.stands_in_shape O.sound hya (by rw [hpl]; exact fun h => nomatch h)
  obtain ⟨several, hsp⟩ := IM.shape_places hsh
  have hm : (⟨1, some l, q, .K10⟩ : Place) ∈
      VerifiableInference.Desc.First.flatPlacesOf (ProofFile.subsOf Z) several := by
    rw [← hsp, ← hpl, ← ee]
    exact List.mem_map.2 ⟨e, he, rfl⟩
  obtain ⟨sub, hsub, _⟩ := IM.k10_in_flat hm
  refine ⟨(List.getElem?_eq_some_iff.1 hsub).1, ?_⟩
  have hf := O.sound
  simp only [ProofFile.faultsAt, ProofFile.faultsOf, List.append_eq_nil_iff, List.map_eq_nil_iff] at hf
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, -⟩, -⟩, -⟩, -⟩ := hf
  have h4 := List.filter_eq_nil_iff.1 h3 e he
  have h5 : ((Bs.all.flatMap fun x => x.2).filter fun b => b.place == e.2).length ≤ 1 := by
    simpa using h4
  have c1 := count_le_flat (ownAt Z) (fun x : Block S Unit => x.place == e.2) l
    ⟨y, hy, by
      show (y.place == e.2) = true
      rw [ee, hpl, hq]
      exact beq_self_eq_true _⟩ (ProofFile.k9Links (ProofFile.k9Stretches Z))
  rw [← own_is Z Bs.G₀] at c1
  have c2 : (((ProofFile.k9Ninth Z).own Bs.G₀).filter fun x : Block S Unit => x.place == e.2).length ≤
      (((ProofFile.k9Ninth Z).blocks Bs.G₀).filter fun b : Block S Cl => b.place == e.2).length := by
    show _ ≤ ((((ProofFile.k9Ninth Z).own Bs.G₀).map fun b => (b.retype : Block S Cl)) ++ _ |>.filter
      fun b : Block S Cl => b.place == e.2).length
    rw [List.filter_append, List.length_append, List.filter_map, List.length_map]
    exact Nat.le_add_right _ _
  have c3 := filter_le_flat (fun x : ProofFile.Lot × List (Block S Cl) => x.2)
    (fun b : Block S Cl => b.place == e.2) _ Bs.all hin
  exact Nat.le_trans c1 (Nat.le_trans c2 (Nat.le_trans c3 h5))

/-- **NO STRAY, NONE TWICE**, at every older hash, with no premise on scope: the list has no
double, and its members are just the numbers of the driver's links. -/
theorem links_once (O : IM.Open o pol lay KL F Z Bs base c A B) :
    (ProofFile.k9Links (ProofFile.k9Stretches Z)).Nodup ∧
      ∀ l, l ∈ ProofFile.k9Links (ProofFile.k9Stretches Z) ↔ l < (ProofFile.subsOf Z).length := by
  refine ⟨List.nodup_iff_count_le_one.2 fun l => ?_,
    fun l => ⟨fun h => (link_once O h).1, fun h => ?_⟩⟩
  · by_cases h : l ∈ ProofFile.k9Links (ProofFile.k9Stretches Z)
    · exact (link_once O h).2
    · rw [List.count_eq_zero_of_not_mem h]
      exact Nat.zero_le _
  · obtain ⟨_, p, _, hp, _⟩ := IM.k9_alone O l _ (List.getElem?_eq_getElem h)
    exact where_in_links hp

end

/-- **IN SCOPE: JUST THE 25, EACH ONCE.** -/
theorem links_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    (ProofFile.k9Links (ProofFile.k9Stretches Z)).Nodup ∧
      ∀ l, l ∈ ProofFile.k9Links (ProofFile.k9Stretches Z) ↔ l < 25 := by
  have h := links_once O
  rw [IM.subs_len hS hR O] at h
  exact h

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.links_once
#print axioms ProofFile.Honest.K10.YesFree.links_scope
