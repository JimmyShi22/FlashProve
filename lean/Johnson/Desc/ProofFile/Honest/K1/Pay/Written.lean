-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Pay/Written.lean: TWO TESTS ON A PLAN, ASKED OF LEAN's KERNEL AT THE
WRITTEN DESCRIPTION WP, AND WHAT THEY GIVE: at a place of the kind K1 the rounds are "SEND seed",
"SEND answer"; behind no fold does the first "SEND seed" stand at such a place. Under the head every
description is alike to WP (K14.planAlike_at_head), so that planOf is the same there.

  k1Names, qTest       the two tests, with code
  sendOnly_of_names    the first gives SendOnly (NoSpender.lean) at a place of the kind K1
  behind_not_k1        the second: the second address of a fold is at no such place
  written_first, written_shared, written_second   the two tests at WP's three chains, by the kernel
  written_counts       WP's chains have 52, 2 and 0 sub-protocols of the kind K1

Limits. The public plan alone. Nothing on any property of the protocol.
-/
import Johnson.AtFull.ProofPlan.WP
import Johnson.IMR.K1Scope
import Johnson.Desc.ProofFile.Honest.K1.Pay.NoSpender

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1.Pay
open VerifiableInference.Desc (Block FileDescription Place KindName)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow ProofFile.Honest.BookPlain
open P2Law.ProofPlan (WP)

/-- **Every sub-protocol of the kind K1 has the rounds of a sending.** -/
def k1Names (l : List PlanB) : Bool :=
  l.all fun x => x.place.kind != .K1 ||
    x.rounds.map (·.entry.name) == ["SEND seed", "SEND answer"]

/-- The address of the first "SEND seed" behind round number e. -/
def seedBehind (l : List PlanB) (e : Nat) : Option Addr :=
  (((l.flatMap (·.rounds)).zipIdx.drop (e + 1)).find? fun r => r.1.entry.name == "SEND seed").bind
    fun s => addrIn l s.2

/-- **Behind no "FOLD epsilon" does the first "SEND seed" stand at the kind K1.** -/
def qTest (l : List PlanB) : Bool :=
  ((l.flatMap (·.rounds)).zipIdx.filter fun r => r.1.entry.name == "FOLD epsilon").all fun r =>
    (seedBehind l r.2).all fun q => q.place.kind != .K1

theorem names_of {l : List PlanB} (ht : k1Names l = true) {x : PlanB} (hx : x ∈ l)
    (hk : x.place.kind = .K1) : x.rounds.map (·.entry.name) = ["SEND seed", "SEND answer"] := by
  have h := List.all_eq_true.1 ht x hx
  rw [hk] at h
  simpa using h

theorem sendOnly_of_names {l : List PlanB} (ht : k1Names l = true) {a : Place}
    (ha : a.kind = .K1) : SendOnly a l := by
  intro x hx ex d hd
  have e := names_of ht hx (by rw [ex]; exact ha)
  have hm : d.entry.name ∈ x.rounds.map (·.entry.name) := List.mem_map_of_mem hd
  rw [e] at hm
  simpa using hm

theorem behind_not_k1 {l : List PlanB} (ht : qTest l = true) {i : Nat} {p q : Addr}
    (h : behindFold l i = some (p, q)) : q.place.kind ≠ .K1 := by
  have h' : ((foldBehind l i).bind fun f =>
      ((((l.flatMap (·.rounds)).zipIdx.drop (f.1 + 1)).find? fun r =>
        r.1.entry.name == "SEND seed").bind fun s => addrIn l s.2).bind fun q =>
          (addrIn l f.1).map fun p => (p, q)) = some (p, q) := h
  obtain ⟨f, hf, h1⟩ := opt_bind h'
  obtain ⟨q', hq, h2⟩ := opt_bind h1
  obtain ⟨p', -, e⟩ := opt_map h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨f1, f2, f3⟩ := f
  obtain ⟨d, hd, hn⟩ := foldBehind_name hf
  have hmem : (d, f1) ∈ (l.flatMap (·.rounds)).zipIdx.filter
      fun r => r.1.entry.name == "FOLD epsilon" :=
    List.mem_filter.2 ⟨List.mem_zipIdx_iff_getElem?.2 hd, by simpa using hn⟩
  have hall := List.all_eq_true.1 ht _ hmem
  have hs : seedBehind l f1 = some q' := hq
  dsimp only at hall
  rw [hs] at hall
  simpa using hall

set_option maxRecDepth 1000000 in
theorem written_first : k1Names (planOf WP.first.blocksInOrder) = true ∧
    qTest (planOf WP.first.blocksInOrder) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem written_shared : k1Names (planOf WP.shared.blocksInOrder) = true ∧
    qTest (planOf WP.shared.blocksInOrder) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem written_second : k1Names (planOf WP.second.blocksInOrder) = true ∧
    qTest (planOf WP.second.blocksInOrder) = true := by decide +kernel

/-- How many sub-protocols of the kind K1 a plan has. -/
def k1Count (l : List PlanB) : Nat := (l.filter (·.place.kind == .K1)).length

theorem k1Count_planOf {S Cl : Type} (bs : List (Block S Cl)) :
    (bs.filter (·.place.kind == .K1)).length = k1Count (planOf bs) := by
  unfold k1Count planOf
  rw [List.filter_map, List.length_map]
  rfl

set_option maxRecDepth 1000000 in
theorem written_counts : k1Count (planOf WP.first.blocksInOrder) = 52 ∧
    k1Count (planOf WP.shared.blocksInOrder) = 2 ∧ k1Count (planOf WP.second.blocksInOrder) = 0 := by decide +kernel

/-- The 52 places of the kind K1 in the first chain: the opening; each link's reads and digits; W's
sending. -/
def k1PlacesW : List Place :=
  ⟨1, some 0, 1, .K1⟩ ::
    (List.range 25).flatMap (fun l => [IM.k1PlaceL l false, IM.k1PlaceL l true]) ++
      [⟨1, none, 4, .K1⟩]

/-- The two places of the kind K1 in the shared chain. -/
def k1PlacesS : List Place := [⟨2, none, 2, .K1⟩, ⟨2, none, 5, .K1⟩]

/-- **Every sub-protocol of the kind K1 stands at a place of the list.** -/
def placesTest (ps : List Place) (l : List PlanB) : Bool :=
  l.all fun x => x.place.kind != .K1 || ps.contains x.place

theorem place_of_test {ps : List Place} {l : List PlanB} (ht : placesTest ps l = true) {x : PlanB}
    (hx : x ∈ l) (hk : x.place.kind = .K1) : x.place ∈ ps := by
  have h := List.all_eq_true.1 ht x hx
  rw [hk] at h
  simpa using h

set_option maxRecDepth 1000000 in
theorem written_places : placesTest k1PlacesW (planOf WP.first.blocksInOrder) = true ∧
    placesTest k1PlacesS (planOf WP.shared.blocksInOrder) = true ∧
    placesTest [] (planOf WP.second.blocksInOrder) = true := by decide +kernel

end ProofFile.Honest.K1.Pay

#print axioms ProofFile.Honest.K1.Pay.sendOnly_of_names
#print axioms ProofFile.Honest.K1.Pay.behind_not_k1
#print axioms ProofFile.Honest.K1.Pay.written_first
#print axioms ProofFile.Honest.K1.Pay.written_shared
#print axioms ProofFile.Honest.K1.Pay.written_second
#print axioms ProofFile.Honest.K1.Pay.written_counts
#print axioms ProofFile.Honest.K1.Pay.written_places
