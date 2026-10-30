-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/KeyLeft.lean: what the sub-protocol behind a lookup's rounds
in the key file's first chain needs of what was heard: ten facts, from the hearing's return, on any
rounds, general in the face. Conditional. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md: see there hearing, heard structure, ledger, slot, form, planes and
leaves. In this file: p is the lookup's place (`PG`, Johnson/Desc/First/Look/K3LookupGeneral.lean); a debt
is an entry of the ledger's list owed, and `Fork.paid` marks it.

What is shown.
  `ScopedG n a`: the form a names no entry of a virtual row, and slots below n alone.
  `LeftG p g G cl G₂`: the ten facts. Here g and G are what was heard and the ledger behind the
    hearing; cl and G₂ are the three claims on the planes and the ledger in which the leaves'
    sumcheck is closed.
  `Fresh p F`: the ledger in front: arrays of the right size; the place's first slot has the number
    0; nothing taken yet; room for just the lookup's slots; all free.
  `paid_ne`, `paid_at`, `paid_keeps`, `paid_size`: marking a debt (`h`: another number; a number
    within the list; a debt that is marked already).
  `leftG_at`: the ten facts, at the claims and the ledger that the flat text of the claims on the
    planes returns.
  `leftG_of_hearV`: and it returns: so there are such claims and such a ledger.

Hypotheses that remain.
  `hF`: `Fresh p F`.
  `hh`: `hearV` returns.
  `hp`: (in `leftG_at`) the flat text of the claims on the planes (`planesG`, K3LookupGeneral.lean)
    returns.

Users. Honest/K3/Parts/KeyFresh.lean [not in this library] calls `leftG_of_hearV`;
Honest/K3/Parts/PacksGuards.lean [not in this library] imports this file. Whose the ten facts are:
they are the fields, in name, order and term, of a structure of the same ten facts that another file
on the key file's chain states as a hypothesis of its own theorem; that file is not imported here.

Limits. All statements are implications. An instance: Honest/K3/Parts/PacksGuards.lean
[not in this library] (by evaluation). The structure of which the facts speak is `toHeardG` of what
`hearV` heard: that the general flat hearing sets that structure where `hearV` returns is the
library's `hearV_flRun` (Johnson/Top/H/K3Via/Bridge.lean; Honest/K3/Law/PlanesGLetter.lean calls
it). These are facts on counts, on marks and on which slots a form names: no sent value is compared.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.Packs
import Johnson.Desc.ProofFile.Honest.K3.Parts.NoEntries
import Johnson.Desc.ProofFile.Honest.K3.Law.PlanesGLetter

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork Aff)
open OnBytes.K.Kc (Tape)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV HeardG PlaneClaim PG hearV planesV planesG toHeardG unpaidG
  doneG)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Digits (heard_counts unpaid_behind row_owed)

/-! ## 1 The ten facts -/

/-- The form names no entry of a virtual row, and slots below n alone. -/
def ScopedG (n : Nat) (a : Aff) : Prop :=
  a.ents.isEmpty = true ∧ ∀ t ∈ a.slots.toList, t.1 < n

/-- **What the sub-protocol behind a lookup's rounds needs of what was heard**: ten facts, each on
counts, on marks in the ledger, or on which slots a form names. -/
structure LeftG (p : PG) (g : HeardG) (G : Fork) (cl : List PlaneClaim) (G₂ : Fork) : Prop where
  /-- the debt "claims on the planes" is unmarked -/
  unpaid : unpaidG (G.paid g.owedObjects) g.owedPlanes = true
  /-- the leaves' sumcheck can be closed -/
  planes : ∃ rest, planesG p.face g (G.paid g.owedObjects) [] = some (cl, G₂, rest)
  three : cl.length = 3
  /-- the ledger has room for just the lookup's slots -/
  room : G₂.ns = p.face.slots
  first : p.first = 0
  /-- a form at least was left; every form names slots of the lookup alone -/
  one : 1 ≤ g.rows.toList.length
  rows : ∀ a ∈ g.rows.toList, ScopedG p.face.slots a
  leads : ∀ c ∈ cl, ScopedG p.face.slots c.lead
  keys : ∀ k ∈ g.keys, ScopedG p.face.slots k.2
  /-- nothing of the lookup is left open, once the third debt is marked -/
  done : doneG p g ((G₂.paid g.owedPlanes).paid g.owedJoin) = true

/-- **The ledger in front of the lookup's rounds.** -/
structure Fresh (p : PG) (F : Fork) : Prop where
  sized : Sized F
  first : p.first = 0
  next : F.next = 0
  ns : F.ns = p.face.slots
  free : ∀ j, j < p.face.slots → ¬ Filled F j

/-! ## 2 Marking a debt -/

/-- Marking a debt leaves every other entry of the list. Conditional on the numbers differing. -/
theorem paid_ne (F : Fork) {i j : Nat} (h : i ≠ j) : (F.paid i).owed[j]? = F.owed[j]? := by
  show (F.owed.modify i _)[j]? = _
  rw [Array.getElem?_modify, if_neg h]

theorem paid_size (F : Fork) (i : Nat) : (F.paid i).owed.size = F.owed.size := by
  show (F.owed.modify i _).size = _
  rw [Array.size_modify]

/-- A debt of the list is marked. Conditional on its number naming an entry. -/
theorem paid_at (F : Fork) {i : Nat} (h : i < F.owed.size) :
    ((F.paid i).owed[i]?).map (·.added) = some true := by
  show ((F.owed.modify i _)[i]?).map _ = _
  rw [Array.getElem?_modify, if_pos rfl, Array.getElem?_eq_getElem h]
  rfl

/-- A mark stays. Conditional on the mark. -/
theorem paid_keeps (F : Fork) (i : Nat) {j : Nat} (h : (F.owed[j]?).map (·.added) = some true) :
    ((F.paid i).owed[j]?).map (·.added) = some true := by
  by_cases hij : i = j
  · subst hij
    have hlt : i < F.owed.size := by
      by_contra hc
      rw [Array.getElem?_eq_none (Nat.not_lt.1 hc)] at h
      exact nomatch h
    exact paid_at F hlt
  · rw [paid_ne F hij]
    exact h

/-! ## 3 The ten facts -/

/-- **The ten facts**, at the claims and the ledger that the flat text of the claims on the planes
returns. Conditional on `Fresh`, on the return of `hearV`, and on that text's. An instance:
Honest/K3/Parts/PacksGuards.lean [not in this library] (by evaluation). -/
theorem leftG_at (p : PG) {F G G₂ : Fork} {rs : List Fmt.RoundView} {g : HeardV} {cl : List PlaneClaim}
    {rest : Tape} (hF : Fresh p F) (hh : hearV p.face F rs = some (g, G))
    (hp : planesG p.face (toHeardG g) (G.paid g.owedObjects) [] = some (cl, G₂, rest)) :
    LeftG p (toHeardG g) G cl G₂ := by
  obtain ⟨hok, hm⟩ := hearV_messages hh
  have h2 := two_le_planes_of_ok _ hok
  have hS := hF.sized
  obtain ⟨c0, cO, cP, cJ⟩ := heard_counts hm
  obtain ⟨_, uP, _⟩ := unpaid_behind hh
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := heard_names h2 hm
  obtain ⟨m1, m2, m3⟩ := hearV_ne hh
  have o3 := hearV_owed3 p.face hS hh
  have LG := hearV_later hh
  have SG : Sized G := LG.sized hS
  have nG := hearV_next p.face hS hh
  rw [hF.next, Nat.zero_add] at n1 n2 n3 n5 n7 nG
  -- the part's own text
  obtain ⟨cl0, hv, _, _⟩ := planesV_of_planesG p.face g hp
  have hp' := planesG_letter p.face hS hh [] hv
  obtain rfl : cl0 = cl := by
    have e := Option.some.inj (hp'.symm.trans hp)
    exact congrArg Prod.fst e
  have hv' := hv
  unfold planesV at hv'
  obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 hv'
  obtain ⟨y1, y2⟩ := y
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  subst e2
  have SP : Sized (G.paid g.owedObjects) := SG
  have L2 := MaskedSum.row_keeps hy
  have nx := MaskedSum.row_next SP hy
  have ow := row_owed hy
  obtain ⟨_, _, fl, _⟩ := OnBytes.PscRun.hideRun_ok _ _ _ _ _ SP (MaskedSum.row_write hy)
  obtain ⟨C, z, F₀, G₀, rs₀, h0, _, _⟩ := leaves_heard p.face hS hm
  have len : (MaskedSum.hidingAt (g.leaves.vars.zip g.leaves.r)).1.length =
      1 + p.face.mu + 2 * p.face.d := by
    rw [(MaskedSum.heard_lenK h0).2.2]
    exact own_leafVars p.face z
  have hlead := (row_names (lo := 0) (hi := p.face.slots) hy n3 (in_empty _ _) (Nat.zero_le _) n5).1
  refine ⟨?_, ⟨rest, hp⟩, by rw [← e1]; rfl, ?_, hF.first, ?_, ?_, ?_, ?_, ?_⟩
  · show ((G.paid g.owedObjects).owed[g.owedPlanes]?.map (·.added)) != some true
    rw [paid_ne G (by omega)]
    exact uP
  · rw [L2.ns]
    show G.ns = _
    rw [LG.ns, hF.ns]
  · show 1 ≤ g.rows.toList.length
    rw [Array.length_toList, c0]
    unfold VerifiableInference.Desc.K3.Face.lins
    omega
  · intro a ha
    exact ⟨m1 a ha, fun t ht => (n1 a ha t ht).2⟩
  · intro c hc
    refine ⟨planesV_ne hh hv c hc, ?_⟩
    rw [← e1] at hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact fun t ht => (hlead t ht).2
    · exact fun t ht => (in_slot (lo := 0) (Nat.zero_le _) n7 t ht).2
    · exact fun t ht => (in_ofConst 0 p.face.slots _ t ht).2
  · intro k hk
    exact ⟨m2 k hk, fun t ht => (n2 k hk t ht).2⟩
  · unfold doneG
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]
    refine ⟨⟨?_, fun j hj => ?_⟩, ?_⟩
    · show p.first + p.face.slots ≤ y2.next
      rw [nx, hF.first]
      show 0 + p.face.slots ≤ G.next
      omega
    · show y2.gotF.getD (p.first + j) false = true
      rw [hF.first, Nat.zero_add]
      by_cases hin : g.leaves.first ≤ j ∧ j < g.leaves.first + (1 + p.face.mu + 2 * p.face.d)
      · have q := (fl (j - g.leaves.first) (by rw [Array.size_replicate, len]; omega)).2.2.1
        rw [show g.leaves.first + (j - g.leaves.first) = j by omega] at q
        exact q
      · have q : Filled G j := hearV_full p.face hS hh j (by rw [hF.next]; exact Nat.zero_le _)
          (by rw [hF.next, Nat.zero_add]; exact hj) (by omega)
        exact (L2.keep j q).1
    · intro i hi
      have sz : (G.paid g.owedObjects).owed.size = G.owed.size := paid_size G _
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · refine paid_keeps _ _ (paid_keeps _ _ ?_)
        rw [ow]
        exact paid_at G (show g.owedObjects < _ by omega)
      · refine paid_keeps _ _ (paid_at _ ?_)
        rw [ow, sz]
        show g.owedPlanes < _
        omega
      · refine paid_at _ ?_
        rw [paid_size, ow, sz]
        show g.owedJoin < _
        omega

/-- **The ten facts hold of some three claims and some ledger**: the flat text of the claims on the
planes returns behind the hearing, once the first debt is marked. Conditional on `Fresh` and on the
return of `hearV`. An instance: Honest/K3/Parts/PacksGuards.lean [not in this library] (by
evaluation). -/
theorem leftG_of_hearV (p : PG) {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV} (hF : Fresh p F)
    (hh : hearV p.face F rs = some (g, G)) : ∃ cl G₂, LeftG p (toHeardG g) G cl G₂ := by
  have hS := hF.sized
  have hroom : F.next + p.face.slots ≤ F.ns := by rw [hF.next, hF.ns]; omega
  have hfree : ∀ j, F.next ≤ j → j < F.next + p.face.slots → ¬ Filled F j := by
    intro j _ b
    rw [hF.next, Nat.zero_add] at b
    exact hF.free j b
  have SG : Sized G := (hearV_later hh).sized hS
  have ho := leaves_owed p.face hS hfree hh
  obtain ⟨cl, G₂, hp, _⟩ := planesG_returns p.face hS hroom hh
    (F' := G.paid g.owedObjects) SG ⟨Nat.le_refl _, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩ ho []
  exact ⟨cl, G₂, leftG_at p hF hh hp⟩

#print axioms ProofFile.Honest.K3.Parts.paid_ne
#print axioms ProofFile.Honest.K3.Parts.paid_size
#print axioms ProofFile.Honest.K3.Parts.paid_at
#print axioms ProofFile.Honest.K3.Parts.paid_keeps
#print axioms ProofFile.Honest.K3.Parts.leftG_at
#print axioms ProofFile.Honest.K3.Parts.leftG_of_hearV

end ProofFile.Honest.K3.Parts
