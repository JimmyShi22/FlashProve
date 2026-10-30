-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/FirstSame.lean: the first chain of the proof file's IOP as written in
Lean is the driver's `firstChain` at a structure `H`; here is said what `H.same`, the test of the
driver's guard on the reply, is, and what `H.block` gives at a place. Theorems only; no file of that
IOP imports this one.
Why. A rule on the driver's own first chain (`eachRep_at_driver`, Johnson/P5J/ReplyAtDriver.lean)
takes as premises that the chain is `firstChain H links several`, that what `H.same` lets pass
leaves the reply that was heard, and a sentence on `H.block` at the place of the kind K7.
OrderStated.lean has the first with some `H`, of which it says nothing more.
  `chainBy_first_fill`   `chainBy Z base fr road = .ok c` gives `join`, `Fr` and `z` with
                         `firstChain (fill (base.map join).dropLast z Fr) (subsOf Z) several`
                         `= some c`, `Fr.toGather = road`, and `chainBy_hands`' clause on `join`;
                         `several` says whether one member of `base` is of the kind K13
  `chainBy_first_same`   so there is an `H` with that chain, with `H.same = road.same`, and such
                         that what `H.block` gives at a place is the member of `base` at that place,
                         or that member with a member of `fr` joined after it behind the guard
  `partsAt_road_same`, `pure_road_same`   `(partsAt T B).road.same = T.same`; at `pureSeat o Z` that
                         is `sameReply`
  `pure_first_same`      the two joined, in the form in which `onlineDescriptionFromPublicPart` calls `chainBy`
  `several_of_k13`       where a member of the driver's chain stands at a place of the kind K13, the
                         driver's flag `several` is true
  `pure_first_at`        `pure_first_same` at `several = true`, from such a member
All but `several_of_k13` are unfoldings: they say how the value was computed. What `sameReply` says
of two states, that `subsOf Z` is a given list, and that the chain has a member of the kind K13 are
not said here.

-/
import Johnson.Desc.ProofFile.Law.OrderStated
import Johnson.Desc.ProofFile.Law.KindPlaces
import Johnson.Desc.First.Driver.PlacesLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open VerifiableInference.Desc (Block Chain FileDescription KindName Place blocksOk)
open VerifiableInference.Desc.First

/-- `chainBy_first_at`, with the driver's structure written out. -/
theorem chainBy_first_fill {Z : Pub} {base : List (Block S Cl)}
    {fr : List (FrameRole × Block S Cl)} {road : Gather S Cl} {c : Chain S Cl}
    (h : chainBy Z base fr road = .ok c) :
    ∃ (join : Block S Cl → Block S Cl) (Fr : Frames S Cl) (z : Block S Cl),
      (base.map join).getLast? = some z ∧
      firstChain (fill (base.map join).dropLast z Fr) (subsOf Z)
        (base.any fun b => b.place.kind == KindName.K13) = some c ∧
      Fr.toGather = road ∧
      ∀ b, join b = b ∨ ∃ x ∈ fr, ∃ l, x.1 = .behind l b.name ∧ b.place.link = some l ∧
        join b = b.andThen b.name (x.2.guarded road.same fun _ => false) := by
  obtain ⟨join, Fr, hc, hr, hj⟩ := chainBy_hands h
  obtain ⟨z, hz, hf⟩ := chainC_first hc
  have hp : ∀ b, (join b).place = b.place := fun b => by
    rcases hj b with e | ⟨x, _, l, _, _, e⟩
    · rw [e]
    · have e' := congrArg (fun y : Block S Cl => y.place) e
      exact e'
  rw [any_kind_map KindName.K13 join hp] at hf
  exact ⟨join, Fr, z, hz, hf, hr, hj⟩

/-- **The first chain is the driver's, at a structure whose test on the reply is `road`'s and whose
sub-protocols are `base`'s.** -/
theorem chainBy_first_same {Z : Pub} {base : List (Block S Cl)}
    {fr : List (FrameRole × Block S Cl)} {road : Gather S Cl} {c : Chain S Cl}
    (h : chainBy Z base fr road = .ok c) :
    ∃ H : Blocks S Cl,
      firstChain H (subsOf Z) (base.any fun b => b.place.kind == KindName.K13) = some c ∧
      H.same = road.same ∧
      ∀ a b, H.block a = some b → ∃ b0 ∈ base, b0.place = a ∧
        (b = b0 ∨ ∃ x ∈ fr, ∃ l, x.1 = .behind l b0.name ∧ b0.place.link = some l ∧
          b = b0.andThen b0.name (x.2.guarded road.same fun _ => false)) := by
  obtain ⟨join, Fr, z, _, hf, hr, hj⟩ := chainBy_first_fill h
  refine ⟨_, hf, congrArg Gather.same hr, fun a b hb => ?_⟩
  have hb' : ((base.map join).dropLast.find? fun y => y.place == a) = some b := hb
  have hm : b ∈ base.map join :=
    (List.dropLast_sublist _).subset (List.mem_of_find?_eq_some hb')
  have hq : (b.place == a) = true :=
    List.find?_some (p := fun y : Block S Cl => y.place == a) hb'
  have ha : b.place = a := eq_of_beq hq
  obtain ⟨b0, h0, rfl⟩ := List.mem_map.1 hm
  rcases hj b0 with e | ⟨x, hx, l, h1, h2, e⟩
  · have e' := congrArg (fun y : Block S Cl => y.place) e
    have e2 : (join b0).place = b0.place := e'
    exact ⟨b0, h0, e2.symm.trans ha, .inl e⟩
  · have e' := congrArg (fun y : Block S Cl => y.place) e
    have e2 : (join b0).place = b0.place := e'
    exact ⟨b0, h0, e2.symm.trans ha, .inr ⟨x, hx, l, h1, h2, e⟩⟩

theorem partsAt_road_same (T : PureSeat) (B : PureBase) : (partsAt T B).road.same = T.same := rfl

theorem pure_road_same (o : SecondHashFunctionArgument) (Z : Pub) (B : PureBase) :
    (partsAt (pureSeat o Z) B).road.same = sameReply := rfl

/-- **In the form in which `onlineDescriptionFromPublicPart` calls `chainBy`: the driver's guard asks `sameReply`.** -/
theorem pure_first_same {o : SecondHashFunctionArgument} {Z : Pub} {B : PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl}
    (h : chainBy Z base (partsAt (pureSeat o Z) B).frames (partsAt (pureSeat o Z) B).road = .ok c) :
    ∃ H : Blocks S Cl,
      firstChain H (subsOf Z) (base.any fun b => b.place.kind == KindName.K13) = some c ∧
      H.same = sameReply ∧
      ∀ a b, H.block a = some b → ∃ b0 ∈ base, b0.place = a ∧
        (b = b0 ∨ ∃ x ∈ (partsAt (pureSeat o Z) B).frames, ∃ l,
          x.1 = .behind l b0.name ∧ b0.place.link = some l ∧
          b = b0.andThen b0.name (x.2.guarded sameReply fun _ => false)) := by
  obtain ⟨H, hf, hs, hB⟩ := chainBy_first_same h
  rw [pure_road_same o Z B] at hs hB
  exact ⟨H, hf, hs, hB⟩

/-! ### The driver's flag -/

theorem no_k13_hear (sub : ModelPart) (first : Bool) : KindName.K13 ∉ kindsBeforeBatching sub first := by
  cases sub <;> cases first <;> decide

theorem no_k13_back : KindName.K13 ∉ backKinds false := by decide

theorem no_k13_linkPlaces {l : Nat} {sub : ModelPart} {a : Place} (h : a ∈ linkPlaces l sub) :
    a.kind ≠ KindName.K13 := by
  intro hk
  unfold linkPlaces at h
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h
  rcases h with (((rfl | h) | (rfl | rfl)) | h) | rfl
  · simp [frameAt] at hk
  · exact no_k13_hear sub (l == 0) (hk ▸ kind_of_addresses h)
  · simp at hk
  · simp [frameAt] at hk
  · rcases mem_closeAddresses h with rfl | rfl | rfl <;> simp at hk
  · simp [frameAt] at hk

/-- A place of the kind K13 stands in the driver's table of all places only where the flag is
true. -/
theorem several_of_k13_place {links : List ModelPart} {several : Bool} {a : Place}
    (hm : a ∈ flatPlacesOf links several) (hk : a.kind = KindName.K13) : several = true := by
  unfold flatPlacesOf at hm
  simp only [List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil,
    or_false] at hm
  rcases hm with ((rfl | ⟨x, _, hl⟩) | hb) | rfl
  · simp [frameAt] at hk
  · exact (no_k13_linkPlaces hl hk).elim
  · cases several with
    | true => rfl
    | false => exact (no_k13_back (hk ▸ kind_of_addresses hb)).elim
  · simp [frameAt] at hk

theorem several_of_k13 {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c : Chain S Cl}
    (h : firstChain H links several = some c) {b : Block S Cl} (hb : b ∈ c.blocksInOrder)
    (hk : b.place.kind = KindName.K13) : several = true :=
  several_of_k13_place
    (by rw [← flat_places H links several c h]; exact List.mem_map_of_mem hb) hk

/-- **`pure_first_same` at the flag `true`**, where the chain has a member of the kind K13. -/
theorem pure_first_at {o : SecondHashFunctionArgument} {Z : Pub} {B : PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl}
    (h : chainBy Z base (partsAt (pureSeat o Z) B).frames (partsAt (pureSeat o Z) B).road = .ok c)
    (hk : ∃ b ∈ c.blocksInOrder, b.place.kind = KindName.K13) :
    ∃ H : Blocks S Cl,
      firstChain H (subsOf Z) true = some c ∧ H.same = sameReply ∧
      ∀ a b, H.block a = some b → ∃ b0 ∈ base, b0.place = a ∧
        (b = b0 ∨ ∃ x ∈ (partsAt (pureSeat o Z) B).frames, ∃ l,
          x.1 = .behind l b0.name ∧ b0.place.link = some l ∧
          b = b0.andThen b0.name (x.2.guarded sameReply fun _ => false)) := by
  obtain ⟨H, hf, hs, hB⟩ := pure_first_same h
  obtain ⟨b, hb, hkb⟩ := hk
  rw [several_of_k13 hf hb hkb] at hf
  exact ⟨H, hf, hs, hB⟩

end ProofFile.Law

#print axioms ProofFile.Law.chainBy_first_fill
#print axioms ProofFile.Law.chainBy_first_same
#print axioms ProofFile.Law.pure_road_same
#print axioms ProofFile.Law.pure_first_same
#print axioms ProofFile.Law.several_of_k13
#print axioms ProofFile.Law.pure_first_at
