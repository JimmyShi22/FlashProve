-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/PureKeeps.lean: FillKeeps.lean's walk, carried to the lots from which the
proof file's IOP as written in Lean is assembled (Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean: `partsAt`,
`onlineDescriptionFromPublicPart`; LotCore.lean: `Lot`). General in the property P of the verifier's state and in the property
R of the rounds. A law file; no running text imports it.

  `keepsD_guardMark`, `keepsRuns_guardMark`   the refusal at a mark of failure hands on the
                   sub-protocol's own state; the runs are the sub-protocol's own.
  `LotKeeps R P L G`   ONE FORM FOR EVERY LOT: what is asked of a lot's sub-protocols at the
                   segments' structures G: `KeepsD` of those that stand inside a segment AND PASS
                   THEIR OWN TEST ON THE PLAN (decide), and outright of those of the kind `frame`
                   (frame); `KeepsRuns` of both sorts (not at the kinds K9 and K10);
                   of the batching as a function: `KeepsD` at every function of claims that keeps
                   P, and `KeepsRuns`.
  `baseOf_all`     the lots' sub-protocols in `PureBase` are the lots' own, at its G₀, which is the
                   segments' structures for a request of zeros (`blankBy`).
  `parts_road`, `parts_base`, `parts_frames`   what `partsAt` makes is made of these.
  `pureZ_front`    where `onlineDescriptionFromPublicPart Z T` returns F: F is `fileDescBy` at a chain c with no entry
                   between its first and its segments; `frontOf c` has 14 entries a segment and 3
                   more (FrontLength.lean); and, AT THAT ONE c, FOR EVERY R AND P: if
                   every lot has `LotKeeps R P` at that G₀, every entry of `frontOf c` that passes
                   its own test on the plan has `KeepsD R P`; so has every such entry of
                   `c.blocksInOrder.take k`, at k ≤ (frontOf c).length.
Limits. A lot's sub-protocol that stands outside the segments and is not of the kind `frame` (the
last code switch, the proximity test, the members' steps, the last commitment) owes nothing and
nothing is said of it. `LotKeeps` is asked of every lot of the seat, also of one that says that its
sub-protocols depend on the request. Nothing on any one property or kind. Nothing on soundness or
on hiding.

-/
import Johnson.Top.H0.K2Hands.FillKeeps
import Johnson.Top.H0.K2Hands.FrontLength
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps1
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open Meaning.K2 (frontOf mem_of_mapM_ok)

variable {R : Fmt.RoundView → Prop} {P : S → Prop}

theorem keepsD_guardMark {b : Block S ProofFile.Cl} (h : KeepsD R P b) :
    KeepsD R P (ProofFile.guardMark b) := by
  intro s s' rs gs hr hy hs
  obtain ⟨t, h1, h2⟩ := bind_ok (x := b.decide s rs gs) hy
  split at h2
  · cases h2
    exact h s _ rs gs hr h1 hs
  · cases h2

theorem keepsRuns_guardMark {b : Block S ProofFile.Cl} (h : KeepsRuns P b) :
    KeepsRuns P (ProofFile.guardMark b) := h

/-- **One form for every lot.** -/
structure LotKeeps (R : Fmt.RoundView → Prop) (P : S → Prop) (L : ProofFile.Lot) (G : ProofFile.Ground) : Prop where
  decide : ∀ b ∈ L.blocks G, b.place.link ≠ none → b.planOk = true → KeepsD R P b
  frame : ∀ b ∈ L.blocks G, b.place.kind = KindName.frame → KeepsD R P b
  runs : ∀ b ∈ L.blocks G, b.place.link ≠ none ∨ b.place.kind = KindName.frame →
    b.place.kind ≠ KindName.K9 → b.place.kind ≠ KindName.K10 → KeepsRuns P b
  batch : ∀ a mk, L.batch G a = some mk →
    ∀ f : ProofFile.Gatherer, (∀ s y, f s = .ok y → P s → P y.2) → KeepsD R P (mk f)
  batchRuns : ∀ a mk, L.batch G a = some mk → ∀ f : ProofFile.Gatherer, KeepsRuns P (mk f)

theorem baseOf_all {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {B : ProofFile.PureBase}
    (h : ProofFile.baseOf Z T = .ok B) :
    ProofFile.blankBy T.links Z = some B.G₀ ∧ B.all = T.lots.map fun L => (L, L.blocks B.G₀) := by
  unfold ProofFile.baseOf at h
  obtain ⟨_, _, h⟩ := ProofFile.Law.exBind_ok h
  obtain ⟨_, _, h⟩ := ProofFile.Law.exBind_ok h
  obtain ⟨G, hG, h⟩ := ProofFile.Law.exBind_ok h
  cases h
  exact ⟨ProofFile.Law.orSay_ok hG, rfl⟩

section parts
variable {T : ProofFile.PureSeat} {B : ProofFile.PureBase}

/-- The batching as a function, as `partsAt` hands it on: a lot's own, behind the refusal at a mark,
under another name. -/
theorem parts_road {a : Place} {mk' : ProofFile.Gatherer → Block S ProofFile.Cl}
    (h : (ProofFile.partsAt T B).road.batch a = some mk') :
    ∃ L ∈ T.lots, ∃ mk, L.batch B.G₀ a = some mk ∧
      ∀ g, (mk' g).decide = (ProofFile.guardMark (mk g)).decide ∧ (mk' g).claims = (mk g).claims ∧
        (mk' g).after = (mk g).after := by
  unfold ProofFile.partsAt at h
  dsimp only at h
  obtain ⟨mk, h2, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨L, hL, h3⟩ := List.exists_of_findSome?_eq_some h2
  exact ⟨L, (List.mem_filter.1 hL).1, mk, h3, fun g => ⟨rfl, rfl, rfl⟩⟩

theorem road_keeps (hT : ∀ L ∈ T.lots, LotKeeps R P L B.G₀) {a : Place}
    {mk' : ProofFile.Gatherer → Block S ProofFile.Cl} (h : (ProofFile.partsAt T B).road.batch a = some mk') :
    (∀ f : ProofFile.Gatherer, (∀ s y, f s = .ok y → P s → P y.2) → KeepsD R P (mk' f)) ∧
      ∀ f : ProofFile.Gatherer, KeepsRuns P (mk' f) := by
  obtain ⟨L, hL, mk, h1, h2⟩ := parts_road h
  refine ⟨fun f hf => keepsD_under (h2 f).1 (keepsD_guardMark ((hT L hL).batch a mk h1 f hf)),
    fun f => ?_⟩
  have k := (hT L hL).batchRuns a mk h1 f
  unfold KeepsRuns at k ⊢
  rw [(h2 f).2.1, (h2 f).2.2]
  exact k

/-- A member of the list of sub-protocols at the places: the batching at a gatherer that gathers
nothing, or a lot's own, behind the refusal at a mark, under the place's name. -/
theorem parts_base {base : List (Block S ProofFile.Cl)} (hb : (ProofFile.partsAt T B).base = .ok base) :
    ∀ b ∈ base,
      (∃ a mk', (ProofFile.partsAt T B).road.batch a = some mk' ∧ b = mk' fun s => .ok ([], s)) ∨
      ∃ x ∈ B.all, ∃ b₀ ∈ x.2, ∃ nm : String, b = { ProofFile.guardMark b₀ with name := nm } := by
  intro b hb'
  obtain ⟨x, hx, e⟩ := mem_of_mapM_ok _ _ _ hb b hb'
  unfold ProofFile.partsAt at hx
  dsimp only at hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  dsimp only at e
  split at e
  · rename_i f _ hface
    cases e
    obtain ⟨mk', h1, rfl⟩ := Option.map_eq_some_iff.1 hface
    exact Or.inl ⟨p.place, mk', h1, rfl⟩
  · rename_i y _ hy
    cases e
    obtain ⟨z, hz, hz2⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hy)
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hz2
    exact Or.inr ⟨z, hz, b₀, List.mem_of_find?_eq_some hb₀, p.name, rfl⟩
  · split at e <;> cases e

/-- A sub-protocol of the kind `frame`, as `partsAt` hands it on: a lot's own of that kind, behind
the refusal at a mark. -/
theorem parts_frames : ∀ x ∈ (ProofFile.partsAt T B).frames,
    ∃ y ∈ B.all, ∃ b₀ ∈ y.2, b₀.place.kind = KindName.frame ∧ x.2 = ProofFile.guardMark b₀ := by
  intro x hx
  unfold ProofFile.partsAt at hx
  dsimp only at hx
  obtain ⟨y, hy, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · cases hx
  · obtain ⟨b₀, hb₀, e⟩ := List.mem_filterMap.1 hx
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hb₀
    refine ⟨y, hy, b₀, h1, eq_of_beq h2, ?_⟩
    split at e
    · cases e
    · cases e
    · cases e
      rfl

end parts

/-- **The first chain of the IOP as written in Lean, in front of the entries behind its last
segment.** One chain c for every R and P. -/
theorem pureZ_front {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescriptionFromPublicPart Z T = .ok F) :
    ∃ (c : Chain S ProofFile.Cl) (A : ProofFile.SharedSeat) (B' : ProofFile.SecondSeat),
      F = ProofFile.fileDescBy T.older T.links Z A B' (fun s => s) (ProofFile.startS Z) c ∧ c.front = [] ∧
      (frontOf c).length = 14 * (ProofFile.subsOf Z).length + 3 ∧
      ∀ (R : Fmt.RoundView → Prop) (P : S → Prop),
        (∀ G, ProofFile.blankBy T.links Z = some G → ∀ L ∈ T.lots, LotKeeps R P L G) →
        (∀ b ∈ frontOf c, b.planOk = true → KeepsD R P b) ∧
          ∀ k, k ≤ (frontOf c).length → ∀ b ∈ c.blocksInOrder.take k, b.planOk = true → KeepsD R P b := by
  obtain ⟨B, hB, -, -, ht⟩ := ProofFile.Law.pureZ_ok h
  obtain ⟨base, c, A, B', hb, hc, -, -, hE⟩ := ProofFile.Law.pureTail_ok ht
  obtain ⟨hG, hall⟩ := baseOf_all hB
  have hlot : ∀ x ∈ B.all, ∃ L ∈ T.lots, x.2 = L.blocks B.G₀ := by
    intro x hx
    rw [hall] at hx
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hx
    exact ⟨L, hL, rfl⟩
  have h0 : c.front = [] ∧ (frontOf c).length = 14 * (ProofFile.subsOf Z).length + 3 := by
    unfold ProofFile.chainBy at hc
    dsimp only at hc
    obtain ⟨z, several, hc'⟩ := chainC_ok hc
    exact ⟨Meaning.K2.firstChain_noFront hc', frontOf_length hc'⟩
  obtain ⟨h0, hlen⟩ := h0
  refine ⟨c, A, B', hE, h0, hlen, fun R P hT => ?_⟩
  have hT := hT B.G₀ hG
  obtain ⟨-, hfr⟩ := chainBy_front (R := R) (P := P) hc
    (fun b hm hl hp => by
      rcases parts_base hb b hm with ⟨a, mk', h1, rfl⟩ | ⟨x, hx, b₀, hb₀, nm, rfl⟩
      · exact (road_keeps hT h1).1 _ fun s y hy hs => by
          cases hy
          exact hs
      · obtain ⟨L, hL, e⟩ := hlot x hx
        exact keepsD_under rfl (keepsD_guardMark ((hT L hL).decide b₀ (e ▸ hb₀) hl hp)))
    (fun b hm hl h9 h10 => by
      rcases parts_base hb b hm with ⟨a, mk', h1, rfl⟩ | ⟨x, hx, b₀, hb₀, nm, rfl⟩
      · exact (road_keeps (R := R) hT h1).2 _
      · obtain ⟨L, hL, e⟩ := hlot x hx
        exact (hT L hL).runs b₀ (e ▸ hb₀) (Or.inl hl) h9 h10)
    (fun x hx => by
      obtain ⟨y, hy, b₀, hb₀, hk, e⟩ := parts_frames x hx
      obtain ⟨L, hL, e'⟩ := hlot y hy
      rw [e]
      exact ⟨keepsD_guardMark ((hT L hL).frame b₀ (e' ▸ hb₀) hk),
        (hT L hL).runs b₀ (e' ▸ hb₀) (Or.inr hk) (by rw [hk]; decide) (by rw [hk]; decide)⟩)
    (fun a mk h1 => (road_keeps hT h1).1)
  exact ⟨hfr, fun k hk b hm => hfr b (take_front h0 hk b hm)⟩

end VerifiableInference.Desc.Keeps1

#print axioms VerifiableInference.Desc.Keeps1.parts_base
#print axioms VerifiableInference.Desc.Keeps1.parts_frames
#print axioms VerifiableInference.Desc.Keeps1.road_keeps
#print axioms VerifiableInference.Desc.Keeps1.pureZ_front
