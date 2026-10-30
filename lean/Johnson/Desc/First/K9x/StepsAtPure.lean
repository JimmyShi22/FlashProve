-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K9x/StepsAtPure.lean: THE ONE PREMISE INSIDE THE ROAD "WHO PAYS K3RanAt"
(KindsAtPure.lean: `RoadAtN`), "the hearing blocks behind b step where their tests on the plan say
yes", BROUGHT DOWN, FOR b A LOOKUP, TO SEVEN LAWS, ONE A LOT, EACH OF THE LOT's OWN BLOCKS.
Definitions, and theorems with their proofs.

FROM WHERE. "Which lot by kind" and "no frame's block is joined but at a link's first place" are
other files': `lot_of_kind`, `lot_K1`, `no_behind` (Johnson/IMR/LotKinds.lean, K1Seat.lean,
LaidFirst.lean).
Called, not typed here.

  `behindKinds`: K1 · K3 · K4 · K5 · K6 · K8 · K11: the kinds of the hearing places from index 2 on.
  `KindsStep hd Z G`: THE SEVEN FIELDS: every block that the kind's lot lays at the letters G steps
    `CF hd` where its own test on the plan says yes.
  `seatedAlone`: at a place of a piece from 2 to 9, of another kind than K9 and K10, `SeatedAs`'
    second arm does not occur: M = { guardMark b₀ with name := n }.
  `stepsOfLot`: a block of a kind of `behindKinds` that a lot of the seated seat lays in a link is
    its kind's own lot's: so it steps, by the field.
  `StepsIn hd Z G ks`: the like for the kinds of a list ks. `stepsInSeven`: at `behindKinds`, by the
    seven fields. `stepsInMerge`: at K11 alone, by the merge's law alone.
  `stepsAtHear`: so the chain's hearing block there steps where its test on the plan says yes.
  `hearPlaces`: a segment's hearing blocks bear the driver's addresses, in order.
  `behindALookup`: in a cut L.hear = h₁ ++ b :: h₂ with b of the kind K3 every member of h₂ stands
    in that link, at a piece from 3 to 9, and is of a kind of `behindKinds`; where six hearing
    blocks or more stand in front of b (the link's second lookup): of the kind K11
    (`kindsBehindDigits`).
  **`stepsBehindLookup`**: under `KindsStep`: in such a cut every member of h₂ steps where its test
    on the plan says yes: THE ROAD's INNER PREMISE.
  **`stepsBehindDigits`**: the same at the link's second lookup, under the merge's law alone: for a
    reading of "heard" that the other kinds' blocks do not leave.

Limits. Frame's laws: no error; nothing on soundness. `KindsStep` is a premise here: paid in
K03Ran.lean by the seven kinds' laws. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.K9x.KindsAtPure
import Johnson.IMR.K1Seat
import Johnson.P5K3R.SitsEvery

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First
open ProofFile (Pub Ground Cl PureBase pureSeat guardMark)

/-- The kinds of a link's hearing places from index 2 on. -/
def behindKinds : List KindName := [.K1, .K3, .K4, .K5, .K6, .K8, .K11]

/-- **The seven laws, one a lot**: every block that the lot lays steps where its own test on the
plan says yes. -/
structure KindsStep (hd : S → Option Forest.Heard) (Z : Pub) (G : Ground) : Prop where
  k1 : ∀ b ∈ (ProofFile.k1Pure Z).blocks G, b.planOk = true → b.Steps (CF hd)
  k3 : ∀ b ∈ (K3Lot.lot Z).blocks G, b.planOk = true → b.Steps (CF hd)
  k4 : ∀ b ∈ (ProofFile.k4Lot Z).blocks G, b.planOk = true → b.Steps (CF hd)
  k5 : ∀ b ∈ (H2K5.lotN Z).blocks G, b.planOk = true → b.Steps (CF hd)
  k6 : ∀ b ∈ (P4.k6Lot Z).blocks G, b.planOk = true → b.Steps (CF hd)
  k8 : ∀ b ∈ (ProofFile.P1K8.lot Z).blocks G, b.planOk = true → b.Steps (CF hd)
  k11 : ∀ b ∈ (K11.lot Z).blocks G, b.planOk = true → b.Steps (CF hd)

/-- At a place of a piece from 2 to 9, of another kind than K9 and K10, no frame's block is joined
behind. -/
theorem seatedAlone {o : ProofFile.SecondHashFunctionArgument} {Z : Pub} {B : PureBase}
    (hB : ProofFile.baseOf Z (pureSeat o Z) = .ok B) {M : Block S Cl}
    (h : SeatedAs (pureSeat o Z) B M) (hk9 : M.place.kind ≠ KindName.K9)
    (hk10 : M.place.kind ≠ KindName.K10) (hn : 2 ≤ M.place.piece ∧ M.place.piece ≤ 9) :
    ∃ lot ∈ ProofFile.onlineFirstChainBlockTables Z, ∃ b₀ ∈ lot.blocks B.G₀, b₀.place = M.place ∧
      ∃ n, M = { guardMark b₀ with name := n } := by
  obtain ⟨lot, hl, b₀, hb₀, hp, -, p, hps, hpp, hM⟩ := h
  rcases hM with e | ⟨y, hy, ⟨l, hr⟩, -⟩
  · exact ⟨lot, hl, b₀, hb₀, hp, _, e⟩
  · exact absurd rfl (IM.no_behind hB hps (by rw [hpp]; exact hk9) (by rw [hpp]; exact hk10)
      (by rw [hpp]; exact hn) hy hr)

/-- A block of one of these kinds that a lot of the seated seat lays in a link steps. -/
theorem stepsOfLot {hd : S → Option Forest.Heard} {Z : Pub} {G : Ground} (K : KindsStep hd Z G)
    {lot : ProofFile.Lot} (hL : lot ∈ ProofFile.onlineFirstChainBlockTables Z) {b₀ : Block S Cl} (hb : b₀ ∈ lot.blocks G) {l : ℕ}
    (hl : b₀.place.link = some l) (hk : b₀.place.kind ∈ behindKinds) (hp : b₀.planOk = true) :
    b₀.Steps (CF hd) := by
  simp only [behindKinds, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with e | e | e | e | e | e | e
  · obtain ⟨x, hx, rfl⟩ := IM.lot_K1 hL hb e hl
    exact K.k1 _ (List.mem_append_left _ (List.mem_map.2 ⟨x, hx, rfl⟩)) hp
  · obtain rfl := IM.lot_of_kind hL hb (L' := K3Lot.lot Z) (by rw [e]; rfl)
    exact K.k3 _ hb hp
  · obtain rfl := IM.lot_of_kind hL hb (L' := ProofFile.k4Lot Z) (by rw [e]; rfl)
    exact K.k4 _ hb hp
  · obtain rfl := IM.lot_of_kind hL hb (L' := H2K5.lotN Z) (by rw [e]; rfl)
    exact K.k5 _ hb hp
  · obtain rfl := IM.lot_of_kind hL hb (L' := P4.k6Lot Z) (by rw [e]; rfl)
    exact K.k6 _ hb hp
  · obtain rfl := IM.lot_of_kind hL hb (L' := ProofFile.P1K8.lot Z) (by rw [e]; rfl)
    exact K.k8 _ hb hp
  · obtain rfl := IM.lot_of_kind hL hb (L' := K11.lot Z) (by rw [e]; rfl)
    exact K.k11 _ hb hp

/-- Every block of a kind of the list ks that a lot of the seated seat lays in a link steps where
its own test on the plan says yes. -/
def StepsIn (hd : S → Option Forest.Heard) (Z : Pub) (G : Ground) (ks : List KindName) : Prop :=
  ∀ lot ∈ ProofFile.onlineFirstChainBlockTables Z, ∀ b₀ ∈ lot.blocks G, ∀ l : ℕ, b₀.place.link = some l →
    b₀.place.kind ∈ ks → b₀.planOk = true → b₀.Steps (CF hd)

theorem stepsInSeven {hd : S → Option Forest.Heard} {Z : Pub} {G : Ground}
    (K : KindsStep hd Z G) : StepsIn hd Z G behindKinds :=
  fun _ hL _ hb _ hl hk hp => stepsOfLot K hL hb hl hk hp

/-- The merge's law alone: for what stands behind the lookup on the digits. -/
theorem stepsInMerge {hd : S → Option Forest.Heard} {Z : Pub} {G : Ground}
    (k11 : ∀ b ∈ (K11.lot Z).blocks G, b.planOk = true → b.Steps (CF hd)) :
    StepsIn hd Z G [.K11] := by
  intro lot hL b₀ hb _ _ hk hp
  obtain rfl := IM.lot_of_kind hL hb (L' := K11.lot Z) (by rw [List.mem_singleton.1 hk]; rfl)
  exact k11 _ hb hp

/-- So the chain's hearing block there steps where its test on the plan says yes. -/
theorem stepsAtHear {hd : S → Option Forest.Heard} {o : ProofFile.SecondHashFunctionArgument} {Z : Pub} {B : PureBase}
    (hB : ProofFile.baseOf Z (pureSeat o Z) = .ok B) {ks : List KindName} (K : StepsIn hd Z B.G₀ ks)
    (h9 : KindName.K9 ∉ ks) (h10 : KindName.K10 ∉ ks) {M : Block S Cl}
    (h : SeatedAs (pureSeat o Z) B M) {l : ℕ} (hl : M.place.link = some l)
    (hk : M.place.kind ∈ ks) (hn : 2 ≤ M.place.piece ∧ M.place.piece ≤ 9)
    (hp : M.planOk = true) : M.Steps (CF hd) := by
  obtain ⟨lot, hL, b₀, hb₀, -, n, rfl⟩ :=
    seatedAlone hB h (fun e => h9 (e ▸ hk)) (fun e => h10 (e ▸ hk)) hn
  exact stepsOfYes b₀ _ ((yesOfDecide (guardMark b₀) _ rfl).trans (yesGuardN b₀))
    (K lot hL b₀ hb₀ l hl hk hp)

/-! ## Which places stand behind a lookup -/

theorem placesOfMapSome {α β : Type} (f : α → Option β) (g : β → α)
    (hg : ∀ a b, f a = some b → g b = a) :
    ∀ (l : List β) (as : List α), l.map some = as.map f → l.map g = as
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | b :: l, a :: as, h => by
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    exact ⟨hg a b h.1.symm, placesOfMapSome f g hg l as h.2⟩

/-- A segment's hearing blocks bear the driver's addresses, in order. -/
theorem hearPlaces (H : Blocks S Cl) (l : ℕ) (sub : ModelPart) (L : Link S Cl)
    (h : linkAt H l sub = some L) :
    L.hear.map (·.place) = addresses (some l) (kindsBeforeBatching sub (l == 0)) :=
  placesOfMapSome (blockAt H) (·.place) (fun a b e => place_of_blockAt H a b e) _ _
    (Shape.linkAt_shape h).2.1

/-- The hearing block at an index: its place. -/
theorem hearPlaceAt (H : Blocks S Cl) (l : ℕ) (sub : ModelPart) (L : Link S Cl)
    (h : linkAt H l sub = some L) (j : ℕ) (x : Block S Cl) (hx : L.hear[j]? = some x) :
    ∃ k, (kindsBeforeBatching sub (l == 0))[j]? = some k ∧
      x.place = { chain := 1, link := some l, piece := j + 1, kind := k } := by
  have e : (addresses (some l) (kindsBeforeBatching sub (l == 0)))[j]? = some x.place := by
    rw [← hearPlaces H l sub L h, List.getElem?_map, hx]
    rfl
  have hlen : j < (kindsBeforeBatching sub (l == 0)).length := by
    rw [← length_addresses (some l)]
    by_contra hc
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at e
    exact nomatch e
  refine ⟨_, List.getElem?_eq_getElem hlen, ?_⟩
  exact Option.some.inj (e.symm.trans
    (IM.addresses_at (some l) _ j _ (List.getElem?_eq_getElem hlen)))

/-- From index 2 on a link's hearing kinds are of `behindKinds`; there are nine at most. -/
theorem kindsBehind (sub : ModelPart) (first : Bool) (j : ℕ) (k : KindName) (hj : 2 ≤ j)
    (hk : (kindsBeforeBatching sub first)[j]? = some k) : k ∈ behindKinds ∧ j + 1 ≤ 9 := by
  have hlen : j < (kindsBeforeBatching sub first).length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hk
    exact nomatch hk
  have h9 : (kindsBeforeBatching sub first).length ≤ 9 := by cases sub <;> cases first <;> decide
  have hall : ((kindsBeforeBatching sub first).drop 2).all (fun k => decide (k ∈ behindKinds)) = true := by
    cases sub <;> cases first <;> decide
  have hm : k ∈ (kindsBeforeBatching sub first).drop 2 := by
    refine List.mem_of_getElem? (i := j - 2) ?_
    rw [List.getElem?_drop, show 2 + (j - 2) = j by omega]
    exact hk
  exact ⟨of_decide_eq_true (List.all_eq_true.1 hall k hm), by omega⟩

/-- Behind the second lookup of a link stands the merge, or nothing. -/
theorem kindsBehindDigits (sub : ModelPart) (first : Bool) (i j : ℕ) (k : KindName)
    (hi : (kindsBeforeBatching sub first)[i]? = some KindName.K3) (h6 : 6 ≤ i) (hij : i < j)
    (hk : (kindsBeforeBatching sub first)[j]? = some k) : k = KindName.K11 := by
  have hlen : j < (kindsBeforeBatching sub first).length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hk
    exact nomatch hk
  have h9 : (kindsBeforeBatching sub first).length ≤ 9 := by cases sub <;> cases first <;> decide
  have hj : j = 7 ∨ j = 8 := by omega
  have hi' : i = 6 ∨ i = 7 := by omega
  rcases hi' with rfl | rfl <;> rcases hj with rfl | rfl <;> cases sub <;> cases first <;>
    first
      | exact absurd hij (by decide)
      | exact absurd hi (by decide)
      | exact absurd hlen (by decide)
      | exact (Option.some.inj hk).symm

/-- **In a cut of a link's hearing blocks at a lookup**: what stands behind. -/
theorem behindALookup (H : Blocks S Cl) (l : ℕ) (sub : ModelPart) (L : Link S Cl)
    (h : linkAt H l sub = some L) (h₁ h₂ : List (Block S Cl)) (b : Block S Cl)
    (hh : L.hear = h₁ ++ b :: h₂) (hb : b.place.kind = KindName.K3) :
    ∀ x ∈ h₂, x.place.link = some l ∧ (2 ≤ x.place.piece ∧ x.place.piece ≤ 9) ∧
      x.place.kind ∈ behindKinds ∧ (6 ≤ h₁.length → x.place.kind = KindName.K11) := by
  intro x hx
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hx
  have hbAt : L.hear[h₁.length]? = some b := by
    rw [hh, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hxAt : L.hear[h₁.length + 1 + n]? = some x := by
    rw [hh, List.getElem?_append_right (by omega),
      show h₁.length + 1 + n - h₁.length = n + 1 by omega]
    exact hn
  obtain ⟨kb, hkb, eb⟩ := hearPlaceAt H l sub L h _ b hbAt
  obtain ⟨kx, hkx, ex⟩ := hearPlaceAt H l sub L h _ x hxAt
  have ekb : kb = KindName.K3 := by
    rw [eb] at hb
    exact hb
  rw [ekb] at hkb
  have h1 := (K3Lot.k3Index sub _ _ hkb).1
  obtain ⟨k₁, k₂⟩ := kindsBehind sub _ _ kx (by omega) hkx
  rw [ex]
  exact ⟨rfl, ⟨by show 2 ≤ h₁.length + 1 + n + 1; omega, k₂⟩, k₁,
    fun h6 => kindsBehindDigits sub _ _ _ kx hkb h6 (by omega) hkx⟩

/-- **THE ROAD's INNER PREMISE AT THE LOOKUP ON THE CALLS** (and at every lookup), under the seven
laws. -/
theorem stepsBehindLookup {hd : S → Option Forest.Heard} {o : ProofFile.SecondHashFunctionArgument} {Z : Pub}
    {B : PureBase} (hB : ProofFile.baseOf Z (pureSeat o Z) = .ok B) (K : KindsStep hd Z B.G₀)
    (H : Blocks S Cl) (l : ℕ) (sub : ModelPart) (L : Link S Cl) (h : linkAt H l sub = some L)
    (hS : ∀ M ∈ L.hear, SeatedAs (pureSeat o Z) B M) (h₁ h₂ : List (Block S Cl)) (b : Block S Cl)
    (hh : L.hear = h₁ ++ b :: h₂) (hb : b.place.kind = KindName.K3) :
    ∀ x ∈ h₂, x.planOk = true → x.Steps (CF hd) := by
  intro x hx hp
  obtain ⟨e₁, e₂, e₃, -⟩ := behindALookup H l sub L h h₁ h₂ b hh hb x hx
  exact stepsAtHear hB (stepsInSeven K) (by decide) (by decide)
    (hS x (by rw [hh]; simp [hx])) e₁ e₃ e₂ hp

/-- **THE SAME AT THE LOOKUP ON THE DIGITS**, under the merge's law alone. -/
theorem stepsBehindDigits {hd : S → Option Forest.Heard} {o : ProofFile.SecondHashFunctionArgument} {Z : Pub}
    {B : PureBase} (hB : ProofFile.baseOf Z (pureSeat o Z) = .ok B)
    (k11 : ∀ b ∈ (K11.lot Z).blocks B.G₀, b.planOk = true → b.Steps (CF hd))
    (H : Blocks S Cl) (l : ℕ) (sub : ModelPart) (L : Link S Cl) (h : linkAt H l sub = some L)
    (hS : ∀ M ∈ L.hear, SeatedAs (pureSeat o Z) B M) (h₁ h₂ : List (Block S Cl)) (b : Block S Cl)
    (hh : L.hear = h₁ ++ b :: h₂) (hb : b.place.kind = KindName.K3) (h6 : 6 ≤ h₁.length) :
    ∀ x ∈ h₂, x.planOk = true → x.Steps (CF hd) := by
  intro x hx hp
  obtain ⟨e₁, e₂, -, e₄⟩ := behindALookup H l sub L h h₁ h₂ b hh hb x hx
  exact stepsAtHear hB (stepsInMerge k11) (by decide) (by decide)
    (hS x (by rw [hh]; simp [hx])) e₁ (List.mem_singleton.2 (e₄ h6)) e₂ hp

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.seatedAlone
#print axioms VerifiableInference.Desc.K9.stepsOfLot
#print axioms VerifiableInference.Desc.K9.stepsInSeven
#print axioms VerifiableInference.Desc.K9.stepsInMerge
#print axioms VerifiableInference.Desc.K9.stepsAtHear
#print axioms VerifiableInference.Desc.K9.placesOfMapSome
#print axioms VerifiableInference.Desc.K9.hearPlaces
#print axioms VerifiableInference.Desc.K9.hearPlaceAt
#print axioms VerifiableInference.Desc.K9.kindsBehind
#print axioms VerifiableInference.Desc.K9.kindsBehindDigits
#print axioms VerifiableInference.Desc.K9.behindALookup
#print axioms VerifiableInference.Desc.K9.stepsBehindLookup
#print axioms VerifiableInference.Desc.K9.stepsBehindDigits
