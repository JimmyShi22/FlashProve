-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/PinOfLots.lean: from the first chain's lots to the pin's clauses on the halves.

The pin (PinHalvesAt, Johnson/FrontRoad/PinPublicSpec.lean) asks two things of a list of halves: at
each place of the smallness test the first half there has the one pinned part; at every other place
the first half has no second stop. This file gets both from a list of lots in which one lot is the
smallness test's and all others are quiet (Johnson/P1K8R/QuietLots.lean) and stand at other kinds.

  find_eq_of_unique   a list's search finds the one element that meets its test
  SmallForm           what is asked of the smallness test's lot, in any reading of the input
  pinHalves_of_lots   the two clauses, at any list of members of the chain

Limits. Public premises stay premises here: that a member's place is the lot's place. Nothing is
said of a run.
-/
import Johnson.P1K8R.QuietLots
import Johnson.FrontRoad.PinPublicSpec
import Johnson.FrontRoad.ParOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open ProofFile.Honest
open ProofFile.Honest.K8 (smallStop windowShare)
open ProofFile.Honest.K9 (quietStop)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open OnBytes.FrontRoad (PinHalvesAt parOwn parOwn_some)

/-- A list's search finds the one element that meets its test. -/
theorem find_eq_of_unique {α : Type} {p : α → Bool} {x : α} :
    ∀ {hs : List α}, x ∈ hs → p x = true → (∀ y ∈ hs, p y = true → y = x) → hs.find? p = some x
  | [], hx, _, _ => by cases hx
  | a :: l, hx, hp, u => by
    by_cases ha : p a = true
    · rw [List.find?_cons_of_pos ha, u a List.mem_cons_self ha]
    · rw [List.find?_cons_of_neg ha]
      rcases List.mem_cons.1 hx with rfl | h
      · exact absurd hp ha
      · exact find_eq_of_unique h hp fun y hy => u y (List.mem_cons_of_mem _ hy)

section
variable {W₀ Rc Xi Tr X S Cl : Type}

/-- Two halves with one place and one list of parts are one. -/
theorem placed_ext {V W Y : Type} {x y : Placed V W Y} (hp : x.place = y.place)
    (hq : x.parts = y.parts) : x = y := by
  cases x
  cases y
  cases hp
  cases hq
  rfl

/-- **What is asked of the smallness test's lot** at a public part Z, a ground G and lists of
matrices mats, at the reader of cells cells: it has one half for each segment, at the segment's
place, with the one pinned part. -/
structure SmallForm (L : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (mats : ℕ → List (ℕ × String × ℕ)) (cells : Tr → Cells) : Prop where
  /-- each half of the lot is a segment's -/
  only : ∀ x ∈ L.halves Z G, ∃ l Xl, G.built[l]? = some Xl ∧
    x.place = ⟨1, some l, (ProofFile.k8Par Z G Xl l).piece, KindName.K8⟩ ∧
    x.parts = [quietStop (smallStop cells (ProofFile.k8Par Z G Xl l, mats l))
      (windowShare (ProofFile.k8Par Z G Xl l))]
  /-- each segment has a half -/
  each : ∀ l Xl, G.built[l]? = some Xl → ∃ x ∈ L.halves Z G,
    x.place = ⟨1, some l, (ProofFile.k8Par Z G Xl l).piece, KindName.K8⟩

/-- **The pin's clauses on the halves, from the lots.** lots: the chain's lots. L8: the smallness
test's. Every other lot is quiet and stands at other kinds. bs: members of the chain. hat: a member
at which parOwn names parameters stands at the place of that segment's half; hno: a member at which
it names none is not of the kind. -/
theorem pinHalves_of_lots {Z : ProofFile.Pub} {G : ProofFile.Ground} {mats : ℕ → List (ℕ × String × ℕ)}
    {cells : Tr → Cells} (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G)
    (lots : List (HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (L8 : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) (h8 : L8 ∈ lots)
    (form : SmallForm L8 Z G mats cells)
    (quiet : ∀ L ∈ lots, L = L8 ∨ LotQuiet L)
    (other : ∀ L ∈ lots, L ≠ L8 → ∀ x ∈ L.halves Z G, x.place.kind ≠ KindName.K8)
    (bs : List (Block S Cl))
    (hat : ∀ b ∈ bs, ∀ l Xl, b.place.link = some l → G.built[l]? = some Xl →
      b.place.kind = KindName.K8 →
      b.place = ⟨1, some l, (ProofFile.k8Par Z G Xl l).piece, KindName.K8⟩)
    (hno : ∀ b ∈ bs, parOwn Z mats b.place = none → b.place.kind ≠ KindName.K8) :
    PinHalvesAt (parOwn Z mats) cells (firstOf Z G lots) bs := by
  have inLot : ∀ x ∈ firstOf Z G lots, ∃ L ∈ lots, x ∈ L.halves Z G := by
    intro x hx
    exact List.mem_flatMap.1 hx
  intro b hb
  cases hp : parOwn Z mats b.place with
  | none =>
    intro g hg
    have hgm : g ∈ firstOf Z G lots := List.mem_of_find?_eq_some hg
    have hb' := List.find?_some hg
    have hpl : g.place = b.place := eq_of_beq hb'
    obtain ⟨L, hL, hx⟩ := inLot g hgm
    rcases quiet L hL with rfl | hq
    · obtain ⟨l, Xl, -, e, -⟩ := form.only g hx
      exact absurd (by rw [← hpl, e]) (hno b hb hp)
    · exact hq Z G g hx
  | some P =>
    obtain ⟨hk, l, G₀, Xl, hl, hG₀, hX, rfl⟩ := parOwn_some Z mats b.place P hp
    obtain rfl : G₀ = G := Option.some.inj (hG₀.symm.trans hG)
    have hplace := hat b hb l Xl hl hX hk
    obtain ⟨x, hx, hxp⟩ := form.each l Xl hX
    obtain ⟨l', Xl', hX', e', ep⟩ := form.only x hx
    have hll : l' = l := by
      have h := congrArg Place.link (e'.symm.trans hxp)
      exact Option.some.inj h
    subst hll
    obtain rfl : Xl' = Xl := Option.some.inj (hX'.symm.trans hX)
    refine ⟨x, find_eq_of_unique (List.mem_flatMap.2 ⟨L8, h8, hx⟩)
      (by rw [hxp, hplace]; exact beq_self_eq_true _) ?_, ep⟩
    intro y hy hyp
    have hyl : y.place = b.place := eq_of_beq hyp
    obtain ⟨L, hL, hyL⟩ := inLot y hy
    by_cases e8 : L = L8
    · subst e8
      obtain ⟨l₂, Xl₂, hX₂, e₂, ep₂⟩ := form.only y hyL
      have h₂ : l₂ = l' := by
        have h := congrArg Place.link (e₂.symm.trans (hyl.trans hplace))
        exact Option.some.inj h
      subst h₂
      obtain rfl : Xl₂ = Xl' := Option.some.inj (hX₂.symm.trans hX)
      exact placed_ext (e₂.trans e'.symm) (ep₂.trans ep.symm)
    · exact absurd (by rw [hyl]; exact hk) (other L hL e8 y hyL)

end

end P1K8

#print axioms P1K8.find_eq_of_unique
#print axioms P1K8.pinHalves_of_lots
