-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Trail.lean: ALONG A CHAIN A FALSE CLAIM GOES INTO ONE OF THE CHAIN's OWN BEGINNINGS OF
A TEST, NAMED BEFOREHAND. A trail leads from a statement to a later one by calm stretches and
beginnings of proximity tests, and BEARS THE LIST of these beginnings as data: for each the
statement in front of it, the group's number and the group. A calm step is a quiet one (tidy to
tidy; no claim lost) along which the statement only grows: so no mark is taken back. Then: whatever
the words are, if not all holds of them that the first statement claims, and all holds that the last
one claims, then at ONE MEMBER OF THAT LIST the batched row holds at few multipliers. The list
stands in front of the words. Theorems.

  Quiet.refl · Quiet.trans   a quiet step is a reflexive, transitive relation on statements.
  Calm ρ S S'          quiet, and the statement only grows. Calm.refl · Calm.trans.
  GroundQuiet.both · groundQuiet_quiet · groundQuiet_calm   the ground's eight plain functions that
                       ask nothing of their caller (Johnson/Desc/GroundQuiet.lean) are calm steps.
  Few ρ x m            the count at a beginning x = (J, g, G): the elements as which a multiplier
                       reads at which the batched row holds of tables that hold the words m are
                       fewer than the rows that the test takes in.
  Trail ρ S l Z        the trail, with its list.
  Trail.front · Trail.append · Trail.tidy · Trail.walk · Trail.grows
  Trail.member_grows   from behind each beginning of the list to the last statement the statement
                       only grows.
  Trail.catches        **the sentence.**
  Trail.catches_to_end  the same where the last statement passes the test for a protocol's end: no
                       premise on the words is left.
What is not claimed. That a chain of blocks gives a trail: that is shown kind by kind and chain by
chain. THAT A MEMBER OF THE LIST IS FIXED IN FRONT OF ITS OWN BATCHING's DRAW is not said by a
trail. "Few" is a count at a statement: that a verifier batches there, draws its multiplier behind
the beginning and tests the batched row is not said. No chance is named. From a first statement that
claims nothing the sentence is empty: it bites from behind the step that lays a false row.

-/
import Johnson.Desc.Means.WalkEnd
import Johnson.Desc.GroundQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means
open Model (Reading)
open VerifiableInference.Desc (Grows grows_begun)
open VerifiableInference.Desc.Ground (GroundQuiet)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- Nothing is done: a quiet step. -/
theorem Quiet.refl (S : Statement) : Quiet ρ S S := ⟨id, fun _ _ c => c⟩

variable {ρ}

/-- Two quiet steps are one. -/
theorem Quiet.trans {A B C : Statement} (q : Quiet ρ A B) (r : Quiet ρ B C) : Quiet ρ A C :=
  ⟨fun t => r.tidy (q.tidy t), fun t m c => q.back t m (r.back (q.tidy t) m c)⟩

variable (ρ)

/-- The ground's eight plain functions that ask nothing of their caller are quiet steps. -/
theorem groundQuiet_quiet : GroundQuiet (Quiet ρ) where
  refl := Quiet.refl ρ
  trans := Quiet.trans
  newGroup := fun _ _ _ _ _ h => quiet_newGroupP ρ h
  recv := fun _ _ _ _ _ h => quiet_recvP ρ h
  join := fun _ _ _ _ _ h => quiet_joinP ρ h
  addRow := fun _ _ _ _ h => quiet_addRowP ρ h
  takeMask := fun _ _ _ _ h => quiet_takeMaskP ρ h
  closeLedger := fun _ _ _ h => quiet_closeLedgerP ρ h
  spendAsMask := fun _ _ _ h => quiet_spendAsMaskP ρ h
  adopt := fun _ _ _ _ _ h => quiet_adoptP ρ h

/-- Quiet, and the statement only grows. -/
def Calm (S S' : Statement) : Prop := Quiet ρ S S' ∧ Grows S S'

/-- Nothing is done: a calm step. -/
theorem Calm.refl (S : Statement) : Calm ρ S S := ⟨Quiet.refl ρ S, Grows.refl S⟩

variable {ρ} in
/-- Two calm steps are one. -/
theorem Calm.trans {A B C : Statement} (q : Calm ρ A B) (r : Calm ρ B C) : Calm ρ A C :=
  ⟨q.1.trans r.1, q.2.trans r.2⟩

/-- Two relations that the eight functions keep, together. -/
theorem _root_.VerifiableInference.Desc.Ground.GroundQuiet.both
    {R R' : Statement → Statement → Prop} (H : GroundQuiet R) (H' : GroundQuiet R') :
    GroundQuiet fun a b => R a b ∧ R' a b where
  refl := fun T => ⟨H.refl T, H'.refl T⟩
  trans := fun a b => ⟨H.trans a.1 b.1, H'.trans a.2 b.2⟩
  newGroup := fun d d' c m n h => ⟨H.newGroup d d' c m n h, H'.newGroup d d' c m n h⟩
  recv := fun f d d' s i h => ⟨H.recv f d d' s i h, H'.recv f d d' s i h⟩
  join := fun d d' g o k h => ⟨H.join d d' g o k h, H'.join d d' g o k h⟩
  addRow := fun d d' g r h => ⟨H.addRow d d' g r h, H'.addRow d d' g r h⟩
  takeMask := fun d d' o n h => ⟨H.takeMask d d' o n h, H'.takeMask d d' o n h⟩
  closeLedger := fun d d' o h => ⟨H.closeLedger d d' o h, H'.closeLedger d d' o h⟩
  spendAsMask := fun d d' o h => ⟨H.spendAsMask d d' o h, H'.spendAsMask d d' o h⟩
  adopt := fun d d' s g i h => ⟨H.adopt d d' s g i h, H'.adopt d d' s g i h⟩

/-- The eight functions are calm steps. -/
theorem groundQuiet_calm : GroundQuiet (Calm ρ) :=
  (groundQuiet_quiet ρ).both VerifiableInference.Desc.Ground.groundKeeps_grows.quiet

/-- The count at a beginning of a test: few multipliers. -/
def Few (x : Statement × Nat × Group) (m : Words K) : Prop :=
  Nat.card {y : K // ∃ (e : E) (out : GroupRow) (T : Tables K), ρ.val e = y ∧
    Bat.combine (Slice.begun x.1 x.2.1 x.2.2) x.2.1
      ⟨layoutOf x.1 x.2.2, Slice.runRows x.1 x.2.2⟩ e = some out ∧
    LaidOn (Slice.begun x.1 x.2.1 x.2.2) (layoutOf x.1 x.2.2) m T ∧
    GroupSays ρ (Slice.begun x.1 x.2.1 x.2.2) (layoutOf x.1 x.2.2) out T} ≤
      (Slice.runRows x.1 x.2.2).size - 1

/-- A trail: calm stretches and beginnings of tests, with the list of the beginnings. -/
inductive Trail : Statement → List (Statement × Nat × Group) → Statement → Prop
  | calm {S Z : Statement} : Calm ρ S Z → Trail S [] Z
  | test {S J Z : Statement} {l : List (Statement × Nat × Group)} (g : Nat) (G : Group) :
      Calm ρ S J → J.groups[g]? = some G → Trail (Slice.begun J g G) l Z →
      Trail S ((J, g, G) :: l) Z

variable {ρ}

/-- A calm stretch in front of a trail. -/
theorem Trail.front {S A Z : Statement} {l : List (Statement × Nat × Group)} (q : Calm ρ S A)
    (h : Trail ρ A l Z) : Trail ρ S l Z := by
  cases h with
  | calm r => exact Trail.calm (q.trans r)
  | test g G r hG t => exact Trail.test g G (q.trans r) hG t

/-- Two trails are one; their lists in a row. -/
theorem Trail.append {S A Z : Statement} {l₁ l₂ : List (Statement × Nat × Group)}
    (h : Trail ρ S l₁ A) (k : Trail ρ A l₂ Z) : Trail ρ S (l₁ ++ l₂) Z := by
  induction h with
  | calm q => exact k.front q
  | test g G q hG _ ih => exact Trail.test g G q hG (ih k)

/-- A trail from a tidy statement ends at a tidy one. -/
theorem Trail.tidy {S Z : Statement} {l : List (Statement × Nat × Group)} (h : Trail ρ S l Z)
    (hT : Tidy S) : Tidy Z := by
  induction h with
  | calm q => exact q.1.tidy hT
  | test g G q hG _ ih => exact ih ((q.1.tidy hT).begun g G hG)

/-- A trail is a walk. -/
theorem Trail.walk {S Z : Statement} {l : List (Statement × Nat × Group)} (h : Trail ρ S l Z) :
    Walk ρ S Z := by
  induction h with
  | calm q => exact q.1.walk
  | test g G q hG _ ih => exact Walk.quiet q.1 (Walk.begun g G hG ih)

/-- Along a trail the statement only grows. -/
theorem Trail.grows {S Z : Statement} {l : List (Statement × Nat × Group)} (h : Trail ρ S l Z) :
    Grows S Z := by
  induction h with
  | calm q => exact q.2
  | test g G q _ _ ih => exact q.2.trans ((grows_begun _ g G).trans ih)

/-- From behind each beginning of the list to the last statement the statement only grows. -/
theorem Trail.member_grows {S Z : Statement} {l : List (Statement × Nat × Group)}
    (h : Trail ρ S l Z) : ∀ x ∈ l, Grows (Slice.begun x.1 x.2.1 x.2.2) Z := by
  induction h with
  | calm _ => exact fun _ hx => by cases hx
  | test g G _ _ t ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact t.grows
    · exact ih x hx

/-- **Along a trail a false claim goes into a member of the trail's own list.** -/
theorem Trail.catches [IsDomain K] [Finite K] {S Z : Statement}
    {l : List (Statement × Nat × Group)} (h : Trail ρ S l Z) (hT : Tidy S) {m : Words K}
    (hbad : ¬ Claims ρ S m) (hend : Claims ρ Z m) : ∃ x ∈ l, Few ρ x m := by
  induction h with
  | calm q => exact absurd (q.1.back hT m hend) hbad
  | @test S J Z l g G q hG _ ih =>
    have tJ := q.1.tidy hT
    have bJ : ¬ Claims ρ J m := fun c => hbad (q.1.back hT m c)
    rcases claims_catches ρ tJ.inOrder tJ.kinds g G hG bJ with c | c
    · obtain ⟨x, hx, f⟩ := ih (tJ.begun g G hG) c hend
      exact ⟨x, List.mem_cons_of_mem _ hx, f⟩
    · exact ⟨(J, g, G), List.mem_cons_self, c⟩

/-- **To the end of a protocol**: no premise on the words at the end is left. -/
theorem Trail.catches_to_end [IsDomain K] [Finite K] {S Z : Statement}
    {l : List (Statement × Nat × Group)} (h : Trail ρ S l Z) (hT : Tidy S)
    (hEnd : (Z.groups.all (·.inRun) && Z.oracles.all fun x => !x.sampled || !x.groups.isEmpty) =
      true)
    (hL : ∀ (o : Nat) (x : Oracle) (g : Nat), Z.oracles[o]? = some x → g ∈ x.groups →
      ∃ G, Z.groups[g]? = some G ∧ o ∈ G.members)
    (hM : ∀ (i : Nat) (G : Group), Z.groups[i]? = some G → G.inRun = true → G.rows = #[]) :
    ∀ m : Words K, ¬ Claims ρ S m → ∃ x ∈ l, Few ρ x m :=
  fun m hbad => h.catches hT hbad (claims_end_of ρ hEnd hL hM (h.tidy hT).noneYet m)

end OnBytes.Means
