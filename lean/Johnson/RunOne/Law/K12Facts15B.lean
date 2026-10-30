-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15B.lean: THE PLACE's FIRST FREE OWN NUMBER AT THE KEY FILE's FIRST PROXIMITY TEST IS THE NUMBER OF ROOTS THAT THE 15 BLOCKS IN FRONT DECLARE (the field "free" of Left15J, Johnson/RunOne/Law/K12Left15J.lean), GENERAL IN X N P, UNDER ONE TEST ON THE DATA. Statements with proofs. IT PAYS NO FIELD OF THE TABLES: NO MEMBER OF Left15J IS SHOWN HERE.
OBJECT. The start that the routine Key.rangesNumbers lays: the place of the first round of the plan that bears the batching's name.
USER. Johnson/RunOne/Law/K12Facts15S.lean.
LETTERS. As Johnson/RunOne/Law/K12Facts15A.lean's. The premise hno: none of the data's rounds in front of the test bears the batching's name. It is a test on the data; it can fail: one round further it is false.

  bat_head: in a list of entries, where none in front bears the name and the next does, the first place of the name is the number of those in front.
  entries_take: round by round the same entry: so the first k.
  front_is: the rounds that the first n blocks declare are the first of the declared rounds without their last.
  front_entries: their entries are the data's.
  start_of: the start is the number of rounds in front.
  free_of: the field.
Limits. hno is shown here of no data. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Facts15A

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Facts15
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key
open Johnson.G.OfPlan (rootsOf Made)
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.Law.RoundsInFront

theorem bat_head_aux (x : Fmt.Entry) (B : List Fmt.Entry) (hx : (x.name == "BAT") = true) :
    ∀ (A : List Fmt.Entry) (i : ℕ), (∀ e ∈ A, (e.name == "BAT") = false) →
      ((((A ++ x :: B).zipIdx i).filter fun p => p.1.name == "BAT").map (·.2)).head? = some (i + A.length)
  | [], i, _ => by
    rw [List.nil_append, List.zipIdx_cons, List.filter_cons]
    simp only [hx, ↓reduceIte, List.map_cons, List.head?_cons, List.length_nil, Nat.add_zero]
  | a :: A, i, h => by
    have ha := h a List.mem_cons_self
    have ih := bat_head_aux x B hx A (i + 1) fun e he => h e (List.mem_cons_of_mem _ he)
    rw [List.cons_append, List.zipIdx_cons, List.filter_cons]
    simp only [ha, Bool.false_eq_true, ↓reduceIte]
    rw [ih, List.length_cons]
    congr 1
    omega

/-- Where none in front bears the name and the next does, the first place of the name is the number of those in front. -/
theorem bat_head (A : List Fmt.Entry) (x : Fmt.Entry) (B : List Fmt.Entry)
    (hA : ∀ e ∈ A, (e.name == "BAT") = false) (hx : (x.name == "BAT") = true) :
    (H2U.batPlaces (A ++ x :: B)).head? = some A.length := by
  have h := bat_head_aux x B hx A 0 hA
  rw [Nat.zero_add] at h
  exact h

theorem entries_take : ∀ (ds : List RDT) (l : List Fmt.DeclaredRound), List.Forall₂ RoundAsG ds l →
    ∀ k, (ds.take k).map (·.entry) = (l.take k).map (·.entry)
  | _, _, .nil, k => by simp
  | _, _, .cons _ _, 0 => by simp
  | _, _, .cons h t, k + 1 => by
    simp only [List.take_succ_cons, List.map_cons, h.1, entries_take _ _ t k]

section
variable {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD) (h : F.data file = .ok D)
  (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (hf : F.first.blocksInOrder = c₁ :: k₁) (n : ℕ)
  (b : Block F.S₁ F.Cl) (hb : (c₁ :: k₁)[n]? = some b)
  (hne : ((c₁ :: k₁).drop (n + 1)).flatMap (·.rounds) ≠ [])
include h hf hb hne

/-- The rounds that the first n blocks declare are the first of the declared rounds without their last. -/
theorem front_is : ((c₁ :: k₁).take n).flatMap (·.rounds) =
    F.roundsDeclaredByBlocks.1.dropLast.take (((c₁ :: k₁).take n).flatMap (·.rounds)).length := by
  have hr := data_reach F file D h c₁ k₁ hf n b hb hne
  have hl : D.ds₁.length = F.roundsDeclaredByBlocks.1.dropLast.length := (roundsOfData F file D h).1.length_eq
  have e2 := rounds_take (c₁ :: k₁) n
  rw [← length_inFront] at e2
  have e1 : F.roundsDeclaredByBlocks.1 = (c₁ :: k₁).flatMap (·.rounds) := by
    show F.first.blocksInOrder.flatMap (·.rounds) = _
    rw [hf]
  rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left (by rw [← List.length_dropLast, ← hl]; omega), e1]
  exact e2

/-- Their entries are the data's. -/
theorem front_entries : (((c₁ :: k₁).take n).flatMap (·.rounds)).map (·.entry) =
    (D.ds₁.take (((c₁ :: k₁).take n).flatMap (·.rounds)).length).map (·.entry) := by
  rw [entries_take _ _ (roundsOfData F file D h).1, ← front_is F file D h c₁ k₁ hf n b hb hne]

end

section
variable {m : Made} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}
  (c₁ : Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl) (k₁ : List (Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl))
  (file : String) (D : WholeD)

/-- **The start that the routine lays is the number of rounds that the 15 blocks in front declare.** -/
theorem start_of (hX : sourceOf m = .ok X) (hN : rangesNumbers m = .ok N)
    (hp : (Key.descriptionFromSource X N P).planOk = true) (hD : (Key.descriptionFromSource X N P).data file = .ok D)
    (q₁ : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁) (hl : (Key.lookupsOf X.Y.k.oneTime).length = 2)
    (hno : ∀ d ∈ D.ds₁.take (((c₁ :: k₁).take 15).flatMap (·.rounds)).length, (d.entry.name == "BAT") = false) :
    N.start = (((c₁ :: k₁).take 15).flatMap (·.rounds)).length := by
  have hk := (PlanPays.rng_pays (plan_of X N P hp)).2.2.1
  obtain ⟨_, _, _, R, _, _, eR⟩ := H2K.Made.rounds_top (rangesParams N).nums _
    (VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts (rangesParams N) hk)
  have hb := K12AtField.rng_at_15 X N P c₁ k₁ q₁ hl
  have hne := behind_ne X N P c₁ k₁ hp q₁ hl
  have hr : (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim)).rounds =
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).rounds :=
    (RngAnyCl.same_k12 (A := Key.Claim) (B := Unit) guardedProximityTestParts (rangesParams N)).rounds
  have e : (Key.descriptionFromSource X N P).roundsDeclaredByBlocks.1 = ((c₁ :: k₁).take 15).flatMap (·.rounds) ++
      ((bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim)).rounds ++
        ((c₁ :: k₁).drop (15 + 1)).flatMap (·.rounds)) := by
    show (Key.descriptionFromSource X N P).first.blocksInOrder.flatMap (·.rounds) = _
    rw [q₁, rounds_part (c₁ :: k₁) 15 _ hb]
  obtain ⟨_, _, _, hst, _, _⟩ := numbers_parts hN
  rw [entries_are hX hp, e, hr, eR, List.map_append, List.cons_append, List.map_cons] at hst
  have hA : ∀ x ∈ (((c₁ :: k₁).take 15).flatMap (·.rounds)).map (·.entry), (x.name == "BAT") = false := by
    intro x hx
    rw [front_entries (Key.descriptionFromSource X N P) file D hD c₁ k₁ q₁ 15 _ hb hne] at hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
    exact hno d hd
  rw [bat_head _ _ _ hA rfl, List.length_map] at hst
  exact (Option.some.inj hst).symm

/-- (free) **The place's first free own number is the number of roots that the 15 blocks in front declare.** -/
theorem free_of (hX : sourceOf m = .ok X) (hN : rangesNumbers m = .ok N)
    (hp : (Key.descriptionFromSource X N P).planOk = true) (hD : (Key.descriptionFromSource X N P).data file = .ok D)
    (q₁ : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁) (hl : (Key.lookupsOf X.Y.k.oneTime).length = 2)
    (hno : ∀ d ∈ D.ds₁.take (((c₁ :: k₁).take 15).flatMap (·.rounds)).length, (d.entry.name == "BAT") = false) :
    (rangesParams N).nums.free = rootsOf (((c₁ :: k₁).take 15).flatMap (·.rounds)) :=
  free_of_start c₁ k₁ hX hN hp q₁ (start_of c₁ k₁ file D hX hN hp hD q₁ hl hno)

end

end Johnson.RunOne.Law.K12Facts15

#print axioms Johnson.RunOne.Law.K12Facts15.bat_head_aux
#print axioms Johnson.RunOne.Law.K12Facts15.bat_head
#print axioms Johnson.RunOne.Law.K12Facts15.entries_take
#print axioms Johnson.RunOne.Law.K12Facts15.front_is
#print axioms Johnson.RunOne.Law.K12Facts15.front_entries
#print axioms Johnson.RunOne.Law.K12Facts15.start_of
#print axioms Johnson.RunOne.Law.K12Facts15.free_of
