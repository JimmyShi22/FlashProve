-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Steps.lean: the honest side of the kind "lookup" (K3). Proofs
of three of the statements of Honest/K3/Law/Statements.lean, which rest on nothing outside the
library and the frame's own definitions. Theorems, with a few definitions.

Terms. Honest/K3/GLOSSARY.md ("course", "form", "job, summand", "stage", "world, worth").

What is shown.
  `quietStep : QuietStep`: a stage that sends nothing leaves the invariant as it is.
  `drawsWork : DrawsWork`: the frame's test on challenges reads no work bit.
  `formWorth : FormWorth`: where the end slots of the stages in front hold the true end values, the
    form that the verifier claims at a stage is worth what it should be.
  `rank`, `stages_sorted`, `mem_front`: what these need on the order of a lookup's stages (further
    definitions: `lt3`, `Fore`, `treeOf`; for `formWorth`: `Holds`).
  `job_front_call` and six like it, `call_seen`, `poly_seen`, `ends_seen`: a stage's job reads
    nothing of what was shown. This is the warrant for `Course.front` (Statements.lean), which gives
    the same `Seen` at every stage.

Hypotheses that remain. The three main theorems have those inside their statements
(Statements.lean).
In the lemmas: `h`, `h'`, `h1`, `h2`, `h3`, `hf`, `hg`: ranks compared, or `Fore`, of two stages or
of the members of lists; `ha`, `hs`, `hy`, `h`, `hm`: a stage is one of the row's, or a number is in
range; `h`, `hT`, `hS`: `Holds` at the stage, at the tie's steps, at the parts' steps; `hp`: the
planes' slots hold the planes' values; `ht`, `h2`: the stage has two end values; two planes at
least. Hypotheses without a name in front of arrows: `idx_ge`, `mem_front` (three), `join_fold`,
`tab_value`.

Users. This file is imported by Honest/K3/Law/LookLeftOf.lean, Honest/K3/Law/SpecCourse.lean,
Honest/K3/Law/StageFacts.lean and Honest/K3/Law/Walk.lean.

Limits. These are lemmas about definitions of the honest side; none says that any summand sums as it
should, and none speaks of a run of the protocol.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Statements
import Johnson.Desc.ProofFile.Honest.K3.RowLaw
import Johnson.Desc.ProofFile.Honest.K3.HeardLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE addE subE mulE)
open OnBytes.Model (Reading Aff Fork eqTab)
open OnBytes.Slice (GE)
open VerifiableInference.Desc.K3 (entriesV entriesFit)

variable {W : Type}

/-! ## A stage's job reads nothing of what was shown -/

section
variable (J : LookJobs W) (a : At) (s : Stage) (w : W) (t : State W Unit) (seen seen' : Seen)

/-- **The call of a stage's job is the same whatever was shown in front of it.** By
unfolding: it fails to compile as soon as `jobOf` (Honest/K3/Row.lean) reads what was shown. So do
the six beneath. -/
theorem job_front_call : (jobAt J a s).callAt w (SumLaw.frontOf t seen) =
    (jobAt J a s).callAt w (SumLaw.frontOf t seen') := rfl

theorem job_front_points : (jobAt J a s).points w (SumLaw.frontOf t seen) =
    (jobAt J a s).points w (SumLaw.frontOf t seen') := rfl

theorem job_front_lead : (jobAt J a s).lead w (SumLaw.frontOf t seen) =
    (jobAt J a s).lead w (SumLaw.frontOf t seen') := rfl

theorem job_front_round : (jobAt J a s).round w (SumLaw.frontOf t seen) =
    (jobAt J a s).round w (SumLaw.frontOf t seen') := rfl

theorem job_front_inY : (jobAt J a s).inY w (SumLaw.frontOf t seen) =
    (jobAt J a s).inY w (SumLaw.frontOf t seen') := rfl

theorem job_front_ends : (jobAt J a s).ends w (SumLaw.frontOf t seen) =
    (jobAt J a s).ends w (SumLaw.frontOf t seen') := rfl

theorem job_front_poly (m : List E) : SumLaw.jobPoly (jobAt J a s) w (SumLaw.frontOf t seen) m =
    SumLaw.jobPoly (jobAt J a s) w (SumLaw.frontOf t seen') m := rfl

end

/-- **Whatever is shown where a stage is played, its call is the course's.** -/
theorem call_seen (R : Course W) (s : Stage) (seen : Seen) :
    (R.job s).callAt R.t.input (SumLaw.frontOf (R.stateAt s) seen) = R.call s := rfl

/-- The like for the summand's polynomial. -/
theorem poly_seen (R : Course W) (s : Stage) (seen : Seen) :
    SumLaw.jobPoly (R.job s) R.t.input (SumLaw.frontOf (R.stateAt s) seen) (R.masks s) = R.poly s :=
      rfl

/-- The like for the true end values. -/
theorem ends_seen (R : Course W) (s : Stage) (seen : Seen) :
    (R.job s).ends R.t.input (SumLaw.frontOf (R.stateAt s) seen)
      ((R.r s).take (R.job s).shape.vs.length) = R.ends s := rfl

/-! ## A stage that sends nothing -/

theorem take_succ_get {α : Type} {l : List α} {n : Nat} {s : α} (h : l[n]? = some s) :
    l.take (n + 1) = l.take n ++ [s] := by
  rw [List.take_add_one, h]
  rfl

/-- **A stage that sends nothing leaves the invariant as it is** (the statement `QuietStep`). -/
theorem quietStep : QuietStep := by
  intro W R n s F hs hc hI
  have ht := take_succ_get hs
  have h0 : s.tail R.f = 0 := by simp [Stage.tail, hc]
  have h1 : s.slots R.f = 0 := by simp [Stage.slots, Stage.own, Stage.tail, hc]
  refine ⟨hI.sized, ?_, hI.room, hI.free, ?_, ?_⟩
  · rw [hI.next]
    simp [slotsIn, ht, h1]
  · intro s' hs' j hj
    rw [ht] at hs'
    rcases List.mem_append.1 hs' with h | h
    · exact hI.filled s' h j hj
    · obtain rfl : s' = s := by simpa using h
      omega
  · intro H mask entry hL hM s' hs' j hj
    rw [ht] at hs'
    rcases List.mem_append.1 hs' with h | h
    · exact hI.ends H mask entry hL hM s' h j hj
    · obtain rfl : s' = s := by simpa using h
      omega

/-! ## Work bits -/

theorem drawFit_work (e : Fmt.Entry) (R : Fmt.Drawn) :
    drawFit (declOf { e with work := 0 }) R = drawFit (declOf e) R := rfl

theorem drawsFit_work : ∀ (es : List Fmt.Entry) (ds : List Fmt.Drawn),
    drawsFit ((es.map fun e => { e with work := 0 }).map declOf) ds = drawsFit (es.map declOf) ds
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | e :: es, d :: ds => by
    simp only [List.map_cons, drawsFit]
    rw [drawFit_work, drawsFit_work es ds]

/-- **The frame's test on challenges reads no work bit** (the statement `DrawsWork`; its hypothesis:
the planner's entries are the verifier's text's but for the work bits). -/
theorem drawsWork : DrawsWork := by
  intro f es ds h
  have h' : (es.map fun e => { e with work := 0 }) = entriesV f := by
    simpa [entriesFit] using h
  rw [← h', drawsFit_work]

/-! ## The order of the stages -/

/-- A stage's rank: the group; the number in the group; the place inside that number. -/
def rank : Stage → Nat × Nat × Nat
  | .shift => (0, 0, 0)
  | .alpha => (1, 0, 0)
  | .tie s => (2, s, 0)
  | .split i => (3, i, 0)
  | .join => (4, 0, 0)
  | .key i m => (5, i, 2 * m)
  | .keyLine i m => (5, i, 2 * m + 1)
  | .tab l => (6, l, 0)
  | .tabLine l => (6, l, 1)
  | .leaves => (7, 0, 0)
  | .zero => (8, 0, 0)
  | .bits => (9, 0, 0)

/-- One rank stands in front of another. -/
def lt3 (a b : Nat × Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

/-- One stage stands in front of another. -/
def Fore (a b : Stage) : Prop := lt3 (rank a) (rank b)

theorem fore_mid {a b : Stage} (h1 : (rank a).1 = (rank b).1) (h2 : (rank a).2.1 < (rank b).2.1) :
    Fore a b := Or.inr ⟨h1, Or.inl h2⟩

theorem fore_last {a b : Stage} (h1 : (rank a).1 = (rank b).1) (h2 : (rank a).2.1 = (rank b).2.1)
    (h3 : (rank a).2.2 < (rank b).2.2) : Fore a b := Or.inr ⟨h1, Or.inr ⟨h2, h3⟩⟩

theorem fore_asymm {a b : Stage} (h : Fore a b) (h' : Fore b a) : False := by
  unfold Fore lt3 at h h'
  omega

theorem pairwise_range_map {g : Nat → Stage} (hg : ∀ i j, i < j → Fore (g i) (g j)) (n : Nat) :
    ((List.range n).map g).Pairwise Fore := by
  rw [List.pairwise_map]
  exact List.Pairwise.imp (fun {a b} h => hg a b h) List.pairwise_lt_range

theorem pairwise_range_flatMap {g : Nat → List Stage} (h1 : ∀ i, (g i).Pairwise Fore)
    (h2 : ∀ i j, i < j → ∀ a ∈ g i, ∀ b ∈ g j, Fore a b) (n : Nat) :
    ((List.range n).flatMap g).Pairwise Fore := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.pairwise_append]
    refine ⟨ih, by simpa using h1 n, ?_⟩
    intro a ha b hb
    obtain ⟨i, hi, hai⟩ := List.mem_flatMap.1 ha
    have hb' : b ∈ g n := by simpa using hb
    exact h2 i n (List.mem_range.1 hi) a hai b hb'

theorem idx_ge : ∀ (l : List Nat) (k : Nat) (x : Nat × Nat), x ∈ l.zipIdx k → k ≤ x.2
  | [], _, _, h => by simp at h
  | _ :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_of_succ_le (idx_ge l (k + 1) x h)

/-- The stages of one part's key tree. -/
def treeOf (x : Nat × Nat) : List Stage :=
  (List.range x.1).flatMap fun m => [Stage.key x.2 m, Stage.keyLine x.2 m]

theorem rank_tree {x : Nat × Nat} {s : Stage} (h : s ∈ treeOf x) :
    (rank s).1 = 5 ∧ (rank s).2.1 = x.2 := by
  obtain ⟨m, _, hm⟩ := List.mem_flatMap.1 h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem tree_sorted (x : Nat × Nat) : (treeOf x).Pairwise Fore := by
  refine pairwise_range_flatMap (fun i => ?_) (fun i j hij a ha b hb => ?_) x.1
  · simp [Fore, lt3, rank]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact fore_last rfl rfl (show 2 * i < 2 * j by omega)
    · exact fore_last rfl rfl (show 2 * i < 2 * j + 1 by omega)
    · exact fore_last rfl rfl (show 2 * i + 1 < 2 * j by omega)
    · exact fore_last rfl rfl (show 2 * i + 1 < 2 * j + 1 by omega)

theorem trees_sorted : ∀ (l : List Nat) (k : Nat), ((l.zipIdx k).flatMap treeOf).Pairwise Fore
  | [], _ => by simp
  | v :: l, k => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.pairwise_append]
    refine ⟨tree_sorted _, trees_sorted l (k + 1), ?_⟩
    intro a ha b hb
    obtain ⟨y, hy, hby⟩ := List.mem_flatMap.1 hb
    have h1 := rank_tree ha
    have h2 := rank_tree hby
    have h3 := idx_ge l (k + 1) y hy
    exact fore_mid (h1.1.trans h2.1.symm) (by rw [h1.2, h2.2]; exact h3)

theorem rank_trees {l : List Nat} {s : Stage} (h : s ∈ (l.zipIdx).flatMap treeOf) :
    (rank s).1 = 5 := by
  obtain ⟨y, _, hy⟩ := List.mem_flatMap.1 h
  exact (rank_tree hy).1

theorem fore_grp {a b : Stage} (h : (rank a).1 < (rank b).1) : Fore a b := Or.inl h

/-- **The stages of a lookup stand in the order of their ranks.** -/
theorem stages_sorted (f : LFace) : (stages f).Pairwise Fore := by
  have hA : ∀ s ∈ (if f.shifted then [Stage.shift] else []), (rank s).1 = 0 := by
    intro s hs
    split at hs
    · obtain rfl : s = .shift := by simpa using hs
      rfl
    · simp at hs
  have hT : ∀ s ∈ (List.range (f.planes - 1)).map Stage.tie, (rank s).1 = 2 := by
    intro s hs
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hs
    rfl
  have hS : ∀ s ∈ (List.range (f.parts.length - 1)).map Stage.split, (rank s).1 = 3 := by
    intro s hs
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hs
    rfl
  have hK : ∀ s ∈ f.parts.zipIdx.flatMap treeOf, (rank s).1 = 5 := fun s hs => rank_trees hs
  have hB : ∀ s ∈ (List.range f.d).flatMap (fun l => [Stage.tab l, Stage.tabLine l]),
      (rank s).1 = 6 := by
    intro s hs
    obtain ⟨l, _, hl⟩ := List.mem_flatMap.1 hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> rfl
  have hL : ∀ s ∈ [Stage.leaves, Stage.zero, Stage.bits], 7 ≤ (rank s).1 := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> simp [rank]
  have pA : (if f.shifted then [Stage.shift] else []).Pairwise Fore := by
    split <;> simp
  have pT : ((List.range (f.planes - 1)).map Stage.tie).Pairwise Fore :=
    pairwise_range_map (g := Stage.tie) (fun _ _ h => fore_mid rfl h) _
  have pS : ((List.range (f.parts.length - 1)).map Stage.split).Pairwise Fore :=
    pairwise_range_map (g := Stage.split) (fun _ _ h => fore_mid rfl h) _
  have pB : ((List.range f.d).flatMap (fun l => [Stage.tab l, Stage.tabLine l])).Pairwise Fore := by
    refine pairwise_range_flatMap (fun i => ?_) (fun i j hij a ha b hb => ?_) f.d
    · simp [Fore, lt3, rank]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> exact fore_mid rfl hij
  have pL : [Stage.leaves, Stage.zero, Stage.bits].Pairwise Fore := by
    simp [Fore, lt3, rank]
  show ((if f.shifted then [Stage.shift] else []) ++ [Stage.alpha] ++
    (List.range (f.planes - 1)).map Stage.tie ++
    (List.range (f.parts.length - 1)).map Stage.split ++ [Stage.join] ++
    f.parts.zipIdx.flatMap treeOf ++
    (List.range f.d).flatMap (fun l => [Stage.tab l, Stage.tabLine l]) ++
    [Stage.leaves, Stage.zero, Stage.bits]).Pairwise Fore
  have g1 : ∀ s ∈ [Stage.alpha], (rank s).1 = 1 := by
    intro s hs
    obtain rfl : s = .alpha := by simpa using hs
    rfl
  have g4 : ∀ s ∈ [Stage.join], (rank s).1 = 4 := by
    intro s hs
    obtain rfl : s = .join := by simpa using hs
    rfl
  simp only [List.pairwise_append, List.mem_append]
  refine ⟨⟨⟨⟨⟨⟨⟨pA, by simp, ?_⟩, pT, ?_⟩, pS, ?_⟩, by simp, ?_⟩, trees_sorted _ 0, ?_⟩, pB, ?_⟩,
    pL, ?_⟩
  all_goals
    intro a ha b hb
    apply fore_grp
  · have := hA a ha; have := g1 b hb; omega
  · have := hT b hb
    rcases ha with h | h
    · have := hA a h; omega
    · have := g1 a h; omega
  · have := hS b hb
    rcases ha with (h | h) | h
    · have := hA a h; omega
    · have := g1 a h; omega
    · have := hT a h; omega
  · have := g4 b hb
    rcases ha with ((h | h) | h) | h
    · have := hA a h; omega
    · have := g1 a h; omega
    · have := hT a h; omega
    · have := hS a h; omega
  · have := hK b hb
    rcases ha with (((h | h) | h) | h) | h
    · have := hA a h; omega
    · have := g1 a h; omega
    · have := hT a h; omega
    · have := hS a h; omega
    · have := g4 a h; omega
  · have := hB b hb
    rcases ha with ((((h | h) | h) | h) | h) | h
    · have := hA a h; omega
    · have := g1 a h; omega
    · have := hT a h; omega
    · have := hS a h; omega
    · have := g4 a h; omega
    · have := hK a h; omega
  · have := hL b hb
    rcases ha with (((((h | h) | h) | h) | h) | h) | h
    · have := hA a h; omega
    · have := g1 a h; omega
    · have := hT a h; omega
    · have := hS a h; omega
    · have := g4 a h; omega
    · have := hK a h; omega
    · have := hB a h; omega

/-- In a list that stands in the order of the ranks, an entry that stands in front of s is among the
entries in front of s's place (all entries, if s is none). -/
theorem mem_front : ∀ {l : List Stage}, l.Pairwise Fore → ∀ {a s : Stage}, a ∈ l → Fore a s →
    a ∈ l.take (l.idxOf s)
  | [], _, _, _, ha, _ => by simp at ha
  | x :: t, hp, a, s, ha, hf => by
    by_cases hx : x = s
    · subst hx
      exfalso
      rcases List.mem_cons.1 ha with rfl | h
      · exact fore_asymm hf hf
      · exact fore_asymm hf ((List.pairwise_cons.1 hp).1 a h)
    · rw [List.idxOf_cons_ne _ hx, List.take_succ_cons]
      rcases List.mem_cons.1 ha with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_front (List.pairwise_cons.1 hp).2 h hf)

/-- The same at a lookup's stages. -/
theorem front_of {f : LFace} {a s : Stage} (ha : a ∈ stages f) (hf : Fore a s) :
    a ∈ (stages f).take (indexOf f s) :=
  mem_front (stages_sorted f) ha hf

/-! ## Which stages stand in the row -/

theorem mem_tie {f : LFace} {j : Nat} (h : j < f.planes - 1) : Stage.tie j ∈ stages f := by
  unfold stages
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
    (List.mem_map.2 ⟨j, List.mem_range.2 h, rfl⟩))))))

theorem mem_split {f : LFace} {i : Nat} (h : i < f.parts.length - 1) :
    Stage.split i ∈ stages f := by
  unfold stages
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.2 ⟨i, List.mem_range.2 h, rfl⟩)))))

theorem mem_keyOf {f : LFace} {y : Nat × Nat} (hy : y ∈ f.parts.zipIdx) {m : Nat} (hm : m < y.1) :
    Stage.key y.2 m ∈ stages f := by
  unfold stages
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.2 ⟨y, hy,
    List.mem_flatMap.2 ⟨m, List.mem_range.2 hm, List.mem_cons_self⟩⟩)))

theorem mem_tabOf {f : LFace} {l : Nat} (h : l < f.d) : Stage.tab l ∈ stages f := by
  unfold stages
  simp only [List.mem_append]
  exact Or.inl (Or.inr (List.mem_flatMap.2 ⟨l, List.mem_range.2 h, List.mem_cons_self⟩))

theorem tie_lt {f : LFace} {j : Nat} (hs : Stage.tie j ∈ stages f) : j < f.planes - 1 := by
  unfold stages at hs
  by_cases hc : f.shifted = true <;> simp [hc] at hs <;> exact hs

theorem split_lt {f : LFace} {i : Nat} (hs : Stage.split i ∈ stages f) :
    i < f.parts.length - 1 := by
  unfold stages at hs
  by_cases hc : f.shifted = true <;> simp [hc] at hs <;> exact hs

/-! ## The forms' worth -/

section
variable (R : Course W) (Wd : OnBytes.Model.World GE)

/-- The end slots of a stage hold its true end values. -/
def Holds (s : Stage) : Prop :=
  ∀ j, j < s.tail R.f → Wd.slot (R.endSlot s + j) = rd (R.T s j)

theorem line_value (s : Stage) (xi : E) (ht : s.tail R.f = 2) (h : Holds R Wd s) :
    (R.line s xi).value Reading.gl Wd = rd (R.lineV s xi) := by
  have h0 : Wd.slot (R.endSlot s) = rd (R.T s 0) := h 0 (by omega)
  have h1 : Wd.slot (R.endSlot s + 1) = rd (R.T s 1) := h 1 (by omega)
  simp only [Course.line, Course.lineV, VerifiableInference.Desc.First.ProdV.stepDown,
    Aff.value_add, Aff.value_scale, Aff.value_slot, h0, h1, Reading.gl.add, Reading.gl.mul]

theorem plane_value (h2 : 2 ≤ R.f.planes) (hT : ∀ k, k < R.f.planes - 1 → Holds R Wd (.tie k))
    (j : Nat) : Wd.slot (R.planeSlot j) = rd (R.planeV j) := by
  unfold Course.planeSlot Course.planeV
  by_cases h0 : j = 0
  · rw [if_pos h0, if_pos h0]
    exact hT 0 (by omega) 2 (show 2 < 3 by omega)
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : j + 1 < R.f.planes
    · rw [if_pos h1, if_pos h1]
      obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
      exact hT (q + 1) (by omega) 1 (show 1 < 2 by omega)
    · rw [if_neg h1, if_neg h1]
      by_cases h3 : R.f.planes = 2
      · rw [if_pos h3, if_pos h3]
        exact hT 0 (by omega) 1 (show 1 < 3 by omega)
      · rw [if_neg h3, if_neg h3]
        obtain ⟨q, hq⟩ : ∃ q, R.f.planes - 2 = q + 1 := ⟨R.f.planes - 3, by omega⟩
        rw [hq]
        exact hT (q + 1) (by omega) 0 (show 0 < 2 by omega)

theorem join_fold (hp : ∀ j, Wd.slot (R.planeSlot j) = rd (R.planeV j)) :
    ∀ (l : List Nat) (c : Aff) (cE : E), c.value Reading.gl Wd = rd cE →
    (l.foldl (fun (c : Aff) j =>
      if j < R.f.planes then
        Aff.addMul c (Aff.slot (R.planeSlot j)) ((eqTab R.pts.rhoT).getD j zeroE)
      else c + Aff.ofConst ((eqTab R.pts.rhoT).getD j zeroE)) c).value Reading.gl Wd =
    rd (l.foldl (fun c j =>
      addE c (mulE ((eqTab R.pts.rhoT).getD j zeroE) (if j < R.f.planes then R.planeV j else oneE)))
      cE)
  | [], _, _, hc => hc
  | j :: l, c, cE, hc => by
    simp only [List.foldl_cons]
    apply join_fold hp l
    by_cases hj : j < R.f.planes
    · simp only [if_pos hj, Aff.value_addMul, Aff.value_slot, hc, hp j, Reading.gl.add,
        Reading.gl.mul]
    · simp only [if_neg hj, Aff.value_add, Aff.value_ofConst, hc, Reading.gl.add, Reading.gl.mul,
        Reading.gl.one, mul_one]

theorem join_value (h2 : 2 ≤ R.f.planes) (hT : ∀ k, k < R.f.planes - 1 → Holds R Wd (.tie k)) :
    R.join.value Reading.gl Wd = rd R.joinV :=
  join_fold R Wd (plane_value R Wd h2 hT) _ _ _ (Aff.value_ofConst _ _ _)

theorem tab_value (h2 : 2 ≤ R.f.planes) (hT : ∀ k, k < R.f.planes - 1 → Holds R Wd (.tie k)) :
    ∀ l, (∀ l', l' < l → Holds R Wd (.tab l')) →
      (R.tabForm l).value Reading.gl Wd = rd (R.tabV l)
  | 0, _ => join_value R Wd h2 hT
  | l + 1, h => line_value R Wd (.tab l) _ rfl (h l (Nat.lt_succ_self l))

theorem root_value (hT : Holds R Wd (.tie 0))
    (hS : ∀ k, k < R.f.parts.length - 1 → Holds R Wd (.split k)) (i : Nat) :
    (R.root i).value Reading.gl Wd = rd (R.rootV i) := by
  unfold Course.root Course.rootV
  by_cases h0 : i + 1 < R.f.parts.length
  · rw [if_pos h0, if_pos h0, Aff.value_slot]
    exact hS i (by omega) 0 (show 0 < 2 by omega)
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : R.f.parts.length ≤ 1
    · rw [if_pos h1, if_pos h1, Aff.value_slot]
      exact hT 0 (show 0 < 3 by omega)
    · rw [if_neg h1, if_neg h1, Aff.value_slot]
      exact hS _ (by omega) 1 (show 1 < 2 by omega)

end

/-- **The form that the verifier claims at a stage is worth what it should be** (the statement
`FormWorth`), for all numbers of the lookup. Conditional, as the statement says, on the tests on
the numbers and on the end slots of the stages in front holding the true end values. -/
theorem formWorth : FormWorth := by
  intro W R Wd s hok hs hprem
  have h2 : 2 ≤ R.f.planes := two_le_planes_of_ok R.f hok
  have hP : ∀ s', s' ∈ stages R.f → Fore s' s → Holds R Wd s' :=
    fun s' h' hf j hj => hprem s' (front_of h' hf) j hj
  have zero : (Aff.ofConst zeroE).value Reading.gl Wd = rd zeroE := Aff.value_ofConst _ _ _
  match s, hs, hP with
  | .shift, _, _ => exact zero
  | .alpha, _, _ => exact zero
  | .join, _, _ => exact zero
  | .keyLine _ _, _, _ => exact zero
  | .tabLine _, _, _ => exact zero
  | .zero, _, _ => exact zero
  | .bits, _, _ => exact zero
  | .tie 0, _, _ => exact zero
  | .tie 1, _, hP =>
    show (Aff.slot _).value Reading.gl Wd = _
    rw [Aff.value_slot]
    exact hP (.tie 0) (mem_tie (by omega)) (fore_mid rfl (show 0 < 1 by omega)) 1
      (show 1 < 3 by omega)
  | .tie (n + 2), hs, hP =>
    have hn : n + 2 < R.f.planes - 1 := by
      rcases hs with h | ⟨y, _, h⟩
      · exact tie_lt h
      · exact nomatch h
    show (Aff.slot _).value Reading.gl Wd = _
    rw [Aff.value_slot]
    exact hP (.tie (n + 1)) (mem_tie (by omega)) (fore_mid rfl (show n + 1 < n + 2 by omega)) 0
      (show 0 < 2 by omega)
  | .split 0, _, hP =>
    show (Aff.slot _).value Reading.gl Wd = _
    rw [Aff.value_slot]
    exact hP (.tie 0) (mem_tie (by omega)) (fore_grp (show 2 < 3 by omega)) 0 (show 0 < 3 by omega)
  | .split (i + 1), hs, hP =>
    have hn : i + 1 < R.f.parts.length - 1 := by
      rcases hs with h | ⟨y, _, h⟩
      · exact split_lt h
      · exact nomatch h
    show (Aff.slot _).value Reading.gl Wd = _
    rw [Aff.value_slot]
    exact hP (.split i) (mem_split (by omega)) (fore_mid rfl (show i < i + 1 by omega)) 1
      (show 1 < 2 by omega)
  | .key i 0, _, hP =>
    exact root_value R Wd (hP _ (mem_tie (by omega)) (fore_grp (show 2 < 5 by omega)))
      (fun k hk => hP _ (mem_split hk) (fore_grp (show 3 < 5 by omega))) i
  | .key i (m + 1), hs, hP =>
    have hm : Stage.key i m ∈ stages R.f := by
      rcases hs with h | ⟨y, hy, h⟩
      · obtain ⟨x, hx, hi, hlt⟩ := mem_key h
        rw [hi]
        exact mem_keyOf hx (by omega)
      · injection h with h1 h2
        rw [h1]
        exact mem_keyOf hy (by omega)
    exact line_value R Wd (.key i m) _ rfl
      (hP _ hm (fore_last rfl rfl (show 2 * m < 2 * (m + 1) by omega)))
  | .tab l, hs, hP =>
    have hl : l < R.f.d := by
      rcases hs with h | ⟨y, _, h⟩
      · exact mem_tab h
      · exact nomatch h
    exact tab_value R Wd h2 (fun k hk => hP _ (mem_tie hk) (fore_grp (show 2 < 6 by omega))) l
      (fun l' hl' => hP _ (mem_tabOf (by omega)) (fore_mid rfl hl'))
  | .leaves, _, hP =>
    exact tab_value R Wd h2 (fun k hk => hP _ (mem_tie hk) (fore_grp (show 2 < 7 by omega))) R.f.d
      (fun l' hl' => hP _ (mem_tabOf hl') (fore_grp (show 6 < 7 by omega)))

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.job_front_call
#print axioms ProofFile.Honest.K3.Law.job_front_points
#print axioms ProofFile.Honest.K3.Law.job_front_lead
#print axioms ProofFile.Honest.K3.Law.job_front_round
#print axioms ProofFile.Honest.K3.Law.job_front_inY
#print axioms ProofFile.Honest.K3.Law.job_front_ends
#print axioms ProofFile.Honest.K3.Law.job_front_poly
#print axioms ProofFile.Honest.K3.Law.call_seen
#print axioms ProofFile.Honest.K3.Law.poly_seen
#print axioms ProofFile.Honest.K3.Law.ends_seen
#print axioms ProofFile.Honest.K3.Law.take_succ_get
#print axioms ProofFile.Honest.K3.Law.quietStep
#print axioms ProofFile.Honest.K3.Law.drawFit_work
#print axioms ProofFile.Honest.K3.Law.drawsFit_work
#print axioms ProofFile.Honest.K3.Law.drawsWork
#print axioms ProofFile.Honest.K3.Law.fore_mid
#print axioms ProofFile.Honest.K3.Law.fore_last
#print axioms ProofFile.Honest.K3.Law.fore_asymm
#print axioms ProofFile.Honest.K3.Law.pairwise_range_map
#print axioms ProofFile.Honest.K3.Law.pairwise_range_flatMap
#print axioms ProofFile.Honest.K3.Law.idx_ge
#print axioms ProofFile.Honest.K3.Law.rank_tree
#print axioms ProofFile.Honest.K3.Law.tree_sorted
#print axioms ProofFile.Honest.K3.Law.trees_sorted
#print axioms ProofFile.Honest.K3.Law.rank_trees
#print axioms ProofFile.Honest.K3.Law.fore_grp
#print axioms ProofFile.Honest.K3.Law.stages_sorted
#print axioms ProofFile.Honest.K3.Law.mem_front
#print axioms ProofFile.Honest.K3.Law.front_of
#print axioms ProofFile.Honest.K3.Law.mem_tie
#print axioms ProofFile.Honest.K3.Law.mem_split
#print axioms ProofFile.Honest.K3.Law.mem_keyOf
#print axioms ProofFile.Honest.K3.Law.mem_tabOf
#print axioms ProofFile.Honest.K3.Law.tie_lt
#print axioms ProofFile.Honest.K3.Law.split_lt
#print axioms ProofFile.Honest.K3.Law.line_value
#print axioms ProofFile.Honest.K3.Law.plane_value
#print axioms ProofFile.Honest.K3.Law.join_fold
#print axioms ProofFile.Honest.K3.Law.join_value
#print axioms ProofFile.Honest.K3.Law.tab_value
#print axioms ProofFile.Honest.K3.Law.root_value
#print axioms ProofFile.Honest.K3.Law.formWorth
