-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/EntriesMade.lean: two tests on the plan of a proximity test, `nzOk` (NzOk.lean)
and `logOk` (CanonOk.lean), say yes wherever the block's own test on the plan does.

The declared rounds' entries are the entries of the rounds of Fmt/M1Plan.lean, but that the first
"FOLD epsilon" may have 32 bytes and a root more (`H2U.layOpens`). nzOk needs no more: it holds
wherever the numbers give rounds. logOk needs that each stage's main code has a ≤ 64; `sizesOk`
(Johnson/Desc/K12/Sizes.lean), a clause of the frame's test on the plan, asks a ≤ 60. Statements and
proofs.
Main names:
  `lay_entries`, `later_entries`, `rounds_entries`: what holds of the entries of the seven kinds of
    rounds, and is not turned by 32 bytes and a root more, holds of every declared round's entry.
    `ok_zip`: a tool.
  `nzOk_made`, `logOk_made`: the two tests from the numbers. `stages_of_ok`, `sizes_of_planOk`: of
    each stage: C.a ≤ 60 and h ≤ k.
  `nzOk_of_planOk`, `logOk_of_planOk`: (proximityTestKind X p).planOk = true gives nzOk p = true and logOk p =
    true, whatever the parts X.
What it means: `nzOk_made` holds at every p whose numbers give rounds: no such plan can fail nzOk.
logOk alone leans on a test of the place: sizesOk's C.a ≤ 60.
What it pays: the premises hnz : nzOk p = true and hlog : logOk p = true of `accK_yes_place`,
`accK_yes_real_const`, `accK_yes_real_own` (AccKPlace.lean, AccKConst.lean, AccKOwn.lean) and of
what they call.
Limits: that planOk says yes at a real place is not shown here: it has been seen in runs only. No
soundness is claimed, and nothing is said on hiding.
-/
import Johnson.Desc.K12.Law.DealMade
import Johnson.Desc.K12.Law.CanonOk

set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Fmt.M1 (rEps rTwo rSeed rCs rLambda rBase laterRounds wMid)
open H2K.First

/-- What holds of every round's entry, and is not turned by 32 bytes and a root more, holds of every
laid round's entry. -/
theorem lay_entries (P : Fmt.Entry → Prop)
    (hP : ∀ e : Fmt.Entry, P e → P { e with msg := 32 + e.msg, roots := 1 }) (own : Bool) :
    ∀ (rs : List Fmt.Round) (seen : Bool) (l : List (List Op)) (out : List Fmt.DeclaredRound),
    (∀ r ∈ rs, P r.entry) → H2U.layOpens own seen rs l = some out → ∀ d ∈ out, P d.entry
  | [], _, [], out, _, h => by
    cases h
    intro d hd
    cases hd
  | [], _, _ :: _, _, _, h => by cases h
  | r :: rs, seen, l, out, hr, h => by
    have h0 : P (if (own && !seen && r.entry.name == "FOLD epsilon") = true then
        { r.entry with msg := 32 + r.entry.msg, roots := 1 } else r.entry) := by
      split
      · exact hP _ (hr r List.mem_cons_self)
      · exact hr r List.mem_cons_self
    have hr' : ∀ x ∈ rs, P x.entry := fun x hx => hr x (List.mem_cons_of_mem _ hx)
    unfold H2U.layOpens at h
    dsimp only at h
    split at h
    · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact h0
      · exact lay_entries P hP own rs _ _ o' hr' h1 d hd
    · split at h
      · split at h
        · cases h
        · obtain ⟨o', h1, rfl⟩ := Option.map_eq_some_iff.1 h
          intro d hd
          rcases List.mem_cons.1 hd with rfl | hd
          · exact h0
          · exact lay_entries P hP own rs _ _ o' hr' h1 d hd
      · cases h

/-- What holds of the six kinds of rounds' entries holds of every round behind "BAT". -/
theorem later_entries (P : Fmt.Entry → Prop) (work : Nat) (S : Fmt.M1.Stage → Prop)
    (h1 : P (rEps "FOLD epsilon").entry) (h2 : P (rTwo "FOLD round").entry)
    (h3 : ∀ s, S s → P (rSeed s).entry) (h4 : ∀ s t W, S s → P (rCs work s t W).entry)
    (h5 : P rLambda.entry) (h6 : ∀ s t, S s → P (rBase work s t).entry) :
    ∀ (rest : List Fmt.M1.Stage) (old : Fmt.M1.Stage) (tree W : Nat), (∀ s ∈ old :: rest, S s) →
    ∀ r ∈ laterRounds work tree W old rest, P r.entry
  | [], old, tree, W, hS, r, hr => by
    simp only [laterRounds, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h5
    · exact h6 _ _ (hS old List.mem_cons_self)
  | new :: rest, old, tree, W, hS, r, hr => by
    simp only [laterRounds, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_replicate] at hr
    rcases hr with ((rfl | ⟨_, rfl⟩) | (rfl | rfl)) | hr
    · exact h1
    · exact h2
    · exact h3 _ (hS new (by simp))
    · exact h4 _ _ _ (hS old List.mem_cons_self)
    · exact later_entries P work S h1 h2 h3 h4 h5 h6 rest new _ _
        (fun s hs => hS s (List.mem_cons_of_mem _ hs)) r hr

/-- The same of the declared rounds. -/
theorem rounds_entries (P : Fmt.Entry → Prop)
    (hP : ∀ e : Fmt.Entry, P e → P { e with msg := 32 + e.msg, roots := 1 })
    (N : H2U.TestNums) (S : Fmt.M1.Stage → Prop) (hS : ∀ s ∈ N.stages, S s)
    (h0 : P { Fmt.M1.rBat.entry with rows := N.rows })
    (h1 : P (rEps "FOLD epsilon").entry) (h2 : P (rTwo "FOLD round").entry)
    (h3 : ∀ s, S s → P (rSeed s).entry) (h4 : ∀ s t W, S s → P (rCs N.work s t W).entry)
    (h5 : P rLambda.entry) (h6 : ∀ s t, S s → P (rBase N.work s t).entry)
    (rds : List Fmt.DeclaredRound) (h : H2U.roundsOfNums N = some rds) : ∀ d ∈ rds, P d.entry := by
  obtain ⟨s, next, rest, R, hs, hR, rfl⟩ := rounds_top N rds h
  intro d hd
  rcases List.mem_cons.1 hd with rfl | hd
  · exact h0
  · exact lay_entries P hP _ _ _ _ R
      (later_entries P N.work S h1 h2 h3 h4 h5 h6 (next :: rest) s 0 0 (hs ▸ hS)) hR d hd

theorem ok_zip (f : Fmt.DeclaredRound × Nat → String) (g : Fmt.DeclaredRound → Bool)
    (ds : List Fmt.DeclaredRound) (h : ∀ d ∈ ds, g d = true) :
    ok (ds.zipIdx.map fun x => (f x, g x.1)) = true := by
  unfold ok
  rw [List.all_map, List.all_eq_true]
  intro x hx
  rw [List.mem_zipIdx_iff_getElem?] at hx
  exact h x.1 (List.mem_of_getElem? hx)

/-- **nzOk is a theorem**: wherever the numbers give rounds. -/
theorem nzOk_made (p : P12) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds) : nzOk p = true := by
  unfold nzOk
  rw [hr, Option.any_some]
  refine ok_zip _ (fun d => decide (d.entry.drawNZ ≤ d.entry.drawE)) rds fun d hd =>
    decide_eq_true ?_
  exact rounds_entries (fun e => e.drawNZ ≤ e.drawE) (fun _ h => h) p.nums (fun _ => True)
    (fun _ _ => trivial) (by simp [Fmt.M1.rBat]) (by decide) (by decide)
    (fun s _ => by simp [rSeed]) (fun s t W _ => by simp [rCs]) (by decide)
    (fun s t _ => by simp [rBase]) rds hr d hd

/-- What sizesOk holds of each stage: of what is spent here. -/
theorem stages_of_ok (answers : Nat) : ∀ (l : List Fmt.M1.Stage) (b : Option Fmt.M1.Stage),
    stagesOk answers b l = true → ∀ s ∈ l, s.C.a ≤ 60 ∧ s.h ≤ s.k
  | [], _, _, s, hs => by cases hs
  | x :: l, b, h, s, hs => by
    unfold stagesOk at h
    simp only [Bool.and_eq_true] at h
    rcases List.mem_cons.1 hs with rfl | hs
    · have h1 := h.1.1
      unfold stageOk codeOk mostA at h1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      exact ⟨h1.1.1.1.1.1.1.1.1.1.2, h1.1.2⟩
    · exact stages_of_ok answers l _ h.2 s hs

/-- **logOk**: where the numbers give rounds and every stage's main code has a ≤ 64. -/
theorem logOk_made (p : P12) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds) (ha : ∀ s ∈ p.nums.stages, s.C.a ≤ 64) :
    logOk p = true := by
  unfold logOk
  rw [hr, Option.any_some]
  refine ok_zip _ (fun d => decide (d.entry.logN ≤ 64)) rds fun d hd => decide_eq_true ?_
  exact rounds_entries (fun e => e.logN ≤ 64) (fun _ h => h) p.nums (fun s => s.C.a ≤ 64) ha
    (by simp [Fmt.M1.rBat]) (by decide) (by decide) (fun s _ => by simp [rSeed])
    (fun s t W h => by simpa [rCs] using h) (by decide) (fun s t h => by simpa [rBase] using h)
    rds hr d hd

/-- What the frame's own test on the plan holds of the stages, whatever the parts. -/
theorem sizes_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) : ∀ s ∈ p.nums.stages, s.C.a ≤ 60 ∧ s.h ≤ s.k := by
  unfold proximityTestKind at hp
  split at hp
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have h := hp.1.1.1.1
    unfold sizesOk at h
    simp only [Bool.and_eq_true] at h
    exact stages_of_ok _ _ _ h.2
  · cases hp

/-- **The block's test on the plan holds nzOk**, whatever the parts. -/
theorem nzOk_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) : nzOk p = true := by
  obtain ⟨rds, hr, _⟩ := rounds_of_planOk X p hp
  exact nzOk_made p rds hr

/-- **The block's test on the plan holds logOk**, whatever the parts. -/
theorem logOk_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) : logOk p = true := by
  obtain ⟨rds, hr, _⟩ := rounds_of_planOk X p hp
  exact logOk_made p rds hr fun s hs => Nat.le_trans (sizes_of_planOk X p hp s hs).1 (by decide)

end H2K.Made

#print axioms H2K.Made.nzOk_made
#print axioms H2K.Made.nzOk_of_planOk
#print axioms H2K.Made.logOk_made
#print axioms H2K.Made.logOk_of_planOk
