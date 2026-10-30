-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.BeforeK12
/-
Johnson/Desc/K12/Law/BeforeLater.lean: THE SHARPER BOUND AT THE LATER STAGES: every tree that a switch behind the first opens is sent in front of THAT STAGE's FIRST ROUND (not only in front of the round behind it): a later fold's first round sends no root. It reads no JoinP5. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  later_eps0: in the rounds laid for the stages behind the first "FOLD epsilon", the first round of each stage but the last sends no root.
  stage_eps0: in a test's declared rounds, the round number foldStart 1 stages j sends no root, for 1 ≤ j, j a stage but the last.
  fixed_back: «Fixed … (start + 1) o» is «Fixed … start o» where the round number start sends no root.
  masks_fixed_later: under opened_sent's premises, for 1 ≤ j: SentBy … (‹the block's first› + foldStart 1 stages j) o: STRICTLY IN FRONT OF THE STAGE's FIRST ROUND. (That is, BY READING, what the library's premise «a word fixed before the block» wants of a later stage's tree; THE BRIDGE from the declared rounds' numbers to the typed chain's letters IS NOT SHOWN HERE.)
Limits: as BeforeK12.lean's. At j = 0 the bound of opened_sent cannot be sharpened so: the first fold's own mask's tree is sent in that fold's first round.

-/
set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Fmt.M1 (laterRounds wMid rTwo rSeed rCs)
open H2K.FixedBefore (Fixed sentIn foldStart fixed_switch fixedOk)
open Johnson.G.OfPlan (rootsOf)

theorem later_eps0 (own : Bool) (work : ℕ) : ∀ (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage)
    (tree W : ℕ) (ls : List (List Op)) (R : List Fmt.DeclaredRound),
    H2U.layOpens own true (laterRounds work tree W cur rest) ls = some R →
    ∀ j, j < rest.length →
      ∃ r, R[(((cur :: rest).take j).map (·.k + 3)).sum]? = some r ∧ r.entry.roots = 0
  | [], _, _, _, _, _, _, j, hj => by simp at hj
  | new :: rest, cur, tree, W, ls, R, h, j, hj => by
    obtain ⟨x, t, R', _, _, h', rfl⟩ := lay_stage own true work tree W cur new rest ls R h
    cases j with
    | zero =>
      refine ⟨⟨epsE own true, [], []⟩, by simp, ?_⟩
      rw [epsE_roots]
      simp
    | succ j =>
      obtain ⟨r, h1, h2⟩ := later_eps0 own work rest new _ _ t R' h' j (by simpa using hj)
      refine ⟨r, ?_, h2⟩
      rw [← h1]
      have e : (((cur :: new :: rest).take (j + 1)).map (·.k + 3)).sum =
          (((⟨epsE own true, [], []⟩ : Fmt.DeclaredRound) :: List.replicate cur.k
            (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
            [(⟨(rSeed new).entry, [], []⟩ : Fmt.DeclaredRound),
              ⟨(rCs work cur tree W).entry, [], x⟩]).length +
          (((new :: rest).take j).map (·.k + 3)).sum := by
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.length_append,
          List.length_cons, List.length_replicate, List.length_nil]
      rw [e]
      have e2 : ((⟨epsE own true, [], []⟩ : Fmt.DeclaredRound) :: List.replicate cur.k
            (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
          (⟨(rSeed new).entry, [], []⟩ :: ⟨(rCs work cur tree W).entry, [], x⟩ :: R') =
          (((⟨epsE own true, [], []⟩ : Fmt.DeclaredRound) :: List.replicate cur.k
            (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
            [(⟨(rSeed new).entry, [], []⟩ : Fmt.DeclaredRound),
              ⟨(rCs work cur tree W).entry, [], x⟩]) ++ R' := by
        simp
      rw [e2, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem stage_eps0 (N : H2U.TestNums) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums N = some rds) (j : ℕ) (h1 : 1 ≤ j) (hj : j + 1 < N.stages.length) :
    ∃ r, rds[foldStart 1 N.stages j]? = some r ∧ r.entry.roots = 0 := by
  obtain ⟨s, next, rest, R', hs, hR, rfl⟩ := rounds_head N rds hr
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h1
  rw [hs] at hj ⊢
  obtain ⟨r, g1, g2⟩ := later_eps0 N.ownMask N.work rest next _ _ _ R' hR i (by
    simp only [List.length_cons] at hj
    omega)
  refine ⟨r, ?_, g2⟩
  rw [← g1]
  have e : foldStart 1 (s :: next :: rest) (1 + i) =
      ((⟨{ Fmt.M1.rBat.entry with rows := N.rows }, [], []⟩ : Fmt.DeclaredRound) ::
        ((⟨epsE N.ownMask false, [], []⟩ :: List.replicate s.k
          (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
        [⟨(rSeed next).entry, [], []⟩, ⟨(rCs N.work s 0 0).entry, [],
          N.first ++ (if N.ownMask then (told N).take 1 else [])⟩])).length +
      (((next :: rest).take i).map (·.k + 3)).sum := by
    unfold foldStart
    rw [Nat.add_comm 1 i]
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.length_append,
      List.length_cons, List.length_replicate, List.length_nil]
    omega
  rw [e]
  have e2 : (⟨{ Fmt.M1.rBat.entry with rows := N.rows }, [], []⟩ : Fmt.DeclaredRound) ::
        ((⟨epsE N.ownMask false, [], []⟩ :: List.replicate s.k
          (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
        (⟨(rSeed next).entry, [], []⟩ :: ⟨(rCs N.work s 0 0).entry, [],
          N.first ++ (if N.ownMask then (told N).take 1 else [])⟩ :: R')) =
      ((⟨{ Fmt.M1.rBat.entry with rows := N.rows }, [], []⟩ : Fmt.DeclaredRound) ::
        ((⟨epsE N.ownMask false, [], []⟩ :: List.replicate s.k
          (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
        [⟨(rSeed next).entry, [], []⟩, ⟨(rCs N.work s 0 0).entry, [],
          N.first ++ (if N.ownMask then (told N).take 1 else [])⟩])) ++ R' := by
    simp
  rw [e2, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem fixed_back (chain : ℕ) (before : List (ℕ × ℕ)) (N : H2U.TestNums)
    (rds : List Fmt.DeclaredRound) (start : ℕ) (r : Fmt.DeclaredRound) (h1 : rds[start]? = some r)
    (h0 : r.entry.roots = 0) (o : Fmt.Shape × Fmt.TreeSource)
    (hF : Fixed chain before N rds (start + 1) o) : Fixed chain before N rds start o := by
  have e : sentIn N rds (start + 1) = sentIn N rds start := by
    unfold sentIn
    rw [List.take_add_one, h1]
    simp [h0]
  unfold Fixed at hF ⊢
  rw [e] at hF
  exact hF

/-- **At a later stage: strictly in front of the stage's first round.** -/
theorem masks_fixed_later {S Cl : Type} (p : P12) (hfx : fixedOk p = true)
    (rds : List Fmt.DeclaredRound) (hr : H2U.roundsOfNums p.nums = some rds)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c from' : ℕ) (pre : List (Block S Cl))
    (b : Block S Cl) (post : List (Block S Cl)) (hbef : b.before = p.before)
    (hrd : b.rounds = rds) (hc : p.place.chain = c + 1)
    (h : beforeAt D O c from' (pre ++ b :: post) = true) (preR postR : List Fmt.DeclaredRound)
    (hDs : chainOf D (c + 1) = preR ++ (rds ++ postR)) (hlen : preR.length = from' + roundsIn pre)
    (hfree : p.nums.free = rootsOf preR) (j : ℕ) (s : Fmt.M1.Stage) (h1 : 1 ≤ j)
    (hj : j + 1 < p.nums.stages.length) (hs : p.nums.stages[j]? = some s) :
    ∀ r ∈ (rds.drop (foldStart 1 p.nums.stages j + 1 + s.k)).take 2, ∀ o ∈ r.opens,
      SentBy D c (from' + roundsIn pre) (from' + roundsIn pre + foldStart 1 p.nums.stages j) o := by
  intro r hr' o ho
  obtain ⟨r0, g1, g2⟩ := stage_eps0 p.nums rds hr j h1 hj
  exact fixed_sent p rds hr D O c from' pre b post hbef hrd hc h preR postR hDs hlen hfree _ o
    (fixed_back _ _ _ _ _ r0 g1 g2 o (fixed_switch p hfx rds hr j s hj hs r hr' o ho))

end H2K.Made

#print axioms H2K.Made.stage_eps0
#print axioms H2K.Made.masks_fixed_later
