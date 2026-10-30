-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.BeforeLater
/-
Johnson/Desc/K12/Law/BeforeSeed.lean: IN FRONT OF THE SEEDS' DRAW: every tree that a stage behind the first opens (a later switch; the base case) is sent NOT LATER THAN THE ROUND "SEND seed" OF THE STAGE BEFORE, whose message stands in front of its draw: the round "CS" behind it sends no root. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
WHY: «in front of the stage's first round» (BeforeLater.lean) admits the round "CS", which stands BEHIND the draw of the seeds.
  later_cs0 | stage_cs0: in a test's declared rounds the round number foldStart 1 stages j + s.k + 2 (stage j's "CS"; j a stage but the last) sends no root.
  foldStart_succ: foldStart 1 stages (j + 1) = foldStart 1 stages j + s.k + 3.
  sent_seed: under opened-trees' premises (BeforeK12.lean), for a stage j but the last: every tree that the switch of stage j + 1 opens (where that is a stage but the last) is SentBy … (‹the block's first› + foldStart 1 stages j + s.k + 2): its round is at most stage j's "SEND seed".
  sent_seed_base: the like for the base case.
Limits: as BeforeK12.lean's: rounds' numbers of the declared plan; trees, not words.

-/
set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Fmt.M1 (laterRounds wMid rTwo rSeed rCs)
open H2K.FixedBefore (Fixed sentIn foldStart fixed_switch fixed_base fixedOk)
open Johnson.G.OfPlan (rootsOf)

theorem stage_cs_at (e : Fmt.DeclaredRound) (k : ℕ) (two seed cs : Fmt.DeclaredRound)
    (R' : List Fmt.DeclaredRound) :
    ((e :: List.replicate k two) ++ (seed :: cs :: R'))[k + 2]? = some cs := by
  have hl : (e :: List.replicate k two).length = k + 1 := by simp
  rw [List.getElem?_append_right (by rw [hl]; omega), hl]
  have h1 : k + 2 - (k + 1) = 1 := by omega
  rw [h1]
  rfl

theorem later_cs0 (own : Bool) (work : ℕ) : ∀ (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage)
    (tree W : ℕ) (ls : List (List Op)) (R : List Fmt.DeclaredRound),
    H2U.layOpens own true (laterRounds work tree W cur rest) ls = some R →
    ∀ (j : ℕ) (s : Fmt.M1.Stage), j < rest.length → (cur :: rest)[j]? = some s →
      ∃ r, R[(((cur :: rest).take j).map (·.k + 3)).sum + (s.k + 2)]? = some r ∧
        r.entry.roots = 0
  | [], _, _, _, _, _, _, j, _, hj, _ => by simp at hj
  | new :: rest, cur, tree, W, ls, R, h, j, s, hj, hs => by
    obtain ⟨x, t, R', _, _, h', rfl⟩ := lay_stage own true work tree W cur new rest ls R h
    cases j with
    | zero =>
      obtain rfl : cur = s := by simpa using hs
      refine ⟨⟨(rCs work cur tree W).entry, [], x⟩, ?_, rfl⟩
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add]
      exact stage_cs_at _ _ _ _ _ _
    | succ j =>
      obtain ⟨r, h1, h2⟩ := later_cs0 own work rest new _ _ t R' h' j s (by simpa using hj)
        (by simpa using hs)
      refine ⟨r, ?_, h2⟩
      rw [← h1]
      have e : (((cur :: new :: rest).take (j + 1)).map (·.k + 3)).sum + (s.k + 2) =
          (((⟨epsE own true, [], []⟩ : Fmt.DeclaredRound) :: List.replicate cur.k
            (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
            [(⟨(rSeed new).entry, [], []⟩ : Fmt.DeclaredRound),
              ⟨(rCs work cur tree W).entry, [], x⟩]).length +
          ((((new :: rest).take j).map (·.k + 3)).sum + (s.k + 2)) := by
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.length_append,
          List.length_cons, List.length_replicate, List.length_nil]
        omega
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

theorem stage_cs0 (N : H2U.TestNums) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums N = some rds) (j : ℕ) (s : Fmt.M1.Stage)
    (hj : j + 1 < N.stages.length) (hs : N.stages[j]? = some s) :
    ∃ r, rds[foldStart 1 N.stages j + (s.k + 2)]? = some r ∧ r.entry.roots = 0 := by
  obtain ⟨s0, next, rest, R', hst, hR, rfl⟩ := rounds_head N rds hr
  rw [hst] at hj hs ⊢
  cases j with
  | zero =>
    obtain rfl : s0 = s := by simpa using hs
    refine ⟨⟨(rCs N.work s0 0 0).entry, [],
      N.first ++ (if N.ownMask then (told N).take 1 else [])⟩, ?_, rfl⟩
    have e : foldStart 1 (s0 :: next :: rest) 0 + (s0.k + 2) = (s0.k + 2) + 1 := by
      simp [foldStart]
      omega
    rw [e, List.getElem?_cons_succ]
    exact stage_cs_at _ _ _ _ _ _
  | succ i =>
    obtain ⟨r, g1, g2⟩ := later_cs0 N.ownMask N.work rest next _ _ _ R' hR i s (by
      simp only [List.length_cons] at hj
      omega) (by simpa using hs)
    refine ⟨r, ?_, g2⟩
    rw [← g1]
    have e : foldStart 1 (s0 :: next :: rest) (i + 1) + (s.k + 2) =
        ((⟨{ Fmt.M1.rBat.entry with rows := N.rows }, [], []⟩ : Fmt.DeclaredRound) ::
          ((⟨epsE N.ownMask false, [], []⟩ :: List.replicate s0.k
            (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
          [⟨(rSeed next).entry, [], []⟩, ⟨(rCs N.work s0 0 0).entry, [],
            N.first ++ (if N.ownMask then (told N).take 1 else [])⟩])).length +
        ((((next :: rest).take i).map (·.k + 3)).sum + (s.k + 2)) := by
      unfold foldStart
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.length_append,
        List.length_cons, List.length_replicate, List.length_nil]
      omega
    rw [e]
    have e2 : (⟨{ Fmt.M1.rBat.entry with rows := N.rows }, [], []⟩ : Fmt.DeclaredRound) ::
          ((⟨epsE N.ownMask false, [], []⟩ :: List.replicate s0.k
            (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
          (⟨(rSeed next).entry, [], []⟩ :: ⟨(rCs N.work s0 0 0).entry, [],
            N.first ++ (if N.ownMask then (told N).take 1 else [])⟩ :: R')) =
        ((⟨{ Fmt.M1.rBat.entry with rows := N.rows }, [], []⟩ : Fmt.DeclaredRound) ::
          ((⟨epsE N.ownMask false, [], []⟩ :: List.replicate s0.k
            (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
          [⟨(rSeed next).entry, [], []⟩, ⟨(rCs N.work s0 0 0).entry, [],
            N.first ++ (if N.ownMask then (told N).take 1 else [])⟩])) ++ R' := by
      simp
    rw [e2, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem foldStart_succ (l : List Fmt.M1.Stage) (j : ℕ) (s : Fmt.M1.Stage) (hs : l[j]? = some s) :
    foldStart 1 l (j + 1) = foldStart 1 l j + (s.k + 2) + 1 := by
  unfold foldStart
  rw [List.take_add_one, hs]
  simp
  omega

/-- **A later switch's trees: not later than "SEND seed" of the stage before.** -/
theorem sent_seed {S Cl : Type} (p : P12) (hfx : fixedOk p = true)
    (rds : List Fmt.DeclaredRound) (hr : H2U.roundsOfNums p.nums = some rds)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c from' : ℕ) (pre : List (Block S Cl))
    (b : Block S Cl) (post : List (Block S Cl)) (hbef : b.before = p.before)
    (hrd : b.rounds = rds) (hc : p.place.chain = c + 1)
    (h : beforeAt D O c from' (pre ++ b :: post) = true) (preR postR : List Fmt.DeclaredRound)
    (hDs : chainOf D (c + 1) = preR ++ (rds ++ postR)) (hlen : preR.length = from' + roundsIn pre)
    (hfree : p.nums.free = rootsOf preR) (j : ℕ) (s s' : Fmt.M1.Stage)
    (hs : p.nums.stages[j]? = some s) (hj : j + 1 + 1 < p.nums.stages.length)
    (hs' : p.nums.stages[j + 1]? = some s') :
    ∀ r ∈ (rds.drop (foldStart 1 p.nums.stages (j + 1) + 1 + s'.k)).take 2, ∀ o ∈ r.opens,
      SentBy D c (from' + roundsIn pre)
        (from' + roundsIn pre + (foldStart 1 p.nums.stages j + (s.k + 2))) o := by
  intro r hr' o ho
  obtain ⟨r0, g1, g2⟩ := stage_eps0 p.nums rds hr (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) hj
  obtain ⟨r1, k1, k2⟩ := stage_cs0 p.nums rds hr j s (by omega) hs
  have F1 := fixed_back _ _ _ _ _ r0 g1 g2 o (fixed_switch p hfx rds hr (j + 1) s' hj hs' r hr' o ho)
  rw [foldStart_succ _ j s hs] at F1
  exact fixed_sent p rds hr D O c from' pre b post hbef hrd hc h preR postR hDs hlen hfree _ o
    (fixed_back _ _ _ _ _ r1 k1 k2 o F1)

/-- **The base case's trees: not later than "SEND seed" of the last stage but one.** -/
theorem sent_seed_base {S Cl : Type} (p : P12) (hfx : fixedOk p = true)
    (rds : List Fmt.DeclaredRound) (hr : H2U.roundsOfNums p.nums = some rds)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c from' : ℕ) (pre : List (Block S Cl))
    (b : Block S Cl) (post : List (Block S Cl)) (hbef : b.before = p.before)
    (hrd : b.rounds = rds) (hc : p.place.chain = c + 1)
    (h : beforeAt D O c from' (pre ++ b :: post) = true) (preR postR : List Fmt.DeclaredRound)
    (hDs : chainOf D (c + 1) = preR ++ (rds ++ postR)) (hlen : preR.length = from' + roundsIn pre)
    (hfree : p.nums.free = rootsOf preR) (j : ℕ) (s : Fmt.M1.Stage)
    (hs : p.nums.stages[j]? = some s) (hlast : j + 2 = p.nums.stages.length) :
    ∀ r ∈ (rds.drop (foldStart 1 p.nums.stages (j + 1))).take 2, ∀ o ∈ r.opens,
      SentBy D c (from' + roundsIn pre)
        (from' + roundsIn pre + (foldStart 1 p.nums.stages j + (s.k + 2))) o := by
  intro r hr' o ho
  obtain ⟨r1, k1, k2⟩ := stage_cs0 p.nums rds hr j s (by omega) hs
  have e : p.nums.stages.length - 1 = j + 1 := by omega
  have F0 := fixed_base p hfx rds hr
  rw [e] at F0
  have F1 := F0 r hr' o ho
  rw [foldStart_succ _ j s hs] at F1
  exact fixed_sent p rds hr D O c from' pre b post hbef hrd hc h preR postR hDs hlen hfree _ o
    (fixed_back _ _ _ _ _ r1 k1 k2 o F1)

end H2K.Made

#print axioms H2K.Made.stage_cs0
#print axioms H2K.Made.foldStart_succ
#print axioms H2K.Made.sent_seed
#print axioms H2K.Made.sent_seed_base
