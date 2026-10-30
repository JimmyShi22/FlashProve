-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SpendMade.lean: `spendOk` is a theorem: the test on a place's rounds and sizes
of Johnson/Desc/K12/Law/SpendOk.lean says yes wherever the test on the plan of the proximity test's
block (the kind K12) does. Statements and proofs.

Why. `spendOk p` is a field of `K12Condition` (Johnson/Desc/K12/Law/ChainHolds.lean) and a premise
of what is built on it. No text that runs asks it. It reads the place alone: the stages' sizes, and
the declared rounds as written (`writtenOf`), which `H2U.roundsOfNums` makes of the place's numbers.
So nothing of `spendOk` is left to ask: the sizes are held by `sizesOk` and by guard (z)'s clause on
the plan, and what a fold's two kinds of round and the base case's first round send and draw is read
off the rounds as they are made.
How. MadeRounds.lean writes the declared rounds out, stage by stage (`lay_stage`, `lay_base`,
`rounds_top`); TieOkMade.lean has that the written rounds are there (`written_made`), the kinds of
the seven names and `layW_rep`. Here a written round is read back off `layW` without following which
shapes are left (`layW_inv`), since `sdB` reads neither a round's tree nor what it opens (`sdB_wr`).
Main names:
  `layW_inv`, `sdB_wr`: as said.
  `Sz`, `Fit`, `fit_of_ok`: what `spendOk` asks of the sizes; from `stagesOk` and C.a ≤ 32.
  `walk_spend`: the walk over the written rounds.
  `spendOk_made`: `spendOk p = true` where the numbers give declared rounds, with as many lists of
    oracle messages, the stages pass `sizesOk`, and every main code has a ≤ 32. Whatever the parts.
  `small_later`: guard (z)'s clause on the plan (Johnson/Desc/K12/JoinGuarded.lean, `ranged`) gives C.a ≤
    32 at every stage: a switch's and the base case's round of positions has that range.
  `spendOk_of_planOk`: `(proximityTestKind guardedProximityTestParts p).planOk = true` gives `spendOk p = true`.
Limits: that the block's test on the plan says yes at a real place is a run's word, not shown here.
`spendOk_of_planOk` is of the parts `guardedProximityTestParts`: `sizesOk` alone allows a ≤ 60. Nothing on soundness.
Nothing on hiding.

-/
import Johnson.Desc.K12.Law.TieOkMade
import Johnson.Desc.K12.Law.SpendOk
import Johnson.Desc.K12.JoinGuarded

set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Fmt.M1 (Stage rEps rTwo rSeed rCs rLambda rBase laterRounds wMid)
open H2K.Pub (WR layW ownOf writtenOf sdB nSB sizedL spendL spendAll spendOk)

theorem okP_app (a b : H2K.Pub.Clauses) :
    H2K.Pub.ok (a ++ b) = true ↔ H2K.Pub.ok a = true ∧ H2K.Pub.ok b = true := by
  unfold H2K.Pub.ok
  rw [List.all_append, Bool.and_eq_true]

theorem okP_tag (j : Nat) (l : H2K.Pub.Clauses) : H2K.Pub.ok (H2K.Pub.tag j l) = H2K.Pub.ok l := by
  unfold H2K.Pub.ok H2K.Pub.tag
  rw [List.all_map]
  rfl

/-- One declared round, read back off the written rounds: whichever shapes are left. -/
theorem layW_inv (r : Fmt.DeclaredRound) (kd : Fmt.Kind) (hkd : Fmt.kindOf r.entry.name = some kd)
    {rs : List Fmt.DeclaredRound} {sh : List Fmt.Shape} {l : List WR}
    (h : layW (r :: rs) sh = some l) :
    ∃ t l' sh', l = wr r kd t :: l' ∧ layW rs sh' = some l' := by
  unfold layW at h
  simp only [hkd] at h
  split at h
  · obtain ⟨l', h1, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨none, l', sh, rfl, h1⟩
  · split at h
    · split at h
      · obtain ⟨l', h1, rfl⟩ := Option.map_eq_some_iff.1 h
        exact ⟨_, l', _, rfl, h1⟩
      · cases h
    · cases h

/-- sdB reads neither the tree nor what is opened. -/
theorem sdB_wr (r : Fmt.DeclaredRound) (kd : Fmt.Kind) (t : Option Fmt.Shape) (ns ne np a : Nat) :
    sdB (wr r kd t) ns ne np a = sdB (wr ⟨r.entry, [], []⟩ kd none) ns ne np a := rfl

/-- What spendOk asks of a stage's sizes. -/
def Sz (a : Stage) : Prop :=
  a.C.a ≤ 32 ∧ a.Z.a ≤ a.C.a ∧ a.C.r + a.C.l ≤ 2 ^ a.C.a ∧ a.Z.r + a.Z.l ≤ 2 ^ a.Z.a

/-- The sizes at every stage; h ≤ k and 1 ≤ k at every stage but the last. -/
def Fit : Stage → List Stage → Prop
  | a, [] => Sz a
  | a, b :: rest => Sz a ∧ a.h ≤ a.k ∧ 1 ≤ a.k ∧ Fit b rest

theorem sized_ok {a : Stage} (h : Sz a) : H2K.Pub.ok (sizedL a) = true := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp [H2K.Pub.ok, sizedL, h1, h2, h3, h4]

/-- The walk over the written rounds. -/
theorem walk_spend (own : Bool) (work : Nat) : ∀ (rest : List Stage) (a : Stage) (seen : Bool)
    (j tree W : Nat) (ls : List (List Op)) (R : List Fmt.DeclaredRound) (sh : List Fmt.Shape)
    (l : List WR), (rest = [] → seen = true) →
    H2U.layOpens own seen (laterRounds work tree W a rest) ls = some R → layW R sh = some l →
    Fit a rest → H2K.Pub.ok (spendL j a rest l) = true
  | [], a, seen, j, tree, W, ls, R, sh, l, hs, h, hl, hF => by
    obtain rfl := hs rfl
    obtain ⟨x, _, _, rfl⟩ := lay_base own work tree W a ls R h
    obtain ⟨t1, l1, sh1, rfl, hl1⟩ := layW_inv _ .elems kLam hl
    obtain ⟨t2, l2, sh2, rfl, hl2⟩ := layW_inv _ .positions kBase hl1
    have hn : l2 = [] := by
      unfold layW at hl2
      cases sh2 with
      | nil => exact (Option.some.inj hl2).symm
      | cons _ _ => cases hl2
    subst hn
    unfold spendL
    rw [okP_tag]
    have hL : sdB (wr ⟨rLambda.entry, [], []⟩ .elems t1) 1 1 0 0 = true := by
      rw [sdB_wr]
      decide
    have := sized_ok hF
    simp only [H2K.Pub.ok, List.all_cons, hL, Bool.true_and] at this ⊢
    exact this
  | b :: rest, a, seen, j, tree, W, ls, R, sh, l, _, h, hl, hF => by
    obtain ⟨hz, hk, h1k, hF'⟩ := hF
    obtain ⟨x, t, R', _, _, h', rfl⟩ := lay_stage own seen work tree W a b rest ls R h
    rw [List.cons_append] at hl
    obtain ⟨t1, l1, sh1, rfl, hl1⟩ := layW_inv _ .join (by rw [epsE_name]; exact kEps) hl
    rw [layW_rep _ .elems kTwo rfl] at hl1
    obtain ⟨l2, hl2, rfl⟩ := Option.map_eq_some_iff.1 hl1
    obtain ⟨t3, l3, sh3, rfl, hl3⟩ := layW_inv _ .seeds kSeed hl2
    obtain ⟨t4, l4, sh4, rfl, hl4⟩ := layW_inv _ .positions kCs hl3
    obtain ⟨n, hn⟩ : ∃ n, a.k = n + 1 := ⟨a.k - 1, by omega⟩
    have hkk : H2K.Pub.kk a = n + 1 := by
      unfold H2K.Pub.kk
      omega
    rw [hn, List.replicate_succ, List.cons_append]
    unfold spendL
    have hd : ∀ (wT wS wC : WR), (wT :: (List.replicate n wT ++ wS :: wC :: l4)).drop
        (H2K.Pub.kk a) = wS :: wC :: l4 := by
      intro wT wS wC
      rw [hkk, ← List.cons_append, ← List.replicate_succ]
      exact List.drop_left' (by simp)
    simp only [hd]
    rw [okP_app, okP_tag]
    refine ⟨?_, walk_spend own work rest b true (j + 1) (tree + 1) (wMid b) t R' sh4 l4
      (fun _ => rfl) h' hl4 hF'⟩
    have hE : sdB (wr ⟨epsE own seen, [], []⟩ .join t1) 1 1 0 0 = true := by
      rw [sdB_wr]
      cases own <;> cases seen <;> decide
    have hT : sdB (wr ⟨(rTwo "FOLD round").entry, [], []⟩ .elems none) 2 1 0 0 = true := by decide
    have := sized_ok hz
    simp only [H2K.Pub.ok, List.all_cons, hE, hT, Bool.true_and] at this ⊢
    exact this

/-- What sizesOk holds of the stages, of what is spent here. -/
theorem fit_of_ok (answers : Nat) : ∀ (rest : List Stage) (a : Stage) (b : Option Stage),
    stagesOk answers b (a :: rest) = true → (∀ s ∈ a :: rest, s.C.a ≤ 32) → Fit a rest
  | rest, a, b, h, h32 => by
    unfold stagesOk at h
    simp only [Bool.and_eq_true] at h
    have h1 := h.1.1
    unfold stageOk codeOk at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hC⟩, ⟨_, hZ⟩⟩, _⟩, _⟩, hza⟩, _⟩, hhk⟩, hlast⟩ := h1
    have hz : Sz a := by
      refine ⟨h32 a List.mem_cons_self, hza, ?_, ?_⟩
      · have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.min_le_left a.C.a 32)
        omega
      · have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.min_le_left a.Z.a 32)
        omega
    cases rest with
    | nil => exact hz
    | cons c rest =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, Bool.and_eq_true,
        decide_eq_true_eq] at hlast
      exact ⟨hz, hhk, hlast.1, fit_of_ok answers rest c _ h.2
        (fun s hs => h32 s (List.mem_cons_of_mem _ hs))⟩

/-- **spendOk is a theorem**: at a place whose numbers give declared rounds, with as many lists of
oracle messages, whose stages pass sizesOk and have main codes of length at most 2 ^ 32. -/
theorem spendOk_made (p : P12) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds) (hlen : p.oracles.length = rds.length)
    (hz : sizesOk p.nums.stages p.answers = true) (h32 : ∀ s ∈ p.nums.stages, s.C.a ≤ 32) :
    spendOk p = true := by
  unfold sizesOk at hz
  simp only [Bool.and_eq_true] at hz
  obtain ⟨a, rest, w0, w, hs, hw, _⟩ := written_made p rds hr hlen
    (fun s hs => (stages_of_ok _ _ _ hz.2 s hs).2)
  obtain ⟨s, next, rest', R, hs', hR, rfl⟩ := rounds_top p.nums rds hr
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hs.symm.trans hs')
  have hw' := hw
  unfold writtenOf at hw'
  rw [hr, Option.bind_some] at hw'
  obtain ⟨t0, l0, sh0, e0, hl0⟩ := layW_inv _ .elems kBat hw'
  obtain ⟨_, rfl⟩ := List.cons.inj e0
  unfold spendOk spendAll
  rw [hs, hw]
  exact walk_spend _ _ _ _ false 0 0 0 _ R sh0 w (fun h => by cases h) hR hl0
    (fit_of_ok _ _ _ _ (by rw [← hs]; exact hz.2) (by rw [← hs]; exact h32))

/-- Guard (z)'s clause on the plan, at every stage: the round of positions of a switch or of the
base case has the stage's C.a as its range. -/
theorem small_later {Cl : Type} (p : P12) (own : Bool) (work : Nat) : ∀ (rest : List Stage)
    (cur : Stage) (seen : Bool) (j tree W : Nat) (l : Laid) (R : List Fmt.DeclaredRound)
    (ls : List (List Op)), (rest = [] → seen = true) →
    H2U.layOpens own seen (laterRounds work tree W cur rest) ls = some R → l.map (·.1) = R →
    (stagesFrom guardedProximityTestParts p j cur rest l : Block T12 Cl).planOk = true →
    ∀ s ∈ cur :: rest, s.C.a ≤ 32
  | [], cur, seen, j, tree, W, l, R, ls, hs, h, hl, hp => by
    obtain rfl := hs rfl
    obtain ⟨x, _, _, rfl⟩ := lay_base own work tree W cur ls R h
    unfold stagesFrom at hp
    simp only [Part.at, guardedProximityTestParts, ranged, Bool.and_eq_true, hl] at hp
    have h2 := hp.2
    simp [rBase] at h2
    intro s hs'
    obtain rfl := List.mem_singleton.1 hs'
    exact h2.2
  | nxt :: rest, cur, seen, j, tree, W, l, R, ls, _, h, hl, hp => by
    obtain ⟨x, t, R', _, _, h', rfl⟩ := lay_stage own seen work tree W cur nxt rest ls R h
    obtain ⟨_, c2, c3⟩ := cuts l _ _ _ R' cur.k (by simp [Nat.add_comm]) hl
    unfold stagesFrom at hp
    simp only [Block.andThen, Part.at, asks, guardedProximityTestParts, ranged, Bool.and_eq_true, c2] at hp
    have h2 := hp.1.1.1.2.2
    simp [rCs] at h2
    intro s hs'
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact h2.2
    · exact small_later p own work rest nxt true (j + 1) (tree + 1) (wMid nxt) _ R' t
        (fun _ => rfl) h' c3 hp.2 s hs'

/-- **The block's test on the plan holds spendOk.** At the parts guardedProximityTestParts: its guard (z) holds
C.a ≤ 32; the rest is the frame's own test, whatever the parts. -/
theorem spendOk_of_planOk {Cl : Type} (p : P12)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Cl).planOk = true) : spendOk p = true := by
  obtain ⟨rds, hr, hlen⟩ := rounds_of_planOk guardedProximityTestParts p hp
  obtain ⟨s, next, rest, R, hs, hR, rfl⟩ := rounds_top p.nums rds hr
  have hp' := hp
  unfold proximityTestKind at hp'
  split at hp'
  · rename_i first rest' rs os h1 h2 h3
    obtain rfl := Option.some.inj (h2.symm.trans hr)
    obtain ⟨rfl, rfl⟩ := List.cons.inj (h1.symm.trans hs)
    simp only [Block.andThen, Bool.and_eq_true] at hp'
    refine spendOk_made p _ hr hlen hp'.1.1.1.1 ?_
    rw [hs]
    refine small_later p _ _ _ _ false 0 0 0 _ R _ (fun h => by cases h) hR ?_ hp'.2.2
    rw [List.map_drop, List.map_fst_zip (Nat.le_of_eq hlen.symm)]
    rfl
  · cases hp'

end H2K.Made

#print axioms H2K.Made.spendOk_made
#print axioms H2K.Made.spendOk_of_planOk
