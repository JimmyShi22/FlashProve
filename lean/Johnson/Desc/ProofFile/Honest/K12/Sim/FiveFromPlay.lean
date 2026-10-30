-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FiveFromPlay.lean

What it proves. The five clauses le, leS, heardFit, heard, fold of OnFree (Sim/ExactFree.lean) and
OnFreeT (Sim/TreesExact.lean), which are one text in both, where the frame's own play of a proximity
test's first part ends: as five conjuncts in these structures' own letters. No simulators' job, no
list of trees and nothing at the test's entry is asked: so a caller lays OnFree or OnFreeT by its
constructor from these five and its own door, asks and tree or trees.

Names.
  five_of_play   Agree is a premise.
  five_of_lent   at the values that the frame lends: Agree is paid.

By what. first_played (Sim/PlayedFirst.lean); take_behind, drop_behind (Sim/OnFromPlay.lean);
agree_of_ties (AgreeBook.lean); agree_carried (Sim/OnFromLent.lean); the frame's authors'
play_opened (Honest/Gap.lean).

Limits.
- The two proofs are further texts of the proofs of onFree_of_play and onFree_of_lent: that part of
  them which makes the five, line for line. The five do not follow from these theorems' arrows: what
  they ask at the entry cannot be had for nothing.
- Asked: FirstTies; h ≤ k at the first stage; the first part's challenges have the declared form;
  "what is shown in front is what the run has shown"; and Agree, or in its place: the lending
  returns, tiesB (a test with code on the book's entries), and "the first stage's message reads of
  the members' stretches those of the job's members alone".
- Where the first fold's fresh table has come earlier (fresh = some f) alone, in five_of_lent.
- It pays none of door, asks, tree or trees. At a state on entry that is the job's own letter rec₀,
  not shown to be the verifier's. Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.OnFromLent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {V W X : Type}

/-- **The five clauses le, leS, heardFit, heard, fold of OnFree and OnFreeT, where the play of the
first part ends**: in these structures' own letters, as five conjuncts; no simulators' job, no list
of trees, nothing at the entry is asked. The premises are onFree_of_play's (Sim/OnFromPlay.lean)
less E; the proof is that proof's part on the five. -/
theorem five_of_play (J : TestJob W X) (mem : ℕ → Stretch) (name : String) (ad : Addr)
    (v : Option V) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (m₀ : Mid W X)
    (D : ℕ → Fmt.Drawn) (ds : List Fmt.Drawn) (T : FirstTies J s next rest D ds)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (c : (firstPart J : Part V W X).Coins)
    (hfit : drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1)) ds = true)
    (Ag : Agree J m₀.st.input (frontBy m₀ 0) s (firstRd J c) (carriedCoins J mem))
    (front : Before) :
    ∃ y, play ((firstPart J : Part V W X).steps name ad (J.laid.take (firstLen J.p.nums.stages)) v
        c) ds [] m₀ = .ok y ∧ y.2.st.input = m₀.st.input ∧
      (y.2.seen = front.seen →
        firstLen J.p.nums.stages ≤ y.2.st.heard.length ∧
        firstLen J.p.nums.stages ≤ y.2.seen.length ∧
        drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
          (y.2.st.lately (firstLen J.p.nums.stages)) = true ∧
        (lastSeen front (firstLen J.p.nums.stages)).map (·.drawn) =
          y.2.st.lately (firstLen J.p.nums.stages) ∧
        (lastSeen front (firstLen J.p.nums.stages)).tail =
          aFold (coinsOf J.p.nums.stages (carriedCoins J mem).hide fun _ => 0) 0 J.s₀ 1
            (rowsAt J mem y.2)
            (rowOf (J.recB y.2.st.input (restFront J y.2) (heardIn J y.2 0))) (heardIn J y.2)) := by
  obtain ⟨y, hy, h1, h2, -⟩ := first_played J name ad v s next rest m₀ D ds T hk c
  refine ⟨y, hy, by rw [h1], fun hseen => ?_⟩
  have hn : firstLen J.p.nums.stages = 2 + s.k := by rw [T.stages]; rfl
  have hs0 : J.s₀ = s := by unfold TestJob.s₀; rw [T.stages]; rfl
  have hlenA : ((⟨[], D 0⟩ : Fmt.RoundView) ::
      aFold (coinsOf (s :: next :: rest) (firstRd J c).hide (firstRd J c).rest) 0 s 1
        (J.first m₀.st.input (frontBy m₀ 0) (firstRd J c))
        (rowOf (J.recB m₀.st.input (frontBy m₀ 0) (D 0))) D).length =
      firstLen J.p.nums.stages := by
    rw [List.length_cons, length_aFold, hn, hk]
    omega
  have hin : y.2.st.input = m₀.st.input := by rw [h1]
  have hheard : y.2.st.heard = m₀.st.heard ++ ds := by rw [h1]
  have hown : y.2.st.own = m₀.st.own := by rw [h1]
  -- the front as the second part's moves lay it is the entry's
  have hop : y.2.opened = m₀.opened := ProofFile.Honest.play_opened _ _ _ _ _ hy
  have hfr : restFront J y.2 = frontBy m₀ 0 := by
    unfold restFront
    rw [frontBy_zero]
    simp only [frontOf, Mid.shown, Seen.front, hheard, hown, h2, hop, take_behind _ _ _ T.len,
      take_behind _ _ _ hlenA] <;> rfl
  have hlat : y.2.st.lately (firstLen J.p.nums.stages) = ds := by
    unfold State.lately
    rw [hheard, drop_behind _ _ _ T.len]
  have hD : ∀ i, i < firstLen J.p.nums.stages → heardIn J y.2 i = D i := fun i hi => by
    unfold heardIn
    rw [hlat, List.getD_eq_getElem _ _ (by rw [T.len]; exact hi)]
    exact T.own i _
  have hlast : lastSeen front (firstLen J.p.nums.stages) = ⟨[], D 0⟩ ::
      aFold (coinsOf (s :: next :: rest) (firstRd J c).hide (firstRd J c).rest) 0 s 1
        (J.first m₀.st.input (frontBy m₀ 0) (firstRd J c))
        (rowOf (J.recB m₀.st.input (frontBy m₀ 0) (D 0))) D := by
    unfold lastSeen
    rw [← hseen, h2, drop_behind _ _ _ hlenA]
  refine ⟨by rw [hheard, List.length_append, T.len]; omega,
    by rw [h2, List.length_append, hlenA]; omega, by rw [hlat]; exact hfit, ?_, ?_⟩
  · -- the challenges that the shown rounds bear are those heard
    rw [hlast, hlat, List.map_cons]
    show D 0 :: (foldShown (sgOf s) _ _ _ fun n => D (1 + n)).map (·.drawn) = ds
    rw [foldShown_drawn]
    refine List.ext_getElem (by simp [T.len, hn, hk]; omega) fun i h3 h4 => ?_
    rw [T.own i h4]
    cases i with
    | zero => rfl
    | succ j => simp [Nat.add_comm]
  · rw [hlast, List.tail_cons]
    unfold rowsAt
    rw [hin, hfr, hD 0 (by rw [hn]; omega), hs0, T.stages]
    refine (aFold_coins (coinsOf (s :: next :: rest) (firstRd J c).hide (firstRd J c).rest)
      (coinsOf (s :: next :: rest) (carriedCoins J mem).hide fun _ => 0) 0 s 1 _ _ _ D Ag.hide
      Ag.table).trans ?_
    exact aFold_congr _ _ _ _ _ _ _ _ fun n hn' => (hD n (by rw [hn, hk]; omega)).symm

/-- **The five at the values that the frame lends**: Agree is paid by agree_of_ties (AgreeBook.lean)
and agree_carried (Sim/OnFromLent.lean), from the lending's return, a test with code on the book's
entries (tiesB) and a clause on the job's text (hrows). The premises are onFree_of_lent's
(Sim/OnFromLent.lean) less E. -/
theorem five_of_lent (J : TestJob W X) (f : Addr × ℕ) (hfr : J.fresh = some f) (Bk : ProverCoinCounts)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart J : Part V W X), restPart J])
    (hl : lendRow Bk rows look J.p.place [(firstPart J : Part V W X), restPart J] 0 = .ok c)
    (hT : tiesB Bk J.p.place J.members.length = true) (name : String) (ad : Addr) (v : Option V)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (m₀ : Mid W X) (D : ℕ → Fmt.Drawn)
    (ds : List Fmt.Drawn) (T : FirstTies J s next rest D ds)
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < J.members.length → mem t = mem' t) →
      μOf (sgOf s) (J.rows₀ m₀.st.input (frontBy m₀ 0) mem) =
        μOf (sgOf s) (J.rows₀ m₀.st.input (frontBy m₀ 0) mem'))
    (hfit : drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1)) ds = true)
    (front : Before) :
    ∃ y, play ((firstPart J : Part V W X).steps name ad (J.laid.take (firstLen J.p.nums.stages)) v
        c.1) ds [] m₀ = .ok y ∧ y.2.st.input = m₀.st.input ∧
      (y.2.seen = front.seen →
        firstLen J.p.nums.stages ≤ y.2.st.heard.length ∧
        firstLen J.p.nums.stages ≤ y.2.seen.length ∧
        drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
          (y.2.st.lately (firstLen J.p.nums.stages)) = true ∧
        (lastSeen front (firstLen J.p.nums.stages)).map (·.drawn) =
          y.2.st.lately (firstLen J.p.nums.stages) ∧
        (lastSeen front (firstLen J.p.nums.stages)).tail =
          aFold (coinsOf J.p.nums.stages (carriedCoins J (stretches _ c.2.1.2.2)).hide fun _ => 0) 0
            J.s₀ 1
            (rowsAt J (stretches _ c.2.1.2.2) y.2)
            (rowOf (J.recB y.2.st.input (restFront J y.2) (heardIn J y.2 0))) (heardIn J y.2)) := by
  obtain ⟨p, ms, fresh, r, ro, tr⟩ := J
  obtain rfl : fresh = some f := hfr
  have hs0 : (⟨p, ms, some f, r, ro, tr⟩ : TestJob W X).s₀ = s := by
    have := T.stages
    show p.nums.stages.headD default = s
    rw [show p.nums.stages = s :: next :: rest from this]
    rfl
  have Ag := agree_of_ties p ms f r ro tr Bk rows look c hl m₀.st.input (frontBy m₀ 0) hT
    (by rw [hs0]; exact hk) (by rw [hs0]; exact hrows)
  rw [hs0] at Ag
  exact five_of_play _ _ name ad v s next rest m₀ D ds T hk c.1 hfit
    (agree_carried _ _ _ _ _ c.2.1 Ag) front

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.five_of_play
#print axioms ProofFile.Honest.K12.five_of_lent
