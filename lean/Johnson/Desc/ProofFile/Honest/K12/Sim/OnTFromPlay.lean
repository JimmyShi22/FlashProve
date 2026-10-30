-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/OnTFromPlay.lean

What it proves. Five of the eight clauses of OnFreeT (Sim/TreesExact.lean: the condition at the
second part's entry where the first round of positions opens a list of trees) follow from the
frame's own play of the first part: le, leS, heardFit, heard, fold. The three that are left, door,
asks and trees, are asked at the test's entry (AtEntryT). It is Sim/OnFromPlay.lean and
Sim/OnFromLent.lean at a list of first trees: OnFree and OnFreeT are one text in six clauses, these
five and door.

Names.
  AtEntryT          the three, at the entry's letters.
  onFreeT_of_play   where the play of the first part ends; Agree is a premise.
  onFreeT_of_lent   at the values that the frame lends: Agree is paid.

By what. first_played (Sim/PlayedFirst.lean); take_behind, drop_behind (Sim/OnFromPlay.lean);
shapeAsks_congr, dataAsks_congr (Sim/PlanCausal.lean); agree_of_ties (AgreeBook.lean); agree_carried
(Sim/OnFromLent.lean); the frame's authors' play_opened (Honest/Gap.lean).

Limits.
- At a state on entry that is the job's own letter rec₀, not shown to be the verifier's.
- The two proofs are second texts of the proofs of onFree_of_play and onFree_of_lent: line for line,
  but for the clause trees, which is handed through. A lemma that both call would turn these files.
- Asked: FirstTies; h ≤ k at the first stage; the first part's challenges have the declared form;
  "what is shown in front is what the run has shown"; and Agree, or in its place: the lending
  returns, tiesB (a test with code on the book's entries), and "the first stage's message reads of
  the members' stretches those of the job's members alone".
- Where the first fold's fresh table has come earlier (fresh = some f) alone, in onFreeT_of_lent.
- Whether a run meets AtEntryT at any place of a file is not shown here. No member is given by name.
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.OnFromLent
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {V W X Pb : Type}

/-- **The three clauses of OnFreeT that are left, at the entry's letters**: AtEntry
(Sim/OnFromPlay.lean) at a list of first trees. w: the input. fr: the front as the first part's
moves lay it. D: the challenges by the round's number in the test. door, asks, trees: OnFreeT's
clauses of these names (Sim/TreesExact.lean), at w for m.st.input, fr for restFront J m, D for
heardIn J m, and J.first w fr (carriedCoins J mem) for rowsAt J mem m. -/
structure AtEntryT (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (pb : Pb) (mem : ℕ → Stretch) (w : W) (fr : Front X)
    (D : ℕ → Fmt.Drawn) (front : Before) : Prop where
  door : J.rec₀ w fr = Js.rec₀ pb (front.cut (firstLen J.p.nums.stages))
  asks : ∃ Dp cc R, Dp.ts.length = os.length ∧ ShapeAsks J w fr (carriedCoins J mem) D K Dp ∧
    DataAsks J w fr (carriedCoins J mem) D Dp cc R
  trees : (J.trees₀ w fr mem (J.first w fr (carriedCoins J mem))).map (·.1) = os.map (·.1.a) ∧
    ∀ (i : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (T : Tree), os[i]? = some o →
      (J.trees₀ w fr mem (J.first w fr (carriedCoins J mem)))[i]? = some T →
      ∃ cols, front.treeCols (srcOf chain o.2).1 (srcOf chain o.2).2 = some cols ∧
        ∀ q ∈ cols, q.2 = T.2 q.1

/-- **Where the play of the first part ends, OnFreeT follows from the three**: onFree_of_play
(Sim/OnFromPlay.lean) at a list of first trees: the same premises, the same proof in the five
clauses le, leS, heardFit, heard, fold; door, asks and trees are handed through. -/
theorem onFreeT_of_play (J : TestJob W X) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (pb : Pb) (mem : ℕ → Stretch) (name : String) (ad : Addr)
    (v : Option V) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (m₀ : Mid W X)
    (D : ℕ → Fmt.Drawn) (ds : List Fmt.Drawn) (T : FirstTies J s next rest D ds)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (c : (firstPart J : Part V W X).Coins)
    (hfit : drawsFit (((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1)) ds = true)
    (Ag : Agree J m₀.st.input (frontBy m₀ 0) s (firstRd J c) (carriedCoins J mem))
    (front : Before)
    (E : AtEntryT J Js K chain os pb mem m₀.st.input (frontBy m₀ 0) D front) :
    ∃ y, play ((firstPart J : Part V W X).steps name ad (J.laid.take (firstLen J.p.nums.stages)) v
        c) ds [] m₀ = .ok y ∧ y.2.st.input = m₀.st.input ∧
      (y.2.seen = front.seen → OnFreeT J Js K chain os pb mem y.2 front) := by
  obtain ⟨y, hy, h1, h2, -⟩ := first_played J name ad v s next rest m₀ D ds T hk c
  refine ⟨y, hy, by rw [h1], fun hseen => ?_⟩
  have hn : firstLen J.p.nums.stages = 2 + s.k := by rw [T.stages]; rfl
  have hs0 : J.s₀ = s := by unfold TestJob.s₀; rw [T.stages]; rfl
  have hA : stA J.p = s := by unfold stA; rw [T.stages]; rfl
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
  have hag : ∀ n, n < 1 + (1 + ((sgOf (stA J.p)).h + (sgOf (stA J.p)).g)) →
      D n = heardIn J y.2 n := fun n hn' => by
    rw [hA] at hn'
    exact (hD n (by rw [hn, hk]; omega)).symm
  obtain ⟨Dp, cc, R, hT, Sh, Dt⟩ := E.asks
  refine
    { le := by rw [hheard, List.length_append, T.len]; omega
      leS := by rw [h2, List.length_append, hlenA]; omega
      heardFit := by rw [hlat]; exact hfit
      heard := ?_
      door := by rw [hin, hfr]; exact E.door
      fold := ?_
      asks := ⟨Dp, cc, R, hT, by rw [hin, hfr]; exact shapeAsks_congr J _ _ _ D _ hag Sh,
        by rw [hin, hfr]; exact dataAsks_congr J _ _ _ D _ hag Dt⟩
      trees := by unfold rowsAt; rw [hin, hfr]; exact E.trees }
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

/-- **At the values that the frame lends**: onFree_of_lent (Sim/OnFromLent.lean) at a list of first
trees: Agree is paid by agree_of_ties (AgreeBook.lean) and agree_carried (Sim/OnFromLent.lean), from
the lending's return, a test with code on the book's entries (tiesB) and a clause on the job's text
(hrows). -/
theorem onFreeT_of_lent (p : P12) (ms : List (Addr × ℕ × Due)) (f : Addr × ℕ)
    (r : W → Front X → T12) (ro : W → Front X → (ℕ → Stretch) → PS)
    (tr : W → Front X → (ℕ → Stretch) → PS → List Tree) (Js : SimJob Pb) (K : Codes) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (pb : Pb) (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d)
    (c : RowCoins [(firstPart ⟨p, ms, some f, r, ro, tr⟩ : Part V W X),
      restPart ⟨p, ms, some f, r, ro, tr⟩])
    (hl : lendRow Bk rows look p.place [(firstPart ⟨p, ms, some f, r, ro, tr⟩ : Part V W X),
      restPart ⟨p, ms, some f, r, ro, tr⟩] 0 = .ok c)
    (hT : tiesB Bk p.place ms.length = true) (name : String) (ad : Addr) (v : Option V)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (m₀ : Mid W X) (D : ℕ → Fmt.Drawn)
    (ds : List Fmt.Drawn)
    (T : FirstTies (⟨p, ms, some f, r, ro, tr⟩ : TestJob W X) s next rest D ds)
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hrows : ∀ mem mem' : ℕ → Stretch, (∀ t, t < ms.length → mem t = mem' t) →
      μOf (sgOf s) (ro m₀.st.input (frontBy m₀ 0) mem) =
        μOf (sgOf s) (ro m₀.st.input (frontBy m₀ 0) mem'))
    (hfit : drawsFit (((laidOf p).take (firstLen p.nums.stages)).map (·.1)) ds = true)
    (front : Before)
    (E : AtEntryT (⟨p, ms, some f, r, ro, tr⟩ : TestJob W X) Js K chain os pb
      (stretches _ c.2.1.2.2) m₀.st.input (frontBy m₀ 0) D front) :
    ∃ y, play ((firstPart ⟨p, ms, some f, r, ro, tr⟩ : Part V W X).steps name ad
        ((⟨p, ms, some f, r, ro, tr⟩ : TestJob W X).laid.take (firstLen p.nums.stages)) v c.1) ds []
        m₀ = .ok y ∧ y.2.st.input = m₀.st.input ∧
      (y.2.seen = front.seen → OnFreeT (⟨p, ms, some f, r, ro, tr⟩ : TestJob W X) Js K chain os pb
        (stretches _ c.2.1.2.2) y.2 front) := by
  have hs0 : (⟨p, ms, some f, r, ro, tr⟩ : TestJob W X).s₀ = s := by
    have := T.stages
    show p.nums.stages.headD default = s
    rw [show p.nums.stages = s :: next :: rest from this]
    rfl
  have Ag := agree_of_ties p ms f r ro tr Bk rows look c hl m₀.st.input (frontBy m₀ 0) hT
    (by rw [hs0]; exact hk) (by rw [hs0]; exact hrows)
  rw [hs0] at Ag
  exact onFreeT_of_play _ Js K chain os pb _ name ad v s next rest m₀ D ds T hk c.1 hfit
    (agree_carried _ _ _ _ _ c.2.1 Ag) front E

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.AtEntryT
#print axioms ProofFile.Honest.K12.onFreeT_of_play
#print axioms ProofFile.Honest.K12.onFreeT_of_lent
