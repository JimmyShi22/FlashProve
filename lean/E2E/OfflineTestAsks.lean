-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineTestAsks.lean: ONE BRIDGE FOR EVERY PROXIMITY TEST WHOSE FIRST FOLD's FRESH TABLE HAS COME EARLIER: from
where a chain's invariant holds IN FRONT OF the test to the two clauses on the asks that are left of the
condition at the test's SECOND part (the clause `asks` of `OnFreeTD`,
Johnson/Desc/ProofFile/Honest/K12/Sim/TreesExactDense.lean), at the state behind the first part's rounds and at
the blocks that the frame hands the second part as carried. General in the job, the chain, the book, the
list of halves, the face and the invariant. Over the trunk alone.

  `AsksInFront`        WHAT IS ASKED IN FRONT, NO CHALLENGE OF THE TEST NAMED: plain data with n trees, `planB`,
                     `FrontAsksD`, `DataFront`: at an input, a front and coins
  `AsksLeft`             WHAT IS CONCLUDED: plain data with n trees, `ShapeAsksD`, `DataAsks`: at a state m, at its
                     front cut back, the carried coins and the challenges that m has heard
  `left_of_front`      (t3) `AsksInFront` at m's input, m's front cut back and the carried coins ⟹ `AsksLeft` at m,
                     where the first part's challenges, as m has heard them, have the declared form
  `FirstPartPublic`        what is asked of the job's public part: five clauses
  `behind_first_steps`, `behind_first_part`   (t1) at the part's own steps; and what `InsideOf` (Honest/Law/Inside.lean) gives behind the first part's rounds: the row
                     of the two parts is lent; the input and the front cut back are those in front of the
                     test; the challenges heard fit
  `carried_of_lent`    what the second part is handed as carried, out of the lending of the row: any chain
  `asks_carried`       (t2) `AsksInFront` reads of the coins all but the second part's own: so at the coins that
                     the second part reads and at the carried coins it is one sentence
  `left_of_inside`     **THE BRIDGE**: `InsideOf` at an invariant A (t4: A NAMED PREMISE) · wherever A holds and the
                     row is lent, `AsksInFront` at the coins that the second part reads ⟹ `AsksLeft` at the state
                     and at the carried blocks

Limits. `InsideOf` and "`AsksInFront` wherever A holds" are premises: no member of either is given here.
`AsksInFront` holds, in `DataFront.allSay`, the one sentence on values: the rows that the test takes in say true
things of the prover's words. The state on entry is the job's own letter, not shown to be the verifier's.
Where the first fold's fresh table has come earlier; three stages or more (`planB`). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K12.ShapeOfTwoDense
import Johnson.Desc.ProofFile.Honest.K12.AsksWholeDense
import Johnson.Desc.ProofFile.Honest.K12.Sim.OnFromPlay
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesExactDense
import Johnson.Desc.ProofFile.Honest.K12.FirstPlayAtRun
import Johnson.Desc.ProofFile.Honest.K12.FormPubAt
import Johnson.Desc.ProofFile.Honest.Law.Inside

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open ProofFile.Honest.Sh (door_facts_dense)
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {W X : Type}

/-- **What is asked in front of the test; no challenge of the test is named.** K: the codes. n: the number
of trees that the first round of positions opens. -/
def AsksInFront (J : TestJob W X) (K : Codes) (n : ℕ) (w : W) (fr : Front X) (C : TestCoins) : Prop :=
  ∃ (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows), Dp.ts.length = n ∧
    planB J.p K n = true ∧ FrontAsksD J w fr K Dp ∧ DataFront J w fr C Dp cc R

/-- **What is left of the condition at the second part's entry**: the clause `asks` of `OnFreeTD`, at n in the
place of the list's length. -/
def AsksLeft (J : TestJob W X) (K : Codes) (n : ℕ) (mem : ℕ → Stretch) (m : Mid W X) : Prop :=
  ∃ (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows), Dp.ts.length = n ∧
    ShapeAsksD J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) K Dp ∧
    DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc R

/-- **From the front to the challenges heard.** -/
theorem left_of_front (J : TestJob W X) (K : Codes) (n : ℕ) (mem : ℕ → Stretch) (m : Mid W X)
    (a next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = a :: next :: rest)
    (hF : formPubB J.p = true)
    (hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      (m.st.lately (firstLen J.p.nums.stages)) = true)
    (h : AsksInFront J K n m.st.input (restFront J m) (carriedCoins J mem)) :
    AsksLeft J K n mem m := by
  obtain ⟨Dp, cc, R, hn', hP, S, Dt⟩ := h
  have hn : firstLen J.p.nums.stages = 2 + a.k := by rw [hst]; rfl
  have hD : heardIn J m = byNo (m.st.lately (firstLen J.p.nums.stages)) := rfl
  rw [hn] at hfit
  have h2 := two_of_draws J m.st.input (restFront J m) (carriedCoins J mem)
    (m.st.lately (2 + a.k)) a next rest hst (formPub_of_B _ _ _ _ hst hF) hfit
  rw [← hn'] at hP
  refine ⟨Dp, cc, R, hn', ?_, ?_⟩
  · rw [hD, hn]
    exact shapeAsksD_of_two J _ _ _ _ K Dp hP S h2.1 h2.2
  · rw [hD, hn]
    exact dataAsks_of_oneD J _ _ _ _ K Dp cc R hP S h2.1 Dt

/-- **What is asked of the job's public part**: two stages or more, k = h + g at the first; the place
declares enough rounds, of the text's sorts; the declared oracle messages fit the text's tables. -/
structure FirstPartPublic (J : TestJob W X) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) :
    Prop where
  stages : J.p.nums.stages = s :: next :: rest
  split : s.k = (sgOf s).h + (sgOf s).g
  enough : firstLen J.p.nums.stages ≤ (H2K.JointK.laidOf J.p).length
  sorts : (H2K.JointK.laidOf J.p).map asked = [] :: bodyItems s (next :: rest)
  tables : tablesFitB J = true

/-- **Behind the first part's rounds, at the part's own steps**: where the frame's play over the first part's
steps returns from a state m₀, at challenges that the sub-protocol's first rounds can draw: the input is m₀'s;
the front cut back is m₀'s front; the challenges, as heard, have the declared form. -/
theorem behind_first_steps {S Cl V : Type} {b : Block S Cl} (J : TestJob W X) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (P : FirstPartPublic J s next rest)
    (hlaid : b.rounds.zip b.oracles = J.laid) (hor : b.oracles.length = b.rounds.length)
    (v : Option V) (c : (firstPart J : Part V W X).Coins) (m₀ : Mid W X) (ds : List Fmt.Drawn)
    (y : List Played × Mid W X)
    (hd : drawsFit (b.rounds.take (firstLen J.p.nums.stages)) ds = true)
    (hy : play ((firstPart J : Part V W X).steps b.name ⟨b.place, 0⟩
      (J.laid.take (firstLen J.p.nums.stages)) v c) ds [] m₀ = .ok y) :
    y.2.st.input = m₀.st.input ∧ restFront J y.2 = frontOf m₀ ∧
      drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
        (y.2.st.lately (firstLen J.p.nums.stages)) = true := by
  have hfst : J.laid.map (·.1) = b.rounds := by
    rw [← hlaid]
    exact List.map_fst_zip (le_of_eq hor.symm)
  have hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1)) ds =
      true := by
    rw [List.map_take]
    show drawsFit ((J.laid.map (·.1)).take _) ds = true
    rw [hfst]
    exact hd
  have hlen : ds.length = firstLen J.p.nums.stages := by
    rw [ProofFile.Honest.drawsFit_length _ _ hfit, List.length_map, List.length_take]
    exact Nat.min_eq_left P.enough
  have T : FirstTies J s next rest (byNo ds) ds :=
    ⟨P.stages, P.enough, P.sorts, P.tables, hlen, fun n hn => (List.getD_eq_getElem _ _ hn).symm⟩
  obtain ⟨y', hy', h1, h2, -⟩ := first_played J b.name ⟨b.place, 0⟩ v s next rest m₀ (byNo ds) ds T
    P.split c
  obtain rfl : y' = y := Except.ok.inj (hy'.symm.trans hy)
  have hn : firstLen J.p.nums.stages = 2 + s.k := by rw [P.stages]; rfl
  have hlenA : ((⟨[], byNo ds 0⟩ : Fmt.RoundView) ::
      aFold (coinsOf (s :: next :: rest) (firstRd J c).hide (firstRd J c).rest) 0 s 1
        (J.first m₀.st.input (frontBy m₀ 0) (firstRd J c))
        (rowOf (J.recB m₀.st.input (frontBy m₀ 0) (byNo ds 0))) (byNo ds)).length =
      firstLen J.p.nums.stages := by
    rw [List.length_cons, length_aFold, hn, P.split]
    omega
  have hheard : y'.2.st.heard = m₀.st.heard ++ ds := by rw [h1]
  have hown : y'.2.st.own = m₀.st.own := by rw [h1]
  have hop : y'.2.opened = m₀.opened := ProofFile.Honest.play_opened _ _ _ _ _ hy
  have hfr : restFront J y'.2 = frontOf m₀ := by
    unfold restFront
    simp only [frontOf, Mid.shown, Seen.front, hheard, hown, h2, hop, take_behind _ _ _ hlen,
      take_behind _ _ _ hlenA]
  have hlat : y'.2.st.lately (firstLen J.p.nums.stages) = ds := by
    unfold State.lately
    rw [hheard, drop_behind _ _ _ hlen]
  exact ⟨by rw [h1], hfr, by rw [hlat]; exact hfit⟩

/-- **Behind the first part's rounds**: where a state m is reached by the frame's play over the first part's
rounds from a state m₀ at which A holds in front of the test's sub-protocol. -/
theorem behind_first_part {S Cl V Pb : Type} {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain : ℕ}
    {hs : List (Placed V W X)} {b : Block S Cl} (J : TestJob W X) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (P : FirstPartPublic J s next rest)
    (hlaid : b.rounds.zip b.oracles = J.laid) (hor : b.oracles.length = b.rounds.length)
    (hhalf : (hs.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J))
    {A : Coins Bk → S → Mid W X → Env → Prop} {k : Coins Bk} {m : Mid W X} {E : Env}
    (hin : InsideOf φ Bk chain hs b A (firstLen J.p.nums.stages) k m E) :
    ∃ st m₀ E₀, ∃ c : RowCoins [(firstPart J : Part V W X), restPart J], A k st m₀ E₀ ∧
      lendRow Bk (Bk.rowsOf chain) (k.look chain) b.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c ∧
      m.st.input = m₀.st.input ∧ restFront J m = frontOf m₀ ∧
      drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
        (m.st.lately (firstLen J.p.nums.stages)) = true := by
  obtain ⟨st, m₀, E₀, l, ds, y, hA, hl, hd, hy, rfl, -⟩ := hin
  obtain ⟨c, hc, rfl⟩ := steps_one_half hhalf hl
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages :=
    Light.first_moves_len J
  have hrs : (J.laid.take (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    rw [List.length_take]
    exact Nat.min_eq_left P.enough
  have hsl := (steps_at J (firstPart J : Part V W X) (firstRd J) 0 (firstLen J.p.nums.stages)
    (first_moves J) b.name ⟨b.place, 0⟩ (J.laid.take (firstLen J.p.nums.stages)) hrs
    (φ.sees m₀.st.input) c.1).1
  have htake : ((proverSideOfProximityTest J : Placed V W X).steps b (φ.sees m₀.st.input) c).take
      (firstLen J.p.nums.stages) =
      (firstPart J : Part V W X).steps b.name ⟨b.place, 0⟩
        (J.laid.take (firstLen J.p.nums.stages)) (φ.sees m₀.st.input) c.1 := by
    show ((firstPart J : Part V W X).steps b.name ⟨b.place, 0⟩
      ((b.rounds.zip b.oracles).take (firstPart J : Part V W X).moves.length)
      (φ.sees m₀.st.input) c.1 ++ _).take _ = _
    rw [hlaid, l1]
    exact List.take_left' hsl
  rw [htake] at hy
  obtain ⟨h1, h2, h3⟩ := behind_first_steps J s next rest P hlaid hor _ c.1 m₀ ds y hd hy
  exact ⟨st, m₀, E₀, c, hA, hc, h1, h2, h3⟩

/-- What the second part of a pair is handed as carried, out of the lending of the pair's row: at any
chain. -/
theorem carried_of_lent {V : Type} {Bk : ProverCoinCounts} (k : Coins Bk) (chain : ℕ) (a : VerifiableInference.Desc.Place)
    (p₀ p₁ : Part V W X) (c : RowCoins [p₀, p₁])
    (hl : lendRow Bk (Bk.rowsOf chain) (k.look chain) a [p₀, p₁] 0 = .ok c) :
    carriedAt Bk k chain ⟨a, 1⟩ p₁ = .ok c.2.1.2.2 := by
  have h1 := (lendRow_cons_ok (lendRow_cons_ok hl).2).1
  unfold carriedAt
  rw [h1]
  rfl

/-- **The sentence in front reads of the coins all but the second part's own.** -/
theorem asks_carried {V : Type} (J : TestJob W X) (K : Codes) (n : ℕ) (w : W) (fr : Front X)
    (c : (restPart J : Part V W X).Coins)
    (h : AsksInFront J K n w fr (restCoins J c)) :
    AsksInFront J K n w fr (carriedCoins J (stretches _ c.2.2)) := by
  obtain ⟨Dp, cc, R, h1, h2, h3, d1, d2, d3, d4⟩ := h
  exact ⟨Dp, cc, R, h1, h2, h3, d1, d2, d3, d4⟩

/-- **THE BRIDGE.** hin: the state m is reached by the frame's play over the first part's rounds from a state
at which A holds in front of the test's sub-protocol. hA: wherever A holds and the row of the two parts is
lent, the sentence in front holds at the coins that the second part reads. -/
theorem left_of_inside {S Cl V Pb : Type} {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain : ℕ}
    {hs : List (Placed V W X)} {b : Block S Cl} (J : TestJob W X) (K : Codes) (n : ℕ)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (P : FirstPartPublic J s next rest)
    (hF : formPubB J.p = true) (hlaid : b.rounds.zip b.oracles = J.laid)
    (hor : b.oracles.length = b.rounds.length)
    (hhalf : (hs.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J))
    {A : Coins Bk → S → Mid W X → Env → Prop} {k : Coins Bk} {m : Mid W X} {E : Env}
    (hin : InsideOf φ Bk chain hs b A (firstLen J.p.nums.stages) k m E)
    (hA : ∀ st m₀ E₀ (c : RowCoins [(firstPart J : Part V W X), restPart J]), A k st m₀ E₀ →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) b.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c →
      AsksInFront J K n m₀.st.input (frontOf m₀) (restCoins J c.2.1))
    (ca : CsAll (restPart J : Part V W X).carries)
    (hca : carriedAt Bk k chain ⟨b.place, 1⟩ (restPart J : Part V W X) = .ok ca) :
    AsksLeft J K n (stretches _ ca) m := by
  obtain ⟨st, m₀, E₀, c, h0, hc, hi, hfr, hfit⟩ := behind_first_part J s next rest P hlaid hor hhalf hin
  obtain rfl : c.2.1.2.2 = ca :=
    Except.ok.inj ((carried_of_lent k chain b.place _ _ c hc).symm.trans hca)
  have h := asks_carried (V := V) J K n _ _ c.2.1 (hA st m₀ E₀ c h0 hc)
  rw [← hi, ← hfr] at h
  exact left_of_front J K n _ m s next rest P.stages hF hfit h

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.AsksInFront
#print axioms ProofFile.Honest.K12.AsksLeft
#print axioms ProofFile.Honest.K12.left_of_front
#print axioms ProofFile.Honest.K12.FirstPartPublic
#print axioms ProofFile.Honest.K12.behind_first_steps
#print axioms ProofFile.Honest.K12.behind_first_part
#print axioms ProofFile.Honest.K12.carried_of_lent
#print axioms ProofFile.Honest.K12.asks_carried
#print axioms ProofFile.Honest.K12.left_of_inside
