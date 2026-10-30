-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/Debts.lean: kind K13, the members' batching: THE ROW's LEMMA IN
THE TERMS IN WHICH A CHAIN's THREAD ASKS IT (Honest/Thread/Thr.lean; the sentences `plays` and `acc`
of Honest/Side.lean): at the steps that `chainSteps` lays for the one member at the kind's place, at
the coins that the book lends. Statements with their proofs. No thread is named: the statements are
at the frame's own functions, so that they can be laid at any thread's fields.
Main names:
  `k13_moved`: **played**: wherever `chainSteps` returns at the member, `play` and `fillCols`
    return, at all coins; no table is sent; no column is read.
  `K13Guards`: what the acceptance asks in front of the place: nine clauses on the verifier's state
    and the plan; no coin is named. `taken_of_room`: one of them as a test with code.
  `k13_accepted`: **accepted**: from `K13Guards`, with nothing asked of a coin or a value (beside
    it: the member's form, the half at its place, and that the member accepts wherever `atM3 P`
    does): whatever `play` and `fillCols` have returned, the member's own step accepts it.
  `K13Front`: what the truth of the row behind the place asks beside. `k13Front_all`: it can be met
    at every list of coins.
  `k13_stepped`: **behind the step**: the state is `withClaim`; the row of its claim is true.

What is not claimed. That `K13Guards` or `K13Front` holds at a thread's sentence in front of the
place. That `chainSteps` returns. Nothing on the public form behind the place. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K13.Inner
import Johnson.Desc.ProofFile.Honest.K13.DebtsKit
import Johnson.Desc.K13.Honest.Room

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Place OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13 (Where battRounds atM3 St)
open VerifiableInference.Desc.K13.Law (Wit ρg Holds dOf)
open VerifiableInference.Desc.K13.Honest (maskAt withClaim rowReads withTaken maskAt_withTaken
  holds_withTaken taken_nodup taken_off_pile pileBelowC takeMasks_length leftAtC leftAtC_iff
  takeMasks_returns)

variable {Cl Cl' W₀ Rc Xi Tr X : Type}

/-- **Played.** b: the member. hs: the chain's halves, of which the kind's stands at the member's
place. Wherever `chainSteps` returns, `play` returns on these steps, at every list of challenges
that fits the kind's rounds; it sends no table; the rounds read no column. -/
theorem k13_moved (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where) (b : Block S Cl)
    (hr : b.rounds = battRounds P) (ho : b.oracles = List.replicate (2 + P.lin.kCol) [])
    {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option (Local W₀ Rc Xi Tr)}
    {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    (hf : (hs.find? fun h => h.place == b.place) = some (proverSideOfClaimCombination weights pile P))
    {l : List (Step (Local W₀ Rc Xi Tr) X)} (hl : chainSteps B rows look v [b] hs = .ok l)
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn) (hd : drawsFit b.rounds ds = true) :
    ∃ p, play l ds [] m =
        .ok (p, ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
            m.seen ++ roundsOf p, m.opened⟩) ∧
      tablesOf p = [] ∧
      ∀ (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
        (tree : Fmt.TreeSource → Option (Place × Table)),
        fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] := by
  obtain ⟨c, -, rfl⟩ := chainSteps_one hf hl
  obtain ⟨p, hp, ht⟩ := k13_plays_returns weights pile P b hr ho v c m ds (by rw [← hr]; exact hd)
  refine ⟨p, hp, ht, fun chain ft stored tree => ?_⟩
  rw [hr, k13_reads_none]
  rfl

/-- **What the acceptance asks in front of the place**: the nine premises of `atM3_accepts_code`
(Johnson/Desc/K13/Honest/Accepts.lean), as one proposition on the verifier's state s and the plan's
P. No coin and no matrix is named. Two of the tests (`memberRowsFit`, `Batt.fits`) are handed the
pile's rows, which hold a sent value as their target; by a reading of their texts they read of a row
lengths, numbers of variables and slots alone: `fitSh_eq`, `formSh_eq`
(Johnson/Desc/K13/Honest/Shape.lean). -/
structure K13Guards (P : Where) (s : S) : Prop where
  fin : ∃ f, s.here = .fin f
  reply : (!P.reply || s.out.reply.isSome) = true
  count : s.out.pending.length = P.rows
  fit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true
  waits : s.noneWaits = true
  form : Batt.fits P.lin.kCol s.out.pending = true
  taken : ∃ t, takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t
  lin : linOk s.st.codes P.lin = true
  msg : ∃ msg, linMessageW P.lin = some msg

/-- **What the truth of the row behind the place asks in front of it**, beside the guards. m: where
the prover's run stands. u: the coins of the stretch that the sumcheck's part spends. W: a matrix
with mask entries: a run's own witness. The prover's pile agrees with the state's in the rows'
weights and column points, whatever x is sampled; W has the matrix that the index's reader gives;
all rows of the pile are true of W; W's mask entries under the slots that the verifier takes are the
coins u. `k13Front_all`: it can be met at every u. -/
structure K13Front (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where) (s : S)
    (m : Mid (Local W₀ Rc Xi Tr) X) (u : List E) (W : Wit GE P.lin.matrixRows P.lin.kCol) :
    Prop where
  rows : ∀ d, (pile m.st.input.x (m.st.heard ++ [d])).map rowReads = s.out.pending.map rowReads
  mat : W.mat = (k13Wit P.lin.matrixRows P.lin.kCol (k13Ask weights pile m.st.input)).mat
  holds : ∀ r ∈ s.out.pending, Holds ρg W r
  coins : ∀ t, takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t →
    ∀ j, j < 2 * P.lin.kCol + 1 →
      ρg.val (u.getD j zeroE) = maskAt W (t.1.map fun i => ⟨s.out.indexMasks, i⟩) j

/-- **`K13Front` can be met at every list of coins u**: from premises that name no coin: the taking
returns; no row of the pile names an entry that the ledger has yet to hand out (`pileBelowC`,
Johnson/Desc/K13/Honest/Fresh.lean); the piles agree; and a Wb with the reader's matrix of which the
rows are true. W is Wb with u laid under the slots that the verifier takes. -/
theorem k13Front_all (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where) {s : S}
    {t : List Nat × St} (m : Mid (Local W₀ Rc Xi Tr) X)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (hbelow : pileBelowC (dOf s).st s.out.indexMasks s.out.pending = true)
    (hpile : ∀ d, (pile m.st.input.x (m.st.heard ++ [d])).map rowReads =
      s.out.pending.map rowReads)
    (Wb : Wit GE P.lin.matrixRows P.lin.kCol)
    (hmat : Wb.mat = (k13Wit P.lin.matrixRows P.lin.kCol (k13Ask weights pile m.st.input)).mat)
    (hrows : ∀ r ∈ s.out.pending, Holds ρg Wb r) (u : List E) :
    K13Front weights pile P s m u
      (withTaken Wb (t.1.map fun i => ⟨s.out.indexMasks, i⟩) fun j => ρg.val (u.getD j zeroE)) := by
  have hlen : (t.1.map fun i => (⟨s.out.indexMasks, i⟩ : Slot)).length = 2 * P.lin.kCol + 1 := by
    rw [List.length_map, takeMasks_length ht]
    show 1 + 2 * P.lin.kCol = _
    omega
  refine ⟨hpile, hmat,
    fun r hr => (holds_withTaken ρg Wb _ _ r (taken_off_pile hbelow ht r hr)).2 (hrows r hr),
    fun t' ht' j hj => ?_⟩
  obtain rfl : t = t' := Option.some.inj (ht.symm.trans ht')
  exact (maskAt_withTaken Wb _ (fun j => ρg.val (u.getD j zeroE)) (taken_nodup ht) j
    (by rw [hlen]; exact hj)).symm

/-- The guards' clause on the taking, as a test with code on the state: the ledger's room
(`leftAtC`, Johnson/Desc/K13/Honest/Room.lean). -/
theorem taken_of_room {P : Where} {s : S}
    (h : leftAtC (dOf s).st s.out.indexMasks (Batt.masksOf P.lin.kCol) = true) :
    ∃ t, takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t :=
  takeMasks_returns ((leftAtC_iff _ _ _).1 h)

/-- **Accepted, from the guards alone.** b: the member: it has the kind's rounds and accepts at s
wherever `atM3 P` does. Whatever `play` has returned on the steps that `chainSteps` lays, and
whatever columns `fillCols` has laid, the member's own step accepts them, taking all columns. AT ALL
COINS: nothing is asked of them, of a matrix or of the pile's filler. -/
theorem k13_accepted (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where) (b : Block S Cl)
    (hr : b.rounds = battRounds P) (ho : b.oracles = List.replicate (2 + P.lin.kCol) [])
    {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option (Local W₀ Rc Xi Tr)}
    {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    (hf : (hs.find? fun h => h.place == b.place) = some (proverSideOfClaimCombination weights pile P))
    {l : List (Step (Local W₀ Rc Xi Tr) X)} (hl : chainSteps B rows look v [b] hs = .ok l)
    {s : S}
    (hdec : ∀ rs gs t', (atM3 (Cl := Cl') P).decide s rs gs = .ok t' → b.decide s rs gs = .ok t')
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn) (hd : drawsFit b.rounds ds = true)
    (hG : K13Guards P s)
    (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table))
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hy : play l ds [] m = .ok y)
    (hc : fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok cols) :
    ∃ s', b.step ft s (roundsOf y.1) cols = .ok (s', cols.length) := by
  obtain ⟨c, -, rfl⟩ := chainSteps_one hf hl
  obtain ⟨⟨f, hfin⟩, hreply, hcount, hfit, hw, hform, ⟨t, ht⟩, hlin, ⟨msg, hmsg⟩⟩ := hG
  obtain ⟨p, row, hp, hc', hst⟩ := k13_step_any weights pile P b hr ho v c m ds
    (by rw [← hr]; exact hd) hdec hfin hreply hcount hfit hw hform ht hlin hmsg chain ft stored tree
  have ey : y = (p, _) := Except.ok.inj (hy.symm.trans hp)
  have ec : cols = [] := Except.ok.inj (hc.symm.trans hc')
  subst ec
  rw [ey]
  exact ⟨_, hst⟩

/-- **Behind the step.** From the guards and `K13Front` at the coins that the book lends: the
member's own step accepts, the state behind is `withClaim`, at what the verifier's taking returns,
and the row of its claim is true of W. -/
theorem k13_stepped (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where) (b : Block S Cl)
    (hr : b.rounds = battRounds P) (ho : b.oracles = List.replicate (2 + P.lin.kCol) [])
    {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option (Local W₀ Rc Xi Tr)}
    {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    (hf : (hs.find? fun h => h.place == b.place) = some (proverSideOfClaimCombination weights pile P))
    {l : List (Step (Local W₀ Rc Xi Tr) X)} (hl : chainSteps B rows look v [b] hs = .ok l)
    {s : S}
    (hdec : ∀ rs gs t', (atM3 (Cl := Cl') P).decide s rs gs = .ok t' → b.decide s rs gs = .ok t')
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn) (hd : drawsFit b.rounds ds = true)
    (hG : K13Guards P s)
    (W : Wit GE P.lin.matrixRows P.lin.kCol)
    (hA : ∀ c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts,
      lendRow B rows look b.place (proverSideOfClaimCombination weights pile P).parts 0 = .ok c →
      K13Front weights pile P s m (coinsE c.2.1.2.1.1) W)
    (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table))
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hy : play l ds [] m = .ok y)
    (hc : fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok cols) :
    ∃ t msg row, takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t ∧
      linMessageW P.lin = some msg ∧
      b.step ft s (roundsOf y.1) cols = .ok (withClaim s t.2.st msg row, cols.length) ∧
      Holds ρg W row := by
  obtain ⟨c, hlend, rfl⟩ := chainSteps_one hf hl
  obtain ⟨⟨f, hfin⟩, hreply, hcount, hfit, hw, hform, ⟨t, ht⟩, hlin, ⟨msg, hmsg⟩⟩ := hG
  obtain ⟨hrows', hmat, hrows, hu⟩ := hA c hlend
  have hd' : drawsFit (battRounds P) ds = true := by rw [← hr]; exact hd
  have hpile : (pile m.st.input.x (m.st.heard ++ ds.take 1)).map rowReads =
      s.out.pending.map rowReads := by
    cases ds with
    | nil => simp [battRounds, drawsFit] at hd'
    | cons d _ => exact hrows' d
  obtain ⟨p, row, hp, hc', hst, hrow⟩ := k13_step weights pile P b hr ho v c m ds hd' hdec hfin
    hreply hcount hfit hw hform ht hlin hmsg hpile W hmat (hu t ht) hrows chain ft stored tree
  have ey : y = (p, _) := Except.ok.inj (hy.symm.trans hp)
  have ec : cols = [] := Except.ok.inj (hc.symm.trans hc')
  subst ec
  rw [ey]
  exact ⟨t, msg, row, ht, hmsg, hst, hrow⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_moved
#print axioms ProofFile.Honest.K13.k13Front_all
#print axioms ProofFile.Honest.K13.taken_of_room
#print axioms ProofFile.Honest.K13.k13_accepted
#print axioms ProofFile.Honest.K13.k13_stepped
#print axioms ProofFile.Honest.K13.K13Guards
#print axioms ProofFile.Honest.K13.K13Front
