-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/Inner.lean: kind K13, the members' batching: THE ROW's LEMMA ON
ITS OWN PLACE (what the sentences of Honest/Side.lean on playing and on acceptance will use at this
row): the frame's `play` goes through on the kind's row, THE KIND's OWN SUB-PROTOCOL (`atM3`,
Johnson/Desc/K13/AtS.lean), AND WHATEVER ACCEPTS WHERE IT DOES, ACCEPTS WHAT IS SHOWN, and the row
that it lays as its claim is true. Statements with their proofs: `k13_plays` (Plays.lean of this
folder) joined with `atM3_accepts_code_gl` (Johnson/Desc/K13/Honest/Accepts.lean).

How much it says. In `k13_inner` and `k13_inner_all` "accepts" is the field `decide` alone;
`k13_step` and `k13_step_all` are of the sub-protocol's step, which also holds the rounds and the
columns against what is declared. The decision tests no sent value: under the nine premises on the
verifier's own state and on the plan it accepts any elements in rounds of this form: so
`k13_step_any` has the acceptance from these nine (beside them: b's form, and that the challenges
fit). What is said of the honest prover's values is that the row is true.

The premises of `k13_inner`. Nine on the verifier's state and on the plan, as `atM3_accepts_code`'s
docstring tells them. Three that tie the prover's side to that state: the pile that the half's
second parameter makes has as many rows as the state's, with the same weights and column points
(hpile: NOT the same targets or mask forms: a row's target in the state is a value that the prover
has sent); the matrix of W is what the index's reader gives (hmat); under the slots that the
verifier takes, W's mask entries are the coins spent (hu). And all rows of the pile are true of W
(hrows). That all of these premises hold together is not shown here. The challenges fit the kind's
rounds.

Which form serves where. `k13_inner` and `k13_step` are at any W that meets hu and hrows: a run's
own witness, where the book and the owner give hu. That hu and hrows can be met together, at every
coin: `k13_inner_all`, `k13_step_all`: from any Wb of which the rows are true, W is Wb with the
coins laid under the taken slots: the slots differ from each other, and no row of the pile names one
of them where the state passes the test `pileBelowC` (Johnson/Desc/K13/Honest/Fresh.lean).
Main names:
  `atM3_oracles`: the joined sub-protocol states no oracle message (its rounds: `atM3_rounds`,
    Johnson/Desc/K13/Law/Tile.lean).
  `k13_inner`: **the lemma.** `k13_inner_all`: **the same at every coin.**
  `k13_step`, `k13_step_all`: **the two at the sub-protocol's own step** (`Block.step`), by the
    frame's `step_iff_decide` (Honest/Law/Cut.lean). `k13_step_any`: **the step accepts, from the
    nine premises**, with nothing asked of a value.

What is not claimed. That the premises on the state hold in a run: they have to be shown of the
parts in front and of the tests on the plan. That in a run the entries under the taken slots ARE the
coins spent: the book's and the owner's matter. The statements are of any sub-protocol b that has
the kind's rounds and accepts at s wherever `atM3 P` does: `atM3 P` is one (`atM3_oracles`, and the
library's `atM3_rounds`); that the member of a proof file's IOP as written in Lean at that place is
one is AtMember.lean's of this folder. The columns are any: the sub-protocol reads none. At kCol = 0
the premise on the pile's form fails, so nothing is said there. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.Plays
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.Desc.K13.Honest.Accepts
import Johnson.Desc.K13.Honest.AcceptsAny
import Johnson.Desc.K13.Honest.PileReads
import Johnson.Desc.K13.Honest.Fresh
import Johnson.Desc.K13.Honest.WithTaken

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13 (Where battRounds atM3 St)
open VerifiableInference.Desc.K13.Law (Wit ρg Holds dOf)
open VerifiableInference.Desc.K13.Honest (maskAt withClaim atM3_accepts_code_gl atM3_accepts_moves
  rowReads
  movesAtM3_congr withTaken maskAt_withTaken holds_withTaken taken_nodup taken_off_pile pileBelowC
  takeMasks_length)

variable {Cl Cl' W₀ Rc Xi Tr X : Type}

/-- The joined sub-protocol states no oracle message. -/
theorem atM3_oracles (P : Where) :
    (atM3 (Cl := Cl) P).oracles = List.replicate (2 + P.lin.kCol) [] := by
  simp [atM3, VerifiableInference.Desc.Block.andThen, VerifiableInference.Desc.K13.frontB,
    VerifiableInference.Desc.K13.still, VerifiableInference.Desc.K13.claimCombinationBlock,
    VerifiableInference.Desc.K13.quietB]

/-- **The row's lemma: `play` goes through; b's `decide` returns `.ok` on the rounds shown, with the
state that `atM3 P` leaves; the row of the claim laid there is true of W.** b: a sub-protocol with
the kind's rounds that accepts at s wherever `atM3 P` does: `atM3 P` itself, or the member of a
proof file's IOP as written in Lean at the place. The premises are told in the head. -/
theorem k13_inner (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where)
    (b : VerifiableInference.Desc.Block S Cl) (hr : b.rounds = battRounds P)
    (ho : b.oracles = List.replicate (2 + P.lin.kCol) []) (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts)
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn)
    (hd : drawsFit (battRounds P) ds = true) {s : S} {f : VerifiableInference.Desc.First.FinOwn}
    {t : List Nat × St} {msg : Array OracleNotice}
    (hdec : ∀ rs gs t', (atM3 (Cl := Cl') P).decide s rs gs = .ok t' → b.decide s rs gs = .ok t')
    (hs : s.here = .fin f)
    (hreply : (!P.reply || s.out.reply.isSome) = true) (hcount : s.out.pending.length = P.rows)
    (hfit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true)
    (hw : s.noneWaits = true) (hform : Batt.fits P.lin.kCol s.out.pending = true)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (hlin : linOk s.st.codes P.lin = true) (hmsg : linMessageW P.lin = some msg)
    (hpile : (pile m.st.input.x (m.st.heard ++ ds.take 1)).map rowReads =
      s.out.pending.map rowReads)
    (W : Wit GE P.lin.matrixRows P.lin.kCol)
    (hmat : W.mat = (k13Wit P.lin.matrixRows P.lin.kCol (k13Ask weights pile m.st.input)).mat)
    (hu : ∀ j, j < 2 * P.lin.kCol + 1 → ρg.val ((coinsE c.2.1.2.1.1).getD j zeroE) =
      maskAt W (t.1.map fun i => ⟨s.out.indexMasks, i⟩) j)
    (hrows : ∀ r ∈ s.out.pending, Holds ρg W r) (cols : List (List (Nat × List UInt64))) :
    ∃ l row, play ((proverSideOfClaimCombination weights pile P).steps b v c) ds [] m =
        .ok (l, ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
            m.seen ++ roundsOf l, m.opened⟩) ∧
      b.decide s ((roundsOf l).map noDigest) cols =
        .ok (withClaim s t.2.st msg row) ∧ Holds ρg W row := by
  obtain ⟨x, eps, gs, hb, hg⟩ := fits_batt P ds hd
  match ds, hb, hpile with
  | d0 :: d1 :: dr, hb, hpile =>
    have hb' : bare d0 :: bare d1 :: dr.map bare = k13Dr x :: k13Dr eps :: gs.map k13Dr := hb
    obtain ⟨h0, hb''⟩ := List.cons.inj hb'
    obtain ⟨h1, hrr⟩ := List.cons.inj hb''
    obtain ⟨l, hp, -, hrd⟩ := k13_plays weights pile P b hr ho v c m d0 d1 dr x eps gs h0 h1
      hrr hg
      W hmat
      (t.1.map fun i => ⟨s.out.indexMasks, i⟩) hu
    obtain ⟨row, ha, hrow⟩ := atM3_accepts_code_gl (Cl := Cl') W hs hreply hcount hfit hw hform ht
      hlin hmsg hrows x eps gs hg cols
    have hpile' : (pile m.st.input.x (m.st.heard ++ [d0])).map rowReads =
        s.out.pending.map rowReads := hpile
    refine ⟨l, row, hp, ?_, hrow⟩
    rw [hrd, movesAtM3_congr ρg k13E W hpile']
    exact hdec _ _ _ ha
  | [], hb, _ => cases hb
  | [d], hb, _ =>
    have hb' : bare d :: [] = k13Dr x :: k13Dr eps :: gs.map k13Dr := hb
    exact absurd (List.cons.inj hb').2 (by simp)

/-- **The same AT EVERY COIN**: Wb: a matrix and mask entries of which all rows of the pile are
true. The conclusion is at Wb with the coins spent laid under the slots that the verifier takes. The
state passes `pileBelowC`: no row of the pile names an entry that the ledger has yet to hand out. -/
theorem k13_inner_all (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where)
    (b : VerifiableInference.Desc.Block S Cl) (hr : b.rounds = battRounds P)
    (ho : b.oracles = List.replicate (2 + P.lin.kCol) []) (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts)
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn)
    (hd : drawsFit (battRounds P) ds = true) {s : S} {f : VerifiableInference.Desc.First.FinOwn}
    {t : List Nat × St} {msg : Array OracleNotice}
    (hdec : ∀ rs gs t', (atM3 (Cl := Cl') P).decide s rs gs = .ok t' → b.decide s rs gs = .ok t')
    (hs : s.here = .fin f)
    (hreply : (!P.reply || s.out.reply.isSome) = true) (hcount : s.out.pending.length = P.rows)
    (hfit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true)
    (hw : s.noneWaits = true) (hform : Batt.fits P.lin.kCol s.out.pending = true)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (hlin : linOk s.st.codes P.lin = true) (hmsg : linMessageW P.lin = some msg)
    (hbelow : pileBelowC (dOf s).st s.out.indexMasks s.out.pending = true)
    (hpile : (pile m.st.input.x (m.st.heard ++ ds.take 1)).map rowReads =
      s.out.pending.map rowReads)
    (Wb : Wit GE P.lin.matrixRows P.lin.kCol)
    (hmat : Wb.mat = (k13Wit P.lin.matrixRows P.lin.kCol (k13Ask weights pile m.st.input)).mat)
    (hrows : ∀ r ∈ s.out.pending, Holds ρg Wb r) (cols : List (List (Nat × List UInt64))) :
    ∃ l row, play ((proverSideOfClaimCombination weights pile P).steps b v c) ds [] m =
        .ok (l, ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
            m.seen ++ roundsOf l, m.opened⟩) ∧
      b.decide s ((roundsOf l).map noDigest) cols =
        .ok (withClaim s t.2.st msg row) ∧
      Holds ρg (withTaken Wb (t.1.map fun i => ⟨s.out.indexMasks, i⟩)
        fun j => ρg.val ((coinsE c.2.1.2.1.1).getD j zeroE)) row := by
  have hlen : (t.1.map fun i => (⟨s.out.indexMasks, i⟩ : Slot)).length = 2 * P.lin.kCol + 1 := by
    rw [List.length_map, takeMasks_length ht]
    show 1 + 2 * P.lin.kCol = _
    omega
  exact k13_inner weights pile P b hr ho v c m ds hd hdec hs hreply hcount hfit hw hform ht
    hlin
    hmsg hpile
    (withTaken Wb (t.1.map fun i => ⟨s.out.indexMasks, i⟩)
      fun j => ρg.val ((coinsE c.2.1.2.1.1).getD j zeroE)) hmat
    (fun j hj => (maskAt_withTaken Wb _ (fun j => ρg.val ((coinsE c.2.1.2.1.1).getD j zeroE))
      (taken_nodup ht) j (by rw [hlen]; exact hj)).symm)
    (fun r hr' => (holds_withTaken ρg Wb _ _ r (taken_off_pile hbelow ht r hr')).2 (hrows r hr'))
    cols

/-- **THE LEMMA AT THE SUB-PROTOCOL's OWN STEP**, in the terms in which the frame asks it: `play`
goes through; the columns that the rounds read are laid: there are none; `Block.step` accepts the
rounds as played and these columns, taking none; the row of the claim laid is true of W. Premises as
in `k13_inner`. -/
theorem k13_step (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where)
    (b : VerifiableInference.Desc.Block S Cl) (hr : b.rounds = battRounds P)
    (ho : b.oracles = List.replicate (2 + P.lin.kCol) []) (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts)
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn)
    (hd : drawsFit (battRounds P) ds = true) {s : S} {f : VerifiableInference.Desc.First.FinOwn}
    {t : List Nat × St} {msg : Array OracleNotice}
    (hdec : ∀ rs gs t', (atM3 (Cl := Cl') P).decide s rs gs = .ok t' → b.decide s rs gs = .ok t')
    (hs : s.here = .fin f)
    (hreply : (!P.reply || s.out.reply.isSome) = true) (hcount : s.out.pending.length = P.rows)
    (hfit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true)
    (hw : s.noneWaits = true) (hform : Batt.fits P.lin.kCol s.out.pending = true)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (hlin : linOk s.st.codes P.lin = true) (hmsg : linMessageW P.lin = some msg)
    (hpile : (pile m.st.input.x (m.st.heard ++ ds.take 1)).map rowReads =
      s.out.pending.map rowReads)
    (W : Wit GE P.lin.matrixRows P.lin.kCol)
    (hmat : W.mat = (k13Wit P.lin.matrixRows P.lin.kCol (k13Ask weights pile m.st.input)).mat)
    (hu : ∀ j, j < 2 * P.lin.kCol + 1 → ρg.val ((coinsE c.2.1.2.1.1).getD j zeroE) =
      maskAt W (t.1.map fun i => ⟨s.out.indexMasks, i⟩) j)
    (hrows : ∀ r ∈ s.out.pending, Holds ρg W r) (chain ft : Nat)
    (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) :
    ∃ l row, play ((proverSideOfClaimCombination weights pile P).steps b v c) ds [] m =
        .ok (l, ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
            m.seen ++ roundsOf l, m.opened⟩) ∧
      fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] ∧
      b.step ft s (roundsOf l) [] = .ok (withClaim s t.2.st msg row, 0) ∧ Holds ρg W row := by
  obtain ⟨l, row, hp, ha, hrow⟩ := k13_inner weights pile P b hr ho v c m ds hd hdec hs hreply
    hcount hfit hw hform ht hlin hmsg hpile W hmat hu hrows
    (VerifiableInference.Desc.regroup
      ((VerifiableInference.Desc.groupsOf ft b.rounds ds).map (·.length)) [])
  have hc : fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] := by
    rw [hr, k13_reads_none]
    rfl
  refine ⟨l, row, hp, hc, ?_, hrow⟩
  exact (step_iff_decide (g := proverSideOfClaimCombination weights pile P) (b := b) s _
    (by rw [k13Half_rounds, hr, battRounds_length])
    (by rw [ho, hr, battRounds_length, List.length_replicate])
    hp (by rw [hr]; exact hd) hc).2 ha

/-- **The same AT EVERY COIN**: as `k13_inner_all`, at the sub-protocol's own step: the row of the
claim laid is true of Wb with the coins spent laid under the slots that the verifier takes. -/
theorem k13_step_all (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where)
    (b : VerifiableInference.Desc.Block S Cl) (hr : b.rounds = battRounds P)
    (ho : b.oracles = List.replicate (2 + P.lin.kCol) []) (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts)
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn)
    (hd : drawsFit (battRounds P) ds = true) {s : S} {f : VerifiableInference.Desc.First.FinOwn}
    {t : List Nat × St} {msg : Array OracleNotice}
    (hdec : ∀ rs gs t', (atM3 (Cl := Cl') P).decide s rs gs = .ok t' → b.decide s rs gs = .ok t')
    (hs : s.here = .fin f)
    (hreply : (!P.reply || s.out.reply.isSome) = true) (hcount : s.out.pending.length = P.rows)
    (hfit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true)
    (hw : s.noneWaits = true) (hform : Batt.fits P.lin.kCol s.out.pending = true)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (hlin : linOk s.st.codes P.lin = true) (hmsg : linMessageW P.lin = some msg)
    (hbelow : pileBelowC (dOf s).st s.out.indexMasks s.out.pending = true)
    (hpile : (pile m.st.input.x (m.st.heard ++ ds.take 1)).map rowReads =
      s.out.pending.map rowReads)
    (Wb : Wit GE P.lin.matrixRows P.lin.kCol)
    (hmat : Wb.mat = (k13Wit P.lin.matrixRows P.lin.kCol (k13Ask weights pile m.st.input)).mat)
    (hrows : ∀ r ∈ s.out.pending, Holds ρg Wb r) (chain ft : Nat)
    (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) :
    ∃ l row, play ((proverSideOfClaimCombination weights pile P).steps b v c) ds [] m =
        .ok (l, ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
            m.seen ++ roundsOf l, m.opened⟩) ∧
      fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] ∧
      b.step ft s (roundsOf l) [] = .ok (withClaim s t.2.st msg row, 0) ∧
      Holds ρg (withTaken Wb (t.1.map fun i => ⟨s.out.indexMasks, i⟩)
        fun j => ρg.val ((coinsE c.2.1.2.1.1).getD j zeroE)) row := by
  have hlen : (t.1.map fun i => (⟨s.out.indexMasks, i⟩ : Slot)).length = 2 * P.lin.kCol + 1 := by
    rw [List.length_map, takeMasks_length ht]
    show 1 + 2 * P.lin.kCol = _
    omega
  exact k13_step weights pile P b hr ho v c m ds hd hdec hs hreply hcount hfit hw hform ht
    hlin
    hmsg hpile
    (withTaken Wb (t.1.map fun i => ⟨s.out.indexMasks, i⟩)
      fun j => ρg.val ((coinsE c.2.1.2.1.1).getD j zeroE)) hmat
    (fun j hj => (maskAt_withTaken Wb _ (fun j => ρg.val ((coinsE c.2.1.2.1.1).getD j zeroE))
      (taken_nodup ht) j (by rw [hlen]; exact hj)).symm)
    (fun r hr' => (holds_withTaken ρg Wb _ _ r (taken_off_pile hbelow ht r hr')).2 (hrows r hr'))
    chain ft stored tree

/-- **THE SUB-PROTOCOL's OWN STEP ACCEPTS, FROM THE NINE PREMISES, AT EVERY COIN** (beside them: b's
form, hr, ho, hdec; the challenges fit): nothing is asked of a matrix, of a mask entry, of the
pile's filler or of the rows' truth. Nothing is said of the row of the claim laid. By
`atM3_accepts_moves` (Johnson/Desc/K13/Honest/AcceptsAny.lean). -/
theorem k13_step_any (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where)
    (b : VerifiableInference.Desc.Block S Cl) (hr : b.rounds = battRounds P)
    (ho : b.oracles = List.replicate (2 + P.lin.kCol) []) (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts)
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn)
    (hd : drawsFit (battRounds P) ds = true) {s : S} {f : VerifiableInference.Desc.First.FinOwn}
    {t : List Nat × St} {msg : Array OracleNotice}
    (hdec : ∀ rs gs t', (atM3 (Cl := Cl') P).decide s rs gs = .ok t' → b.decide s rs gs = .ok t')
    (hs : s.here = .fin f)
    (hreply : (!P.reply || s.out.reply.isSome) = true) (hcount : s.out.pending.length = P.rows)
    (hfit : memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true)
    (hw : s.noneWaits = true) (hform : Batt.fits P.lin.kCol s.out.pending = true)
    (ht : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t)
    (hlin : linOk s.st.codes P.lin = true) (hmsg : linMessageW P.lin = some msg) (chain ft : Nat)
    (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) :
    ∃ l row, play ((proverSideOfClaimCombination weights pile P).steps b v c) ds [] m =
        .ok (l, ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
            m.seen ++ roundsOf l, m.opened⟩) ∧
      fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] ∧
      b.step ft s (roundsOf l) [] = .ok (withClaim s t.2.st msg row, 0) := by
  obtain ⟨l, hp, -, W, rows, fresh, x, eps, gs, hg, hrd⟩ :=
    k13_plays_form weights pile P b hr ho v c m ds hd
  obtain ⟨row, ha⟩ := atM3_accepts_moves (Cl := Cl') ρg k13E hs hreply hcount hfit hw hform ht hlin
    hmsg W rows fresh x eps gs hg
    (VerifiableInference.Desc.regroup
      ((VerifiableInference.Desc.groupsOf ft b.rounds ds).map (·.length)) [])
  have hc : fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] := by
    rw [hr, k13_reads_none]
    rfl
  refine ⟨l, row, hp, hc, ?_⟩
  refine (step_iff_decide (g := proverSideOfClaimCombination weights pile P) (b := b) s _
    (by rw [k13Half_rounds, hr, battRounds_length])
    (by rw [ho, hr, battRounds_length, List.length_replicate])
    hp (by rw [hr]; exact hd) hc).2 ?_
  rw [hrd]
  exact hdec _ _ _ ha

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.atM3_oracles
#print axioms ProofFile.Honest.K13.k13_inner
#print axioms ProofFile.Honest.K13.k13_inner_all
#print axioms ProofFile.Honest.K13.k13_step
#print axioms ProofFile.Honest.K13.k13_step_all
#print axioms ProofFile.Honest.K13.k13_step_any
