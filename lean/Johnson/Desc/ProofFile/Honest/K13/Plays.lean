-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/Plays.lean: kind K13, the members' batching: THE FRAME's `play`
GOES THROUGH ON THE KIND's ROW, AT EVERY COIN, WHEREVER THE RUN STANDS, AT EVERY LIST OF CHALLENGES
THAT FITS THE KIND's ROUNDS, AND WHAT IT SHOWS ARE THE ROUNDS OF THE KIND's HONEST PROVER
(`movesAtM3`, Johnson/Desc/K13/Honest/MovesAtM3.lean) at the matrix that the index's reader gives,
at the pile that the half's second parameter makes, and at mask entries that are the coins spent.
One definition (`k13X`), and statements with their proofs.

How. The quiet part and `sumPart` are moves that say scalars (Honest/SumLaw/Said.lean); on the steps
of `sumPart`, laid at a wider input, `play` returns the rounds `sumOut` (Honest/SumLaw/Out.lean),
each without a table (`plays_unit_sumPart`, PlaysSum.lean there; `play_steps_whole`,
PlaysWhole.lean, for the quiet part); two stretches are joined by `play_append`
(Honest/Law/Play.lean); the scalars read as the kind's (VarOut.lean, Tie.lean of this folder).
Main names:
  `k13_all`, `k13X`, `k13_poly`, `k13_sumOut`: the sumcheck's part at the kind's job, written out.
  `items_sigma`, `items_eps`, `items_round`, `k13_scalars`, `stated_rounds`: the kind's rounds state
    the numbers of scalars that the call sends.
  `k13X_snoc`, `none_stated`: x is the last challenge in front; no oracle message is stated.
  `k13Sum_moves`, `battRounds_length`, `k13Half_rounds`, `k13Pairs_parts`: the row has one move for
    each round; the side's parts are the row's.
  `readsOf_none`, `k13_reads_none`: the kind's rounds read no column.
  `k13_plays`: **the law.** `k13_plays_form`, `k13_plays_returns`: that `play` goes through, and the
    form of what it shows, with no premise on coins.

What is not claimed. That the book lends the coins. `play` is asked with nothing to fall back on
(back := []), as the frame asks it. That the coins spent are the mask entries under the slots that
the verifier takes: a premise (hu). Nothing on the decision: that it accepts these rounds is
Johnson/Desc/K13/Honest/Accepts.lean's. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.PlaysSum
import Johnson.Desc.ProofFile.Honest.SumLaw.PlaysWhole
import Johnson.Desc.ProofFile.Honest.SumLaw.OutMore
import Johnson.Desc.ProofFile.Honest.K13.VarOut
import Johnson.Desc.ProofFile.Honest.K13.Tie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes (E Slot zeroE)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Oracle noDigest)
open VerifiableInference.Desc.Part.MaskedSum (Var)
open VerifiableInference.Desc.K13 (Where battRounds)
open VerifiableInference.Desc.K13.Law (Wit ρg)
open VerifiableInference.Desc.K13.Honest (tabsOf quadAll foldsAll maskAt sumU sent sent_eq
  codeRounds shownRound movesAtM3)
open ProofFile.Honest.SumLaw

/-! ## The sumcheck's part at the kind's job -/

/-- The call's variables. -/
theorem k13_all (nR k : Nat) (w : K13Ask) (fr : Front Unit) :
    ((k13Job nR k).callAt w fr).all = plains k := by
  rw [all_none _ _ _ rfl]
  exact withPoints_plain 3 k

/-- x, of the challenges in front of the sumcheck's part: the last of them. -/
def k13X (heard : List Fmt.Drawn) : E := (drawnE (heard.drop (heard.length - 1))).headD zeroE

/-- The job's polynomials read as the tables' coefficients. -/
theorem k13_poly (nR k : Nat) (w : K13Ask) (fr : Front Unit) (m : List E) :
    ReadsAs ρg k (jobPoly (k13Job nR k) w fr m) (fun seen => quadAll (foldsAll seen
      (tabsOf ρg (k13Wit nR k w) (w.pile fr.heard) (ρg.val (k13X fr.heard))))) := fun rs hrs => by
  have e : jobPoly (k13Job nR k) w fr m rs =
      k13Round nR k w (w.pile fr.heard) (k13X fr.heard) rs := by
    unfold jobPoly
    rw [if_pos (by
      show rs.length < (List.replicate k (Var.plain 3)).length
      rw [List.length_replicate]
      exact hrs)]
    rfl
  rw [e]
  exact k13Round_reads k nR k w _ _ rs hrs

/-- **The part's rounds at the kind's job**, without the sealed digest. W: the matrix and the mask
entries. fresh: the mask entries that were taken. -/
theorem k13_sumOut {name endName : String} {nR k : Nat} (c : SumCoins name endName (k13Job nR k))
    (t : State K13Ask Unit) (seen : Seen) (W : Wit GE nR k) (hmat : W.mat = (k13Wit nR k
      t.input).mat)
    (fresh : List Slot)
    (hu : ∀ j, j < 2 * k + 1 → ρg.val ((firstRun c).getD j zeroE) = maskAt W fresh j)
    (d1 : Fmt.Drawn) (dr : List Fmt.Drawn) (eps : E) (gs : List E) (h1 : bare d1 = k13Dr eps)
    (hr : dr.map bare = gs.map k13Dr) (hg : gs.length = k) :
    (sumOut (k13Job nR k) c t seen (d1 :: dr)).map noDigest =
      shownRound [k13E (sumU (maskAt W fresh) k)] eps ::
        (codeRounds k13E (sent (maskAt W fresh) (ρg.val eps) k 0
          (tabsOf ρg W (t.input.pile t.heard) (ρg.val (k13X t.heard))) (gs.map ρg.val)) gs).map
          fun p => shownRound p.1 p.2 := by
  have hl : dr.length = k := by
    have := congrArg List.length hr
    rw [List.length_map, List.length_map] at this
    omega
  have he : elemOf d1 = eps := by
    have e : elemOf d1 = elemOf (bare d1) := rfl
    rw [e, h1]
    rfl
  have hs : sumOut (k13Job nR k) c t seen (d1 :: dr) =
      rvSaid [plainFirst k (firstRun c)] d1 ::
        (varOut (elemOf d1) (jobPoly (k13Job nR k) t.input (frontOf t seen) (endRun c))
          (vwOf k (firstRun c)) zeroE [] (dr.take (plains k).length) ++ []) := by
    show rvSaid (saidFirst (k13Job nR k) ((k13Job nR k).callAt t.input (frontOf t seen)).all
      (frontOf t seen)
        (firstRun c) (endRun c) [] t.input) d1 ::
      (varOut (elemOf d1) (jobPoly (k13Job nR k) t.input (frontOf t seen) (endRun c))
        (sharesOf 0 ((k13Job nR k).callAt t.input (frontOf t seen)).all (firstRun c)) zeroE []
        (dr.take ((k13Job nR k).callAt t.input (frontOf t seen)).all.length) ++ []) = _
    rw [k13_all]
    rfl
  have hp : (plains k).length = k := List.length_replicate
  rw [hs, List.append_nil, hp, List.take_of_length_le (Nat.le_of_eq hl), List.map_cons,
    noDigest_varOut, hr, he]
  have e1 : noDigest (rvSaid [plainFirst k (firstRun c)] d1) =
      shownRound [k13E (sumU (maskAt W fresh) k)] eps := by
    show (⟨(sayE [plainFirst k (firstRun c)]).vals.map Said.got, bare d1⟩ : Fmt.RoundView) = _
    rw [h1, said_shown]
    show shownRound [k13E (ρg.val (plainFirst k (firstRun c)))] eps = _
    rw [k13_first_reads W fresh _ hu]
  rw [e1, varOut_plain (maskAt W fresh) eps (k13_poly nR k t.input (frontOf t seen) (endRun c)) k
    (firstRun c) 0 [] gs zeroE (Nat.zero_add k) (fun j hj => by rw [hu j hj, Nat.zero_add]) hg]
  have e2 := sent_eq (maskAt W fresh) (ρg.val eps)
    (tabsOf ρg (k13Wit nR k t.input) (t.input.pile t.heard) (ρg.val (k13X t.heard))) k 0 []
    (gs.map ρg.val)
  rw [tabsOf_mat hmat]
  have e3 : foldsAll ([] : List GE)
      (tabsOf ρg (k13Wit nR k t.input) (t.input.pile t.heard) (ρg.val (k13X t.heard))) =
      tabsOf ρg (k13Wit nR k t.input) (t.input.pile t.heard) (ρg.val (k13X t.heard)) := rfl
  rw [e3] at e2
  rw [e2]
  rfl

/-! ## The row -/

/-- x is the last challenge in front. -/
theorem k13X_snoc (H : List Fmt.Drawn) (d : Fmt.Drawn) : k13X (H ++ [d]) = elemOf d := by
  unfold k13X
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.drop_left']
  · rfl
  · rfl

/-- No oracle message is stated at 2 + k rounds. -/
theorem none_stated (k : Nat) :
    List.replicate (2 + k) ([] : List Oracle) = [] :: [] :: List.replicate k [] := by
  rw [Nat.add_comm]
  rfl

/-- What the first round cuts, but for roots: nothing. -/
theorem items_sigma (p : Where) :
    ({ entry := VerifiableInference.Desc.K13.sigmaEntry p } : Fmt.DeclaredRound).items.filter
      (· != .root) = [] := by
  simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, VerifiableInference.Desc.K13.sigmaEntry]

/-- The round of the sum: one element. -/
theorem items_eps (p : Where) :
    ({ entry := VerifiableInference.Desc.K13.epsEntry p } : Fmt.DeclaredRound).items.filter
      (· != .root) = [Fmt.Item.e] := by
  simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, VerifiableInference.Desc.K13.epsEntry]

/-- A variable's round: two elements. -/
theorem items_round (p : Where) :
    ({ entry := VerifiableInference.Desc.K13.roundEntry p } : Fmt.DeclaredRound).items.filter
      (· != .root) = [Fmt.Item.e, Fmt.Item.e] := by
  simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, VerifiableInference.Desc.K13.roundEntry,
    List.replicate_succ]

/-- How many scalars the call's rounds send. -/
theorem k13_scalars (k : Nat) : scalarsOf (k13Shape k) = 1 :: List.replicate k 2 := by
  show [0 + 1] ++ (List.replicate k (Var.plain 3)).map (fun v => v.d - 1) ++ [] = _
  rw [List.map_replicate, List.append_nil]
  rfl

/-- The variables' rounds state two scalars each, and no oracle message. -/
theorem stated_rounds (p : Where) : ∀ n : Nat, StatedBy (List.replicate n 2)
    (List.replicate n
      (({ entry := VerifiableInference.Desc.K13.roundEntry p } : Fmt.DeclaredRound), []))
  | 0 => trivial
  | n + 1 => ⟨items_round p, rfl, stated_rounds p n⟩

/-- The sumcheck's part has one move for the sum and one for each variable. -/
theorem k13Sum_moves (p : Where) :
    (k13Sum p).moves.length = 1 + p.lin.kCol := by
  refine (moves_length (V := Unit) (runName indexMaskRun ⟨k13Place p, 1⟩ "sum") "no ends"
    (k13Job p.lin.matrixRows p.lin.kCol)).trans ?_
  rw [sumGs_length _ _ _ ⟨fun _ _ => 0, fun _ => []⟩ { heard := [], own := () }, k13_all]
  show 1 + (List.replicate p.lin.kCol (Var.plain 3)).length + 0 = _
  rw [List.length_replicate]
  rfl

/-- The kind's rounds are 2 + kCol. -/
theorem battRounds_length (p : Where) : (battRounds p).length = 2 + p.lin.kCol := by
  simp only [battRounds, List.length_cons, List.length_replicate]
  omega

/-- Rounds that open no tree and read no committed table read no column. -/
theorem readsOf_none (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) :
    ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = [] ∧ d.opens = []) → readsOf chain ft stored tree ds Rs = []
  | [], _, _ => by simp [readsOf]
  | _ :: _, [], _ => by simp [readsOf]
  | d :: ds, R :: Rs, h => by
    have ih := readsOf_none chain ft stored tree ds Rs fun e he => h e (List.mem_cons_of_mem _ he)
    simp only [readsOf, (h d List.mem_cons_self).1, (h d List.mem_cons_self).2, ih]
    rfl

/-- **The kind's rounds read no column.** -/
theorem k13_reads_none (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) (p : Where)
    (Rs : List Fmt.Drawn) : readsOf chain ft stored tree (battRounds p) Rs = [] :=
  readsOf_none chain ft stored tree _ Rs fun d hd => by
    unfold battRounds at hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨rfl, rfl⟩
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨rfl, rfl⟩
    rw [List.eq_of_mem_replicate hd]
    exact ⟨rfl, rfl⟩

variable {S Cl W₀ Rc Xi Tr X : Type}

/-- The row has one move for each of the kind's rounds. -/
theorem k13Half_rounds (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where) :
    (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile p).rounds = 2 + p.lin.kCol := by
  show 0 + (List.replicate 1 _).length + ((k13Sum p).moves.map _).length = _
  rw [List.length_map, k13Sum_moves, List.length_replicate]
  omega

/-- The parts of the kind's side are the row's. -/
theorem k13Pairs_parts {Pb : Type} (weights : W₀ → Weights) (pile : PileOf Xi)
    (p : Where) :
    (k13Pairs (Rc := Rc) (Tr := Tr) (X := X) (Pb := Pb) weights pile p).map (·.1) =
      k13Row weights pile p := rfl

/-- **THE LAW: `play` goes through on the kind's row, and what it shows, without the sealed digest,
are the rounds `movesAtM3`.** b: a sub-protocol with the kind's rounds. c: the coins that the row is
handed. m: where the run stands. d0, d1, dr: the challenges, which without the sealed digest are x,
eps and gs. W: the matrix that the index's reader gives, with mask entries; fresh: slots under which
these entries are the coins spent. -/
theorem k13_plays (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where)
    (b : Block S Cl)
    (hr : b.rounds = battRounds p) (ho : b.oracles = List.replicate (2 + p.lin.kCol) [])
    (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile p).parts)
    (m : Mid (Local W₀ Rc Xi Tr) X) (d0 d1 : Fmt.Drawn) (dr : List Fmt.Drawn) (x eps : E)
    (gs : List E) (h0 : bare d0 = k13Dr x) (h1 : bare d1 = k13Dr eps)
    (hrr : dr.map bare = gs.map k13Dr) (hg : gs.length = p.lin.kCol)
    (W : Wit GE p.lin.matrixRows p.lin.kCol)
    (hmat : W.mat = (k13Wit p.lin.matrixRows p.lin.kCol (k13Ask weights pile m.st.input)).mat)
    (fresh : List Slot)
    (hu : ∀ j, j < 2 * p.lin.kCol + 1 →
      ρg.val ((coinsE c.2.1.2.1.1).getD j zeroE) = maskAt W fresh j) :
    ∃ l, play ((proverSideOfClaimCombination weights pile p).steps b v c) (d0 :: d1 :: dr) [] m =
        .ok (l, ⟨⟨m.st.input, m.st.heard ++ d0 :: d1 :: dr, m.st.own⟩, m.loc ++ d0 :: d1 :: dr,
          m.seen ++ roundsOf l, m.opened⟩) ∧ tablesOf l = [] ∧
      (roundsOf l).map noDigest =
        movesAtM3 ρg k13E W (pile m.st.input.x (m.st.heard ++ [d0])) fresh x eps gs := by
  have hdl : dr.length = p.lin.kCol := by
    have := congrArg List.length hrr
    rw [List.length_map, List.length_map] at this
    omega
  -- the two parts, and the declared rounds, each with no oracle message
  let P0 : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X := quietPart
  let P1 : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
    (k13Sum p).lift (fun _ => ()) (k13Ask weights pile) (fun _ => ()) fun x _ => x
  let R0 : List (Fmt.DeclaredRound × List Oracle) :=
    [({ entry := VerifiableInference.Desc.K13.sigmaEntry p }, [])]
  let R1 : List (Fmt.DeclaredRound × List Oracle) :=
    ({ entry := VerifiableInference.Desc.K13.epsEntry p }, []) ::
      List.replicate p.lin.kCol ({ entry := VerifiableInference.Desc.K13.roundEntry p }, [])
  have hz : b.rounds.zip b.oracles = R0 ++ R1 := by
    rw [hr, ho, none_stated]
    show _ :: _ :: (List.replicate p.lin.kCol _).zip (List.replicate p.lin.kCol _) = _
    rw [List.zip_replicate']
    rfl
  have hlen : (d1 :: dr).length =
      (sumGs (runName indexMaskRun ⟨k13Place p, 1⟩ "sum") "no ends"
        (k13Job p.lin.matrixRows p.lin.kCol)).length := by
    rw [← moves_length (V := Unit)]
    show _ = (k13Sum p).moves.length
    rw [k13Sum_moves, List.length_cons, hdl]
    omega
  have hn : P1.moves.length = 1 + p.lin.kCol := by
    show ((k13Sum p).moves.map _).length = _
    rw [List.length_map, k13Sum_moves]
  have hR1 : R1.length = 1 + p.lin.kCol := by
    show (List.replicate p.lin.kCol _).length + 1 = _
    rw [List.length_replicate]
    omega
  have hsteps : (proverSideOfClaimCombination weights pile p).steps b v c =
      P0.steps b.name ⟨b.place, 0⟩ R0 v c.1 ++ P1.steps b.name ⟨b.place, 1⟩ R1 v c.2.1 := by
    show rowSteps b.name b.place v [P0, P1] 0 (b.rounds.zip b.oracles) c = _
    rw [hz]
    show P0.steps b.name ⟨b.place, 0⟩ R0 v c.1 ++
      (P1.steps b.name ⟨b.place, 1⟩ (R1.take P1.moves.length) v c.2.1 ++ []) = _
    rw [List.append_nil, List.take_of_length_le (by rw [hR1, hn])]
  -- the first part
  have hp0 := play_steps_whole P0 (fun _ _ => rfl) (fun _ _ _ => rfl) b.name ⟨b.place, 0⟩
    R0 v c.1 [d0] [] m [saidPlayed b.name ⟨b.place, 0⟩ ⟨[], d0⟩] (by
      exact fitsFrom_mvOf c.1 [0] R0 [fun _ _ _ => []] _ _ _ ⟨items_sigma p, rfl, trivial⟩
        ⟨fun _ _ => rfl, trivial⟩ rfl) rfl
  -- the second part
  let t1 : State (Local W₀ Rc Xi Tr) X := ⟨m.st.input, m.st.heard ++ [d0], m.st.own⟩
  let m1 : Mid (Local W₀ Rc Xi Tr) X := ⟨t1, m.loc ++ [d0], m.seen ++ [⟨[], d0⟩], m.opened⟩
  have hso := k13_sumOut (name := runName indexMaskRun ⟨k13Place p, 1⟩ "sum") (endName := "no ends")
    c.2.1 (t1.narrow (k13Ask weights pile) fun _ => ()) m1.shown W hmat fresh hu d1 dr eps gs h1 hrr
    hg
  have hp1 := plays_unit_sumPart (V := Local W₀ Rc Xi Tr) (X := X) (fun _ => ())
    (k13Ask weights pile) (runName indexMaskRun ⟨k13Place p, 1⟩ "sum") "no ends"
    (k13Job p.lin.matrixRows p.lin.kCol) c.2.1
    (fun v hv => by
      rw [List.eq_of_mem_replicate hv]
      exact Nat.le_succ 2)
    b.name ⟨b.place, 1⟩ R1 (by
      show StatedBy (scalarsOf (k13Shape p.lin.kCol)) R1
      rw [k13_scalars]
      exact ⟨items_eps p, rfl, stated_rounds p p.lin.kCol⟩) v (d1 :: dr) hlen [] m1
  -- the two joined
  refine ⟨saidPlayed b.name ⟨b.place, 0⟩ ⟨[], d0⟩ ::
    (sumOut (k13Job p.lin.matrixRows p.lin.kCol) c.2.1
      (t1.narrow (k13Ask weights pile) fun _ => ()) m1.shown (d1 :: dr)).map
      (saidPlayed b.name ⟨b.place, 1⟩), ?_, ?_, ?_⟩
  · rw [hsteps]
    show play _ ([d0] ++ d1 :: dr) [] m = _
    rw [play_append _ _ _ _ _ _ (by rfl), hp0]
    show ((play (P1.steps b.name ⟨b.place, 1⟩ R1 v c.2.1) (d1 :: dr) _ m1).map fun z => _) = _
    rw [List.drop_nil]
    refine (congrArg (Except.map _) hp1).trans ?_
    show Except.ok _ = Except.ok _
    have e2 : roundsOf (saidPlayed b.name ⟨b.place, 0⟩ ⟨[], d0⟩ ::
        (sumOut (k13Job p.lin.matrixRows p.lin.kCol) c.2.1
          (t1.narrow (k13Ask weights pile) fun _ => ()) m1.shown (d1 :: dr)).map
          (saidPlayed b.name ⟨b.place, 1⟩)) =
        ⟨[], d0⟩ :: sumOut (k13Job p.lin.matrixRows p.lin.kCol) c.2.1
          (t1.narrow (k13Ask weights pile) fun _ => ()) m1.shown (d1 :: dr) :=
      congrArg (_ :: ·) (roundsOf_said _ _ _)
    rw [e2]
    simp [m1, t1, List.append_assoc]
  · exact tablesOf_said b.name ⟨b.place, 1⟩ _
  · show noDigest ⟨[], d0⟩ :: (roundsOf ((sumOut _ _ _ _ _).map _)).map noDigest = _
    rw [roundsOf_said, hso]
    show (⟨[], bare d0⟩ : Fmt.RoundView) :: _ = _
    rw [h0]
    have ex : k13X (m.st.heard ++ [d0]) = x := by
      rw [k13X_snoc]
      have e : elemOf d0 = elemOf (bare d0) := rfl
      rw [e, h0]
      rfl
    show _ :: shownRound _ eps :: (codeRounds k13E (sent _ _ _ 0 (tabsOf ρg W
      (pile m.st.input.x (m.st.heard ++ [d0])) (ρg.val (k13X (m.st.heard ++ [d0])))) _)
      gs).map _ = _
    rw [ex]
    rfl

/-- **`play` goes through on the kind's row, AT EVERY COIN, wherever the run stands, and at every
list of challenges that fits the kind's rounds**, and leaves the run with these challenges heard and
the rounds shown, the columns opened as they were; no round has a table; and what is shown, without
the sealed digest, has the form of the rounds `movesAtM3`, at some matrix, mask entries, rows and
slots. Nothing is asked of the coins, of the input or of the pile's filler. -/
theorem k13_plays_form (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where) (b : Block S Cl)
    (hr : b.rounds = battRounds p) (ho : b.oracles = List.replicate (2 + p.lin.kCol) [])
    (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile p).parts)
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn)
    (hd : drawsFit (battRounds p) ds = true) :
    ∃ l, play ((proverSideOfClaimCombination weights pile p).steps b v c) ds [] m =
        .ok (l, ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
            m.seen ++ roundsOf l, m.opened⟩) ∧
      tablesOf l = [] ∧
      ∃ (W : Wit GE p.lin.matrixRows p.lin.kCol) (rows : List OnBytes.TensorRow)
        (fresh : List Slot) (x eps : E) (gs : List E), gs.length = p.lin.kCol ∧
        (roundsOf l).map noDigest = movesAtM3 ρg k13E W rows fresh x eps gs := by
  obtain ⟨x, eps, gs, hb, hg⟩ := fits_batt p ds hd
  match ds, hb with
  | d0 :: d1 :: dr, hb =>
    have hb' : bare d0 :: bare d1 :: dr.map bare = k13Dr x :: k13Dr eps :: gs.map k13Dr := hb
    obtain ⟨h0, hb''⟩ := List.cons.inj hb'
    obtain ⟨h1, hrr⟩ := List.cons.inj hb''
    obtain ⟨l, hp, htab, hrd⟩ := k13_plays weights pile p b hr ho v c m d0 d1 dr x eps gs h0 h1 hrr
      hg
      ⟨(k13Wit p.lin.matrixRows p.lin.kCol (k13Ask weights pile m.st.input)).mat,
        fun s => ρg.val ((coinsE c.2.1.2.1.1).getD s.index zeroE)⟩ rfl
      ((List.range (2 * p.lin.kCol + 1)).map fun j => ⟨0, j⟩) (fun j hj => by
        show _ = ρg.val ((coinsE c.2.1.2.1.1).getD
          (((List.range (2 * p.lin.kCol + 1)).map fun j => (⟨0, j⟩ : Slot)).getD j default).index
          zeroE)
        have e : ((List.range (2 * p.lin.kCol + 1)).map fun j => (⟨0, j⟩ : Slot)).getD j default =
            ⟨0, j⟩ := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
        rw [e])
    exact ⟨l, hp, htab, _, _, _, x, eps, gs, hg, hrd⟩
  | [], hb => cases hb
  | [d], hb =>
    have hb' : bare d :: [] = k13Dr x :: k13Dr eps :: gs.map k13Dr := hb
    exact absurd (List.cons.inj hb').2 (by simp)

/-- The first two of these alone. -/
theorem k13_plays_returns (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where) (b : Block S Cl)
    (hr : b.rounds = battRounds p) (ho : b.oracles = List.replicate (2 + p.lin.kCol) [])
    (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile p).parts)
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn)
    (hd : drawsFit (battRounds p) ds = true) :
    ∃ l, play ((proverSideOfClaimCombination weights pile p).steps b v c) ds [] m =
        .ok (l, ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
            m.seen ++ roundsOf l, m.opened⟩) ∧
      tablesOf l = [] := by
  obtain ⟨l, hp, ht, -⟩ := k13_plays_form weights pile p b hr ho v c m ds hd
  exact ⟨l, hp, ht⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_all
#print axioms ProofFile.Honest.K13.k13_poly
#print axioms ProofFile.Honest.K13.k13_sumOut
#print axioms ProofFile.Honest.K13.k13X_snoc
#print axioms ProofFile.Honest.K13.none_stated
#print axioms ProofFile.Honest.K13.items_sigma
#print axioms ProofFile.Honest.K13.items_eps
#print axioms ProofFile.Honest.K13.items_round
#print axioms ProofFile.Honest.K13.k13_scalars
#print axioms ProofFile.Honest.K13.stated_rounds
#print axioms ProofFile.Honest.K13.k13Sum_moves
#print axioms ProofFile.Honest.K13.battRounds_length
#print axioms ProofFile.Honest.K13.readsOf_none
#print axioms ProofFile.Honest.K13.k13_reads_none
#print axioms ProofFile.Honest.K13.k13Half_rounds
#print axioms ProofFile.Honest.K13.k13Pairs_parts
#print axioms ProofFile.Honest.K13.k13_plays
#print axioms ProofFile.Honest.K13.k13_plays_form
#print axioms ProofFile.Honest.K13.k13_plays_returns
#print axioms ProofFile.Honest.K13.k13X
