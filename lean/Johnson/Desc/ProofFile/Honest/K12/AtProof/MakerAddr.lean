-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/MakerAddr.lean

What it proves. Laws on the text of the maker of the book of random values: its addresses at a
proximity test: which part holds a round of the test; that the first fold behind a round in front of
the test, with no fold between, is the test's own first fold, of the first stage's k rounds, which
sends a root just where the place's numbers say so; that the pair (the fold's part, the part that
sends what the fold leaves) is the test's two parts; and so that the spender of the entry which the
maker lays for a fresh table sent in front of the test is the test's first part. On lists of
sub-protocols without their states' types (PlanB): so at two chains laid one behind the other too.
They read the declared rounds alone: no label and no list of sendings.

Names.
  addrIn_skip, addrIn_two, addrIn_at_test   the part that holds a round.
  drop_at, dropWhile_at, find_at            on a numbered list.
  layOpens_quiet, fold_roots                the test's second round and its root.
  names_run, get_front, get_test, test_names, name_round, name_seed, names_behind, test_len
      helpers: the rounds' names around a test.
  foldBehind_test, behindFold_test, spender_at_test   the laws.

By what. The texts of addrIn, foldBehind (Honest/BookFolds.lean), behindFold
(Honest/BookCarry.lean), H2U.layOpens, H2U.roundsOfNums (Johnson/Desc/K12/TestEntries.lean);
rounds_names, headRun_rep (MakerCut.lean); takeWhile_fst (MakerTies.lean).

Limits.
- The premise on the cut (hc) is cut_k12's conclusion (MakerCut.lean) at planOf's member of a
  sub-protocol of the kind K12: that step is a caller's.
- The premise that no "FOLD epsilon" stands between (hno) is on the description's rounds in front:
  it is paid at no description here.
- Not yet laws on the book that bookWhole returns.
- They move no count. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.MakerCut
import Johnson.Desc.ProofFile.Honest.K12.AtProof.MakerTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof

/-- The maker's "part that holds round number i" steps over the sub-protocols in front. -/
theorem addrIn_skip : ∀ (pre l : List PlanB) (i : ℕ),
    addrIn (pre ++ l) ((pre.flatMap (·.rounds)).length + i) = addrIn l i
  | [], l, i => by
    show addrIn l (0 + i) = addrIn l i
    rw [Nat.zero_add]
  | p :: pre, l, i => by
    have e0 : ((p :: pre).flatMap (·.rounds)).length + i =
        p.rounds.length + ((pre.flatMap (·.rounds)).length + i) := by
      rw [List.flatMap_cons, List.length_append, Nat.add_assoc]
    rw [e0]
    show (if p.rounds.length + ((pre.flatMap (·.rounds)).length + i) < p.rounds.length then _
      else addrIn (pre ++ l)
        (p.rounds.length + ((pre.flatMap (·.rounds)).length + i) - p.rounds.length)) = _
    rw [if_neg (by omega), Nat.add_sub_cancel_left, addrIn_skip pre l i]

/-- At a sub-protocol that is cut in two. -/
theorem addrIn_two (b : PlanB) (t : List PlanB) (a r i : ℕ) (hc : b.cut = [a, r])
    (hi : i < b.rounds.length) : addrIn (b :: t) i = some ⟨b.place, if i < a then 0 else 1⟩ := by
  show (if i < b.rounds.length then
    some (⟨b.place, (((b.cut.foldl (fun (l : List ℕ × ℕ) k => (l.1 ++ [l.2], l.2 + k))
      ([], 0)).1.filter (· ≤ i)).length - 1)⟩ : Addr) else _) = _
  rw [if_pos hi, hc]
  show some (⟨b.place, (([0, 0 + a] : List ℕ).filter (· ≤ i)).length - 1⟩ : Addr) = _
  rw [Nat.zero_add]
  by_cases h : i < a
  · simp [h]
  · have h' : a ≤ i := by omega
    simp [h, h']

/-- **Which part holds a round of a proximity test, by the maker's text**: the first part the first
firstLen rounds, the second part the rest. On a list of sub-protocols without their states' types:
so at two chains laid one behind the other too. hc: the cut is the pair's: at planOf of a
sub-protocol of the kind K12 that is cut_k12 (MakerCut.lean). -/
theorem addrIn_at_test (pre t : List PlanB) (b : PlanB) (N : H2U.TestNums)
    (hc : b.cut = [firstLen N.stages, restLen N.stages]) (i : ℕ) (hi : i < b.rounds.length) :
    addrIn (pre ++ b :: t) ((pre.flatMap (·.rounds)).length + i) =
      some ⟨b.place, if i < firstLen N.stages then 0 else 1⟩ := by
  rw [addrIn_skip]
  exact addrIn_two b t _ _ i hc hi

/-- A numbered list from its member number n on. -/
theorem drop_at {α : Type} (R : List α) (n : ℕ) (x : α) (hx : R[n]? = some x) :
    R.zipIdx.drop n = (x, n) :: R.zipIdx.drop (n + 1) := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hx
  have hl : n < R.zipIdx.length := by
    rw [List.length_zipIdx]
    exact hlt
  rw [List.drop_eq_getElem_cons hl, List.getElem_zipIdx, Nat.zero_add]

/-- On a numbered list: dropping while a test on the first field says yes, from number i + 1 on,
stops at the first member from there on at which it says no. -/
theorem dropWhile_at {α : Type} (p : α → Bool) (R : List α) (x : α) : ∀ (d i n : ℕ), i + 1 + d = n →
    R[n]? = some x → p x = false →
    (∀ j y, i + 1 ≤ j → j < n → R[j]? = some y → p y = true) →
    (R.zipIdx.drop (i + 1)).dropWhile (fun r => p r.1) = (x, n) :: R.zipIdx.drop (n + 1)
  | 0, i, n, hd, hx, hpx, _ => by
    obtain rfl : i + 1 = n := hd
    rw [drop_at R (i + 1) x hx, List.dropWhile_cons, hpx]
    rfl
  | d + 1, i, n, hd, hx, hpx, hb => by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hx
    have hy : R[i + 1]? = some (R[i + 1]'(by omega)) := List.getElem?_eq_getElem (by omega)
    have hp := hb (i + 1) _ (Nat.le_refl _) (by omega) hy
    rw [drop_at R (i + 1) _ hy, List.dropWhile_cons, hp]
    exact dropWhile_at p R x d (i + 1) n (by omega) hx hpx
      fun j y h1 h2 h3 => hb j y (by omega) h2 h3

/-- On a numbered list: the first member from number i + 1 on at which a test on the first field
says yes. -/
theorem find_at {α : Type} (q : α → Bool) (R : List α) (x : α) : ∀ (d i n : ℕ), i + 1 + d = n →
    R[n]? = some x → q x = true →
    (∀ j y, i + 1 ≤ j → j < n → R[j]? = some y → q y = false) →
    (R.zipIdx.drop (i + 1)).find? (fun r => q r.1) = some (x, n)
  | 0, i, n, hd, hx, hqx, _ => by
    obtain rfl : i + 1 = n := hd
    rw [drop_at R (i + 1) x hx, List.find?_cons, hqx]
  | d + 1, i, n, hd, hx, hqx, hb => by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hx
    have hy : R[i + 1]? = some (R[i + 1]'(by omega)) := List.getElem?_eq_getElem (by omega)
    have hq := hb (i + 1) _ (Nat.le_refl _) (by omega) hy
    rw [drop_at R (i + 1) _ hy, List.find?_cons, hq]
    exact find_at q R x d (i + 1) n (by omega) hx hqx
      fun j y h1 h2 h3 => hb j y (by omega) h2 h3

/-- layOpens at a round that opens no tree. -/
theorem layOpens_quiet (own seen : Bool) (r : Fmt.Round) (rs : List Fmt.Round)
    (l : List (List (Fmt.Shape × Fmt.TreeSource))) (ho : r.opens.isEmpty = true) :
    H2U.layOpens own seen (r :: rs) l =
      (H2U.layOpens own (seen || r.entry.name == "FOLD epsilon") rs l).map
        (⟨if own && !seen && (r.entry.name == "FOLD epsilon") then
          { r.entry with msg := 32 + r.entry.msg, roots := 1 } else r.entry, [], []⟩ :: ·) := by
  simp only [H2U.layOpens, ho, if_true]

/-- The test's second declared round, "FOLD epsilon", sends a root just where the place's numbers
say that the first fold sends its own fresh table. -/
theorem fold_roots (N : H2U.TestNums) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : N.stages = s :: next :: rest) (ds : List Fmt.DeclaredRound)
    (h : H2U.roundsOfNums N = some ds) :
    ∃ d, ds[1]? = some d ∧ (d.entry.roots != 0) = N.ownMask := by
  unfold H2U.roundsOfNums at h
  rw [hst] at h
  have h' : H2U.layOpens N.ownMask false
      ({ Fmt.M1.rBat with entry := { Fmt.M1.rBat.entry with rows := N.rows } } ::
        Fmt.M1.rEps "FOLD epsilon" ::
        (List.replicate s.k (Fmt.M1.rTwo "FOLD round") ++
          [Fmt.M1.rSeed next, Fmt.M1.rCs N.work s 0 0] ++
          Fmt.M1.laterRounds N.work (0 + 1) (Fmt.M1.wMid next) next rest)) _ = some ds := h
  rw [layOpens_quiet _ _ _ _ _ rfl, layOpens_quiet _ _ _ _ _ rfl] at h'
  obtain ⟨l1, h1, rfl⟩ := Option.map_eq_some_iff.1 h'
  obtain ⟨l2, -, rfl⟩ := Option.map_eq_some_iff.1 h1
  refine ⟨_, rfl, ?_⟩
  cases N.ownMask <;> rfl

/-- The run of a name at the head of declared rounds is the run at the head of their names. -/
theorem names_run (s : String) (l : List Fmt.DeclaredRound) :
    (l.takeWhile fun r => r.entry.name == s).length = headRun s (l.map (·.entry.name)) := by
  unfold headRun
  rw [List.takeWhile_map, List.length_map]
  rfl

/-- A round in front of the sub-protocol b. -/
theorem get_front (pre t : List PlanB) (b : PlanB) (j : ℕ)
    (hj : j < (pre.flatMap (·.rounds)).length) :
    ((pre ++ b :: t).flatMap (·.rounds))[j]? = (pre.flatMap (·.rounds))[j]? := by
  rw [List.flatMap_append, List.getElem?_append_left hj]

/-- A round of the sub-protocol b. -/
theorem get_test (pre t : List PlanB) (b : PlanB) (j : ℕ) (hj : j < b.rounds.length) :
    ((pre ++ b :: t).flatMap (·.rounds))[(pre.flatMap (·.rounds)).length + j]? = b.rounds[j]? := by
  rw [List.flatMap_append, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.flatMap_cons, List.getElem?_append_left hj]

/-- The name of a test's round number j. -/
theorem test_names (b : PlanB) (N : H2U.TestNums) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : N.stages = s :: next :: rest)
    (hr : H2U.roundsOfNums N = some b.rounds) (j : ℕ) :
    (b.rounds[j]?).map (·.entry.name) =
      ("BAT" :: "FOLD epsilon" :: (List.replicate s.k "FOLD round" ++
        "SEND seed" :: "CS" :: laterNames next rest))[j]? := by
  rw [← List.getElem?_map, rounds_names N s next rest hst b.rounds hr]
  rfl

/-- The names of a test's rounds: a round of the first fold. -/
theorem name_round (k j : ℕ) (hj : j < k) (Z : List String) :
    (("BAT" : String) :: "FOLD epsilon" :: (List.replicate k "FOLD round" ++ Z))[2 + j]? =
      some "FOLD round" := by
  rw [Nat.add_comm]
  show (List.replicate k ("FOLD round" : String) ++ Z)[j]? = _
  rw [List.getElem?_append_left (by rw [List.length_replicate]; exact hj), List.getElem?_replicate,
    if_pos hj]

/-- The first switch's sending. -/
theorem name_seed (k : ℕ) (Z : List String) :
    (("BAT" : String) :: "FOLD epsilon" ::
      (List.replicate k "FOLD round" ++ "SEND seed" :: Z))[2 + k]? = some "SEND seed" := by
  rw [Nat.add_comm]
  show (List.replicate k ("FOLD round" : String) ++ "SEND seed" :: Z)[k]? = _
  rw [List.getElem?_append_right (by rw [List.length_replicate]), List.length_replicate,
    Nat.sub_self]
  rfl

/-- The names behind a test's "FOLD epsilon". -/
theorem names_behind (pre t : List PlanB) (b : PlanB) (N : H2U.TestNums) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : N.stages = s :: next :: rest)
    (hr : H2U.roundsOfNums N = some b.rounds) :
    (((pre ++ b :: t).flatMap (·.rounds)).drop
      ((pre.flatMap (·.rounds)).length + 1 + 1)).map (·.entry.name) =
      List.replicate s.k "FOLD round" ++ "SEND seed" ::
        ("CS" :: laterNames next rest ++ (t.flatMap (·.rounds)).map (·.entry.name)) := by
  rw [List.flatMap_append, Nat.add_assoc, List.drop_append,
    List.drop_of_length_le (Nat.le_add_right _ _), List.nil_append, Nat.add_sub_cancel_left,
    List.flatMap_cons, List.map_drop, List.map_append,
    rounds_names N s next rest hst b.rounds hr]
  show ((("BAT" : String) :: "FOLD epsilon" :: (List.replicate s.k "FOLD round" ++
    "SEND seed" :: "CS" :: laterNames next rest)) ++ _).drop 2 = _
  simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.append_assoc]

/-- A test of two stages or more has at least these rounds. -/
theorem test_len (b : PlanB) (N : H2U.TestNums) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : N.stages = s :: next :: rest)
    (hr : H2U.roundsOfNums N = some b.rounds) : 2 + s.k + 2 ≤ b.rounds.length := by
  have e := congrArg List.length (rounds_names N s next rest hst b.rounds hr)
  rw [List.length_map] at e
  rw [e]
  show 2 + s.k + 2 ≤ (("BAT" : String) :: "FOLD epsilon" :: (List.replicate s.k "FOLD round" ++
    "SEND seed" :: "CS" :: laterNames next rest)).length
  simp only [List.length_cons, List.length_append, List.length_replicate]
  omega

/-- **The first fold behind a round in front of a proximity test is the test's own first fold**,
where no "FOLD epsilon" stands between: its round is the test's second; whether it sends a root is
the place's flag; it has the first stage's k rounds. n: the rounds in front of the test. -/
theorem foldBehind_test (pre t : List PlanB) (b : PlanB) (N : H2U.TestNums)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : N.stages = s :: next :: rest)
    (hr : H2U.roundsOfNums N = some b.rounds) (i n : ℕ)
    (hn : n = (pre.flatMap (·.rounds)).length) (hi : i ≤ n)
    (hno : ∀ j y, i + 1 ≤ j → j < n → (pre.flatMap (·.rounds))[j]? = some y →
      (y.entry.name != "FOLD epsilon") = true) :
    foldBehind (pre ++ b :: t) i = some (n + 1, N.ownMask, s.k) := by
  subst hn
  obtain ⟨d, hd, hroot⟩ := fold_roots N s next rest hst b.rounds hr
  have hlen := test_len b N s next rest hst hr
  have hdn : d.entry.name = "FOLD epsilon" := by
    have e := test_names b N s next rest hst hr 1
    rw [hd] at e
    exact Option.some.inj e
  have hR1 : ((pre ++ b :: t).flatMap (·.rounds))[(pre.flatMap (·.rounds)).length + 1]? =
      some d := by
    rw [get_test pre t b 1 (by omega), hd]
  have hbefore : ∀ j y, i + 1 ≤ j → j < (pre.flatMap (·.rounds)).length + 1 →
      ((pre ++ b :: t).flatMap (·.rounds))[j]? = some y →
      (fun r : Fmt.DeclaredRound => r.entry.name != "FOLD epsilon") y = true := by
    intro j y h1 h2 h3
    by_cases hj : j < (pre.flatMap (·.rounds)).length
    · rw [get_front pre t b j hj] at h3
      exact hno j y h1 hj h3
    · obtain rfl : j = (pre.flatMap (·.rounds)).length + 0 := by omega
      rw [get_test pre t b 0 (by omega)] at h3
      have e := test_names b N s next rest hst hr 0
      rw [h3] at e
      have e' : y.entry.name = "BAT" := Option.some.inj e
      show (y.entry.name != "FOLD epsilon") = true
      rw [e']
      decide
  have hpd : (fun r : Fmt.DeclaredRound => r.entry.name != "FOLD epsilon") d = false := by
    show (d.entry.name != "FOLD epsilon") = false
    rw [hdn]
    decide
  have hdw := dropWhile_at (fun r : Fmt.DeclaredRound => r.entry.name != "FOLD epsilon")
    ((pre ++ b :: t).flatMap (·.rounds)) d ((pre.flatMap (·.rounds)).length - i) i
    ((pre.flatMap (·.rounds)).length + 1) (by omega) hR1 hpd hbefore
  have hrun : ((((pre ++ b :: t).flatMap (·.rounds)).zipIdx.drop
      ((pre.flatMap (·.rounds)).length + 1 + 1)).takeWhile
        fun r => r.1.entry.name == "FOLD round").length = s.k := by
    rw [takeWhile_fst (fun r : Fmt.DeclaredRound => r.entry.name == "FOLD round"), List.map_drop,
      List.zipIdx_map_fst, names_run, names_behind pre t b N s next rest hst hr,
      headRun_rep "FOLD round" "SEND seed" (by decide)]
  unfold foldBehind
  dsimp only
  rw [hdw]
  show some ((pre.flatMap (·.rounds)).length + 1, d.entry.roots != 0,
    ((((pre ++ b :: t).flatMap (·.rounds)).zipIdx.drop
      ((pre.flatMap (·.rounds)).length + 1 + 1)).takeWhile
        fun r => r.1.entry.name == "FOLD round").length) = _
  rw [hrun, hroot]

/-- **And the pair (the fold's part, the part that sends what the fold leaves) is the test's two
parts.** -/
theorem behindFold_test (pre t : List PlanB) (b : PlanB) (N : H2U.TestNums)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : N.stages = s :: next :: rest)
    (hr : H2U.roundsOfNums N = some b.rounds)
    (hc : b.cut = [firstLen N.stages, restLen N.stages]) (i n : ℕ)
    (hn : n = (pre.flatMap (·.rounds)).length) (hi : i ≤ n)
    (hno : ∀ j y, i + 1 ≤ j → j < n → (pre.flatMap (·.rounds))[j]? = some y →
      (y.entry.name != "FOLD epsilon") = true) :
    behindFold (pre ++ b :: t) i = some (⟨b.place, 0⟩, ⟨b.place, 1⟩) := by
  have h0 := foldBehind_test pre t b N s next rest hst hr i n hn hi hno
  subst hn
  have hlen := test_len b N s next rest hst hr
  have hfl : firstLen N.stages = 2 + s.k := by
    rw [hst]
    rfl
  obtain ⟨z, hz, hzn⟩ : ∃ z, b.rounds[2 + s.k]? = some z ∧ z.entry.name = "SEND seed" := by
    have e := test_names b N s next rest hst hr (2 + s.k)
    rw [name_seed] at e
    obtain ⟨z, hz, hzn⟩ := Option.map_eq_some_iff.1 e
    exact ⟨z, hz, hzn⟩
  have hRz : ((pre ++ b :: t).flatMap (·.rounds))[(pre.flatMap (·.rounds)).length + (2 + s.k)]? =
      some z := by
    rw [get_test pre t b (2 + s.k) (by omega), hz]
  have hbetween : ∀ j y, (pre.flatMap (·.rounds)).length + 1 + 1 ≤ j →
      j < (pre.flatMap (·.rounds)).length + (2 + s.k) →
      ((pre ++ b :: t).flatMap (·.rounds))[j]? = some y →
      (fun r : Fmt.DeclaredRound => r.entry.name == "SEND seed") y = false := by
    intro j y h1 h2 h3
    obtain ⟨u, rfl⟩ : ∃ u, j = (pre.flatMap (·.rounds)).length + (2 + u) :=
      ⟨j - (pre.flatMap (·.rounds)).length - 2, by omega⟩
    rw [get_test pre t b (2 + u) (by omega)] at h3
    have e := test_names b N s next rest hst hr (2 + u)
    rw [h3, name_round s.k u (by omega)] at e
    have e' : y.entry.name = "FOLD round" := Option.some.inj e
    show (y.entry.name == "SEND seed") = false
    rw [e']
    decide
  have hqz : (fun r : Fmt.DeclaredRound => r.entry.name == "SEND seed") z = true := by
    show (z.entry.name == "SEND seed") = true
    rw [hzn]
    decide
  have hfind := find_at (fun r : Fmt.DeclaredRound => r.entry.name == "SEND seed")
    ((pre ++ b :: t).flatMap (·.rounds)) z s.k ((pre.flatMap (·.rounds)).length + 1)
    ((pre.flatMap (·.rounds)).length + (2 + s.k)) (by omega) hRz hqz hbetween
  unfold behindFold
  rw [h0]
  show ((((((pre ++ b :: t).flatMap (·.rounds)).zipIdx.drop
    ((pre.flatMap (·.rounds)).length + 1 + 1)).find?
      fun r => r.1.entry.name == "SEND seed").bind fun x => addrIn (pre ++ b :: t) x.2).bind
    fun q => (addrIn (pre ++ b :: t) ((pre.flatMap (·.rounds)).length + 1)).map
      fun p => (p, q)) = _
  rw [hfind]
  show ((addrIn (pre ++ b :: t) ((pre.flatMap (·.rounds)).length + (2 + s.k))).bind
    fun q => (addrIn (pre ++ b :: t) ((pre.flatMap (·.rounds)).length + 1)).map
      fun p => (p, q)) = _
  rw [addrIn_at_test pre t b N hc (2 + s.k) (by omega), addrIn_at_test pre t b N hc 1 (by omega),
    hfl, if_neg (by omega), if_pos (by omega)]
  rfl

/-- **So the spender of the entry that the maker lays for a fresh table sent in front of a proximity
test, with no fold between, is the test's first part.** -/
theorem spender_at_test (pre t : List PlanB) (b : PlanB) (N : H2U.TestNums)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : N.stages = s :: next :: rest)
    (hr : H2U.roundsOfNums N = some b.rounds)
    (hc : b.cut = [firstLen N.stages, restLen N.stages]) (i n : ℕ)
    (hn : n = (pre.flatMap (·.rounds)).length) (hi : i ≤ n)
    (hno : ∀ j y, i + 1 ≤ j → j < n → (pre.flatMap (·.rounds))[j]? = some y →
      (y.entry.name != "FOLD epsilon") = true) (f k : ℕ) (r : Bool)
    (hf : foldBehind (pre ++ b :: t) i = some (f, r, k)) :
    addrIn (pre ++ b :: t) f = some ⟨b.place, 0⟩ ∧ k = s.k ∧ r = N.ownMask := by
  have h0 := foldBehind_test pre t b N s next rest hst hr i n hn hi hno
  rw [h0] at hf
  obtain ⟨rfl, rfl, rfl⟩ : n + 1 = f ∧ N.ownMask = r ∧ s.k = k := by
    have e := Option.some.inj hf
    exact ⟨congrArg (·.1) e, congrArg (·.2.1) e, congrArg (·.2.2) e⟩
  refine ⟨?_, rfl, rfl⟩
  subst hn
  have hlen := test_len b N s next rest hst hr
  rw [addrIn_at_test pre t b N hc 1 (by omega), hst]
  show some (⟨b.place, if 1 < 2 + s.k then 0 else 1⟩ : Addr) = _
  rw [if_pos (by omega)]

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.addrIn_skip
#print axioms ProofFile.Honest.K12.AtProof.addrIn_two
#print axioms ProofFile.Honest.K12.AtProof.addrIn_at_test
#print axioms ProofFile.Honest.K12.AtProof.drop_at
#print axioms ProofFile.Honest.K12.AtProof.dropWhile_at
#print axioms ProofFile.Honest.K12.AtProof.find_at
#print axioms ProofFile.Honest.K12.AtProof.layOpens_quiet
#print axioms ProofFile.Honest.K12.AtProof.fold_roots
#print axioms ProofFile.Honest.K12.AtProof.names_run
#print axioms ProofFile.Honest.K12.AtProof.get_front
#print axioms ProofFile.Honest.K12.AtProof.get_test
#print axioms ProofFile.Honest.K12.AtProof.test_names
#print axioms ProofFile.Honest.K12.AtProof.name_round
#print axioms ProofFile.Honest.K12.AtProof.name_seed
#print axioms ProofFile.Honest.K12.AtProof.names_behind
#print axioms ProofFile.Honest.K12.AtProof.test_len
#print axioms ProofFile.Honest.K12.AtProof.foldBehind_test
#print axioms ProofFile.Honest.K12.AtProof.behindFold_test
#print axioms ProofFile.Honest.K12.AtProof.spender_at_test
