-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Fast/Says.lean: the closing of a segment (K10): functions, meant for a test program,
that return what the honest prover's part for this kind sends in chosen rounds, and that make the part's data once for
all the chosen rounds. With theorems: what they return is what the part shows when it is played by `play`
(Honest/Frame.lean). Definitions with code, and theorems.

The setting. The part is `closePart (foldShellT true J foldWords)` (Honest/K10/Half.lean, Sim.lean), where J is a job
(`CloseJob`, Honest/K10/Job.lean): the parameters of one place. Write k for `J.pub.par.k`. The part has 2 + k rounds,
numbered from 0: "BAT" (nothing is sent), "FOLD epsilon" (one element), and k times "FOLD round" (two elements each). In
each of the last k + 1 rounds its move makes the closing's data anew (`closeAsk`, Job.lean: among them two tables).
`plays_is` (Honest/K10/SimSent.lean) proves that the played rounds are `saysAt` at one value of the data, `askZero`: the
data made with 0 for each coin of the run that the part spends; `saysAt` lays the run in afterwards. The functions here
evaluate that right-hand side. One thing differs on purpose. Where the data are not made (`askZero` is `none`), no move
of the part returns an error: it sends what the fold's words say of empty tables. The functions here return an error
there, so that a caller sees it.

  `askZeroF`, `askZeroF_eq`   `askZero` with `closeAskF` (Honest/K10/Fast/Tables.lean) in the place of `closeAsk`; the
                   two return the same
  `closeData`, `closeData_ok`, `closeData_error`   the data by `closeAskF`, or an error whose words begin with
                   "K10: the closing has no data". Where it returns data A, `askZero` is `some A`; where it returns an
                   error, `askZero` is `none`
  `saysOf`         for each round number of a list: the items of `saysAt` at data A
  `closeSaysAt`, `closeSays`   the function at a job J. It asks three tests of its arguments: there are 2 + k
                   challenges; each has drawn just one element; each asked round number is below 2 + k. Then it calls
                   `closeData` once, and then `saysOf`. `closeSays` takes the challenges as one list; `closeSaysAt`
                   takes them apart
  `closeSays_shape`, `closeSaysAt_ok`   where the function returns a value: the three tests have passed, `askZero` is
                   `some A`, and the value is `saysOf` at A. So it returns no value where the data are not made
  `get_of_range`   on lists: if the image of l under f is the image of 0 .. n - 1 under g, then l has a member number j
                   for each j below n, and f of it is g j
  **`closeSays_plays`**, **`closeSays_is`**   let m be any state of a run, c any coins of the part, and let `closeSays`
                   return L at m's input, `m.shown` and heard challenges and at c. Then `play` of the part's steps
                   from m returns a value y, and for each asked round number j the played round number j exists and its
                   items are L's member for j. The second theorem says the same of a given y
  **`closeSays_none`**   where the three tests pass and `closeSays` returns an error, `askZero` is `none`: the case in
                   which the part sends the words at empty tables (`askWith`, SimSent.lean)
  `closeCoins`, `closeCoins_of`   the coins that a book of coins gives the part at a place: the value of `lendRow`
                   (Honest/Frame.lean) at the list of this one part, without the list's empty tail
  **`steps_close_at`**   `steps_close` (Honest/K10/Thr/Plays.lean) says "for some value of the part's coins"; here the
                   value is named. Where `chainSteps` (Honest/Frame.lean) returns for the closing's block alone,
                   `closeCoins` returns, and the steps are the part's steps at the coins that it returns
  `jobSays`, **`jobSays_is`**   `closeSays` at the coins of `closeCoins`. Where `chainSteps` returns l for the block
                   alone, `play` of l returns y, and `jobSays` returns L: for each asked round number j the played round
                   number j exists and its items are L's member for j

The form of the conclusion: `L.map some = js.map fun j => (y.1[j]?).map (·.vals)`. L has one member for each asked
number, in the order asked. That member is the field `vals` of the played round: the round's items as words, the form in
which a view or a stored run holds them (`Fmt.RoundView.vals`). `plays_is` also says that no round sends a table; that is not
repeated.

The type of the coins. The part is two parts joined: the one for "BAT", which has no coin, and the fold's. Its coins are
typed at the joined counts, and `handSnd` (Honest/Frame.lean) takes the fold's share out of them. `closeSays` takes that
share, as `spentRun` and `askOr` (Sim.lean) do: its type names neither V nor X (the types of what a part's second stop
may read and of the prover's own state). `closeCoins` and `jobSays` name the part, so they are typed at V and X; in
`jobSays` the two are explicit arguments, because no other argument fixes them.

Limits. Nothing is measured here: no time and no memory. That the data are made once is read in the text, and of
compiled code: `closeData` is an argument of `Except.map`, outside the map over the round numbers, and compiled code
evaluates an argument before the call; no line tests it. What a round costs beside the data is the cost of
`foldWords.round` (Honest/K10/Words.lean), which is called as the part calls it. The functions do not check: that w, sn
and h0 are the input, what was shown and the heard challenges of any run; that the data's arrays have the tables'
sizes (`askFits`, Words.lean), or are the tables of anything that was sent; of a challenge, more than that it drew one
element (`drawFit`, Honest/Frame.lean, asks more). `closeSays` does not check that c comes from a book. Of the tests of
`chainSteps`, `jobSays` asks the lending alone: not the cut, not the number of rounds, not the rows and entries for
parts that are not there; and it asks none of the book's own tests. So it may return a value where `chainSteps` returns
an error; in `jobSays_is` that `chainSteps` returns is a premise. The theorems speak of `play` at the steps of this one
block, with no stored rounds to fall back on (the empty list), as `plays_is` does: nothing is proved of a whole chain's
play. J is a variable: nothing is asked of `J.stAt` or `J.rows`. An error's words are for a reader: no theorem speaks of
them. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.SimSent
import Johnson.Desc.ProofFile.Honest.K10.Fast.Tables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E zeroE)
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par entries)

variable {V W X : Type}

/-! ## 1 The closing's data, with the tables built the faster way -/

/-- `askZero` (Honest/K10/SimSent.lean) with `closeAskF` in the place of `closeAsk`: the closing's data, made with 0 for
each coin of the run that is spent; nothing where the making returns an error or no statement is at hand. -/
def askZeroF (J : CloseJob W) (w : W) (sn : Seen) (h0 : List Fmt.Drawn) (d0 : Fmt.Drawn)
    (ca : CsAll (closeCarries J.pub)) : Option FoldAsk :=
  (closeAskF J w sn h0 d0 (fun _ => zeroE) ca).toOption.join

/-- `askZeroF` returns what `askZero` returns, at all arguments. -/
theorem askZeroF_eq (J : CloseJob W) (w : W) (sn : Seen) (h0 : List Fmt.Drawn) (d0 : Fmt.Drawn)
    (ca : CsAll (closeCarries J.pub)) : askZeroF J w sn h0 d0 ca = askZero J w sn h0 d0 ca := by
  unfold askZeroF askZero
  rw [closeAskF_eq]

/-- **The same data, or an error in words.** An error where `closeAskF` returns one, with its words behind this file's,
and where it returns nothing (no statement is at hand): the two cases in which `askZeroF` is `none`. -/
def closeData (J : CloseJob W) (w : W) (sn : Seen) (h0 : List Fmt.Drawn) (d0 : Fmt.Drawn)
    (ca : CsAll (closeCarries J.pub)) : Except String FoldAsk :=
  match closeAskF J w sn h0 d0 (fun _ => zeroE) ca with
  | .ok (some A) => .ok A
  | .ok none => .error "K10: the closing has no data: no statement is at hand"
  | .error e => .error ("K10: the closing has no data: " ++ e)

/-- Where `closeData` returns data A, `askZero` is `some A`. -/
theorem closeData_ok (J : CloseJob W) (w : W) (sn : Seen) (h0 : List Fmt.Drawn) (d0 : Fmt.Drawn)
    (ca : CsAll (closeCarries J.pub)) (A : FoldAsk) (h : closeData J w sn h0 d0 ca = .ok A) :
    askZero J w sn h0 d0 ca = some A := by
  rw [← askZeroF_eq]
  unfold closeData at h
  unfold askZeroF
  cases hq : closeAskF J w sn h0 d0 (fun _ => zeroE) ca with
  | error _ =>
    rw [hq] at h
    exact nomatch h
  | ok o =>
    rw [hq] at h
    cases o with
    | none => exact nomatch h
    | some B => exact congrArg some (Except.ok.inj h)

/-- Where `closeData` returns an error, `askZero` is `none`. -/
theorem closeData_error (J : CloseJob W) (w : W) (sn : Seen) (h0 : List Fmt.Drawn) (d0 : Fmt.Drawn)
    (ca : CsAll (closeCarries J.pub)) (e : String) (h : closeData J w sn h0 d0 ca = .error e) :
    askZero J w sn h0 d0 ca = none := by
  rw [← askZeroF_eq]
  unfold closeData at h
  unfold askZeroF
  cases hq : closeAskF J w sn h0 d0 (fun _ => zeroE) ca with
  | error _ => rfl
  | ok o =>
    rw [hq] at h
    cases o with
    | none => rfl
    | some B => exact nomatch h

/-! ## 2 What the part sends at chosen rounds -/

/-- The items of `saysAt` at data A, for each round number of the list js, in the list's order. u: the run that is
spent. d1: what "FOLD epsilon" drew. gs: what the rounds "FOLD round" drew. -/
def saysOf (J : CloseJob W) (A : FoldAsk) (u : Fin (2 * J.pub.par.k + 1) → E) (d1 : Fmt.Drawn)
    (gs : List Fmt.Drawn) (js : List Nat) : List (List Fmt.ItemValue) :=
  js.map fun j => (saysAt J (some A) u d1 gs j).vals.map Said.got

/-- `closeSays` at challenges that are taken apart: d0: what "BAT" drew; d1: what "FOLD epsilon" drew; gs: what the
rounds "FOLD round" drew. The three tests, each with an error of its own; then the data, once; then `saysOf`. -/
def closeSaysAt (J : CloseJob W) (w : W) (sn : Seen) (h0 : List Fmt.Drawn) (d0 d1 : Fmt.Drawn)
    (gs : List Fmt.Drawn) (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (js : List Nat) :
    Except String (List (List Fmt.ItemValue)) :=
  if gs.length = J.pub.par.k then
    if (d0 :: d1 :: gs).all (fun d => d.elems.length == 1) then
      if js.all (fun j => decide (j < 2 + J.pub.par.k)) then
        (closeData J w sn h0 d0 c.2.2).map fun A => saysOf J A (spentRun J c) d1 gs js
      else .error "K10: a round is asked for that the part does not have"
    else .error "K10: a challenge has not drawn just one element"
  else .error "K10: the challenges are not as many as the part's rounds"

/-- **What the closing's part sends at the rounds js**, from 0 ("BAT"), each round's items as a view shows them. w: the
input. sn, h0: what was shown and the challenges heard before the part. ds: the part's own 2 + k challenges. c: the
fold's share of the part's coins. The data are made once. An error if there are not 2 + k challenges, if one of them has
not drawn just one element, if a number of js is not below 2 + k, or if the data are not made (`closeData`). -/
def closeSays (J : CloseJob W) (w : W) (sn : Seen) (h0 ds : List Fmt.Drawn)
    (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (js : List Nat) :
    Except String (List (List Fmt.ItemValue)) :=
  match ds with
  | d0 :: d1 :: gs => closeSaysAt J w sn h0 d0 d1 gs c js
  | _ => .error "K10: the challenges are not as many as the part's rounds"

/-- Where `closeSays` returns a value, the list of challenges has at least two members, and the value is
`closeSaysAt`'s. -/
theorem closeSays_shape (J : CloseJob W) (w : W) (sn : Seen) (h0 ds : List Fmt.Drawn)
    (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (js : List Nat) (L : List (List Fmt.ItemValue))
    (hL : closeSays J w sn h0 ds c js = .ok L) :
    ∃ d0 d1 gs, ds = d0 :: d1 :: gs ∧ closeSaysAt J w sn h0 d0 d1 gs c js = .ok L := by
  cases ds with
  | nil => exact nomatch hL
  | cons d0 t =>
    cases t with
    | nil => exact nomatch hL
    | cons d1 gs => exact ⟨d0, d1, gs, rfl, hL⟩

/-- Where `closeSaysAt` returns a value, its three tests have passed, `askZero` is `some A`, and the value is `saysOf`
at A. -/
theorem closeSaysAt_ok (J : CloseJob W) (w : W) (sn : Seen) (h0 : List Fmt.Drawn) (d0 d1 : Fmt.Drawn)
    (gs : List Fmt.Drawn) (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (js : List Nat)
    (L : List (List Fmt.ItemValue)) (hL : closeSaysAt J w sn h0 d0 d1 gs c js = .ok L) :
    gs.length = J.pub.par.k ∧ (∀ d ∈ d0 :: d1 :: gs, d.elems.length = 1) ∧
      (∀ j ∈ js, j < 2 + J.pub.par.k) ∧
      ∃ A, askZero J w sn h0 d0 c.2.2 = some A ∧ L = saysOf J A (spentRun J c) d1 gs js := by
  unfold closeSaysAt at hL
  split at hL
  · rename_i hk
    split at hL
    · rename_i h1
      split at hL
      · rename_i hj
        cases hA : closeData J w sn h0 d0 c.2.2 with
        | error _ =>
          rw [hA] at hL
          exact nomatch hL
        | ok A =>
          rw [hA] at hL
          exact ⟨hk, fun d hd => beq_iff_eq.1 (List.all_eq_true.1 h1 d hd),
            fun j hm => of_decide_eq_true (List.all_eq_true.1 hj j hm), A,
            closeData_ok J w sn h0 d0 c.2.2 A hA, (Except.ok.inj hL).symm⟩
      · exact nomatch hL
    · exact nomatch hL
  · exact nomatch hL

/-! ## 3 It is what the frame's own play of the part shows -/

/-- A list whose image under f is the image of 0 .. n - 1 under g has, at a number j below n, a member whose image under
f is g j. -/
theorem get_of_range {α β : Type} (l : List α) (f : α → β) (n : Nat) (g : Nat → β)
    (e : l.map f = (List.range n).map g) (j : Nat) (hj : j < n) : (l[j]?).map f = some (g j) := by
  rw [← List.getElem?_map, e, List.getElem?_map, List.getElem?_range hj, Option.map_some]

/-- **Where `closeSays` returns L, the frame's `play` of the part returns, and at each asked round number the played
round exists and its items are L's member for that number.** m: the state of a run before the part. c: the part's coins.
-/
theorem closeSays_plays (J : CloseJob W) (name : String) (a : Addr) (v : Option V)
    (c : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins) (m : Mid W X)
    (ds : List Fmt.Drawn) (js : List Nat) (L : List (List Fmt.ItemValue))
    (hL : closeSays J m.st.input m.shown m.st.heard ds (handSnd c) js = .ok L) :
    ∃ y, play ((closePart (foldShellT true J foldWords)).steps name a (closeRounds J.pub.par) v c) ds [] m =
        .ok y ∧
      L.map some = js.map fun j => (y.1[j]?).map (·.vals) := by
  obtain ⟨d0, d1, gs, rfl, hL'⟩ := closeSays_shape J _ _ _ ds _ js L hL
  obtain ⟨hk, h1, hj, A, hA, rfl⟩ := closeSaysAt_ok J _ _ _ d0 d1 gs _ js L hL'
  obtain ⟨y, hy, e⟩ := plays_is J name a v c m d0 d1 gs hk h1 (some A) hA.symm
  refine ⟨y, hy, ?_⟩
  have e2 : y.1.map (fun p => p.vals) = (List.range (2 + J.pub.par.k)).map fun i =>
      (saysAt J (some A) (spentRun J (handSnd c)) d1 gs i).vals.map Said.got := by
    have e1 := congrArg (List.map Prod.fst) e
    rw [List.map_map, List.map_map] at e1
    exact e1
  unfold saysOf
  rw [List.map_map]
  exact List.map_congr_left fun j hm => (get_of_range y.1 (fun p => p.vals) _ _ e2 j (hj j hm)).symm

/-- **The same of a given value of `play`**: where `play` of the part returns y and `closeSays` returns L, L holds the
items of y's rounds at the asked numbers. -/
theorem closeSays_is (J : CloseJob W) (name : String) (a : Addr) (v : Option V)
    (c : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins) (m : Mid W X)
    (ds : List Fmt.Drawn) (js : List Nat) (L : List (List Fmt.ItemValue)) (y : List Played × Mid W X)
    (hL : closeSays J m.st.input m.shown m.st.heard ds (handSnd c) js = .ok L)
    (hy : play ((closePart (foldShellT true J foldWords)).steps name a (closeRounds J.pub.par) v c) ds [] m =
      .ok y) :
    L.map some = js.map fun j => (y.1[j]?).map (·.vals) := by
  obtain ⟨y', hy', e⟩ := closeSays_plays J name a v c m ds js L hL
  have ey : y = y' := Except.ok.inj (hy.symm.trans hy')
  rw [ey]
  exact e

/-- **Where the three tests on the arguments pass and `closeSays` returns an error, `askZero` is `none`**: there the
part sends what the fold's words say at empty tables. -/
theorem closeSays_none (J : CloseJob W) (w : W) (sn : Seen) (h0 : List Fmt.Drawn) (d0 d1 : Fmt.Drawn)
    (gs : List Fmt.Drawn) (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (js : List Nat)
    (e : String) (hk : gs.length = J.pub.par.k) (h1 : ∀ d ∈ d0 :: d1 :: gs, d.elems.length = 1)
    (hj : ∀ j ∈ js, j < 2 + J.pub.par.k) (h : closeSays J w sn h0 (d0 :: d1 :: gs) c js = .error e) :
    askZero J w sn h0 d0 c.2.2 = none := by
  have h' : closeSaysAt J w sn h0 d0 d1 gs c js = .error e := h
  have t1 : ((d0 :: d1 :: gs).all fun d => d.elems.length == 1) = true :=
    List.all_eq_true.2 fun d hd => beq_iff_eq.2 (h1 d hd)
  have tj : (js.all fun j => decide (j < 2 + J.pub.par.k)) = true :=
    List.all_eq_true.2 fun j hm => decide_eq_true (hj j hm)
  unfold closeSaysAt at h'
  rw [if_pos hk, if_pos t1, if_pos tj] at h'
  cases hA : closeData J w sn h0 d0 c.2.2 with
  | ok A =>
    rw [hA] at h'
    exact nomatch h'
  | error e' => exact closeData_error J w sn h0 d0 c.2.2 e' hA

/-! ## 4 The part's coins, as the book gives them -/

/-- **The coins that the book gives the closing's part at the place pl**: the frame's `lendRow` at the list of this one
part, from part number 0, without the empty tail. rows, look: the book's table for the chain, and the coins that the
chain may be given, as `chainSteps` takes them. -/
def closeCoins (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d) (pl : Place)
    (J : CloseJob W) : Except String (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins :=
  (lendRow Bk rows look pl ([closePart (foldShellT true J foldWords)] : List (Part V W X)) 0).map fun r => r.1

/-- Where `lendRow` returns r at the list of this one part, `closeCoins` returns r's first member. -/
theorem closeCoins_of (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d) (pl : Place)
    (J : CloseJob W) (r : RowCoins ([closePart (foldShellT true J foldWords)] : List (Part V W X)))
    (hr : lendRow Bk rows look pl ([closePart (foldShellT true J foldWords)] : List (Part V W X)) 0 = .ok r) :
    closeCoins (V := V) (X := X) Bk rows look pl J = .ok r.1 := by
  unfold closeCoins
  rw [hr]
  rfl

/-- **Where `chainSteps` returns for the closing's block alone, `closeCoins` returns at the block's place, and the steps
are the part's steps at that value.** hz: the block's rounds and oracle messages, zipped, are the closing's declared
rounds. hh: the first prover's side of the list at the block's place has this one part. -/
theorem steps_close_at {S' Cl : Type} (Bk : ProverCoinCounts) (J : CloseJob W) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (v : Option V) (blk : Block S' Cl) (hs : List (Placed V W X))
    (l : List (Step W X)) (hz : blk.rounds.zip blk.oracles = closeRounds J.pub.par)
    (hh : ∃ g, (hs.find? fun h => h.place == blk.place) = some g ∧
      g.parts = [closePart (foldShellT true J foldWords)])
    (hl : chainSteps Bk rows look v [blk] hs = .ok l) :
    ∃ c, closeCoins (V := V) (X := X) Bk rows look blk.place J = .ok c ∧
      l = (closePart (foldShellT true J foldWords)).steps blk.name ⟨blk.place, 0⟩ (closeRounds J.pub.par) v c := by
  obtain ⟨⟨gp, gparts⟩, hg, hparts⟩ := hh
  have hparts' : gparts = [closePart (foldShellT true J foldWords)] := hparts
  subst hparts'
  unfold chainSteps at hl
  rw [hg] at hl
  simp only at hl
  split at hl
  · exact nomatch hl
  split at hl
  · exact nomatch hl
  split at hl
  · exact nomatch hl
  split at hl
  · exact nomatch hl
  split at hl
  · exact nomatch hl
  cases hc : lendRow Bk rows look blk.place
      ([closePart (foldShellT true J foldWords)] : List (Part V W X)) 0 with
  | error _ => rw [hc] at hl; exact nomatch hl
  | ok c =>
    rw [hc] at hl
    have e : l = (⟨gp, [closePart (foldShellT true J foldWords)]⟩ : Placed V W X).steps blk v c ++ [] :=
      (Except.ok.inj hl).symm
    refine ⟨c.1, closeCoins_of Bk rows look blk.place J c hc, ?_⟩
    rw [e, List.append_nil]
    unfold Placed.steps
    rw [hz]
    show (closePart (foldShellT true J foldWords) : Part V W X).steps blk.name ⟨blk.place, 0⟩
      ((closeRounds J.pub.par).take (closePart (V := V) (X := X) (foldShellT true J foldWords)).moves.length) v
      c.1 ++ [] = _
    rw [List.append_nil, moves_len, List.take_length]

/-! ## 5 The function at a job, a book and a run's coins -/

/-- **What the closing's part sends at the rounds js, at the coins that the book gives it at the place pl.** V, X: the
types at which the prover's sides of the chain are typed. The other arguments as `closeCoins`' and `closeSays`'. An
error where `closeCoins` returns one, with its words, and where `closeSays` does. -/
def jobSays (V X : Type) (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d) (pl : Place)
    (J : CloseJob W) (w : W) (sn : Seen) (h0 ds : List Fmt.Drawn) (js : List Nat) :
    Except String (List (List Fmt.ItemValue)) :=
  match closeCoins (V := V) (X := X) Bk rows look pl J with
  | .error e => .error ("K10: the book does not give the part its coins: " ++ e)
  | .ok c => closeSays J w sn h0 ds (handSnd c) js

/-- **Where `chainSteps` returns l for the closing's block alone, `play` of l returns y from the state m, and `jobSays`
returns L at m's input, `m.shown` and heard challenges: L holds the items of y's rounds at the asked numbers.** hp:
pl is the block's place. hz, hh: as in `steps_close_at`. -/
theorem jobSays_is {S' Cl : Type} (Bk : ProverCoinCounts) (J : CloseJob W) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (v : Option V) (blk : Block S' Cl) (hs : List (Placed V W X))
    (l : List (Step W X)) (pl : Place) (hp : blk.place = pl)
    (hz : blk.rounds.zip blk.oracles = closeRounds J.pub.par)
    (hh : ∃ g, (hs.find? fun h => h.place == blk.place) = some g ∧
      g.parts = [closePart (foldShellT true J foldWords)])
    (hl : chainSteps Bk rows look v [blk] hs = .ok l) (m : Mid W X) (ds : List Fmt.Drawn) (js : List Nat)
    (L : List (List Fmt.ItemValue)) (y : List Played × Mid W X)
    (hL : jobSays V X Bk rows look pl J m.st.input m.shown m.st.heard ds js = .ok L)
    (hy : play l ds [] m = .ok y) :
    L.map some = js.map fun j => (y.1[j]?).map (·.vals) := by
  subst hp
  obtain ⟨c, hc, rfl⟩ := steps_close_at Bk J rows look v blk hs l hz hh hl
  unfold jobSays at hL
  rw [hc] at hL
  have hL' : closeSays J m.st.input m.shown m.st.heard ds (handSnd c) js = .ok L := hL
  exact closeSays_is J blk.name ⟨blk.place, 0⟩ v c m ds js L y hL' hy

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.askZeroF
#print axioms ProofFile.Honest.K10.askZeroF_eq
#print axioms ProofFile.Honest.K10.closeData
#print axioms ProofFile.Honest.K10.closeData_ok
#print axioms ProofFile.Honest.K10.closeData_error
#print axioms ProofFile.Honest.K10.saysOf
#print axioms ProofFile.Honest.K10.closeSaysAt
#print axioms ProofFile.Honest.K10.closeSays
#print axioms ProofFile.Honest.K10.closeSays_shape
#print axioms ProofFile.Honest.K10.closeSaysAt_ok
#print axioms ProofFile.Honest.K10.get_of_range
#print axioms ProofFile.Honest.K10.closeSays_plays
#print axioms ProofFile.Honest.K10.closeSays_is
#print axioms ProofFile.Honest.K10.closeSays_none
#print axioms ProofFile.Honest.K10.closeCoins
#print axioms ProofFile.Honest.K10.closeCoins_of
#print axioms ProofFile.Honest.K10.steps_close_at
#print axioms ProofFile.Honest.K10.jobSays
#print axioms ProofFile.Honest.K10.jobSays_is
