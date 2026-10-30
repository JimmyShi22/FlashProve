-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/Plays.lean: the honest side of the sub-protocol "the output
head's own rounds" (`headRow`, Honest/K6/Part.lean) PLAYS at the member of a chain's `Thread` at
which it stands: the debt `Plays` of Honest/Thread/Pays.lean; with the whole list of rounds that the
frame's `play` returns, as one term, and that term in eight pieces. Definitions with code, and
statements with their proofs. EVERY STATEMENT ON A MEMBER IS CONDITIONAL: on `K6Seated`
(Honest/K6/Law/Seated.lean).

What it is not. Nothing is said of the VALUES that are sent: `k6Out` names them, and no statement
here holds them against the verifier's claims. `K6Seated` is shown here of no description of the
protocol; that its clauses can be met together is tried at a small size
(Honest/K6/Law/PlaysToy.lean, which is not in the library). That `chainSteps` returns at the member
is a premise of the debt itself, and is shown by no statement here (the frame has it from one return
of its `ready`: Honest/Thread/Laid.lean, which this file does not import). Whether a move looks at
the opened columns that it is handed is not said here. Nothing is claimed on soundness, completeness
or hiding.

  1  `sayQuiet`, `sayScalars`, `saySum`, `headSayers`, `headSayers_parts`, `headSayers_ok`,
     `headSayers_ns`, `headRow_eq`   the eight parts with what their moves say: A SECOND TEXT of
     `headParts`, tied to it by two equations that are proved; a tool of the proofs
  2  `headRow_cut`, `headCut_sum`, `headHalf_rounds`   the row is cut as `headCut` says, and has the
     verifier's number of rounds: no premise
  3  `k6Out`, `k6Pieces`, `k6Coin`, `k6Piece`, `k6Out_rounds`, `k6Out_eight`, `k6_front`,
     `k6Pieces_at`, `k6Coin_0` to `k6Coin_7`, `k6_count`, `k6Piece_at`, `k6_share_length`,
     `k6Piece_shape`, `k6Piece_alone`   **the rounds as played, as one term of the seated row's own
     coins; and its eight pieces**, each as a term of its share of the coins, of the state that has
     heard the `headInFront p i` challenges in front of it, of what has been shown in front of it,
     and of its share of the challenges
  4  `k6_played`, `k6_cols`, `k6_fresh`, `k6_env`   at the member: what its Steps are and what
     `play` returns on them; it reads no column; no new tree is at hand behind it; the tables at
     hand stay as they are
  5  `k6_plays`, `k6_playsS`   **IT PLAYS**; and the same asked from the pair of the thread and what
     is said
  6  `k6_fits`, `k6_bare`   what was played passes the general step's tests on form; taking the
     sealed digest out of the played rounds changes nothing

What is spent. Of the sentence `Thr` in front nothing is read for `k6_plays`: these parts have no
stop and send no table, and the member's declared rounds open no column (`k6_cols`), so they play
from every stand. The lending of the coins is a premise of `Plays` itself.

What is called. The row's law `sayRow_plays` with its pieces (Honest/Small/SaidRow.lean); the
rounds' shapes (Honest/K6/Law/Rounds.lean); of the frame `steps_one_half`, `fits_played`,
`playsS_of`, `foldl_moves`, `drawsFit_length`, `play_yields`, `yields_drawn`; of the masked
sumcheck's law `sumPart_moves`, `lensBy_sumGs`, `scalarsOf_length`, `fillCols_none`, `add_none`;
`scalarsPart_moves`, `scalarsSaid_length`, `digest_of_fit`, `noDigest_of_none`. The statements at
the member, and the proofs of `k6_fresh`, `k6_env`, `k6_plays` and `k6_bare`, follow the like laws
on the attention segment's own rounds (Honest/K5/Law/Plays.lean, not in the library) nearly line for
line.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.Seated
import Johnson.Desc.ProofFile.Honest.Small.SaidRow
import Johnson.Desc.ProofFile.Honest.K6.Law.Rounds
import Johnson.Desc.ProofFile.Honest.Law.Thread
import Johnson.Desc.ProofFile.Honest.Thread.Shape
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E)
open VerifiableInference.Desc (Block Place OpenedColumn noDigest)
open VerifiableInference.Desc.Kinds (Head.Par)
open ProofFile.Honest.SumLaw
open ProofFile.Honest.Small

/-! ## 1 The eight parts, with what their moves say -/

/-- A round in which nothing is sent. -/
def sayQuiet : Sayer HeadAsk := ⟨quietPart, [fun _ _ _ => []], [0]⟩

/-- A round of n scalars, each under a mask entry. -/
def sayScalars (name : String) (n : Nat) (vals : HeadAsk → Front Unit → List E) : Sayer HeadAsk :=
  ⟨scalarsPart name n vals, [fun c seen t => scalarsSaid n vals c.2.1.1 seen t], [n]⟩

/-- A masked sumcheck. -/
def saySum (name endName : String) (J : SumJob HeadAsk Unit) : Sayer HeadAsk :=
  ⟨sumPart name endName J, sumGs name endName J, scalarsOf J.shape⟩

/-- **The eight parts of the row**, each with what its moves say: the text of `headParts`. -/
def headSayers (p : Head.Par) (at_ : Place) : List (Sayer HeadAsk) :=
  [sayQuiet,
   sayScalars (headRunName at_ 1 headScalarsUse) 9 (fun a fr => headNine p a fr.heard),
   saySum (headRunName at_ 2 "sum") (headRunName at_ 2 "ends") (headSquaresJob p),
   sayQuiet,
   sayScalars (headRunName at_ 4 headScalarsUse) 7 (fun a fr => headSeven p a fr.heard),
   saySum (headRunName at_ 5 "sum") (headRunName at_ 5 "ends") (headProductsJob p),
   saySum (headRunName at_ 6 "sum") (headRunName at_ 6 "ends") (headNormedJob p),
   saySum (headRunName at_ 7 "sum") (headRunName at_ 7 "ends") (headLogitsJob p)]

/-- Their parts are the row's. No premise. -/
theorem headSayers_parts (p : Head.Par) (at_ : Place) :
    (headSayers p at_).map (·.part) = headParts p at_ := rfl

theorem sayQuiet_ok : sayQuiet.Ok :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, fun _ => ⟨fun _ _ => rfl, trivial⟩⟩

theorem sayScalars_ok (name : String) (n : Nat) (vals : HeadAsk → Front Unit → List E) :
    (sayScalars name n vals).Ok :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, scalarsPart_moves name n vals, rfl,
    fun c => ⟨fun s t => scalarsSaid_length n vals c.2.1.1 s t, trivial⟩⟩

/-- Conditional: every variable has at least two coefficients. -/
theorem saySum_ok (name endName : String) (J : SumJob HeadAsk Unit)
    (h2 : ∀ v ∈ J.shape.vs, 2 ≤ v.d) : (saySum name endName J).Ok :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, sumPart_moves name endName J,
    (scalarsOf_length name endName J).symm, fun c => lensBy_sumGs name endName J c h2⟩

/-- Every variable of a call of the row's shape has at least two coefficients. -/
theorem pointShape_two (lead n ends : Nat) : ∀ v ∈ (pointShape lead n ends).vs, 2 ≤ v.d := by
  intro v hv
  obtain rfl := (List.mem_replicate.1 hv).2
  exact Nat.le_succ 2

/-- Each is as `Sayer.Ok` says. No premise. -/
theorem headSayers_ok (p : Head.Par) (at_ : Place) : ∀ s ∈ headSayers p at_, s.Ok := by
  intro s hs
  simp only [headSayers, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sayQuiet_ok
  · exact sayScalars_ok _ _ _
  · exact saySum_ok _ _ _ (pointShape_two _ _ _)
  · exact sayQuiet_ok
  · exact sayScalars_ok _ _ _
  · exact saySum_ok _ _ _ (pointShape_two _ _ _)
  · exact saySum_ok _ _ _ (pointShape_two _ _ _)
  · exact saySum_ok _ _ _ (pointShape_two _ _ _)

/-- Their counts are `headSent`'s. No premise. -/
theorem headSayers_ns (p : Head.Par) (at_ : Place) :
    (headSayers p at_).map (·.ns) = headSent p := rfl

section Member
variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Tr X Pb : Type}

/-- The seated row is these parts, lifted. No premise. -/
theorem headRow_eq (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) :
    headRow (X := X) wit p at_ = sayParts wit (headSayers p at_) := rfl

/-- The row is cut as `headCut` says: the list against which the frame's `chainSteps` holds the
book's cut for the place. No premise. -/
theorem headRow_cut (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) :
    (headRow (X := X) wit p at_).map (·.moves.length) = headCut p := by
  show (sayParts (V := Local W₀ Rc Inst Tr) (X := X) wit (headSayers p at_)).map
    (·.moves.length) = _
  rw [sayParts_moves wit _ (headSayers_ok p at_), ← headSent_cut, ← headSayers_ns p at_,
    List.map_map]
  rfl

/-- The cut adds up to the verifier's number of rounds. No premise. -/
theorem headCut_sum (p : Head.Par) : (headCut p).sum = p.rounds.length := by
  rw [head_rounds_length, List.length_flatten, headSent_cut]

/-- The half has as many rounds as the verifier's text declares. No premise. -/
theorem headHalf_rounds (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) :
    (⟨at_, headRow wit p at_⟩ :
      Placed (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).rounds = p.rounds.length := by
  unfold Placed.rounds
  rw [foldl_moves, Nat.zero_add, headRow_cut, headCut_sum]

/-- **THE SUB-PROTOCOL's ROUNDS AS PLAYED, AS ONE TERM**: of the member's name, the reader of the
small input, the place's public numbers, the place, the row's coins, the state, what has been shown
in front (`Seen`: the rounds, and the opened columns where any are handed), and the challenges. -/
def k6Out (nm : String) (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place)
    (c : RowCoins (headRow (X := X) wit p at_))
    (t : State (Local W₀ Rc Inst Tr) X) (seen : Seen) (ds : List Fmt.Drawn) : List Played :=
  sayOut nm at_ wit (headSayers p at_) 0 c t seen ds

/-- **The same as a view shows them, part by part**: eight lists. -/
def k6Pieces (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place)
    (c : RowCoins (headRow (X := X) wit p at_)) (t : State (Local W₀ Rc Inst Tr) X)
    (seen : Seen) (ds : List Fmt.Drawn) : List (List Fmt.RoundView) :=
  sayPieces wit (headSayers p at_) c t seen ds

/-- Part number i of the row with what its moves say, and its share of the row's coins. At a
written i it unfolds: at 2, to the sumcheck on the squares and `c.2.2.1`. -/
def k6Coin (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place)
    (c : RowCoins (headRow (X := X) wit p at_)) (i : Nat) :
    Option ((s : Sayer HeadAsk) × s.part.Coins) :=
  sayCoin wit (headSayers p at_) c i

/-- The rounds as played are the eight pieces, one behind the other. No premise. -/
theorem k6Out_rounds (nm : String) (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par)
    (at_ : Place) (c : RowCoins (headRow (X := X) wit p at_)) (t : State (Local W₀ Rc Inst Tr) X)
    (seen : Seen) (ds : List Fmt.Drawn) :
    roundsOf (k6Out nm wit p at_ c t seen ds) = (k6Pieces wit p at_ c t seen ds).flatten :=
  sayOut_rounds nm at_ wit (headSayers p at_) 0 c t seen ds

/-- A sum by folding from the left. -/
theorem foldl_add_sum : ∀ (l : List Nat) (k : Nat), l.foldl (· + ·) k = k + l.sum
  | [], k => (Nat.add_zero k).symm
  | a :: l, k => by
    rw [List.foldl_cons, foldl_add_sum l, List.sum_cons, Nat.add_assoc]

/-- In front of part number i stand the rounds that `headInFront` counts. No premise. -/
theorem k6_front (p : Head.Par) (at_ : Place) (i : Nat) :
    sayFront (headSayers p at_) i = headInFront p i := by
  unfold sayFront headInFront
  rw [List.length_flatMap, foldl_add_sum, Nat.zero_add, ← headSent_cut, ← headSayers_ns p at_,
    List.map_map, List.map_take]
  rfl

/-- **THE ROUNDS OF PART NUMBER i OF THE ROW**: what its moves say at its share of the coins, from
the state that has heard the challenges of the `headInFront p i` rounds in front of it, at what was
shown in front of the row, with the pieces in front of the part laid behind its rounds (`Seen.plus`:
the opened columns are those in front of the row), at its share of the challenges. CONDITIONAL on
`k6Coin wit p at_ c i = some x`, which names x and fails at every i from 8 on. -/
theorem k6Pieces_at (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place)
    (c : RowCoins (headRow (X := X) wit p at_)) (t : State (Local W₀ Rc Inst Tr) X)
    (seen : Seen) (ds : List Fmt.Drawn) (i : Nat)
    (x : (s : Sayer HeadAsk) × s.part.Coins) (h : k6Coin wit p at_ c i = some x) :
    (k6Pieces wit p at_ c t seen ds)[i]? = some (outOf (x.1.gs.map (· x.2))
      ((⟨t.input, t.heard ++ ds.take (headInFront p i), t.own⟩ :
        State (Local W₀ Rc Inst Tr) X).narrow wit fun _ => ())
      (seen.plus (((k6Pieces wit p at_ c t seen ds).take i).flatten))
      ((ds.drop (headInFront p i)).take x.1.ns.length)) := by
  rw [← k6_front p at_ i]
  exact sayPieces_at wit (headSayers p at_) c t seen ds i x h

/-! ### The eight pieces, for whoever spends the term -/

section Pieces
variable (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place)
  (c : RowCoins (headRow (X := X) wit p at_)) (t : State (Local W₀ Rc Inst Tr) X)
  (seen : Seen) (ds : List Fmt.Drawn)

/-- Which part stands at each number, with its share of the coins. No premise. -/
theorem k6Coin_0 : k6Coin wit p at_ c 0 = some ⟨sayQuiet, c.1⟩ := rfl
theorem k6Coin_1 : k6Coin wit p at_ c 1 = some
    ⟨sayScalars (headRunName at_ 1 headScalarsUse) 9 (fun a fr => headNine p a fr.heard), c.2.1⟩ :=
  rfl
theorem k6Coin_2 : k6Coin wit p at_ c 2 = some
    ⟨saySum (headRunName at_ 2 "sum") (headRunName at_ 2 "ends") (headSquaresJob p), c.2.2.1⟩ := rfl
theorem k6Coin_3 : k6Coin wit p at_ c 3 = some ⟨sayQuiet, c.2.2.2.1⟩ := rfl
theorem k6Coin_4 : k6Coin wit p at_ c 4 = some
    ⟨sayScalars (headRunName at_ 4 headScalarsUse) 7 (fun a fr => headSeven p a fr.heard),
      c.2.2.2.2.1⟩ := rfl
theorem k6Coin_5 : k6Coin wit p at_ c 5 = some
    ⟨saySum (headRunName at_ 5 "sum") (headRunName at_ 5 "ends") (headProductsJob p),
      c.2.2.2.2.2.1⟩ := rfl
theorem k6Coin_6 : k6Coin wit p at_ c 6 = some
    ⟨saySum (headRunName at_ 6 "sum") (headRunName at_ 6 "ends") (headNormedJob p),
      c.2.2.2.2.2.2.1⟩ := rfl
theorem k6Coin_7 : k6Coin wit p at_ c 7 = some
    ⟨saySum (headRunName at_ 7 "sum") (headRunName at_ 7 "ends") (headLogitsJob p),
      c.2.2.2.2.2.2.2.1⟩ := rfl

/-- Piece number i; empty beyond the eighth. -/
def k6Piece (i : Nat) : List Fmt.RoundView := ((k6Pieces wit p at_ c t seen ds)[i]?).getD []

/-- **THE ROUNDS AS PLAYED ARE THE EIGHT PIECES**, bracketed to the right. No premise. -/
theorem k6Out_eight (nm : String) :
    roundsOf (k6Out nm wit p at_ c t seen ds) =
      k6Piece wit p at_ c t seen ds 0 ++ (k6Piece wit p at_ c t seen ds 1 ++
        (k6Piece wit p at_ c t seen ds 2 ++ (k6Piece wit p at_ c t seen ds 3 ++
          (k6Piece wit p at_ c t seen ds 4 ++ (k6Piece wit p at_ c t seen ds 5 ++
            (k6Piece wit p at_ c t seen ds 6 ++ k6Piece wit p at_ c t seen ds 7)))))) := by
  rw [k6Out_rounds]
  show _ ++ (_ ++ (_ ++ (_ ++ (_ ++ (_ ++ (_ ++ (_ ++ []))))))) = _
  rw [List.append_nil]
  rfl

/-- A part's number of rounds is the cut's member. CONDITIONAL on `k6Coin wit p at_ c i = some x`,
which fails at every i from 8 on. -/
theorem k6_count (i : Nat) (x : (s : Sayer HeadAsk) × s.part.Coins)
    (h : k6Coin wit p at_ c i = some x) : x.1.ns.length = (headCut p).getD i 0 := by
  have h1 := sayCoin_fst wit (headSayers p at_) c i x h
  rw [← headSent_cut, ← headSayers_ns p at_, List.map_map, List.getD_eq_getElem?_getD,
    List.getElem?_map, h1]
  rfl

/-- **PIECE NUMBER i**: what the part's moves say at its share of the coins, from the state that has
heard the challenges of the `headInFront p i` rounds in front, at what was shown in front of the
row, with the pieces in front laid behind its rounds (`Seen.plus`: the opened columns are those in
front of the row), at its share of the challenges, as the cut counts it. CONDITIONAL on
`k6Coin wit p at_ c i = some x`, which fails at every i from 8 on. -/
theorem k6Piece_at (i : Nat) (x : (s : Sayer HeadAsk) × s.part.Coins)
    (h : k6Coin wit p at_ c i = some x) :
    k6Piece wit p at_ c t seen ds i = outOf (x.1.gs.map (· x.2))
      ((⟨t.input, t.heard ++ ds.take (headInFront p i), t.own⟩ :
        State (Local W₀ Rc Inst Tr) X).narrow wit fun _ => ())
      (seen.plus (((k6Pieces wit p at_ c t seen ds).take i).flatten))
      ((ds.drop (headInFront p i)).take ((headCut p).getD i 0)) := by
  unfold k6Piece
  rw [k6Pieces_at wit p at_ c t seen ds i x h, k6_count wit p at_ c i x h]
  rfl

/-- The share has the cut's number of challenges. Conditional: there are as many challenges as
declared rounds. -/
theorem k6_share_length (i : Nat) (x : (s : Sayer HeadAsk) × s.part.Coins)
    (h : k6Coin wit p at_ c i = some x) (hl : ds.length = p.rounds.length) :
    ((ds.drop (headInFront p i)).take ((headCut p).getD i 0)).length = (headCut p).getD i 0 := by
  rw [← k6_count wit p at_ c i x h, ← k6_front p at_ i]
  exact sayShare_length _ i x.1 (sayCoin_fst wit (headSayers p at_) c i x h) ds
    (hl.trans (head_rounds_length p))

/-- **A piece has the cut's number of rounds, and they bear its share of the challenges.**
Conditional: there are as many challenges as declared rounds. -/
theorem k6Piece_shape (i : Nat) (x : (s : Sayer HeadAsk) × s.part.Coins)
    (h : k6Coin wit p at_ c i = some x) (hl : ds.length = p.rounds.length) :
    (k6Piece wit p at_ c t seen ds i).length = (headCut p).getD i 0 ∧
      (k6Piece wit p at_ c t seen ds i).map (·.drawn) =
        (ds.drop (headInFront p i)).take ((headCut p).getD i 0) := by
  have hk : x.1.Ok := headSayers_ok p at_ x.1
    (List.mem_of_getElem? (sayCoin_fst wit (headSayers p at_) c i x h))
  have hs := k6_share_length wit p at_ c ds i x h hl
  have hg : (x.1.gs.map (· x.2)).length =
      ((ds.drop (headInFront p i)).take ((headCut p).getD i 0)).length := by
    rw [List.length_map, hk.count, hs, k6_count wit p at_ c i x h]
  rw [k6Piece_at wit p at_ c t seen ds i x h]
  exact ⟨(outOf_length _ _ _ _ hg).trans hs, outOf_drawn _ _ _ _ hg⟩

/-- **Played alone at that state, behind these rounds and at that share, the part says the piece.**
Conditional: there are as many challenges as declared rounds. -/
theorem k6Piece_alone (i : Nat) (x : (s : Sayer HeadAsk) × s.part.Coins)
    (h : k6Coin wit p at_ c i = some x) (hl : ds.length = p.rounds.length) :
    alone x.1.part x.2
      ((⟨t.input, t.heard ++ ds.take (headInFront p i), t.own⟩ :
        State (Local W₀ Rc Inst Tr) X).narrow wit fun _ => ())
      (seen.plus (((k6Pieces wit p at_ c t seen ds).take i).flatten))
      ((ds.drop (headInFront p i)).take ((headCut p).getD i 0)) =
        some (k6Piece wit p at_ c t seen ds i) := by
  have hk : x.1.Ok := headSayers_ok p at_ x.1
    (List.mem_of_getElem? (sayCoin_fst wit (headSayers p at_) c i x h))
  rw [k6Piece_at wit p at_ c t seen ds i x h]
  exact hk.alone x.2 _ _ _
    ((k6_share_length wit p at_ c ds i x h hl).trans (k6_count wit p at_ c i x h).symm)

end Pieces

variable (T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb) {b : Nat}
  {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place} {blk : Block S Cl}

/-- **What the member's Steps are, and what `play` returns on them: the whole list.** CONDITIONAL:
on `K6Seated`; the challenges are such as the member's rounds can draw; `chainSteps` has returned,
that is: the book has lent the row its coins. c: these coins, part by part, as `lendRow` lends them.
-/
theorem k6_played (Hs : K6Seated T b wit p at_ blk) {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option (Local W₀ Rc Inst Tr)}
    {l : List (Step (Local W₀ Rc Inst Tr) X)} {ds : List Fmt.Drawn}
    (hd : drawsFit blk.rounds ds = true) (hl : chainSteps Bk rows look v [blk] T.hs = .ok l)
    (m : Mid (Local W₀ Rc Inst Tr) X) :
    ∃ c, lendRow Bk rows look at_ (headRow wit p at_) 0 = .ok c ∧
      l = (⟨at_, headRow wit p at_⟩ :
        Placed (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X).steps blk v c ∧
      play l ds [] m = .ok (k6Out blk.name wit p at_ c m.st m.shown ds,
        ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
          m.seen ++ roundsOf (k6Out blk.name wit p at_ c m.st m.shown ds), m.opened⟩) := by
  obtain ⟨c, hc, rfl⟩ := steps_one_half Hs.half hl
  rw [Hs.place] at hc
  refine ⟨c, hc, rfl, ?_⟩
  have hlen : ds.length = ((headSayers p at_).flatMap (·.ns)).length := by
    rw [drawsFit_length _ _ hd, Hs.rounds, head_rounds_length]
    rfl
  have hst : StatedBy ((headSayers p at_).flatMap (·.ns)) (blk.rounds.zip blk.oracles) := by
    rw [Hs.rounds, Hs.oracles]
    exact head_stated p
  show play (rowSteps blk.name blk.place v _ 0 (blk.rounds.zip blk.oracles) c) ds [] m = _
  rw [Hs.place]
  exact sayRow_plays blk.name at_ wit v (headSayers p at_) 0 c _ ds [] m (headSayers_ok p at_)
    hst hlen

/-- **The member reads no column.** CONDITIONAL: on `K6Seated`. -/
theorem k6_cols (Hs : K6Seated T b wit p at_ blk) (chain ft : Nat)
    (stored : Nat → Nat → Option (List UInt64)) (tree : Fmt.TreeSource → Option (Place × Table))
    (ds : List Fmt.Drawn) :
    fillCols (readsOf chain ft stored tree blk.rounds ds) [] = .ok [] := by
  rw [Hs.rounds]
  exact fillCols_none chain ft stored tree _ ds (head_reads_nothing p) []

/-- **No tree is at hand behind the member that is not at hand in front of it.** CONDITIONAL: on
`K6Seated`. -/
theorem k6_fresh (Hs : K6Seated T b wit p at_ blk) : T.fresh b = [] := by
  have ho : blk.oracles.flatMap id = [] := by
    rw [Hs.oracles, List.flatMap_eq_nil_iff]
    intro x hx
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hx
    rfl
  have ht : treesTo T.bs (b + 1) = treesTo T.bs b := by
    unfold treesTo
    rw [List.take_add_one, Hs.member, List.flatMap_append, List.length_append]
    show _ + ([blk].flatMap fun x => x.oracles.flatMap id).length = _
    rw [List.flatMap_cons, ho]
    rfl
  unfold Thread.fresh Thread.hand
  rw [ht, List.filter_eq_nil_iff]
  intro σ hσ
  simp [hσ]

/-- **The tables at hand stay as they are, and no column is laid.** CONDITIONAL: on `K6Seated`; no
tree is at hand above those sent (a clause of `Thr` in front); the challenges are such as the
member's rounds can draw (hd); the prover's side of the member's step has been made (hM:
`T.Moved`: it is what y and cols are). -/
theorem k6_env (Hs : K6Seated T b wit p at_ blk) {k : Coins Bk}
    {m : Mid (Local W₀ Rc Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Inst Tr) X} {cols : List OpenedColumn}
    (hd : drawsFit blk.rounds ds = true) (hE : ∀ n, E.sent ≤ n → E.tree (.own n) = none)
    (hM : T.Moved blk k m E ds y cols) : E.add y.1 = E ∧ cols = [] := by
  obtain ⟨⟨l, hl, hp⟩, hc⟩ := hM
  obtain ⟨c, -, -, hq⟩ := k6_played T Hs hd hl m
  rw [hp] at hq
  have hy := congrArg (·.1) (Except.ok.inj hq)
  rw [k6_cols T Hs] at hc
  refine ⟨add_none E y.1 ?_ hE, (Except.ok.inj hc).symm⟩
  rw [show y.1 = _ from hy]
  exact sayOut_tables _ _ _ _ _ _ _ _ _

/-- **IT PLAYS**: the debt `Plays` (Honest/Thread/Pays.lean) at the member at which the
sub-protocol's half stands. CONDITIONAL: on `K6Seated`, which is shown here of no description. Of
`Thr` in front and of "nothing stops" the proof reads nothing: these parts have no stop and send no
table, and the member's declared rounds open no column (`k6_cols`). -/
theorem k6_plays (Hs : K6Seated T b wit p at_ blk) : Plays T b := by
  intro blk' hb k s m E ds l _ hd _ hl
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hb)
  obtain ⟨c, -, -, hp⟩ := k6_played T Hs hd hl m
  refine ⟨_, [], ⟨⟨l, hl, hp⟩, k6_cols T Hs _ _ _ _ _⟩, ?_⟩
  rw [k6_fresh T Hs]
  intro σ hσ
  cases hσ

/-- **IT PLAYS, asked from the pair** of the thread and what is said (`PlaysS`,
Honest/Thread/PaysS.lean), at every letter Said: by the frame's own `playsS_of`. CONDITIONAL: on
`K6Seated`. -/
theorem k6_playsS (Hs : K6Seated T b wit p at_ blk)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop) : PlaysS T Said b :=
  playsS_of T Said (k6_plays T Hs)

/-- **What was played and read passes the general step's own tests on rounds and columns**: the
frame's `FitsAt` (Honest/Thread/Shape.lean) at the member, with the two counts. The proof is the
frame's own for "where a half stands" (`fitsAt_half`, Honest/Thread/ShapeRow.lean), line for line,
at this member: that file stands over the frame's toy row, which no law should import. CONDITIONAL:
on `K6Seated`. -/
theorem k6_fits (Hs : K6Seated T b wit p at_ blk) : FitsAt T b := by
  intro blk' hblk' k m En ds y cols hd hMv
  rw [Hs.member] at hblk'
  cases hblk'
  unfold Thread.Moved at hMv
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hMv
  obtain ⟨c, -, rfl⟩ := steps_one_half Hs.half hl
  exact (fits_played (by rw [headHalf_rounds, Hs.rounds])
    (by rw [Hs.oracles, Hs.rounds, List.length_map]) hy hd hc).1

/-- **AT THIS MEMBER, TAKING THE SEALED DIGEST OUT OF THE PLAYED ROUNDS CHANGES NOTHING.**
CONDITIONAL: on `K6Seated`; the challenges are such as the member's rounds can draw; `play` has
returned at these challenges, on whatever list of Steps. -/
theorem k6_bare (Hs : K6Seated T b wit p at_ blk) {l : List (Step (Local W₀ Rc Inst Tr) X)}
    {ds : List Fmt.Drawn} (hd : drawsFit blk.rounds ds = true)
    {m : Mid (Local W₀ Rc Inst Tr) X} {y : List Played × Mid (Local W₀ Rc Inst Tr) X}
    (hp : play l ds [] m = .ok y) : (roundsOf y.1).map noDigest = roundsOf y.1 := by
  have hdr : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hp)
  have hn := digest_of_fit _ _ hd (by
    rw [Hs.rounds]
    exact head_unsealed p)
  refine noDigest_of_none _ fun r hr => hn _ ?_
  rw [← hdr]
  exact List.mem_map.2 ⟨r, hr, rfl⟩

end Member

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headSayers_parts
#print axioms ProofFile.Honest.K6.sayQuiet_ok
#print axioms ProofFile.Honest.K6.sayScalars_ok
#print axioms ProofFile.Honest.K6.saySum_ok
#print axioms ProofFile.Honest.K6.pointShape_two
#print axioms ProofFile.Honest.K6.headSayers_ok
#print axioms ProofFile.Honest.K6.headSayers_ns
#print axioms ProofFile.Honest.K6.headRow_eq
#print axioms ProofFile.Honest.K6.headRow_cut
#print axioms ProofFile.Honest.K6.headCut_sum
#print axioms ProofFile.Honest.K6.headHalf_rounds
#print axioms ProofFile.Honest.K6.k6Out_rounds
#print axioms ProofFile.Honest.K6.foldl_add_sum
#print axioms ProofFile.Honest.K6.k6_front
#print axioms ProofFile.Honest.K6.k6Pieces_at
#print axioms ProofFile.Honest.K6.k6Coin_0
#print axioms ProofFile.Honest.K6.k6Coin_1
#print axioms ProofFile.Honest.K6.k6Coin_2
#print axioms ProofFile.Honest.K6.k6Coin_3
#print axioms ProofFile.Honest.K6.k6Coin_4
#print axioms ProofFile.Honest.K6.k6Coin_5
#print axioms ProofFile.Honest.K6.k6Coin_6
#print axioms ProofFile.Honest.K6.k6Coin_7
#print axioms ProofFile.Honest.K6.k6Out_eight
#print axioms ProofFile.Honest.K6.k6_count
#print axioms ProofFile.Honest.K6.k6Piece_at
#print axioms ProofFile.Honest.K6.k6_share_length
#print axioms ProofFile.Honest.K6.k6Piece_shape
#print axioms ProofFile.Honest.K6.k6Piece_alone
#print axioms ProofFile.Honest.K6.k6_played
#print axioms ProofFile.Honest.K6.k6_cols
#print axioms ProofFile.Honest.K6.k6_fresh
#print axioms ProofFile.Honest.K6.k6_env
#print axioms ProofFile.Honest.K6.k6_plays
#print axioms ProofFile.Honest.K6.k6_playsS
#print axioms ProofFile.Honest.K6.k6_fits
#print axioms ProofFile.Honest.K6.k6_bare
#print axioms ProofFile.Honest.K6.sayQuiet
#print axioms ProofFile.Honest.K6.sayScalars
#print axioms ProofFile.Honest.K6.saySum
#print axioms ProofFile.Honest.K6.headSayers
#print axioms ProofFile.Honest.K6.k6Out
#print axioms ProofFile.Honest.K6.k6Pieces
#print axioms ProofFile.Honest.K6.k6Coin
#print axioms ProofFile.Honest.K6.k6Piece
