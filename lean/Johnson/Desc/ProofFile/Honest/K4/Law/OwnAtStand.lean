-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/OwnAtStand.lean: CONDITIONAL. Statements with their proofs.

Not shown here. No property is claimed. That the premises can be met: no example is known. THE START
OF EACH SUMCHECK IS A PREMISE, AND IT IS THE JOB's OWN CONTENT: that the verifier's claimed form is
worth the total of the cube of whatever job the maker returns. In `rows_stand` alone it is shown:
there the claimed form is one slot, and the honest part has sent that total under it; that this
total is the batch of the row products is another statement's (`rowBatch_zero` at `Opened.cl8`, as
Johnson/Road/K4/W/Join.lean calls it). Not here: the own claims of the second token sumcheck and of
the batched sumcheck (the latter: Law/StackAtStand.lean). That the step of K4's member accepts is a
premise. Nothing on the law of any coin. Nothing on soundness, on completeness or on any other
property.

Words. K4: the sub-protocol of the feed-forward layers' own rounds. A stand: `K4Stand`
(Law/SlotsTrue.lean): the member's step has accepted what the honest row has played. Ledger: `Fork`
(OnBytes/Model/). World of a ledger, on the mask row that is read off the witness: `worldBehind`
(Law/SlotsOwn.lean). The hearing: `hearFl`; the runs "front" and "back": `formsFrontWith`,
`formsBack` (OnBytes/Desc/First/K4/Plain.lean). The start of a sumcheck: the form that the verifier
takes as its claimed sum. "Later" is `OnBytes.PscRun.Later`.

What is here: UNDER THE PREMISES NAMED BELOW the own claims of five masked sumchecks of K4 are worth
0 at a stand, in the world of a ledger that is late enough. Each is a field of the hypotheses
`OwnFront`, `OwnBack` (Johnson/Road/K4/W/Join.lean), and section 4 builds these two structures of
them. Calls of the five statements of Law/FlatLed.lean, which say so of a return of the hearing;
here their premises are shown at a stand.

THE PREMISES of each of the five: `K4Stand` · `Thr`, the proposition of `Thread` on a stand
(Honest/Thread/Thr.lean): with it the public test `k4Fits` accepts at the stand's own challenges and
input (`K4Seated.fits`) · the start (not in `rows_stand`). No `drawsFit` is asked: what these
statements read of the challenges' shape the member's step has tested (`stand_elems`). BESIDES:
  in `gated_stand`: `K4LookTieAt` (Law/ScriptAt.lean), one field: the lookup's point: no statement
      shows it;
  in `rows_stand`: at least one norm: at a stand no statement shows it; where the public test
      `planNumsB` accepts, `planNums_of_B` has it (Johnson/Desc/First/K4/Returns/Needs.lean, which
      this file does not import); from `K4Plan` the number of norms is the reference sizes'
      (`halvesNums_of_plan`, Law/W/HalvesNums.lean, field NI) · a
      return of "front" from the ledger that the step leaves · hsh: what that ledger shows under
      the slots of the sumcheck's end values: "front" reads that array first, at its own public
      data's number of norms, which nothing here ties to K4's;
  in `merge_stand`: a return of "back" from a later ledger.
THE TWO RETURNS are had behind a run of the verifier that has accepted. In a statement that is to
show that it accepts they are to be shown: the library's `runs_return_behind`
(Johnson/Road/K4/Total/RunsReturnLaw.lean) has both from a return of the hearing, at public data
with the hearing's layout and numbers of rounds, under premises at the ledger IN FRONT of the member
(`Asks`; no slot from its next on is filled; `WinFree`), which are premises in their turn.
Law/RunsAtStand.lean has both returns at a stand, from the library's `KeptAsks`.

  `entryAt`, `seenAt`, `partDs`, `partRounds`   what a part whose first round is number R of the row
      finds: its state, the rounds shown in front; its own n challenges; its own n rounds as played
  `rowSteps_cut`   GENERAL IN THE ROW: a row's Steps, cut at a part, for the frame's `play_cut`
      (Honest/Law/Cut.lean)
  `k4_alone`   **a masked sumcheck's rounds in the played row are what the part, played alone from
      its entry, returns** (`alone`, Honest/SumLaw/Terms.lean)
  `drawsOfSum`, `k4DrawsTail`, `k4Draws`, `k4_draws_table`, `flatten_cut`, `k4_draws`   how many
      elements each round of each part samples; these numbers are the column "drawn" of the
      verifier's table; so a masked sumcheck's challenges have the call's shape (`drawsOk`, the same
      file)
  `roundsFit_elems`, `stand_elems`, `stand_own_fits`   what the member's step has tested of the
      challenges' shape; so what has been heard at a prefix has the table's shape
  `stand_fits`   the public test at the stand's own challenges and input
  `stand_led_tape`   the library's `LedG` (Johnson/Road/K4/OwnLedgersG.lean) at a stand, ON THE TAPE
      OF THE PLAYED ROUNDS, from the ledger in front of the member to the one that the step leaves
      (`stand_led`, Law/PtsAtStand.lean, says it of some tape and some ledgers)
  `squares_stand`, `rows_stand`, `gated_stand`, `gated2_stand`, `merge_stand`   **the five**
  `ownFront_stand`, `ownBack_stand`   **the two structures**: the first whole, at one world; the
      second from the batched sumcheck's own claim, a hypothesis, and the merge's

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.Plays
import Johnson.Desc.ProofFile.Honest.Small.PlayRow
import Johnson.Desc.ProofFile.Honest.Gap
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsOwn
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatLed
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatPaired
import Johnson.Road.K4.W.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Reading Aff Fork wsForkStart powers orderRange)
open OnBytes.Model.Layer (Own downFrom normsStart)
open OnBytes.PscRun (Sized Later)
open OnBytes.Desc.First.P1 (tapeEps)
open OnBytes.Desc.First.K4 (Par k0 rowsSummand mergeSlots formsFrontWith formsBack)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Place Oracle Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)
open ProofFile.Honest.SumLaw (alone drawsOk frontOf sumGs SumCoins)
open ProofFile.Honest.K4.SlotsOwn (SumAt worldBehind sumAt_some own_ground squares_hs rows_hs gated_hs
  gated2_hs merge_hs)

/-! ## 1 General in the row -/

section
variable {V W X : Type}

/-- **A row's Steps, cut at a part**: those of the parts in front, as many as these have moves; the
part's own, at its stretch of the declared rounds and at its coins; those of the parts behind.
General in the row. -/
theorem rowSteps_cut (name : String) (a : Place) (v : Option V) : ∀ (ps : List (Part V W X))
    (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle)) (c : RowCoins ps) (i : Nat)
    (p : Part V W X) (cp : p.Coins), rowAt? ps c i = some ⟨p, cp⟩ →
    movesTo ps ps.length ≤ rs.length →
    ∃ l₁ l₃, rowSteps name a v ps j rs c =
        l₁ ++ p.steps name ⟨a, j + i⟩ ((rs.drop (movesTo ps i)).take p.moves.length) v cp ++ l₃ ∧
      l₁.length = movesTo ps i
  | [], _, _, _, _, _, _, h, _ => by simp [rowAt?] at h
  | q :: ps, j, rs, c, 0, p, cp, h, _ => by
    have h' : (⟨q, (show q.Coins × RowCoins ps from c).1⟩ : (p : Part V W X) × p.Coins) =
        ⟨p, cp⟩ := Option.some.inj h
    cases h'
    exact ⟨[], rowSteps name a v ps (j + 1) (rs.drop q.moves.length)
      (show q.Coins × RowCoins ps from c).2, rfl, rfl⟩
  | q :: ps, j, rs, c, i + 1, p, cp, h, hr => by
    have z : movesTo (q :: ps) (i + 1) = q.moves.length + movesTo ps i := by
      simp [movesTo, List.take_succ_cons]
    have zl : movesTo (q :: ps) (q :: ps).length = q.moves.length + movesTo ps ps.length := by
      simp [movesTo, List.take_succ_cons]
    rw [zl] at hr
    obtain ⟨l₁, l₃, h1, h2⟩ := rowSteps_cut name a v ps (j + 1) (rs.drop q.moves.length)
      (show q.Coins × RowCoins ps from c).2 i p cp h (by rw [List.length_drop]; omega)
    refine ⟨q.steps name ⟨a, j⟩ (rs.take q.moves.length) v
      (show q.Coins × RowCoins ps from c).1 ++ l₁, l₃, ?_, ?_⟩
    · show q.steps name ⟨a, j⟩ (rs.take q.moves.length) v (show q.Coins × RowCoins ps from c).1 ++
        rowSteps name a v ps (j + 1) (rs.drop q.moves.length)
          (show q.Coins × RowCoins ps from c).2 = _
      rw [h1, z, List.drop_drop, show j + 1 + i = j + (i + 1) by omega, List.append_assoc,
        List.append_assoc, List.append_assoc]
    · rw [List.length_append, steps_length, List.length_take, h2, z]
      omega

/-- A part's rounds end within the row's. -/
theorem movesTo_le : ∀ (ps : List (Part V W X)) (i : Nat) (p : Part V W X), ps[i]? = some p →
    movesTo ps i + p.moves.length ≤ movesTo ps ps.length
  | [], _, _, h => by simp at h
  | q :: ps, 0, p, h => by
    obtain rfl : q = p := by simpa using h
    simp [movesTo, List.take_succ_cons]
  | q :: ps, i + 1, p, h => by
    have ih := movesTo_le ps i p (by simpa using h)
    have z : movesTo (q :: ps) (i + 1) = q.moves.length + movesTo ps i := by
      simp [movesTo, List.take_succ_cons]
    have zl : movesTo (q :: ps) (q :: ps).length = q.moves.length + movesTo ps ps.length := by
      simp [movesTo, List.take_succ_cons]
    rw [z, zl]
    omega

end

/-! ## 2 A masked sumcheck's part in K4's played row -/

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- The state that a part of K4's row at the small input finds, whose first round is number R. -/
def entryAt (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn) (R : Nat) : State K4In Unit :=
  ⟨k4Wit Q cells weights tokens (look Q) m.st.input, m.st.heard ++ ds.take R, ()⟩

/-- The rounds shown in front of it. -/
def seenAt (m : Mid (Local W₀ Rc Xi Tr) X) (y : List Played × Mid (Local W₀ Rc Xi Tr) X)
    (R : Nat) : Seen :=
  m.shown.plus (roundsOf (y.1.take R))

/-- Its own n challenges. -/
def partDs (ds : List Fmt.Drawn) (R n : Nat) : List Fmt.Drawn := (ds.drop R).take n

/-- Its own n rounds, as played. -/
def partRounds (y : List Played × Mid (Local W₀ Rc Xi Tr) X) (R n : Nat) : List Fmt.RoundView :=
  ((roundsOf y.1).drop R).take n

variable {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
  {c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts}

/-- **A MASKED SUMCHECK's ROUNDS IN THE PLAYED ROW ARE WHAT THE PART, PLAYED ALONE FROM ITS ENTRY,
RETURNS.** General in the part's number and in its job. hp: the part in the row at the small input,
on which the rounds in front are counted; hcp: the same part as the row seats it, with the coins
that it is handed. CONDITIONAL on the seat and on a return of the frame's `play`. -/
theorem k4_alone {V : Type}
    (Pl : K4Played T b cells weights tokens look Q p blk k m E ds y cols c) (i : Nat)
    (name endName : String) (J : SumJob K4In Unit)
    (hp : (k4RowIn Q)[i]? = some (sumPart name endName J)) (cp : SumCoins name endName J)
    (hcp : SumAt c i name endName J cp) :
    alone (sumPart (V := V) name endName J) cp
        (entryAt Q cells weights tokens look m ds (movesTo (k4RowIn Q) i))
        (seenAt m y (movesTo (k4RowIn Q) i))
        (partDs ds (movesTo (k4RowIn Q) i) (sumGs name endName J).length) =
      some (partRounds y (movesTo (k4RowIn Q) i) (sumGs name endName J).length) := by
  obtain ⟨⟨l, hl, hy⟩, _⟩ := Pl.moved
  obtain ⟨c', hc', rfl, ho, hr⟩ := chainSteps_one hl Pl.seat.half
  obtain rfl : c' = c := by
    rw [Pl.seat.place] at hc'
    exact Except.ok.inj (hc'.symm.trans Pl.lent)
  have hmt : movesTo (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts i =
      movesTo (k4RowIn Q) i := movesTo_lift _ _ _ _ _ i
  have hn : (k4SeatOf (Rc := Rc) (X := X) Q cells weights tokens (look Q)
      (sumPart name endName J)).moves.length = (sumGs name endName J).length := by
    show ((sumPart (V := Unit) name endName J).moves.map _).length = _
    rw [List.length_map, SumLaw.moves_length]
  have hrl : (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).rounds =
      movesTo (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts
        (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts.length := by
    unfold Placed.rounds movesTo
    rw [foldl_moves, Nat.zero_add, List.take_length]
  have hzl : (blk.rounds.zip blk.oracles).length = blk.rounds.length := by
    rw [List.length_zip, ho, Nat.min_self]
  have hcp' : rowAt? (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts c' i =
      some ⟨k4SeatOf (Rc := Rc) (X := X) Q cells weights tokens (look Q)
        (sumPart name endName J), cp⟩ := hcp
  obtain ⟨l₁, l₃, hcut, hl1⟩ := rowSteps_cut blk.name blk.place (T.φ.sees m.st.input) _ 0
    (blk.rounds.zip blk.oracles) c' i
    (k4SeatOf (Rc := Rc) (X := X) Q cells weights tokens (look Q) (sumPart name endName J)) cp
    hcp' (by rw [hzl, ← hr, hrl])
  have hy' := hy
  unfold Placed.steps at hy'
  rw [hcut] at hy'
  obtain ⟨y₁, y₂, y₃, p1, p2, _, rfl⟩ := play_cut hy'
  obtain ⟨b1, _, b3⟩ := play_mid _ _ _ _ _ p1
  have b2 := play_heard _ _ _ _ _ p1
  have len1 : y₁.1.length = l₁.length := yields_length _ _ _ _ (play_yields _ _ _ _ _ p1)
  have len2 := yields_length _ _ _ _ (play_yields _ _ _ _ _ p2)
  have hpart : (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts[i]? =
      some (k4SeatOf Q cells weights tokens (look Q) (sumPart name endName J)) := by
    show ((k4RowIn Q).map _)[i]? = _
    rw [List.getElem?_map, hp]
    rfl
  have hfar : movesTo (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts i +
      (sumGs name endName J).length ≤ blk.rounds.length := by
    rw [← hr, hrl, ← hn]
    exact movesTo_le _ i _ hpart
  have hrs : (((blk.rounds.zip blk.oracles).drop
      (movesTo (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts i)).take
      (k4SeatOf (Rc := Rc) (X := X) Q cells weights tokens (look Q)
        (sumPart name endName J)).moves.length).length =
      (k4SeatOf (Rc := Rc) (X := X) Q cells weights tokens (look Q)
        (sumPart name endName J)).moves.length := by
    rw [List.length_take, List.length_drop, hzl, hn]
    omega
  have hsl : ((k4SeatOf (Rc := Rc) (X := X) Q cells weights tokens (look Q)
      (sumPart name endName J)).steps blk.name ⟨blk.place, 0 + i⟩
      (((blk.rounds.zip blk.oracles).drop
        (movesTo (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts i)).take
        (k4SeatOf (Rc := Rc) (X := X) Q cells weights tokens (look Q)
          (sumPart name endName J)).moves.length) (T.φ.sees m.st.input) cp).length =
      (sumGs name endName J).length := by
    rw [steps_length, hrs, Nat.min_self, hn]
  rw [hsl] at p2 len2
  rw [hl1, hmt] at p2 b2 len1
  rw [hmt] at hrs
  obtain ⟨q1, _, _⟩ := Small.played_of_steps _ _ _ _ _ _ _ _ _ _ hrs p2
  have q2 := SumLaw.playedFrom_rounds blk.name ⟨blk.place, 0 + i⟩ cp
    (k4SeatOf (Rc := Rc) (X := X) Q cells weights tokens (look Q)
      (sumPart name endName J)).moves y₁.2.st y₁.2.shown
    ((ds.drop (movesTo (k4RowIn Q) i)).take (sumGs name endName J).length)
  have q2' : SumLaw.aloneFrom cp (k4SeatOf (Rc := Rc) (X := X) Q cells weights tokens (look Q)
      (sumPart name endName J)).moves y₁.2.st y₁.2.shown
      ((ds.drop (movesTo (k4RowIn Q) i)).take (sumGs name endName J).length) =
      some (roundsOf y₂.1) := q2.symm.trans (congrArg (Option.map roundsOf) q1)
  have q3 := SumLaw.alone_lift_unit (X := X) (fun _ : Local W₀ Rc Xi Tr => ())
    (k4Wit Q cells weights tokens (look Q)) (sumPart (V := Unit) name endName J) cp y₁.2.st
    y₁.2.shown ((ds.drop (movesTo (k4RowIn Q) i)).take (sumGs name endName J).length)
  have e_st : y₁.2.st.narrow (k4Wit Q cells weights tokens (look Q)) (fun _ => ()) =
      entryAt Q cells weights tokens look m ds (movesTo (k4RowIn Q) i) := by
    unfold State.narrow entryAt
    rw [b1, b2]
  have e_seen : y₁.2.shown =
      seenAt m (y₁.1 ++ y₂.1 ++ y₃.1, y₃.2) (movesTo (k4RowIn Q) i) := by
    unfold seenAt
    show (⟨y₁.2.seen, y₁.2.opened⟩ : Seen) =
      ⟨m.seen ++ roundsOf ((y₁.1 ++ y₂.1 ++ y₃.1).take (movesTo (k4RowIn Q) i)), m.opened⟩
    rw [b3, play_opened _ _ _ _ _ p1, List.append_assoc, ← len1, List.take_left]
  have e_rounds : roundsOf y₂.1 = partRounds (y₁.1 ++ y₂.1 ++ y₃.1, y₃.2)
      (movesTo (k4RowIn Q) i) (sumGs name endName J).length := by
    unfold partRounds roundsOf
    show _ = (((y₁.1 ++ y₂.1 ++ y₃.1).map _).drop (movesTo (k4RowIn Q) i)).take _
    rw [← List.map_drop, ← List.map_take, List.append_assoc, ← len1, List.drop_left, ← len2,
      List.take_left]
  have main : alone (sumPart (V := Unit) name endName J) cp
      (entryAt Q cells weights tokens look m ds (movesTo (k4RowIn Q) i))
      (seenAt m (y₁.1 ++ y₂.1 ++ y₃.1, y₃.2) (movesTo (k4RowIn Q) i))
      ((ds.drop (movesTo (k4RowIn Q) i)).take (sumGs name endName J).length) =
      some (roundsOf y₂.1) := by
    rw [← e_st, ← e_seen]
    exact q3.symm.trans q2'
  rw [← e_rounds]
  exact main

/-- How many elements each round of a masked sumcheck of n variables with end values samples. -/
def drawsOfSum (n : Nat) : List Nat := [1] ++ List.replicate n 1 ++ [1, 0]

/-- One list for each of the sixteen parts behind the quiet parts in front: how many elements each
of its rounds samples. -/
def k4DrawsTail (Q : K4Pub) : List (List Nat) :=
  [[1], [Q.P.rd.lNI], drawsOfSum Q.P.rd.muV, [1], [1], drawsOfSum Q.P.y.h.lt,
   drawsOfSum Q.P.y.h.lt, [1], drawsOfSum Q.hp.lamS, drawsOfSum Q.P.rd.muH, [1],
   [Q.P.y.h.ll - 1], drawsOfSum Q.P.rd.muH2, [1], [1], drawsOfSum Q.P.wsLay.lk]

/-- **How many elements each round of each part of K4's row samples.** Numbers typed anew: they are
held against the verifier's table by `k4_draws_table`. -/
def k4Draws (Q : K4Pub) : List (List Nat) :=
  (if Q.g == 0 then [[Q.P.y.h.lt], [Q.P.y.ls + Q.P.y.h.lt], [Q.P.y.lPd - Q.P.y.ls]]
    else [[Q.P.y.h.lt]]) ++ k4DrawsTail Q

/-- **One behind the other they are the column "drawn" of the verifier's table of rounds.** -/
theorem k4_draws_table (Q : K4Pub) :
    (k4Draws Q).flatten = (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g).map (·.drawn) := by
  cases hg : (Q.g == 0) <;>
    simp [k4Draws, k4DrawsTail, drawsOfSum, OnBytes.Desc.First.K4.rounds,
      OnBytes.Desc.First.K4.masked, OnBytes.Desc.First.K4.layerRds, OnBytes.Desc.First.K4.pointRd,
      OnBytes.Desc.First.K4.batchRd, hg]

/-- A member of a list of lists, cut out of the lists laid one behind the other. -/
theorem flatten_cut {α : Type} : ∀ (L : List (List α)) (i : Nat) (x : List α), L[i]? = some x →
    (L.flatten.drop ((L.take i).map (·.length)).sum).take x.length = x
  | [], _, _, h => by simp at h
  | y :: L, 0, x, h => by
    obtain rfl : y = x := by simpa using h
    simp
  | y :: L, i + 1, x, h => by
    have ih := flatten_cut L i x (by simpa using h)
    rw [List.flatten_cons, List.take_succ_cons, List.map_cons, List.sum_cons,
      ← List.drop_drop, List.drop_left]
    exact ih

/-- n ones in front. -/
theorem ones_take_sum (n : Nat) (L : List Nat) (j : Nat) :
    ((List.replicate n 1 ++ L).take (n + j)).sum = n + (L.take j).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : n + 1 + j = (n + j) + 1 := by omega
    rw [e, List.replicate_succ, List.cons_append, List.take_succ_cons, List.sum_cons, ih]
    omega

/-- Each list has as many members as its part has rounds. -/
theorem k4Draws_lengths (Q : K4Pub) : (k4Draws Q).map (·.length) =
    List.replicate (k0 Q.g) 1 ++ (k4Tail Q).map (·.moves.length) := by
  rw [k4Tail_moves]
  rcases k0_cases Q.g with ⟨hg, hk⟩ | ⟨hg, hk⟩ <;>
    simp [k4Draws, k4DrawsTail, drawsOfSum, hg, hk, List.replicate]

/-- A member behind the quiet parts in front. -/
theorem k4Draws_at (Q : K4Pub) (j : Nat) : (k4Draws Q)[k0 Q.g + j]? = (k4DrawsTail Q)[j]? := by
  unfold k4Draws
  rcases k0_cases Q.g with ⟨hg, hk⟩ | ⟨hg, hk⟩
  · rw [if_pos hg, hk, List.getElem?_append_right (by simp)]
    simp
  · rw [if_neg (by rw [hg]; exact Bool.false_ne_true), hk,
      List.getElem?_append_right (by simp)]
    simp

/-- **A masked sumcheck's challenges have the call's shape.** FREE OF THE FRAME. hE: each challenge
holds as many elements as the table's row for its round says, and they are as many as the rows. j:
the part's number behind the quiet parts in front. nv: the number of its variables. kk: any call of
nv variables with end values. -/
theorem k4_draws
    (hE : ds.map (·.elems.length) = (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g).map (·.drawn))
    (j nv : Nat) (hj : (k4DrawsTail Q)[j]? = some (drawsOfSum nv))
    (kk : VerifiableInference.Desc.Part.MaskedSum.Call) (hv : kk.vs.length = nv)
    (he : kk.ends.isSome = true) :
    drawsOk kk (partDs ds (movesTo (k4RowIn Q) (k0 Q.g + j)) (nv + 3)) = true := by
  have hR : movesTo (k4RowIn Q) (k0 Q.g + j) =
      (((k4Draws Q).take (k0 Q.g + j)).map (·.length)).sum := by
    rw [k4_moves_at, List.map_take, k4Draws_lengths, ones_take_sum]
  have hn : (drawsOfSum nv).length = nv + 3 := by
    simp [drawsOfSum]
  have hcut := flatten_cut (k4Draws Q) (k0 Q.g + j) _ ((k4Draws_at Q j).trans hj)
  rw [← hR, k4_draws_table, ← hE, hn, ← List.map_drop, ← List.map_take] at hcut
  obtain ⟨e, hee⟩ := Option.isSome_iff_exists.1 he
  unfold drawsOk partDs
  rw [hcut, beq_iff_eq]
  unfold VerifiableInference.Desc.Part.MaskedSum.entries drawsOfSum
  rw [hee]
  simp [VerifiableInference.Desc.Part.MaskedSum.entry]
  refine (List.eq_replicate_iff.2 ⟨by rw [List.length_map, hv], ?_⟩).symm
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.1 hx
  rfl

/-- Rounds that pass the general step's test on shapes have sampled as many elements as their
declared rounds say, and are as many. -/
theorem roundsFit_elems : ∀ (zs : List Fmt.DeclaredRound) (R : List Fmt.RoundView),
    VerifiableInference.Desc.roundsFit zs R = true →
    R.map (·.drawn.elems.length) = zs.map (·.entry.drawE)
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | z :: zs, r :: R, h => by
    have h' : (r.vals.map VerifiableInference.Desc.itemOf == z.items.filter (· != .root) &&
        r.drawn.elems.length == z.entry.drawE && r.drawn.poss.length == z.entry.poss &&
        r.drawn.trits.length == z.entry.trits && r.drawn.poss.all (· < 2 ^ z.entry.logN) &&
        r.drawn.trits.all (fun t => t == -1 || t == 0 || t == 1) &&
        VerifiableInference.Desc.drawsMarkedNonzeroHaveNonzeroWords z r &&
        VerifiableInference.Desc.roundsFit zs R) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨⟨⟨⟨⟨_, h2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, h8⟩ := h'
    rw [List.map_cons, List.map_cons, h2, roundsFit_elems zs R h8]

/-- **The public test accepts at the stand's own challenges and input.** CONDITIONAL on the seat and
on `Thr`. -/
theorem stand_fits (Se : K4Seated T b cells weights tokens look Q p blk)
    (hT : Thr T b k s m E) : k4Fits Q (look Q m.st.heard) (tokens m.st.input.x) = true :=
  Se.fits m.st.heard m.st.input hT.2.1 hT.2.2.2.2.2.2

/-- **At a stand each of the member's challenges holds as many elements as the table's row for its
round says, and they are as many as the rows**: the member's step has tested just that on the rounds
as played (`roundsFit`, Johnson/Desc/Block.lean). -/
theorem stand_elems
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o) :
    ds.map (·.elems.length) = (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g).map (·.drawn) := by
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.stepped.1
  have hf := ((VerifiableInference.Desc.step_iff _ _ _ _ _ _ _).1 Z.stepped.2).1.1
  have h1 := roundsFit_elems _ _ hf
  have h2 := yields_drawn l ds [] y.1 (play_yields l ds [] m y hy)
  rw [← h2, List.map_map]
  refine h1.trans ?_
  rw [k4_rounds Z.seat, List.map_map, List.map_map]
  rfl

/-- **So what has been heard at a prefix of them has the shape of the verifier's table of rounds**
(`OwnFits`, Johnson/Desc/K4/Honest/Law/PtsSizes.lean). `k4_own_fits` (Law/OwnFits.lean) says it from
`drawsFit`; here it comes of the step. CONDITIONAL on the stand and on `Thr` there. -/
theorem stand_own_fits
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (n : Nat) : PtsLaw.OwnFits Q (m.st.heard ++ ds.take n) := by
  intro j d x hj hx
  rw [k4_own_drop Z.seat hT] at hj
  have hdj : ds[j]? = some d := by
    rw [List.getElem?_take] at hj
    split at hj
    · exact hj
    · cases hj
  have h := congrArg (·[j]?) (stand_elems Z)
  simp only [List.getElem?_map, hdj, hx, Option.map_some] at h
  exact Option.some.inj h

/-- **The library's `LedG` at a stand, on the tape of the played rounds**, from the ledger in front
of the member to the one that the step leaves, at what the step has heard of the lookup. -/
theorem stand_led_tape
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o) :
    ∃ (a : VerifiableInference.Desc.K9.Part) (H1 : OnBytes.Model.Layer.Heard)
      (hd2 : OnBytes.Model.Level) (tT : OnBytes.Model.Tsc)
      (F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork) (u5 : OnBytes.K.Kc.Tape),
      VerifiableInference.Desc.K9.segAt? s = some a ∧
      OnBytes.Road.K4.LedG { Q.P with tokv := s.tokv } Q.hp Q.g o.H.fo o a.F A.F
        (OnBytes.K.Kc.paired (roundsOf y.1) (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)) [] H1 hd2
        tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5 := by
  obtain ⟨a, a₀, fo, ha, ha0, haF, _, hh, _⟩ :=
    step_tape Z.seat Z.sits Z.stepped Z.seg Z.heard
  have hSd : Sized a.F := by
    rw [haF]
    exact Z.sized a₀ ha0
  have h' : OnBytes.Desc.First.K4.hear OnBytes.Desc.First.K4.engFl { Q.P with tokv := s.tokv } Q.hp
      Q.g fo a.F (OnBytes.K.Kc.paired (roundsOf y.1) (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)) =
      some (o, A.F, []) := hh
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L⟩ :=
    OnBytes.Road.K4.own_ledG hSd h'
  obtain rfl : o.H.fo = fo := led_fo L
  exact ⟨a, H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, ha, L⟩

/-! ## 3 The five -/

/-- **THE SQUARES' LEVEL: ITS OWN CLAIM IS WORTH 0**: `OwnFront.squares`. F: any ledger later than
the one that the step leaves. CONDITIONAL on the named premises; hσ: the start. -/
theorem squares_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (ds' : List Fmt.Drawn) (F : Fork) (hL : Later A.F F)
    (entry : Nat → Nat → Nat → Cb.Gl.E)
    (hσ : ∀ j, jobSquares Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ1 Q.g))) = some j →
      (normsStart Q.P.y o.H.sW
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ1 Q.g))).gp
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ1 Q.g))).rhoI
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ1 Q.g))).PV).1.value Reading.gl
          (worldBehind T own rdOf k y A ds' F entry) = Reading.gl.val j.cube.total) :
    o.H.wpl.row.value Reading.gl (worldBehind T own rdOf k y A ds' F entry) = 0 := by
  obtain ⟨a, H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, _, L⟩ := stand_led_tape Z
  obtain ⟨_, c, _, _, _, Pl, _⟩ := stand_ground Z
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.stepped.1
  have hp := k4RowIn_at Q 2
  obtain ⟨cp, hcp⟩ := sumAt_some c (k0 Q.g + 2) _ _ (squaresSum Q) hp
  have ha := k4_alone (V := Unit) Pl (k0 Q.g + 2) _ _ (squaresSum Q) hp cp hcp
  have hn : ∀ a b : String, (sumGs a b (squaresSum Q)).length = Q.P.rd.muV + 3 := fun a b => by
    rw [SumLaw.sumGs_count]
    show (List.replicate (Q.P.rd.muV) _).length + 3 = _
    rw [List.length_replicate]
  have hdr := k4_draws (stand_elems Z) 2 Q.P.rd.muV rfl
    ((squaresSum Q).callAt (k4Wit Q cells weights tokens (look Q) m.st.input)
      (frontOf (entryAt Q cells weights tokens look m ds (rJ1 Q.g)) (seenAt m y (rJ1 Q.g))))
    (by
      show (withPoints (List.replicate Q.P.rd.muV _) _).length = _
      rw [SumLaw.withPoints_length, List.length_replicate]) rfl
  rw [hn, (k4_row_nums Q).m1] at ha
  rw [(k4_row_nums Q).m1] at hdr
  obtain ⟨v1, hF⟩ := L.c1
  rw [← L.kWpl] at hF
  have e0 := (k4StartAt_eq Q).1
  exact squares_led m.st.heard L ds (stand_drawn hy _) (stand_reach Z)
    (k4_heard_front Z.seat hT) _ _ _ cp (entryAt Q cells weights tokens look m ds (rJ1 Q.g))
    (seenAt m y (rJ1 Q.g)) _ _ (by rw [e0]; rfl) (stand_fits Z.seat hT)
    (stand_own_fits Z hT _) hdr ha
    (squares_hs Z c Pl.lent _ _ cp hcp ds' F hL entry hF _ _) hσ
    (by rw [e0]; exact tapeIs_paired_drop _ _ _ _)

/-- **THE TOKEN SUMCHECK ON THE ROW PRODUCTS: ITS OWN CLAIM IS WORTH 0**: `OwnFront.rowV`. NO START
IS ASKED. F₁: the ledger that "front" leaves, run from the ledger that the step leaves. F: any
ledger later than F₁. sh: what the ledger that the step leaves shows under the slots of the
sumcheck's end values. CONDITIONAL on the named premises. -/
theorem rows_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (ds' : List Fmt.Drawn) {rows : Bool}
    {P' : OnBytes.Model.Layer.Pub} {g' : Nat} {fs₁ : Array Aff} {F₁ : Fork}
    (hf : formsFrontWith rows P' g' o A.F = some (fs₁, F₁)) (F : Fork) (hL : Later F₁ F)
    (entry : Nat → Nat → Nat → Cb.Gl.E) (hNI : 1 ≤ Q.P.y.NI)
    (sh : Array OnBytes.E)
    (hsh : ((Array.range (4 * Q.P.y.NI)).mapM fun i => A.F.shown (o.H.tV.sEnd + i)) = some sh) :
    (o.H.tV.p.rowForm (rowsSummand Q.P.y o.H sh) {}).value Reading.gl
      (worldBehind T own rdOf k y A ds' F entry) = 0 := by
  obtain ⟨a, H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, _, L⟩ := stand_led_tape Z
  obtain ⟨_, c, _, _, _, Pl, _⟩ := stand_ground Z
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.stepped.1
  have hp := k4RowIn_at Q 5
  obtain ⟨cp, hcp⟩ := sumAt_some c (k0 Q.g + 5) _ _ (rowsSum Q) hp
  have ha := k4_alone (V := Unit) Pl (k0 Q.g + 5) _ _ (rowsSum Q) hp cp hcp
  have hn : ∀ a b : String, (sumGs a b (rowsSum Q)).length = Q.P.y.h.lt + 3 := fun a b => by
    rw [SumLaw.sumGs_count]
    show (List.replicate (Q.P.y.h.lt) _).length + 3 = _
    rw [List.length_replicate]
  have hdr := k4_draws (stand_elems Z) 5 (Q.P.y.h.lt) rfl
    ((rowsSum Q).callAt (k4Wit Q cells weights tokens (look Q) m.st.input)
      (frontOf (entryAt Q cells weights tokens look m ds (rJ2 Q.P Q.g)) (seenAt m y (rJ2 Q.P Q.g))))
    (by
      show (withPoints (List.replicate (Q.P.y.h.lt) _) _).length = _
      rw [SumLaw.withPoints_length, List.length_replicate]) rfl
  rw [hn, (k4_row_nums Q).m2] at ha
  rw [(k4_row_nums Q).m2] at hdr
  obtain ⟨v2, hF⟩ := L.c2
  rw [← L.kTV] at hF
  have e1 := (k4StartAt_eq Q).2.1
  have hLA : Later A.F F := (OnBytes.Desc.First.K4.formsFrontWith_later hf).trans hL
  have hcl := (opened_left Z ds' F hLA entry).cl8
  -- the claimed sum's slot is the next slot of the ledger from which the sumcheck has run
  have hsCl : o.H.tV.sCl = F8.next := (led_sCl L).1
  have hxl : Q.P.y.h.xl = 5 := by
    have hc := fits_covers (stand_fits Z.seat hT)
    unfold OnBytes.Desc.First.K4.covers at hc
    simp only [Bool.and_eq_true] at hc
    exact beq_iff_eq.1 hc.1.1.1.1
  obtain ⟨_, _, _, F1, _, _, _, _, _, hW, _, _⟩ := OnBytes.Desc.First.K4.formsFrontWith_some hf
  obtain ⟨_, _, hO, _, _⟩ := own_ground Z
  exact rows_led m.st.heard L ds (stand_drawn hy _) (stand_reach Z)
    (k4_heard_front Z.seat hT) _ _ _ cp (entryAt Q cells weights tokens look m ds (rJ2 Q.P Q.g))
    (seenAt m y (rJ2 Q.P Q.g)) _ _ (by rw [e1]; rfl) (stand_fits Z.seat hT)
    (stand_own_fits Z hT _) hdr ha
    (rows_hs Z c Pl.lent _ _ cp hcp ds' hf F hL entry hF _ _) hxl hNI
    (fun j hj => by
      rw [OnBytes.Model.Aff.value_slot, ← hsCl]
      refine hcl.trans ?_
      have hj' : jobRows Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
            (m.st.heard ++ ds.take (rJ2 Q.P Q.g))) = some j := hj
      unfold leadWord
      rw [hj']
      show Reading.gl.val ((j.lead).getD 0 zeroE) = _
      rw [jobRows_lead hj']
      rfl)
    (by rw [e1]; exact tapeIs_paired_drop _ _ _ _) A.F F1 sh (Fo.Later.refl A.F) hO.sized hW hsh

/-- **THE FIRST GATED LEVEL: ITS OWN CLAIM IS WORTH 0**: `OwnFront.gated1`. CONDITIONAL on the named
premises; hσ: the start; of hLk one field is read: the lookup's point. -/
theorem gated_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) (ds' : List Fmt.Drawn) (F : Fork)
    (hL : Later A.F F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    (hσ : ∀ tb, gatedTabs Q (k4Wit Q cells weights tokens (look Q) m.st.input) = some tb →
      (Aff.slot o.K.sH1).value Reading.gl (worldBehind T own rdOf k y A ds' F entry) =
        Reading.gl.val (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
          (downFrom (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
              (m.st.heard ++ ds.take (rJ5 Q.P Q.hp Q.g))).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
            ztOf Q (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
              (m.st.heard ++ ds.take (rJ5 Q.P Q.hp Q.g)))) tb).cube.total) :
    o.hd.row.value Reading.gl (worldBehind T own rdOf k y A ds' F entry) = 0 := by
  obtain ⟨a, H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, _, L⟩ := stand_led_tape Z
  obtain ⟨_, c, _, _, _, Pl, _⟩ := stand_ground Z
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.stepped.1
  have hp := k4RowIn_at Q 9
  obtain ⟨cp, hcp⟩ := sumAt_some c (k0 Q.g + 9) _ _ (gatedSum Q) hp
  have ha := k4_alone (V := Unit) Pl (k0 Q.g + 9) _ _ (gatedSum Q) hp cp hcp
  have hn : ∀ a b : String, (sumGs a b (gatedSum Q)).length = Q.P.rd.muH + 3 := fun a b => by
    rw [SumLaw.sumGs_count]
    show (List.replicate (Q.P.rd.muH) _).length + 3 = _
    rw [List.length_replicate]
  have hdr := k4_draws (stand_elems Z) 9 (Q.P.rd.muH) rfl
    ((gatedSum Q).callAt (k4Wit Q cells weights tokens (look Q) m.st.input)
      (frontOf (entryAt Q cells weights tokens look m ds (rJ5 Q.P Q.hp Q.g))
        (seenAt m y (rJ5 Q.P Q.hp Q.g))))
    (by
      show (withPoints (List.replicate (Q.P.rd.muH) _) _).length = _
      rw [SumLaw.withPoints_length, List.length_replicate]) rfl
  rw [hn, (k4_row_nums Q).m5] at ha
  rw [(k4_row_nums Q).m5] at hdr
  obtain ⟨v5, hF⟩ := L.c5
  have e4 := (k4StartAt_eq Q).2.2.2.2.1
  exact gated_led m.st.heard L ds (stand_drawn hy _) (stand_reach Z)
    (k4_heard_front Z.seat hT) _ _ _ cp
    (entryAt Q cells weights tokens look m ds (rJ5 Q.P Q.hp Q.g))
    (seenAt m y (rJ5 Q.P Q.hp Q.g)) _ _ (by rw [e4]; rfl) (stand_zx Z hLk)
    (stand_fits Z.seat hT) (stand_own_fits Z hT _) hdr ha
    (gated_hs Z c Pl.lent _ _ cp hcp ds' F hL entry hF _ _) hσ
    (by rw [e4]; exact tapeIs_paired_drop _ _ _ _)

/-- **THE SECOND GATED LEVEL: ITS OWN CLAIM IS WORTH 0**: `OwnFront.gated2`. CONDITIONAL on the
named premises; hσ: the start. -/
theorem gated2_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (ds' : List Fmt.Drawn) (F : Fork) (hL : Later A.F F)
    (entry : Nat → Nat → Nat → Cb.Gl.E)
    (hσ : ∀ tb, gatedTabs2 Q (k4Wit Q cells weights tokens (look Q) m.st.input) = some tb →
      (OnBytes.Road.Rows.start2 Q.P.y.LamM o.K.sH1
          (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
            (m.st.heard ++ ds.take (rJ6 Q.P Q.hp Q.g))).rhoM).value Reading.gl
          (worldBehind T own rdOf k y A ds' F entry) =
        Reading.gl.val (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
          ((ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
              (m.st.heard ++ ds.take (rJ6 Q.P Q.hp Q.g))).rhoM ++
            downFrom (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
              (m.st.heard ++ ds.take (rJ6 Q.P Q.hp Q.g))).rs Q.P.y.lfe ++
            (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
              (m.st.heard ++ ds.take (rJ6 Q.P Q.hp Q.g))).rt) tb).cube.total) :
    ∀ o2, o.hd2 = some o2 →
      o2.row.value Reading.gl (worldBehind T own rdOf k y A ds' F entry) = 0 := by
  obtain ⟨a, H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, _, L⟩ := stand_led_tape Z
  obtain ⟨_, c, _, _, _, Pl, _⟩ := stand_ground Z
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.stepped.1
  have hp := k4RowIn_at Q 12
  obtain ⟨cp, hcp⟩ := sumAt_some c (k0 Q.g + 12) _ _ (gated2Sum Q) hp
  have ha := k4_alone (V := Unit) Pl (k0 Q.g + 12) _ _ (gated2Sum Q) hp cp hcp
  have hn : ∀ a b : String, (sumGs a b (gated2Sum Q)).length = Q.P.rd.muH2 + 3 := fun a b => by
    rw [SumLaw.sumGs_count]
    show (List.replicate (Q.P.rd.muH2) _).length + 3 = _
    rw [List.length_replicate]
  have hdr := k4_draws (stand_elems Z) 12 (Q.P.rd.muH2) rfl
    ((gated2Sum Q).callAt (k4Wit Q cells weights tokens (look Q) m.st.input)
      (frontOf (entryAt Q cells weights tokens look m ds (rJ6 Q.P Q.hp Q.g))
        (seenAt m y (rJ6 Q.P Q.hp Q.g))))
    (by
      show (withPoints (List.replicate (Q.P.rd.muH2) _) _).length = _
      rw [SumLaw.withPoints_length, List.length_replicate]) rfl
  rw [hn, (k4_row_nums Q).m6] at ha
  rw [(k4_row_nums Q).m6] at hdr
  have e5 := (k4StartAt_eq Q).2.2.2.2.2.1
  exact gated2_led m.st.heard L ds (stand_drawn hy _) (stand_reach Z)
    (k4_heard_front Z.seat hT) _ _ _ cp
    (entryAt Q cells weights tokens look m ds (rJ6 Q.P Q.hp Q.g))
    (seenAt m y (rJ6 Q.P Q.hp Q.g)) _ _ (by rw [e5]; rfl)
    (stand_fits Z.seat hT) (stand_own_fits Z hT _) hdr ha
    (gated2_hs Z c Pl.lent _ _ cp hcp ds' F hL entry hd2 L.eHd2 L.c6 _ _) hσ
    (by rw [e5]; exact tapeIs_paired_drop _ _ _ _)

/-- **THE MERGE: ITS OWN CLAIM IS WORTH 0**: `OwnBack.merge`. F₁: a ledger later than the one that
the step leaves. F₂: the ledger that "back" leaves, run from F₁. F: any ledger later than F₂.
CONDITIONAL on the named premises; hσ: the start: its powers are those of the first element of the
challenge of the batching round in front of the merge (0 where that challenge holds none). -/
theorem merge_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (ds' : List Fmt.Drawn) {F₁ F₂ : Fork} {fs₂ : Array Aff}
    (h1 : Later A.F F₁) (hb : formsBack o F₁ = some (fs₂, F₂))
    (F : Fork) (hL : Later F₂ F)
    (entry : Nat → Nat → Nat → Cb.Gl.E)
    (hσ : ∀ cls, mergeClaimsAt Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1))) = some cls →
      (wsForkStart (mergeSlots Q.hp Q.g o)
          (powers ((ownE ds (rE Q.P Q.hp Q.g) 1).headD zeroE)
            (mergeSlots Q.hp Q.g o).size)).value Reading.gl
          (worldBehind T own rdOf k y A ds' F entry) =
        Reading.gl.val (mergeJobOf Q.P.wsLay
          (k4Wit Q cells weights tokens (look Q) m.st.input).w cls
          (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
            (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1))).rhoW).cube.total) :
    (o.wo.toWsMerged.p.rowForm o.wo.toWsMerged.fvp {}).value Reading.gl
      (worldBehind T own rdOf k y A ds' F entry) = 0 := by
  obtain ⟨a, H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, _, L⟩ := stand_led_tape Z
  obtain ⟨_, c, _, _, _, Pl, _⟩ := stand_ground Z
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.stepped.1
  have hp := k4RowIn_at Q 15
  obtain ⟨cp, hcp⟩ := sumAt_some c (k0 Q.g + 15) _ _ (mergeSum Q) hp
  have ha := k4_alone (V := Unit) Pl (k0 Q.g + 15) _ _ (mergeSum Q) hp cp hcp
  have hn : ∀ a b : String, (sumGs a b (mergeSum Q)).length = Q.P.wsLay.lk + 3 := fun a b => by
    rw [SumLaw.sumGs_count]
    show (List.replicate (Q.P.wsLay.lk) _).length + 3 = _
    rw [List.length_replicate]
  have hdr := k4_draws (stand_elems Z) 15 (Q.P.wsLay.lk) rfl
    ((mergeSum Q).callAt (k4Wit Q cells weights tokens (look Q) m.st.input)
      (frontOf (entryAt Q cells weights tokens look m ds (rE Q.P Q.hp Q.g + 1))
        (seenAt m y (rE Q.P Q.hp Q.g + 1))))
    (by
      show (withPoints (List.replicate (Q.P.wsLay.lk) _) _).length = _
      rw [SumLaw.withPoints_length, List.length_replicate]) rfl
  rw [hn, k4_moves_merge] at ha
  rw [k4_moves_merge] at hdr
  obtain ⟨cl, hF⟩ := L.c7
  have e6 := (k4StartAt_eq Q).2.2.2.2.2.2
  obtain ⟨F1, _, hW, _⟩ := OnBytes.Desc.First.K4.formsBack_some hb
  obtain ⟨_, _, hO, _, _⟩ := own_ground Z
  -- the element that batches the merge's claims, in the challenges' letters
  have hu : tapeEps u5 = (ownE ds (rE Q.P Q.hp Q.g) 1).headD zeroE := by
    rw [L.u5e, (cuts { Q.P with tokv := s.tokv } Q.hp Q.g _).2.2.2.2.2.2]
    exact tape_beta hy _ _
  exact merge_led m.st.heard L ds (stand_reach Z) (k4_heard_front Z.seat hT) _ _ _ cp
    (entryAt Q cells weights tokens look m ds (rE Q.P Q.hp Q.g + 1))
    (seenAt m y (rE Q.P Q.hp Q.g + 1)) _ _ (by rw [e6]; rfl) (stand_fits Z.seat hT)
    (stand_own_fits Z hT _) hdr ha
    (merge_hs Z c Pl.lent _ _ cp hcp ds' h1 hb F hL entry L.sG5 hF _ _)
    (by rw [hu]; exact hσ) (by rw [e6]; exact tapeIs_paired_drop _ _ _ _) F₁ F1
    (OnBytes.Desc.First.K4.later_fo h1) (h1.sized hO.sized) hW

/-! ## 4 The two structures -/

/-- **`OwnFront`, WHOLE, AT ONE WORLD**: that of a ledger later than the one that "front" leaves.
The three starts are asked at that world. CONDITIONAL on the named premises. -/
theorem ownFront_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) (ds' : List Fmt.Drawn) {rows : Bool}
    {P' : OnBytes.Model.Layer.Pub} {g' : Nat} {fs₁ : Array Aff} {F₁ : Fork}
    (hf : formsFrontWith rows P' g' o A.F = some (fs₁, F₁)) (F : Fork) (hL : Later F₁ F)
    (entry : Nat → Nat → Nat → Cb.Gl.E) (hNI : 1 ≤ Q.P.y.NI) (sh : Array OnBytes.E)
    (hsh : ((Array.range (4 * Q.P.y.NI)).mapM fun i => A.F.shown (o.H.tV.sEnd + i)) = some sh)
    (hσ1 : ∀ j, jobSquares Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ1 Q.g))) = some j →
      (normsStart Q.P.y o.H.sW
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ1 Q.g))).gp
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ1 Q.g))).rhoI
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ1 Q.g))).PV).1.value Reading.gl
          (worldBehind T own rdOf k y A ds' F entry) = Reading.gl.val j.cube.total)
    (hσ5 : ∀ tb, gatedTabs Q (k4Wit Q cells weights tokens (look Q) m.st.input) = some tb →
      (Aff.slot o.K.sH1).value Reading.gl (worldBehind T own rdOf k y A ds' F entry) =
        Reading.gl.val (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
          (downFrom (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
              (m.st.heard ++ ds.take (rJ5 Q.P Q.hp Q.g))).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
            ztOf Q (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
              (m.st.heard ++ ds.take (rJ5 Q.P Q.hp Q.g)))) tb).cube.total)
    (hσ6 : ∀ tb, gatedTabs2 Q (k4Wit Q cells weights tokens (look Q) m.st.input) = some tb →
      (OnBytes.Road.Rows.start2 Q.P.y.LamM o.K.sH1
          (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
            (m.st.heard ++ ds.take (rJ6 Q.P Q.hp Q.g))).rhoM).value Reading.gl
          (worldBehind T own rdOf k y A ds' F entry) =
        Reading.gl.val (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
          ((ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
              (m.st.heard ++ ds.take (rJ6 Q.P Q.hp Q.g))).rhoM ++
            downFrom (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
              (m.st.heard ++ ds.take (rJ6 Q.P Q.hp Q.g))).rs Q.P.y.lfe ++
            (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
              (m.st.heard ++ ds.take (rJ6 Q.P Q.hp Q.g))).rt) tb).cube.total) :
    OnBytes.Road.K4.W.OwnFront Reading.gl (worldBehind T own rdOf k y A ds' F entry) Q.P o sh := by
  have hLA : Later A.F F := (OnBytes.Desc.First.K4.formsFrontWith_later hf).trans hL
  exact ⟨squares_stand Z hT ds' F hLA entry hσ1, rows_stand Z hT ds' hf F hL entry hNI sh hsh,
    gated_stand Z hT hLk ds' F hLA entry hσ5, gated2_stand Z hT ds' F hLA entry hσ6⟩

/-- **`OwnBack`**, from the batched sumcheck's own claim, which is a hypothesis here, and the
merge's. CONDITIONAL on the named premises. -/
theorem ownBack_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (ds' : List Fmt.Drawn) {F₁ F₂ : Fork} {fs₂ : Array Aff}
    (h1 : Later A.F F₁) (hb : formsBack o F₁ = some (fs₂, F₂))
    (F : Fork) (hL : Later F₂ F)
    (entry : Nat → Nat → Nat → Cb.Gl.E)
    (hstack : o.K.rowS.value Reading.gl (worldBehind T own rdOf k y A ds' F entry) = 0)
    (hσ : ∀ cls, mergeClaimsAt Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1))) = some cls →
      (wsForkStart (mergeSlots Q.hp Q.g o)
          (powers ((ownE ds (rE Q.P Q.hp Q.g) 1).headD zeroE)
            (mergeSlots Q.hp Q.g o).size)).value Reading.gl
          (worldBehind T own rdOf k y A ds' F entry) =
        Reading.gl.val (mergeJobOf Q.P.wsLay
          (k4Wit Q cells weights tokens (look Q) m.st.input).w cls
          (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
            (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1))).rhoW).cube.total) :
    OnBytes.Road.K4.W.OwnBack Reading.gl (worldBehind T own rdOf k y A ds' F entry) o := by
  exact ⟨hstack, merge_stand Z hT ds' h1 hb F hL entry hσ⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.rowSteps_cut
#print axioms ProofFile.Honest.K4.movesTo_le
#print axioms ProofFile.Honest.K4.ones_take_sum
#print axioms ProofFile.Honest.K4.k4Draws_lengths
#print axioms ProofFile.Honest.K4.k4Draws_at
#print axioms ProofFile.Honest.K4.k4_alone
#print axioms ProofFile.Honest.K4.k4_draws_table
#print axioms ProofFile.Honest.K4.flatten_cut
#print axioms ProofFile.Honest.K4.k4_draws
#print axioms ProofFile.Honest.K4.roundsFit_elems
#print axioms ProofFile.Honest.K4.stand_fits
#print axioms ProofFile.Honest.K4.stand_elems
#print axioms ProofFile.Honest.K4.stand_own_fits
#print axioms ProofFile.Honest.K4.stand_led_tape
#print axioms ProofFile.Honest.K4.squares_stand
#print axioms ProofFile.Honest.K4.rows_stand
#print axioms ProofFile.Honest.K4.gated_stand
#print axioms ProofFile.Honest.K4.gated2_stand
#print axioms ProofFile.Honest.K4.merge_stand
#print axioms ProofFile.Honest.K4.ownFront_stand
#print axioms ProofFile.Honest.K4.ownBack_stand
