-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/SeatedPlays.lean: THE SMALLNESS TEST AT ITS OWN MEMBER: WHAT ITS
PLAY IS, AND THE FIRST OF ITS DEBTS: IT PLAYS (`Spec.small_plays`,
Johnson/Desc/ProofFile/Honest/K8/Seated.lean). Lemmas on the frame's own definitions and the kind's
row, general in the thread; none of the library's goals.

  `round_bare`   the kind's declared round cuts no item but roots, opens no stored tree and no tree
  `seated_rounds`   at the seat the member's rounds are that one round
  `row_play`   a row that is one quiet part with a second stop, played by the frame's `play` at one
                   round without an oracle message, where the stop is silent at both askings: the
                   value, written out (`quiet_play_stop`,
                   Johnson/Desc/ProofFile/Honest/K9/QuietMember.lean, at a row)
  `silent_of_chain`   where nothing of the member stops (`chainStopAt` at the one member says none)
                   the kind's second stop is silent at both askings
  `seated_play`   AT THE SEAT: the Steps that `chainSteps` lays for the member, played at one
                   challenge d from any stand m at which nothing of it stops: one round, in which
                   nothing is sent; the input is kept; d is heard
  `seated_cols`   the member's round reads no column
  `seated_fresh`   no tree is new behind the member
  **`small_plays`**
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.Seated
import Johnson.Desc.ProofFile.Honest.K8.QuietForm
import Johnson.Desc.ProofFile.Honest.Thread.QuietLaw
import Johnson.Desc.ProofFile.Honest.Law.Thread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Par Seats approximateRangeProofDrawKind atS round)
open ProofFile.Honest.K9 (quietStop silent_of_stopAt quiet_play_stop)

variable {W₀ Rc Xi Tr X Pb : Type} {Bk : ProverCoinCounts}

/-- The kind's declared round. -/
theorem round_bare (p : Par) :
    (round p).items.filter (· != .root) = [] ∧ (round p).stored = [] ∧ (round p).opens = [] :=
  ⟨by simp [VerifiableInference.Desc.First.K8.round, Fmt.DeclaredRound.items, Fmt.Entry.cut], rfl, rfl⟩

theorem seated_rounds {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {blk : Block S Claim} {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)}
    (h : K8Seated T b blk cells P) : blk.rounds = [round P.1] := h.seats.1

/-- What the one round's play yields. -/
def playedAt {W X : Type} (name : String) (a : Place) (d : Fmt.Drawn) (m : Mid W X) :
    List Played × Mid W X :=
  ([⟨name, a, 0, true, [], [], d⟩],
    ⟨{ m.st.hears d with own := (m.st.hears d).own }, m.loc ++ [d], m.seen ++ [⟨[], d⟩], m.opened⟩)

/-- A row that is one quiet part with a second stop, played. -/
theorem row_play {V W X : Type} (hh : V → List Fmt.Drawn → List Fmt.Drawn → Option String)
    (sh : Odds) (d₀ : Fmt.DeclaredRound) (hi : d₀.items.filter (· != .root) = []) (name : String)
    (a : Place) (v : Option V) (d : Fmt.Drawn) (m : Mid W X)
    (h0 : (v.bind fun u => hh u m.loc []) = none) (h1 : (v.bind fun u => hh u m.loc [d]) = none) :
    ∀ (ps : List (Part V W X)) (c : RowCoins ps), ps = [quietStop hh sh] →
      play (rowSteps name a v ps 0 [(d₀, [])] c) [d] [] m = .ok (playedAt name a d m) := by
  intro ps c e
  subst e
  have e2 : rowSteps name a v [(quietStop hh sh : Part V W X)] 0 [(d₀, [])] c =
      (quietStop hh sh : Part V W X).steps name ⟨a, 0⟩ [(d₀, [])] v c.1 := by
    simp [rowSteps, quietStop, quietPart]
  rw [e2]
  exact quiet_play_stop hh sh d₀ hi name ⟨a, 0⟩ v c.1 d m h0 h1

/-- Where nothing of the member stops, the kind's second stop is silent at both askings. -/
theorem silent_of_chain {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {blk : Block S Claim} {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)}
    (h : K8Seated T b blk cells P) (v : Option (Local W₀ Rc Xi Tr)) (loc : List Fmt.Drawn)
    (d : Fmt.Drawn) (hs : chainStopAt v [blk] T.hs loc [d] = none) :
    (v.bind fun u => smallStop cells P u loc []) = none ∧
      (v.bind fun u => smallStop cells P u loc [d]) = none := by
  refine silent_of_stopAt (W := Local W₀ Rc Xi Tr) (X := X) (smallStop cells P) (windowShare P.1) v
    loc d ?_
  intro hx
  simp only [chainStopAt, h.half, Option.bind_some, seated_rounds h, List.length_cons,
    List.length_nil, small_parts W₀ Rc Xi Tr X cells P h.named, rowStopAt] at hs
  have e : (quietStop (smallStop cells P) (windowShare P.1) :
      Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).moves.length = 1 := rfl
  simp [e, hx] at hs

/-- **At the seat: the member's play.** -/
theorem seated_play {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {blk : Block S Claim} {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)}
    (h : K8Seated T b blk cells P) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option (Local W₀ Rc Xi Tr)) (l : List (Step (Local W₀ Rc Xi Tr) X))
    (hl : chainSteps Bk rows look v [blk] T.hs = .ok l) (d : Fmt.Drawn)
    (m : Mid (Local W₀ Rc Xi Tr) X) (hs : chainStopAt v [blk] T.hs m.loc [d] = none) :
    play l [d] [] m = .ok (playedAt blk.name blk.place d m) := by
  obtain ⟨c, -, rfl⟩ := steps_one_half h.half hl
  obtain ⟨h0, h1⟩ := silent_of_chain h v m.loc d hs
  unfold Placed.steps
  rw [seated_rounds h, h.oracles]
  exact row_play (smallStop cells P) (windowShare P.1) (round P.1) (round_bare P.1).1 blk.name
    blk.place v d m h0 h1 _ c (small_parts W₀ Rc Xi Tr X cells P h.named)

/-- The member's round reads no column. -/
theorem seated_cols (p : Par) (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (ds : List Fmt.Drawn) :
    fillCols (readsOf chain ft stored tree [round p] ds) [] = .ok [] := by
  cases ds with
  | nil => rfl
  | cons d t => cases t <;> rfl

/-- No tree is new behind the member. -/
theorem seated_fresh {T : Thread Bk S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {blk : Block S Claim} {cells : Tr → Cells} {P : Par × List (Nat × String × Nat)}
    (h : K8Seated T b blk cells P) : T.fresh b = [] := by
  have e : T.hand (b + 1) = T.hand b := by
    unfold Thread.hand
    rw [treesTo_succ h.here, h.oracles]
    rfl
  unfold Thread.fresh
  rw [e]
  exact List.filter_eq_nil_iff.2 fun σ hσ => by simp [hσ]

theorem small_plays : Spec.small_plays := by
  intro W₀ Rc Xi Tr X Pb Bk T b blk cells P h blk' hblk' k s m E ds l _ hd hstop hl
  rw [h.here] at hblk'
  cases hblk'
  rw [seated_rounds h] at hd
  obtain ⟨d, rfl, _⟩ := drawsFit_one hd
  refine ⟨playedAt blk.name blk.place d m, [],
    ⟨⟨l, hl, seated_play h _ _ _ l hl d m hstop⟩, ?_⟩, ?_⟩
  · rw [seated_rounds h]
    exact seated_cols P.1 _ _ _ _ _
  · rw [seated_fresh h]
    exact fun σ hσ => nomatch hσ

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.seated_play
#print axioms ProofFile.Honest.K8.small_plays
