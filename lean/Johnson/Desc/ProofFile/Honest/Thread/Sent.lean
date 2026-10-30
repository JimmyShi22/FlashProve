-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Sent.lean: AT A STAND INSIDE A MEMBER (`Inside`,
Honest/Thread/Pays.lean; from the pair: `InsideS`, Honest/Thread/OnSaid.lean): HELPS FOR WHOEVER
PAYS A DEBT THERE, AND ONE FORM: A TREE THAT A ROW's EARLIER PART SENDS IS HELD AGAINST THE THREAD's
TABLE ONCE, right behind the sending part; from that one sentence follow the same at every later
round of the member, where a later part's sentence at its entry reads the tree (`OnFrom`,
`OnFromS`), and the clause on the member's new trees that `Plays` | `PlaysS` owe at the member's
end. Two definitions: premises' forms; and lemmas. General in the thread: no kind is named.

  1  `Env.add_own`, `inside_own`   the trees that the rounds played inside the member have sent
  2  `Thread.handAt_elim`, `Thread.col_of_handAt`   what "at hand, and shows what the thread's table
     shows" says
  3  `rowSteps_take_head`   a row's Steps, cut behind its first part
  4  `SentAt`, `SentAtS`   THE FORM; the pair's twin; `sentAtS_of`: the twin is the weaker premise
  5  `handAt_more`, `sentAt_more`, `sentAtS_more`   it stays so behind further rounds of the member
  6  `inside_of_moved`, `insideS_of_moved`, `trees_of_sent`, `trees_of_sentS`   the clause at the
     member's end

THE PRICE OF THE FORM. A sentence at an entry that is had from the thread's table spends `TrueTo`'s
bound on a listed position, under the named premise that len at the tree is at most the table's
logLength: `Table.same` speaks below the table's length alone. An author who reads its own part's
text instead owes no such premise.

Worked at the fourth toy row: Honest/Thread/Four/FourOnce.lean, FourKit.lean (not in the sealed
library).

Limits. Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by
round, and as many challenges as rounds): `handAt_more`, `inside_of_moved`, `insideS_of_moved`,
`trees_of_sent`, `trees_of_sentS`. `rowSteps_take_head` cuts one part off: a cut behind the j-th
part in one sentence wants the row's coins cut likewise, for which no term is typed. The forms have
not been weighed. None is one of the library's goals. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.OnSaid
import Johnson.Desc.ProofFile.Honest.Thread.ThrRow
import Johnson.Desc.ProofFile.Honest.Law.Rule.RowModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Oracle)

/-! ## 1 The trees that rounds played have sent -/

/-- **Behind rounds that were played the chain's next own trees are these rounds' tables, in the
order of sending.** -/
theorem Env.add_own (E : Env) (ps : List Played) (i : Nat) :
    (E.add ps).tree (.own (E.sent + i)) = ((tablesOf ps)[i]?).bind id := by
  show (if E.sent + i < E.sent then E.tree (.own (E.sent + i))
    else ((tablesOf ps)[E.sent + i - E.sent]?).bind id) = _
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **INSIDE A MEMBER**: `Inside`, taken apart, with the trees that the rounds played have sent: by
the thread's clause (X) on how many trees stand sent in front of the member. -/
theorem inside_own {b n : Nat} {k : Coins Bk} {m : Mid W X} {E : Env}
    (h : Inside T b n k m E) :
    ∃ (blk : Block S Cl) (s : S) (m₀ : Mid W X) (E₀ : Env) (l : List (Step W X))
      (ds : List Fmt.Drawn) (ps : List Played), T.bs[b]? = some blk ∧ Thr T b k s m₀ E₀ ∧
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m₀.st.input) [blk] T.hs =
        .ok l ∧
      drawsFit (blk.rounds.take n) ds = true ∧ play (l.take n) ds [] m₀ = .ok (ps, m) ∧
      ∀ i, E.tree (.own (treesTo T.bs b + i)) = ((tablesOf ps)[i]?).bind id := by
  unfold Inside at h
  obtain ⟨blk, s, m₀, E₀, l, ds, y, hblk, hA, hl, hd, hy, rfl, rfl⟩ := h
  have hA' := hA
  unfold Thr Thread.Made at hA'
  have hs : E₀.sent = treesTo T.bs b := hA'.2.2.2.2.1.2.2.1
  refine ⟨blk, s, m₀, E₀, l, ds, y.1, hblk, hA, hl, hd, hy, fun i => ?_⟩
  rw [← hs]
  exact Env.add_own E₀ y.1 i

/-! ## 2 What "at hand" says -/

/-- **A table is at hand behind the source, from the thread's sender, and shows what the thread's
table shows.** -/
theorem Thread.handAt_elim {σ : Fmt.TreeSource} {k : Coins Bk} {m : Mid W X} {E : Env}
    (h : T.handAt σ k m E = true) :
    ∃ pt, E.tree σ = some pt ∧ pt.1 = (T.tableAt σ k m).1 ∧
      pt.2.same (T.tableAt σ k m).2 = true := by
  unfold Thread.handAt at h
  cases hE : E.tree σ with
  | none =>
    rw [hE] at h
    cases h
  | some pt =>
    rw [hE] at h
    have h' : (pt.1 == (T.tableAt σ k m).1 && pt.2.same (T.tableAt σ k m).2) = true := h
    rw [Bool.and_eq_true] at h'
    exact ⟨pt, rfl, beq_iff_eq.1 h'.1, h'.2⟩

/-- **Its columns below the thread's table's length are that table's.** -/
theorem Thread.col_of_handAt {σ : Fmt.TreeSource} {k : Coins Bk} {m : Mid W X} {E : Env}
    (h : T.handAt σ k m E = true) :
    ∃ pt, E.tree σ = some pt ∧ ∀ x, x < 2 ^ (T.tableAt σ k m).2.logLength →
      pt.2.col x = (T.tableAt σ k m).2.col x := by
  obtain ⟨pt, hE, -, hs⟩ := T.handAt_elim h
  obtain ⟨hl, hc⟩ := Table.same_elim hs
  exact ⟨pt, hE, fun x hx => hc x (by
    rw [hl]
    exact hx)⟩

end

/-! ## 3 A row's Steps, cut behind its first part -/

/-- **THE FIRST SO MANY STEPS OF A ROW ARE ITS FIRST PART's OWN, AT THAT PART's COINS; THE OTHERS
ARE THE REST OF THE ROW's**, where the sub-protocol has at least as many rounds as the part has
moves. -/
theorem rowSteps_take_head {V W Y : Type} (name : String) (a : Place) (v : Option V)
    (p : Part V W Y) (ps : List (Part V W Y)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (c : RowCoins (p :: ps))
    (h : p.moves.length ≤ rs.length) :
    (rowSteps name a v (p :: ps) j rs c).take p.moves.length =
        p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1 ∧
      (rowSteps name a v (p :: ps) j rs c).drop p.moves.length =
        rowSteps name a v ps (j + 1) (rs.drop p.moves.length) c.2 := by
  have h1 : (rs.take p.moves.length).length ≤ p.moves.length := by
    rw [List.length_take]
    exact Nat.min_le_left _ _
  have hl : (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1).length = p.moves.length := by
    rw [steps_len p name ⟨a, j⟩ _ v c.1 h1, List.length_take, Nat.min_eq_left h]
  have e : rowSteps name a v (p :: ps) j rs c =
      p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1 ++
        rowSteps name a v ps (j + 1) (rs.drop p.moves.length) c.2 := rfl
  rw [e]
  exact ⟨List.take_left' hl, List.drop_left' hl⟩

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-! ## 4 The form -/

/-- **BEHIND THE FIRST n ROUNDS OF THE MEMBER NUMBER b THE TREE BEHIND σ IS AT HAND AND SHOWS WHAT
THE THREAD's TABLE SHOWS.** It is a definition: a premise's form. Nothing is claimed of it, and it
is none of the library's goals. -/
def SentAt (b n : Nat) (σ : Fmt.TreeSource) : Prop :=
  ∀ k m E, Inside T b n k m E → T.handAt σ k m E = true

/-- **THE PAIR's TWIN**: the same, asked from a stand that was reached from the pair of the thread
and what is said. It is a definition: a premise's form. Nothing is claimed of it, and it is none of
the library's goals. -/
def SentAtS (Said : Nat → Coins Bk → Mid W X → Prop) (b n : Nat) (σ : Fmt.TreeSource) : Prop :=
  ∀ k m E, InsideS T Said b n k m E → T.handAt σ k m E = true

/-- The twin is the weaker premise. -/
theorem sentAtS_of (Said : Nat → Coins Bk → Mid W X → Prop) {b n : Nat} {σ : Fmt.TreeSource}
    (h : SentAt T b n σ) : SentAtS T Said b n σ :=
  fun k m E hI => h k m E (inside_of_insideS T Said hI)

/-! ## 5 It stays so behind further rounds of the member -/

/-- **The play of the member's first n + j Steps, cut behind n**: the first n are played too, at the
first n challenges; and a tree that is at hand behind them, and fixed by the challenges heard there,
is at hand behind all n + j. -/
theorem handAt_more {b n j : Nat} {σ : Fmt.TreeSource} {blk : Block S Cl} {k : Coins Bk} {s : S}
    {m₀ : Mid W X} {E₀ : Env} {l : List (Step W X)} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} (hn : n + j ≤ blk.rounds.length)
    (hx : T.fixed σ ≤ T.front + roundsTo T.bs b + n) (hA : Thr T b k s m₀ E₀)
    (hl : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m₀.st.input) [blk] T.hs =
      .ok l)
    (hd : drawsFit (blk.rounds.take (n + j)) ds = true)
    (hy : play (l.take (n + j)) ds [] m₀ = .ok y) :
    ∃ y₁, drawsFit (blk.rounds.take n) (ds.take n) = true ∧
      play (l.take n) (ds.take n) [] m₀ = .ok y₁ ∧
      (T.handAt σ k y₁.2 (E₀.add y₁.1) = true → T.handAt σ k y.2 (E₀.add y.1) = true) := by
  have hnl : l.length = blk.rounds.length := by
    have e := congrArg List.length (steps_decl hl)
    rw [List.length_map, List.flatMap_cons, List.flatMap_nil, List.append_nil] at e
    exact e
  have hnr : n ≤ blk.rounds.length := Nat.le_trans (Nat.le_add_right n j) hn
  have hdl : ds.length = n + j := by
    rw [drawsFit_length _ _ hd, List.length_take, Nat.min_eq_left hn]
  have h1 : (ds.take n).length = (l.take n).length := by
    rw [List.length_take, List.length_take, hdl, hnl, Nat.min_eq_left (Nat.le_add_right n j),
      Nat.min_eq_left hnr]
  have hd₁ : drawsFit (blk.rounds.take n) (ds.take n) = true := by
    have e := hd
    rw [List.take_add, drawsFit_append, Bool.and_eq_true, List.length_take,
      Nat.min_eq_left hnr] at e
    exact e.1
  rw [List.take_add, ← List.take_append_drop n ds, play_append _ _ _ _ _ _ h1] at hy
  obtain ⟨y₁, hy₁, hy⟩ := exBind_ok hy
  obtain ⟨z, hz, rfl⟩ := exMap_ok hy
  refine ⟨y₁, hd₁, hy₁, fun h₁ => ?_⟩
  have hA' := hA
  unfold Thr at hA'
  obtain ⟨-, hF, -, -, hM, -, -⟩ := hA'
  unfold Thread.Made at hM
  obtain ⟨-, -, -, hTi, -⟩ := hM
  have hx' : T.fixed σ ≤ y₁.2.st.heard.length := by
    rw [play_heard _ _ _ _ _ hy₁, List.length_append, T.heard_length hF, List.length_take, hdl,
      Nat.min_eq_left (Nat.le_add_right n j)]
    exact hx
  have h₂ := T.handAt_next (ps := z.1) (play_mid _ _ _ _ _ hz).1 (play_heard _ _ _ _ _ hz) hx'
    (Env.add_tight hTi y₁.1) h₁
  show T.handAt σ k z.2 (E₀.add (y₁.1 ++ z.1)) = true
  rw [← Env.add_add]
  exact h₂

theorem sentAt_more {b n j : Nat} {σ : Fmt.TreeSource} {blk : Block S Cl}
    (hblk : T.bs[b]? = some blk) (hn : n + j ≤ blk.rounds.length)
    (hx : T.fixed σ ≤ T.front + roundsTo T.bs b + n) (h : SentAt T b n σ) :
    SentAt T b (n + j) σ := by
  intro k m E hI
  unfold Inside at hI
  obtain ⟨blk', s, m₀, E₀, l, ds, y, hb', hA, hl, hd, hy, rfl, rfl⟩ := hI
  rw [hblk] at hb'
  cases hb'
  obtain ⟨y₁, hd₁, hy₁, hgo⟩ := handAt_more T hn hx hA hl hd hy
  refine hgo (h k _ _ ?_)
  unfold Inside
  exact ⟨blk, s, m₀, E₀, l, ds.take n, y₁, hblk, hA, hl, hd₁, hy₁, rfl, rfl⟩

theorem sentAtS_more (Said : Nat → Coins Bk → Mid W X → Prop) {b n j : Nat} {σ : Fmt.TreeSource}
    {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (hn : n + j ≤ blk.rounds.length)
    (hx : T.fixed σ ≤ T.front + roundsTo T.bs b + n) (h : SentAtS T Said b n σ) :
    SentAtS T Said b (n + j) σ := by
  intro k m E hI
  unfold InsideS at hI
  obtain ⟨blk', s, m₀, E₀, l, ds, y, hb', hA, hS, hl, hd, hy, rfl, rfl⟩ := hI
  rw [hblk] at hb'
  cases hb'
  obtain ⟨y₁, hd₁, hy₁, hgo⟩ := handAt_more T hn hx hA hl hd hy
  refine hgo (h k _ _ ?_)
  unfold InsideS
  exact ⟨blk, s, m₀, E₀, l, ds.take n, y₁, hblk, hA, hS, hl, hd₁, hy₁, rfl, rfl⟩

/-! ## 6 The clause at the member's end -/

/-- Behind the member's whole step the run stands behind all its rounds. -/
theorem inside_of_moved {b : Nat} {blk : Block S Cl} {k : Coins Bk} {s : S} {m : Mid W X}
    {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hblk : T.bs[b]? = some blk) (hA : Thr T b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hMv : T.Moved blk k m E ds y cols) : Inside T b blk.rounds.length k y.2 (E.add y.1) := by
  unfold Thread.Moved at hMv
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  have hnl : l.length = blk.rounds.length := by
    have e := congrArg List.length (steps_decl hl)
    rw [List.length_map, List.flatMap_cons, List.flatMap_nil, List.append_nil] at e
    exact e
  unfold Inside
  refine ⟨blk, s, m, E, l, ds, y, hblk, hA, hl, ?_, ?_, rfl, rfl⟩
  · rw [List.take_length]
    exact hd
  · rw [← hnl, List.take_length]
    exact hy

/-- The pair's twin. -/
theorem insideS_of_moved (Said : Nat → Coins Bk → Mid W X → Prop) {b : Nat} {blk : Block S Cl}
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List OpenedColumn} (hblk : T.bs[b]? = some blk)
    (hA : ThrS T Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hMv : T.Moved blk k m E ds y cols) :
    InsideS T Said b blk.rounds.length k y.2 (E.add y.1) := by
  unfold Thread.Moved at hMv
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  have hnl : l.length = blk.rounds.length := by
    have e := congrArg List.length (steps_decl hl)
    rw [List.length_map, List.flatMap_cons, List.flatMap_nil, List.append_nil] at e
    exact e
  unfold InsideS
  refine ⟨blk, s, m, E, l, ds, y, hblk, hA.1, hA.2, hl, ?_, ?_, rfl, rfl⟩
  · rw [List.take_length]
    exact hd
  · rw [← hnl, List.take_length]
    exact hy

/-- **THE CLAUSE ON THE MEMBER's NEW TREES, AT ITS END**: the premise hT of `plays_of_playsOn`
(Honest/Thread/FileRow.lean), letter for letter. -/
theorem trees_of_sent {b : Nat} {blk : Block S Cl} (hblk : T.bs[b]? = some blk)
    (h : ∀ σ ∈ T.fresh b, SentAt T b blk.rounds.length σ) :
    ∀ k s m E ds y cols, Thr T b k s m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1) :=
  fun k _ _ _ _ _ _ hA hd hMv σ hσ => h σ hσ k _ _ (inside_of_moved T hblk hA hd hMv)

/-- The pair's twin: what `PlaysS` (Honest/Thread/PaysS.lean) owes of the member's new trees. -/
theorem trees_of_sentS (Said : Nat → Coins Bk → Mid W X → Prop) {b : Nat} {blk : Block S Cl}
    (hblk : T.bs[b]? = some blk) (h : ∀ σ ∈ T.fresh b, SentAtS T Said b blk.rounds.length σ) :
    ∀ k s m E ds y cols, ThrS T Said b k s m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1) :=
  fun k _ _ _ _ _ _ hA hd hMv σ hσ => h σ hσ k _ _ (insideS_of_moved T Said hblk hA hd hMv)

end

end ProofFile.Honest

#print axioms ProofFile.Honest.Env.add_own
#print axioms ProofFile.Honest.inside_own
#print axioms ProofFile.Honest.Thread.handAt_elim
#print axioms ProofFile.Honest.Thread.col_of_handAt
#print axioms ProofFile.Honest.rowSteps_take_head
#print axioms ProofFile.Honest.sentAtS_of
#print axioms ProofFile.Honest.handAt_more
#print axioms ProofFile.Honest.sentAt_more
#print axioms ProofFile.Honest.sentAtS_more
#print axioms ProofFile.Honest.inside_of_moved
#print axioms ProofFile.Honest.insideS_of_moved
#print axioms ProofFile.Honest.trees_of_sent
#print axioms ProofFile.Honest.trees_of_sentS
