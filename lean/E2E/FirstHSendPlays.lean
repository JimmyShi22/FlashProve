-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHSendPlays.lean: the frame's play of a sending and of the batching, at halves whose input is
the prover's own: `K1.proverSideOfSending`, where the library's laws stand at `placeHalf` over `PlaceIn`, and
`K13.proverSideOfClaimCombination` at any type of state, where the library's stand at the proof file's. The proofs are the
library's (Johnson/Desc/ProofFile/Honest/K1/Plays.lean, K1/PlaysS.lean, K13/Debts.lean,
K13/AtThread.lean), at these halves. General in the thread.

  `playedSend`: a sending's two rounds as played.
  `send_row_silent`, `played_send`: its stops never stop; the frame's terms for a row return it.
  `send_moved`, `send_moved_term`: the play and the columns' laying return, and what is played.
  `plays_send`: `Plays` from the thread alone, where the thread's tables at the sending's trees are
    the sender's own term (the form of `send_Plays`, Honest/K14/SendingsPaid.lean).
  `moved_k13`, `plays_k13`: the batching's.

Limits. Premises on the member, the half and the job stay premises. Nothing on acceptance.
-/
import Johnson.Desc.ProofFile.Honest.K1.Plays
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.ProofFile.Honest.K1.ScriptLendRow
import Johnson.Desc.ProofFile.Honest.K14.KitTwo
import Johnson.Desc.ProofFile.Honest.Thread.Sent
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.ProofFile.Honest.K13.Debts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Slice VerifiableInference.Desc
open ProofFile.Honest ProofFile.Honest.K1
open Johnson.Prover.Send (Rows shapeAt col answers)
open ProofFile.Honest.Small (playedRow fitsRow stateRow play_row_whole member_played)
open ProofFile.Honest.K14 (fresh_mem_own)
open ProofFile.Honest.SumLaw (playedFrom fitsFrom stateFrom aloneFrom)

section Send
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **A sending's two rounds as played.** c: the part's own coins. -/
def playedSend (name : String) (J : SendJob W X) (c : Cs (dueR J.P J.ride)) (t : State W X)
    (seen : Seen) (d₀ d₁ : Fmt.Drawn) : List Played :=
  [⟨name, J.P.place, 0, true, [], (treeTables J.P (J.rows c seen t 0)).map some, d₀⟩,
   ⟨name, J.P.place, 0, true,
      ((answers J.P (stAt J.P J.first) J.first
          (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P
            (J.rows c (seen.plus [⟨[], d₀⟩]) (t.hears d₀) 1))
          (seedsAt J.P [d₀])).map fun a => Said.got (.answer (toE a))), [], d₁⟩]

/-- The member's two rounds as the verifier's step is handed them: without the sealed digest. -/
theorem rounds_send (name : String) (J : SendJob W X) (c : Cs (dueR J.P J.ride)) (t : State W X)
    (seen : Seen) (d₀ d₁ : Fmt.Drawn) :
    (roundsOf (playedSend name J c t seen d₀ d₁)).map noDigest =
      [noDigest ⟨[], d₀⟩,
        noDigest ⟨(answers J.P (stAt J.P J.first) J.first
          (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P
            (J.rows c (seen.plus [⟨[], d₀⟩]) (t.hears d₀) 1))
          (seedsAt J.P [d₀])).map fun a => Said.got (.answer (toE a)), d₁⟩] := rfl

/-- The last challenge heard. -/
theorem hears_lately (t : State W X) (d : Fmt.Drawn) : (t.hears d).lately 1 = [d] := by
  show (t.heard ++ [d]).drop ((t.heard ++ [d]).length - 1) = [d]
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.drop_left]

/-- The stops of a sending's half never stop. -/
theorem send_row_silent (J : SendJob W X) (v : Option V) (loc ds : List Fmt.Drawn) :
    rowStopAt v (proverSideOfSending (V := V) J).parts loc ds = none := by
  cases v <;> simp [proverSideOfSending, rowStopAt, Part.stopAt, sendPart]

/-- **The frame's terms for a row return the two rounds**, and every message fits its round. -/
theorem played_send (name : String) (J : SendJob W X) (hf : sendFits J.P J.ride = true)
    (c : RowCoins (proverSideOfSending (V := V) J).parts) (t : State W X) (seen : Seen)
    (d₀ d₁ : Fmt.Drawn) (hd : drawsFit (K1.rounds J.P) [d₀, d₁] = true) :
    playedRow name J.P.place (proverSideOfSending (V := V) J).parts 0 c t seen [d₀, d₁] =
        some (playedSend name J c.1.1 t seen d₀ d₁) ∧
      fitsRow (proverSideOfSending (V := V) J).parts ((K1.rounds J.P).zip (K1.oracles J.P)) c t seen
        [d₀, d₁] = true := by
  have hs : seedsFit J.P [d₀] = true := by
    obtain ⟨a, b, e, h⟩ := k1_draws_two J.P _ hd
    cases e
    exact h
  have hl := hears_lately t d₀
  have f1 := k1_first_fits J.P (J.rows c.1.1 seen t 0)
  have f2 := k1_second_fits J.P _ (Johnson.Prover.Send.length_answers J.P (stAt J.P J.first) J.first
    (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P
      (J.rows c.1.1 (seen.plus [⟨[], d₀⟩]) (t.hears d₀) 1)) (seedsAt J.P [d₀]))
  constructor
  · simp [proverSideOfSending, playedRow, playedFrom, sendPart, playedSend, hf, hl, hs, stateFrom, roundsOf]
  · simp [proverSideOfSending, fitsRow, fitsFrom, sendPart, hf, hl, hs, stateFrom, aloneFrom, K1.rounds,
      K1.oracles]
    exact ⟨f1, f2⟩

/-- **The member's play and its columns' laying return.** -/
theorem send_moved (T : Thread Bk S Cl V W X Pb) (blk : Block S Cl) (J : SendJob W X)
    (hsh : blk.place = J.P.place ∧ blk.rounds = K1.rounds J.P ∧ blk.oracles = K1.oracles J.P)
    (hh : (T.hs.find? fun g => g.place == J.P.place) = some (proverSideOfSending J))
    (hf : sendFits J.P J.ride = true) :
    ∀ k m E ds l, drawsFit blk.rounds ds = true →
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs = .ok l →
      ∃ y, T.Moved blk k m E ds y [] := by
  intro k m E ds l hd hl
  obtain ⟨hp, hr, ho⟩ := hsh
  have hf' : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfSending J) := by
    rw [hp]
    exact hh
  have hl₀ := hl
  obtain ⟨c, -, rfl⟩ := steps_one_half hf' hl
  rw [hr] at hd
  obtain ⟨d₀, d₁, rfl, -⟩ := k1_draws_two J.P ds hd
  obtain ⟨h1, h2⟩ := played_send (V := V) blk.name J hf c m.st m.shown d₀ d₁ hd
  obtain ⟨y, hy⟩ : ∃ y, play (rowSteps blk.name J.P.place (T.φ.sees m.st.input)
      (proverSideOfSending J).parts 0 ((K1.rounds J.P).zip (K1.oracles J.P)) c) [d₀, d₁] [] m = .ok y :=
    ⟨_, play_row_whole blk.name J.P.place (T.φ.sees m.st.input) (proverSideOfSending J).parts 0
      ((K1.rounds J.P).zip (K1.oracles J.P)) c [d₀, d₁] [] m _ (send_row_silent J _ _ _) h2 h1⟩
  refine ⟨y, ?_⟩
  unfold Thread.Moved
  refine ⟨⟨_, hl₀, ?_⟩, ?_⟩
  · unfold Placed.steps
    rw [hp, hr, ho]
    exact hy
  · rw [hr]
    exact k1_cols_return _ _ _ _ _ _

/-- **And what is played is the term**, at the coins that the book lends. -/
theorem send_moved_term (T : Thread Bk S Cl V W X Pb) (blk : Block S Cl) (J : SendJob W X)
    (hsh : blk.place = J.P.place ∧ blk.rounds = K1.rounds J.P ∧ blk.oracles = K1.oracles J.P)
    (hh : (T.hs.find? fun g => g.place == J.P.place) = some (proverSideOfSending J))
    (hf : sendFits J.P J.ride = true) :
    ∀ k m E ds y cols, drawsFit blk.rounds ds = true → T.Moved blk k m E ds y cols →
      ∃ c d₀ d₁, lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.P.place
          (proverSideOfSending (V := V) J).parts 0 = .ok c ∧ ds = [d₀, d₁] ∧ cols = [] ∧
        y.1 = playedSend blk.name J c.1.1 m.st m.shown d₀ d₁ ∧
        y.2.st.input = m.st.input ∧ y.2.st.heard = m.st.heard ++ ds := by
  intro k m E ds y cols hd hM
  obtain ⟨hp, hr, ho⟩ := hsh
  have hf' : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfSending J) := by
    rw [hp]
    exact hh
  unfold Thread.Moved at hM
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  obtain ⟨c, hc1, -, hpl, -, hy2⟩ := member_played hf' hl hy
  rw [hr] at hd hc
  obtain ⟨d₀, d₁, rfl, -⟩ := k1_draws_two J.P ds hd
  obtain ⟨h1, -⟩ := played_send (V := V) blk.name J hf c m.st m.shown d₀ d₁ hd
  rw [hp] at hpl hc1
  rw [k1_cols_return] at hc
  refine ⟨c, d₀, d₁, hc1, rfl, (Except.ok.inj hc).symm, Option.some.inj (hpl.symm.trans h1), ?_, ?_⟩
  · rw [hy2]
    simp [proverSideOfSending, stateRow, stateFrom, sendPart, State.hears]
  · rw [hy2]
    simp [proverSideOfSending, stateRow, stateFrom, sendPart, State.hears]

/-- **It plays**, from the thread alone, where the thread's tables at the sending's trees are the
sender's own term, fixed by the challenges heard in front. hdata: of what stands in front the job's
data read what was heard alone. -/
theorem plays_send (T : Thread Bk S Cl V W X Pb) (b : Nat) (blk : Block S Cl) (J : SendJob W X)
    (own₀ : X) (hblk : T.bs[b]? = some blk)
    (hsh : blk.place = J.P.place ∧ blk.rounds = K1.rounds J.P ∧ blk.oracles = K1.oracles J.P)
    (hh : (T.hs.find? fun g => g.place == J.P.place) = some (proverSideOfSending J))
    (hf : sendFits J.P J.ride = true)
    (hdata : ∀ w (fr fr' : Front X), fr.heard = fr'.heard → J.data w fr = J.data w fr')
    (htab : ∀ τ, τ < J.P.trees.length → ∀ k w h, T.table (.own (treesTo T.bs b + τ)) k w h =
      treeTbl T.chain id J own₀ τ k w h)
    (hfix : ∀ τ, τ < J.P.trees.length →
      T.fixed (.own (treesTo T.bs b + τ)) = T.front + roundsTo T.bs b) :
    Plays T b := by
  intro blk' hb k s m E ds l hT hd _ hl
  rw [hblk] at hb
  obtain rfl : blk = blk' := Option.some.inj hb
  obtain ⟨y, hM⟩ := send_moved T blk J hsh hh hf k m E ds l hd hl
  refine ⟨y, [], hM, ?_⟩
  intro σ hσ
  obtain ⟨τ, hτ, rfl⟩ := fresh_mem_own T hblk hσ
  have hcount : (blk.oracles.flatMap id).length = J.P.trees.length := by
    rw [hsh.2.2]
    simp [K1.oracles]
  rw [hcount] at hτ
  obtain ⟨c, d₀, d₁, hc, -, -, hy, hin, hheard⟩ :=
    send_moved_term T blk J hsh hh hf k m E ds y [] hd hM
  have hcut : lentCut k T.chain ⟨J.P.place, 0⟩ (dueR J.P J.ride) = some c.1.1 :=
    cut_of_lendHalf _ k T.chain J.P.place (sendPart J) c hc
  have hsent : E.sent = treesTo T.bs b := hT.2.2.2.2.1.2.2.1
  have htabs : tablesOf y.1 =
      (treeTables J.P (J.rows c.1.1 m.shown m.st 0)).map fun u => some (J.P.place, u) := by
    rw [hy]
    simp [tablesOf, playedSend, Function.comp_def]
  have hr : rowsLaid J own₀ c.1.1 m.st.input m.st.heard = J.rows c.1.1 m.shown m.st 0 := by
    have q := rowsLaid_part J own₀ hdata c.1.1 m.shown m.st 0
    rw [Nat.sub_zero, List.take_length] at q
    exact q
  have hlen : τ < (treeTables J.P (J.rows c.1.1 m.shown m.st 0)).length := by
    rw [treeTables_length]
    exact hτ
  have htree : (E.add y.1).tree (.own (treesTo T.bs b + τ)) =
      some (scriptTable J own₀ τ c.1.1 m.st.input m.st.heard) := by
    rw [← hsent, Env.add_own, htabs, List.getElem?_map, List.getElem?_eq_getElem hlen]
    unfold scriptTable
    rw [hr, List.getElem?_eq_getElem hlen]
    rfl
  have hlenH : m.st.heard.length = T.front + roundsTo T.bs b := by
    have e := drawsFit_length _ _ hT.2.1
    rw [List.length_append] at e
    exact e
  have htb : T.tableAt (.own (treesTo T.bs b + τ)) k y.2 =
      scriptTable J own₀ τ c.1.1 m.st.input m.st.heard := by
    unfold Thread.tableAt
    rw [htab τ hτ, hin, hheard, hfix τ hτ, ← hlenH, List.take_left]
    exact treeTbl_some T.chain id J own₀ τ k c.1.1 hcut _ _
  unfold Thread.handAt
  rw [htree, htb]
  simp [Table.same]

end Send

section Batching
open ProofFile.Honest.K13
open VerifiableInference.Desc.K13 (Where battRounds)

variable {S Cl W₀ Rc Xi Tr X Pb : Type} {Bk : ProverCoinCounts}

/-- **Played**, at any type of state. -/
theorem moved_k13 (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where) (b : Block S Cl)
    (hr : b.rounds = battRounds P) (ho : b.oracles = List.replicate (2 + P.lin.kCol) [])
    {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option (Local W₀ Rc Xi Tr)}
    {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    (hf : (hs.find? fun h => h.place == b.place) = some (proverSideOfClaimCombination weights pile P))
    {l : List (Step (Local W₀ Rc Xi Tr) X)} (hl : chainSteps B rows look v [b] hs = .ok l)
    (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn) (hd : drawsFit b.rounds ds = true) :
    ∃ p, play l ds [] m =
        .ok (p, ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds, m.seen ++ roundsOf p,
          m.opened⟩) ∧
      tablesOf p = [] ∧
      ∀ (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
        (tree : Fmt.TreeSource → Option (Place × Table)),
        fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] := by
  obtain ⟨c, -, rfl⟩ := chainSteps_one hf hl
  obtain ⟨p, hp, ht⟩ := k13_plays_returns weights pile P b hr ho v c m ds (by rw [← hr]; exact hd)
  refine ⟨p, hp, ht, fun chain ft stored tree => ?_⟩
  rw [hr, k13_reads_none]
  rfl

/-- **It plays**, at all coins, with no premise on the thread's sentence in front. -/
theorem plays_k13 (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) {b : Nat}
    {blk : Block S Cl} (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where)
    (hblk : T.bs[b]? = some blk) (hr : blk.rounds = battRounds P)
    (ho : blk.oracles = List.replicate (2 + P.lin.kCol) [])
    (hf : (T.hs.find? fun h => h.place == blk.place) = some (proverSideOfClaimCombination weights pile P)) :
    Plays T b := by
  intro blk' hb k s m En ds l _ hd _ hl
  rw [hblk] at hb
  cases hb
  obtain ⟨p, hp, -, hc⟩ := moved_k13 weights pile P blk hr ho hf hl m ds hd
  refine ⟨_, [], ⟨⟨l, hl, hp⟩, hc _ _ _ _⟩, ?_⟩
  rw [fresh_none T hblk (by rw [ho]; simp)]
  intro σ hσ
  cases hσ

end Batching

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.played_send
#print axioms AtPublicFiles.FirstH.send_moved
#print axioms AtPublicFiles.FirstH.send_moved_term
#print axioms AtPublicFiles.FirstH.plays_send
#print axioms AtPublicFiles.FirstH.moved_k13
#print axioms AtPublicFiles.FirstH.plays_k13
