-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/YesShown.lean: the kind "the code switch" (K2): THE MEMBER's
STEP DOWN TO THE KIND's OWN DECISION, WITH THE TWO ROUNDS AND THE GROUPS OF COLUMNS WRITTEN OUT:
what the half played, and what was shown. Under the record at a switch (`K2SeatedL`,
Honest/K2/SeatedL.lean). One statement with its proof; no definition.

  `yes_shown_at_switch` all eleven clauses of `yes_at_switch`'s end
                    (Honest/K2/Law/YesAtSwitch.lean), AND: the two rounds are `(roundsOf y.1).map
                    noDigest`, one equation · the groups are no letter any more: `shownGroups
                    L.thread.ft blk (roundsOf y.1) cols` (Johnson/Desc/K14/Law/Bridge.lean) stands
                    in their place, in the member's decision and in `AtYes`

WHY. `yes_at_switch` puts the rounds r₁, r₂ and the groups gs under "there are", with no equation.
Whoever states a premise "at every yes that the step can hold" over that end must state it AT EVERY
r₁, r₂, gs THAT THE VERIFIER ACCEPTS ON THE WAY TO s': also at columns that no honest half showed. A
premise on what the opened symbols are cannot be paid so by an honest side: that accepted columns
open one thing alone is another matter. (Our reader's find, at a law of ours that did just that.)
Here the caller knows which rounds and which groups are meant.

How. `yes_at_switch`'s own proof, to the line, but for the closing tuple: its proof had these terms
in hand; one `rfl` more. ITS PROOF IS SO WRITTEN A THIRD TIME (`step_at_switch`,
Honest/K2/Law/StepAtSwitch.lean, has its first two thirds): both elder laws follow from this one;
they are frozen and have left the house: at a lining they become calls.

Spends of the record: what `yes_at_switch` spends. Limits: those of YesAtSwitch.lean, all. The
columns cols are hS's: that they are read off the trees of what the half sent lies in
`Thread.Moved`: not drawn out here. Under `Stepped`: it holds of nothing at a book of coins that
lends the part nothing. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.StepAtSwitch
import Johnson.Desc.K14.Law.Bridge
import Johnson.Desc.Sound.Gather
import Johnson.Top.H0.K2Hears.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block roundsFit noDigest OpenedColumn fieldPrimeWord groupsOf)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 rounds AtYes yes_whole)
open VerifiableInference.Desc.Sound (MsgT Mem)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (answers)
open _root_.Desc.K14.Law (shownGroups)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers} {lay : OnBytes.Params.ReqLayout}
  {segs : List SegmentPub} {p : SwitchPlace} {q : P2} {before : S → Except String S}
  {after : S → S → Except String S} {seg first : Nat} {Zp : ProofFile.Pub} {arr : ℕ → ℕ → ℕ}
  {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **THE STEP DOWN TO THE KIND's OWN DECISION, AT THE ROUNDS PLAYED AND THE COLUMNS SHOWN.** hA:
the thread's invariant in front of the member (`ThrS`). hS: `Thread.Stepped`: the half has moved,
and the member's own step returns s' at what was played. FREE LETTERS OF THE RECORD: D · readers ·
rad · before · after; and, inside its field `sends`, the type Lt and the states d, d'. `readers`
takes the whole input. NOT IN FRONT OF A LAW OVER COINS. -/
theorem yes_shown_at_switch
    (R : K2SeatedL L b blk D readers lay segs p q before after seg first Zp arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s') :
    ∃ (c : SwitchCoins p.sizes p.others p.foldVars p.carries)
      (V : Nat → Johnson.Prover.Send.Rows) (r₁ r₂ : Fmt.RoundView) (s₁ t : S) (x : _root_.Tw.K2.Front)
      (z : _root_.Tw.K2.Sent) (S3 : OnBytes.Statement) (Y : Array OnBytes.E)
      (rows : List OnBytes.Row) (G : OnBytes.Group) (cd : OnBytes.Code),
      handed 0 p k = some c ∧
      switchRowsLaid D readers (lotClosingAt lay segs) p c m.st.input m.st.heard = .ok V ∧
      (roundsOf y.1).map noDigest = [r₁, r₂] ∧
      blk.decide s [r₁, r₂] (shownGroups L.thread.ft blk (roundsOf y.1) cols) = .ok s' ∧
      roundsFit (rounds q) [r₁, r₂] = true ∧
      (r₁.drawn.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true ∧
      r₂.vals = (answers (switchPar p) (K1.stAt (switchPar p) s.st.oracles.size) s.st.oracles.size
        (Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size (switchPar p) V)
        (VerifiableInference.Desc.K1.seedsOf (switchPar p) r₁)).map .answer ∧
      before s = .ok s₁ ∧
      AtYes q s₁ t r₁ r₂ (shownGroups L.thread.ft blk (roundsOf y.1) cols) x z S3 Y rows G cd ∧
      after s₁ t = .ok s' ∧
      y.2.st.input = m.st.input ∧ y.2.st.heard = m.st.heard ++ ds := by
  obtain ⟨⟨⟨l, hl, hy⟩, -⟩, hstep⟩ := hS
  obtain ⟨⟨-, -, -, -, -, -, hval⟩, -⟩ := hA
  have hf' : (L.hs.find? fun g => g.place == blk.place) =
      some (switchHalf (coreSender freshTable) D readers (lotClosingAt lay segs) p) := by
    rw [R.shape.1]
    exact R.half
  obtain ⟨c, hlend, el⟩ := steps_one_half hf' hl
  obtain ⟨d₁, d₂, hq⟩ : ∃ d₁ d₂, rounds q = [d₁, d₂] := ⟨_, _, rfl⟩
  rw [R.shape.2.1, hq] at hd
  obtain ⟨x₁, x₂, rfl, -⟩ := draws_two d₁ d₂ ds hd
  obtain ⟨V, m', hV, hy', hi⟩ := half_played_rows D readers (lotClosingAt lay segs) p blk d₁ d₂
    q.sent [] (by rw [R.shape.2.1, R.shape.2.2, hq]; rfl) (L.thread.φ.sees m.st.input) c x₁ x₂ m
    R.serves R.roomy R.placeOk (rounds_items q d₁ d₂ hq).1 R.trees
    (by rw [R.answersNo]; exact (rounds_items q d₁ d₂ hq).2) rfl
    ((returnsLaw D readers lay segs p R.closes m.st.input m.st.heard c.1.2.2).trans
      (R.publicAt _ hval)) s.st.oracles.size
  rw [← el] at hy'
  obtain rfl : y = (_, m') := Except.ok.inj (hy.symm.trans hy')
  obtain ⟨hfit, -⟩ := VerifiableInference.Desc.K1.step_ok _ blk s s' _ _ _ hstep
  have hdec := _root_.Desc.K14.Law.step_groups _ blk s s' _ _ _ hstep
  have hw : (x₁.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true :=
    ProofFile.Honest.K1.draws_words hd
  obtain ⟨s₁, t, hb, hk, ha⟩ := (R.decides s _ _ s' rfl (by
    unfold _root_.Desc.K14.Law.shownGroups
    rw [VerifiableInference.Desc.Sound.regroup_len, List.length_map, R.shape.2.1]
    simp [groupsOf, rounds, roundsOf])).1 hdec
  obtain ⟨x, z, S3, Y, rows, G, cd, A⟩ := yes_whole q s₁ _ _ _ t hk
  refine ⟨c.1, V, noDigest ⟨[], x₁⟩, noDigest ⟨_, x₂⟩, s₁, t, x, z, S3, Y, rows, G, cd, ?_,
    hV, rfl, hdec, ?_, hw, ?_, hb, A, ha, hi, play_heard _ _ _ _ _ hy'⟩
  · have h := lent_part Bk (Bk.rowsOf 0) (k.look 0) blk.place (coreSender freshTable) D readers
      (lotClosingAt lay segs) p c hlend
    unfold handed
    rw [← R.shape.1, h]
    rfl
  · rw [R.shape.2.1] at hfit
    exact (VerifiableInference.Desc.roundsFit_noDigest _ _).trans hfit
  · show (((answers (switchPar p) (K1.stAt (switchPar p) s.st.oracles.size) s.st.oracles.size
      (Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size (switchPar p) V)
      (K1.seedsAt (switchPar p) [x₁])).map OnBytes.Slice.toE).map
        ProofFile.Honest.Said.answer).map ProofFile.Honest.Said.got = _
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun a ha' => ?_
    show Fmt.ItemValue.answer (OnBytes.Slice.ofE (OnBytes.Slice.toE a)) = _
    rw [ProofFile.Honest.K1.answers_canon _ _ _ _ _ a ha']

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.yes_shown_at_switch
