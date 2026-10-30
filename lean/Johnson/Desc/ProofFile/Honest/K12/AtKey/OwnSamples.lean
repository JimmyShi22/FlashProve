-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OwnSamples.lean: the sample rows of two of the own test's three
members have no written-out factor: the index masks' message and W, from the first chain's fold alone. Steps
of the verifier's: nothing is shown of any prover.

  `plain_rowsOf`    every row that a sending lays on a message is plain
  `send_new`        behind a sending's yes, a new message with answers is sampled and its rows are plain
  `size_of_same`    `SameMsgs` keeps the number of messages
  `after_send`      at a first chain cut at a sending: the same, at the state behind that block, and the sampled
                    message stands so at the fold's end (`SmpStay`)
  `sample_idx`      the first chain's end: message 0 is sampled, with plain rows
  `sample_w`        the first chain's end: the last message but one is sampled, with plain rows

Why the fold and not a relation. `SamplesPlain` is no relation that the ground's functions keep: the admitting
takes any rows. What keeps a sampled message is `SmpStay` (Johnson/Desc/K1/Law/SmpStay.lean), so the rows are read
once, behind the sending, and carried.

By what. `decideSend_iff` (K1/Law/Writes3.lean), `outs_spec`, `wr`, `sampleRow_plain` (K12/PlainAtEight.lean),
`send_laid` (Key/Laid/SendLaid.lean), `idx_named`, `w_named`, `idx_at`, `flat_smp₁`, `foldBlocks_cons_ok`, `flat_last`.

Limits.
- FORM ALONE: nothing on what a row holds of.
- `sample_w` stands on the two premises on the plan that W's message holds two notices and that the first is
  sampled: hsz, hans.
- Of Omega nothing is said here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnMarks
import Johnson.Desc.ProofFile.Honest.K12.PlainAtEight
import Johnson.Desc.Key.Laid.SendLaid
import Johnson.RunOne.KeyMsgAll
import E2E.KeyThreads
import E2E.KeyKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12.AtKey
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.K1 (Par decideSend decideSend_iff shapesOf behind wr outs outs_spec seedsOf
  answersIn rowsOf SameMsgs SmpStay)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi Claim FirstState descriptionFromSource sendIndexMasks sendW pieces)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.Ground (By)
open Johnson.RunOne.KeyKeeps (st₁)
open Johnson.RunOne.KeyWalk (flat_smp₁)
open Johnson.RunOne.KeyMsg (Named idx_named w_named two_of_fit bW)
open Johnson.RunOne.KeySendGood (parIdx parW gW idx_at w_at rounds_idx rounds_w)
open VerifiableInference.Desc.Key (rootsBefore batchRound)
open ProofFile.Honest.K12.Light (sampleRow_plain)
open Desc.Plain (DState)

/-- **Every row that a sending lays on a message is plain.** -/
theorem plain_rowsOf (codes : Codes) (seeds : List (List E × E)) (o : ℕ) (s : OracleShape) (ys : List E) :
    ∀ r ∈ (rowsOf codes seeds o s ys).toList, PlainRow r := by
  intro r hr
  unfold rowsOf at hr
  rw [List.toList_toArray] at hr
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hr
  exact sampleRow_plain _ _ _ _ _ _

/-- **Behind a sending's yes, a new message with answers is sampled and its rows are plain.** -/
theorem send_new {L : Type} (P : Par) (owed : Option ℕ) (d d' : DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array ℕ)
    (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (k : ℕ) (hk : k < (shapesOf P).length)
    (ha : (shapesOf P)[k].answers ≠ 0) :
    ∃ x : OnBytes.Oracle, d'.st.oracles[d.st.oracles.size + k]? = some x ∧ x.sampled = true ∧
      ∀ r ∈ x.sampleRows.toList, PlainRow r := by
  obtain ⟨⟨_, _, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
  obtain ⟨ys', -, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
    d.st.oracles.size (answersIn r₂) hf k hk
  have hx : (behind P d (seedsOf P r₁) (answersIn r₂)).st.oracles[d.st.oracles.size + k]? =
      some (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys') := by
    show (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
      (answersIn r₂)).toArray[d.st.oracles.size + k]? = _
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
    simpa using hget
  refine ⟨_, hx, by simp [wr, ha], fun r hr => ?_⟩
  simp only [wr, ha, if_false] at hr
  exact plain_rowsOf _ _ _ _ _ r hr

/-- `SameMsgs` keeps the number of messages. -/
theorem size_of_same {A B : Statement} (h : SameMsgs A B) : B.oracles.size = A.oracles.size := by
  have key : ∀ j, (B.oracles[j]?).isSome = (A.oracles[j]?).isSome := fun j => by
    have e := congrArg Option.isSome (h.2 j)
    simpa using e
  rcases Nat.lt_trichotomy B.oracles.size A.oracles.size with hl | he | hl
  · have k₁ := key B.oracles.size
    rw [getElem?_neg B.oracles _ (Nat.lt_irrefl _), getElem?_pos A.oracles _ hl] at k₁
    simp at k₁
  · exact he
  · have k₁ := key A.oracles.size
    rw [getElem?_neg A.oracles _ (Nat.lt_irrefl _), getElem?_pos B.oracles _ hl] at k₁
    simp at k₁

variable {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}

/-- A list, cut at a member. -/
theorem cut_of_get {α : Type} {l : List α} {m : ℕ} {b : α} (h : l[m]? = some b) :
    l = l.take m ++ b :: l.drop (m + 1) := by
  obtain ⟨hm, e⟩ := List.getElem?_eq_some_iff.1 h
  have t := List.take_append_drop m l
  rw [List.drop_eq_getElem_cons hm, e] at t
  exact t.symm

/-- **At a first chain cut at a sending.** a: the state in front of it; s': the state behind it. -/
theorem after_send (Q : Par) (b₀ : Block FirstState Claim) (m : ℕ)
    (hb : (descriptionFromSource Xs Nr Pl).first.blocksInOrder[m]? = some b₀)
    (hr : b₀.rounds = VerifiableInference.Desc.K1.rounds Q) (hS : Named Q b₀) (ft : ℕ)
    {s e : FirstState} {rs r : List Fmt.RoundView} {cols c : List OpenedColumn}
    (h : foldBlocks ft (descriptionFromSource Xs Nr Pl).first.blocksInOrder s rs cols = .ok (e, r, c)) (k : ℕ)
    (hk : k < (shapesOf Q).length) (ha : (shapesOf Q)[k].answers ≠ 0) :
    ∃ (a s' : FirstState) (r₀ r' : List Fmt.RoundView) (c₀ c' : List OpenedColumn),
      foldBlocks ft ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.take m) s rs cols = .ok (a, r₀, c₀) ∧
      foldBlocks ft ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.drop (m + 1)) s' r' c' = .ok (e, r, c) ∧
      (st₁ s').oracles.size = (st₁ a).oracles.size + Q.sent.size ∧
      ∃ x : OnBytes.Oracle, (st₁ e).oracles[(st₁ a).oracles.size + k]? = some x ∧ x.sampled = true ∧
        ∀ r ∈ x.sampleRows.toList, PlainRow r := by
  have hf := cut_of_get hb
  rw [hf] at h
  obtain ⟨a, r₀, c₀, h₁, h₂⟩ := Johnson.Desc.First.Walk.Tied.fold_split ft _ _ s rs cols _ h
  obtain ⟨s', n, -, hstep, hrest⟩ :=
    VerifiableInference.Desc.Sound.foldBlocks_cons_ok ft b₀ _ a r₀ c₀ _ h₂
  have hfit₀ := (VerifiableInference.Desc.Plain.step_fits hstep).1
  have hfit : VerifiableInference.Desc.roundsFit (VerifiableInference.Desc.K1.rounds Q)
      (List.take b₀.rounds.length r₀) = true := by
    rw [← hr]
    exact hfit₀
  obtain ⟨r₁, r₂, hR⟩ := two_of_fit _ _ _ hfit
  obtain ⟨gs, hd⟩ := _root_.Desc.K14.Law.step_decides ft b₀ a s' _ c₀ n hstep
  rw [hR] at hd
  obtain ⟨ids, d', hyes, hsame⟩ := hS a s' _ _ gs hd
  obtain ⟨x, hx, hxs, hxp⟩ := send_new Q a.debt _ d' _ _ ids hyes k hk ha
  have hsz : (st₁ s').oracles.size = (st₁ a).oracles.size + Q.sent.size := by
    rw [size_of_same hsame]
    exact (VerifiableInference.Desc.Key.LaidW.send_laid Q a.debt _ d' _ _ ids hyes).size
  have e₀ := hsame.2 ((st₁ a).oracles.size + k)
  have hx₀ : d'.st.oracles[(st₁ a).oracles.size + k]? = some x := hx
  rw [hx₀] at e₀
  obtain ⟨y, hy, ey⟩ := Option.map_eq_some_iff.1 e₀
  have ey₁ : y.sampled = x.sampled := congrArg (fun p => p.2.1) ey
  have ey₂ : y.sampleRows = x.sampleRows := congrArg (fun p => p.2.2) ey
  have hstay : SmpStay (st₁ s') (st₁ e) :=
    VerifiableInference.Desc.Keeps.foldBlocks_keeps (By SmpStay st₁)
      (fun _ => SmpStay.refl _) (fun _ _ _ p q => p.trans q) ft _
      (fun b hb' => flat_smp₁ b (List.mem_of_mem_drop hb')) s' _ _ _ hrest
  obtain ⟨z, hz, -, hzs, hzr⟩ := hstay.2 _ y hy (ey₁.trans hxs)
  exact ⟨a, s', r₀, _, c₀, _, h₁, hrest, hsz, z, hz, hzs,
    fun q hq => hxp q (by rw [← ey₂, ← hzr]; exact hq)⟩

/-- **The first chain's end: message 0 is sampled, with plain rows.** -/
theorem sample_idx {x : (descriptionFromSource Xs Nr Pl).XiPub} {e : FirstState} {rs r : List Fmt.RoundView} {cols c : List OpenedColumn}
    (h : foldBlocks 0 (descriptionFromSource Xs Nr Pl).first.blocksInOrder ((descriptionFromSource Xs Nr Pl).start₁ x) rs cols = .ok (e, r, c))
    (ha : Xs.Y.k.oneTime.indexMasks.shape.answers ≠ 0) :
    ∃ y : OnBytes.Oracle, (st₁ e).oracles[0]? = some y ∧ y.sampled = true ∧
      ∀ r ∈ y.sampleRows.toList, PlainRow r := by
  have hsh : shapesOf (parIdx Xs) = [Xs.Y.k.oneTime.indexMasks.shape] := by
    unfold parIdx
    rw [Johnson.RunOne.KeyMsg.shapes_of]
    rfl
  have hk : 0 < (shapesOf (parIdx Xs)).length := by
    rw [hsh]
    exact Nat.succ_pos _
  have hz : (shapesOf (parIdx Xs))[0].answers ≠ 0 := by
    simpa [hsh] using ha
  obtain ⟨a, s', r₀, r', c₀, c', h₁, -, -, y, hy, hs, hp⟩ := after_send (Xs := Xs) (Nr := Nr) (Pl := Pl)
    (parIdx Xs) _ 0 (idx_at Xs Nr Pl) (rounds_idx Xs) (idx_named _ _ _) 0 h 0 hk hz
  have ea : a = (descriptionFromSource Xs Nr Pl).start₁ x := by
    rw [List.take_zero] at h₁
    unfold foldBlocks at h₁
    exact congrArg Prod.fst (Except.ok.inj h₁).symm
  have hs0 : (st₁ a).oracles.size = 0 := by
    rw [ea]
    rfl
  rw [hs0] at hy
  exact ⟨y, hy, hs, hp⟩

/-- **The first chain's end: W's message, the last but one, is sampled, with plain rows.** -/
theorem sample_w {bw : Block FirstState Claim} {msg : Array OracleNotice}
    (hb : sendW Xs.Y.k.oneTime pieces (rootsBefore Xs.Y.D.1 (batchRound Xs.Y.D.1)) (gW Xs) = some bw)
    (hm : OnBytes.linMessageW Xs.Y.k.oneTime.lin = some msg) (hsz : (parW Xs msg).sent.size = 2)
    (hk : 0 < (shapesOf (parW Xs msg)).length) (ha : (shapesOf (parW Xs msg))[0].answers ≠ 0)
    {s e : FirstState} {rs r : List Fmt.RoundView} {cols c : List OpenedColumn}
    (h : foldBlocks 0 (descriptionFromSource Xs Nr Pl).first.blocksInOrder s rs cols = .ok (e, r, c)) :
    ∃ y : OnBytes.Oracle, (st₁ e).oracles[(st₁ e).oracles.size - 2]? = some y ∧ y.sampled = true ∧
      ∀ r ∈ y.sampleRows.toList, PlainRow r := by
  obtain ⟨a, s', r₀, r', c₀, c', -, h₂, hs', y, hy, hs, hp⟩ := after_send (Xs := Xs) (Nr := Nr) (Pl := Pl)
    (parW Xs msg) _ (bW Xs Nr Pl) (w_at Xs Nr Pl hb) (rounds_w hm hb) (w_named hm hb) 0 h 0 hk ha
  -- behind W's sending stands the seal alone, which hands the state on
  obtain ⟨blk, hl, -, -, -, hd⟩ := AtPublicFiles.AtFiles.flat_last (descriptionFromSource Xs Nr Pl).first
  have hback : (descriptionFromSource Xs Nr Pl).first.back.length = 4 := by
    show ([_, _, _] ++ (sendW Xs.Y.k.oneTime pieces (rootsBefore Xs.Y.D.1 (batchRound Xs.Y.D.1))
      (gW Xs)).toList).length = 4
    rw [hb]
    rfl
  have hlen : (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length = bW Xs Nr Pl + 2 := by
    rw [VerifiableInference.Desc.Chain.flat_eq]
    simp only [List.length_append, List.length_cons, List.length_map, List.length_nil, hback]
    unfold bW
    omega
  have hdrop : (descriptionFromSource Xs Nr Pl).first.blocksInOrder.drop (bW Xs Nr Pl + 1) = [blk] := by
    have hl' : (descriptionFromSource Xs Nr Pl).first.blocksInOrder[bW Xs Nr Pl + 1]? = some blk := by
      have e₁ : (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length - 1 = bW Xs Nr Pl + 1 := by omega
      rw [← e₁]
      exact hl
    obtain ⟨hm', ev⟩ := List.getElem?_eq_some_iff.1 hl'
    rw [List.drop_eq_getElem_cons hm', ev, List.drop_of_length_le (by omega)]
  rw [hdrop] at h₂
  obtain ⟨s'', n, -, hstep, hend⟩ := VerifiableInference.Desc.Sound.foldBlocks_cons_ok 0 blk [] s' _ _ _ h₂
  have es'' : s'' = e := by
    unfold foldBlocks at hend
    exact congrArg Prod.fst (Except.ok.inj hend)
  obtain ⟨gs, hdc⟩ := _root_.Desc.K14.Law.step_decides 0 blk s' s'' _ _ n hstep
  rw [hd] at hdc
  have e₂ : s'' = s' := AtPublicFiles.KeyThread.end_same (S := FirstState)
    (fun t => [("end: no count of rows is owed", t.noneWaits)] ++
      VerifiableInference.Desc.Key.untestedButOwn t) s' s'' hdc
  have hsize : (st₁ e).oracles.size - 2 = (st₁ a).oracles.size := by
    rw [← es'', e₂, hs', hsz]
    omega
  rw [hsize]
  exact ⟨y, by simpa using hy, hs, hp⟩

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.plain_rowsOf
#print axioms ProofFile.Honest.K12.AtKey.send_new
#print axioms ProofFile.Honest.K12.AtKey.size_of_same
#print axioms ProofFile.Honest.K12.AtKey.cut_of_get
#print axioms ProofFile.Honest.K12.AtKey.after_send
#print axioms ProofFile.Honest.K12.AtKey.sample_idx
#print axioms ProofFile.Honest.K12.AtKey.sample_w
