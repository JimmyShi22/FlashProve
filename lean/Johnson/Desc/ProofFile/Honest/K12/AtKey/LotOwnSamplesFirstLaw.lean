-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnSamplesFirstLaw.lean: A SENDING's SAMPLE ROWS SAY THEIR CLAIMS OF THE
SENDER's OWN WORDS AT THE END OF THE CHAIN's FOLD, where the round of the answers holds the sender's own answers. At
letters: the chain's blocks, the verifier's plan Q, the rows V and the rounds are bound variables. No coin, no run and
no prover's term is named.

  `fold_leaves_the_rest`     what a fold leaves of its rounds: the list without the blocks' own rounds
  `says_of_stay`             a row that names one sampled message says the same at a statement in which that message
                             has stayed (`SmpStay`)
  `says_of_words`            such a row reads the words at its own message alone
  `PlansAlike`               two plans of a sending with the same notices and the same codes
  `answers_of_alike`, `held_of_alike`   the sender's term for its answers, and the held words, are the same at both
  `sending_says`             behind a yes of the sending's decision whose second round holds these answers: every
                             sample row of a new message says its claim of the held words, and names that message alone
  `after_sending_says`       THE LAW: the fold of a chain, cut at a sending: the same at the fold's end

Why. The form's half (the rows are plain, the message is sampled) is `after_send` (AtKey/OwnSamples.lean). This is the
values' half, by the same walk.

By what. `send_says`, `behind_at`, `wr_sampled`, `size_sent` (Johnson/Prover/Send/) · `part_answers`, `value_named`,
`size_same`, `onTable_same` (Honest/K1/AnswersChain.lean) · `answers_any_first` (Honest/K1/FirstFree.lean) · `names_new`,
`says_sameMsgs` (Honest/K1/Law/SendAtBlock.lean) · `decideSend_iff` (Johnson/Desc/K1/Law/Writes3.lean) ·
`foldBlocks_keeps` (Johnson/Desc/FoldKeeps.lean) · `foldBlocks_cons_ok`, `foldBlocks_append_ok` (Johnson/Desc/RunLaws.lean).

Hypotheses. hans: the equation on the round of the answers. It is met by nothing here.

Limits.
- SPEAKS OF ANSWERS, WHICH HANG ON THE PADS (through the seed's factor): `sending_says`, `after_sending_says`: each an
  implication from an equation on a round's values, at every V.
- That any run's rounds meet hans is not said. Nothing on how V is made.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.SendAtBlock
import Johnson.Desc.ProofFile.Honest.K1.FirstFree
import Johnson.Desc.K1.Law.SmpStay
import Johnson.Desc.K14.Law.Step
import Johnson.Desc.FoldKeeps
import Johnson.Desc.RunLaws
import Johnson.Desc.Plain.PieceFits
import Johnson.RunOne.KeyMsgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtKey
open OnBytes (Statement Oracle)
open OnBytes.Slice (GE rdE)
open OnBytes.Means (Words Says AllSay)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks noDigest)
open VerifiableInference.Desc.K1 (Par decideSend decideSend_iff seedsOf answersIn SameMsgs SmpStay)
open VerifiableInference.Desc.Key (Claim FirstState)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.Ground (By)
open VerifiableInference.Desc.First.Close (NamesOne)
open Johnson.Prover.Send (Rows shapeAt answers)
open Johnson.RunOne.KeyKeeps (st₁)
open Johnson.RunOne.KeyMsg (Named two_of_fit)
open ProofFile.Honest.K1 (stAt value_named size_same onTable_same part_answers answers_any_first names_new
  says_sameMsgs)
open Desc.Plain (DState)

/-- **What a fold leaves of its rounds.** -/
theorem fold_leaves_the_rest {S Cl : Type} (ft : ℕ) : ∀ (l : List (Block S Cl)) (s t : S)
    (rs r : List Fmt.RoundView) (cols c : List OpenedColumn), foldBlocks ft l s rs cols = .ok (t, r, c) →
    r = rs.drop (l.flatMap (·.rounds)).length
  | [], s, t, rs, r, cols, c, h => by
    unfold foldBlocks at h
    have e : rs = r := congrArg (fun x => x.2.1) (Except.ok.inj h)
    rw [e]
    rfl
  | b :: l, s, t, rs, r, cols, c, h => by
    obtain ⟨-, s', k, -, h'⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h
    rw [fold_leaves_the_rest ft l s' t _ r _ c h', List.drop_drop]
    congr 1
    simp only [List.flatMap_cons, List.length_append]

/-- **A row that names one sampled message says the same where that message has stayed.** -/
theorem says_of_stay {A B : Statement} (h : SmpStay A B) {o : ℕ} {x : Oracle}
    (hx : A.oracles[o]? = some x) (hs : x.sampled = true) (r : OnBytes.Row) (hN : NamesOne r o)
    (m : Words GE) : Says rdE B r m ↔ Says rdE A r m := by
  obtain ⟨x', hx', hsh, -, -⟩ := h.2 o x hx hs
  have hshape : (B.oracles[o]?).map (·.shape) = (A.oracles[o]?).map (·.shape) := by
    rw [hx, hx']
    exact congrArg some hsh
  unfold Says
  rw [value_named B r o hN m, value_named A r o hN m,
    onTable_same A B r m m o .main (size_same A B o h.1 hshape .main) (fun _ => rfl),
    onTable_same A B r m m o .mask (size_same A B o h.1 hshape .mask) (fun _ => rfl)]

/-- **Such a row reads the words at its own message alone.** -/
theorem says_of_words (A : Statement) {o : ℕ} (r : OnBytes.Row) (hN : NamesOne r o) (m m' : Words GE)
    (hm : ∀ part i, m' o part i = m o part i) : Says rdE A r m' ↔ Says rdE A r m := by
  unfold Says
  rw [value_named A r o hN m', value_named A r o hN m,
    onTable_same A A r m m' o .main rfl (hm .main), onTable_same A A r m m' o .mask rfl (hm .mask)]

/-- **Two plans of a sending with the same notices and the same codes.** Place, the ground's two numbers, the bits of
work, the parts' names and the groups told may differ. -/
structure PlansAlike (P Q : Par) : Prop where
  sent : P.sent = Q.sent
  codes : P.codes = Q.codes

/-- The held words are the same at both. -/
theorem held_of_alike {P Q : Par} (h : PlansAlike P Q) (w : Words GE) (f : ℕ) (V : ℕ → Rows) :
    Johnson.Prover.Send.held w f P V = Johnson.Prover.Send.held w f Q V := by
  unfold Johnson.Prover.Send.held shapeAt
  rw [h.sent]

/-- **The sender's term for its answers is the same at both.** -/
theorem answers_of_alike {P Q : Par} (h : PlansAlike P Q) (f : ℕ) (V : ℕ → Rows) (r₁ : Fmt.RoundView) :
    answers P (stAt P f) f (Johnson.Prover.Send.held (fun _ _ _ => 0) f P V) (seedsOf P r₁) =
      answers Q (stAt Q f) f (Johnson.Prover.Send.held (fun _ _ _ => 0) f Q V) (seedsOf Q r₁) := by
  rw [held_of_alike h]
  unfold answers stAt shapeAt seedsOf Par.coordinates Par.seeds Par.tuple
  rw [h.sent, h.codes]

/-- **Behind a yes of the sending's decision whose second round holds the sender's answers.** f: any number: the term
does not hang on it (`answers_any_first`). SPEAKS OF ANSWERS, WHICH HANG ON THE PADS. -/
theorem sending_says {L : Type} (Q : Par) (owed : Option ℕ) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array ℕ) (h : decideSend Q owed d [r₁, r₂] = .ok (ids, d')) (V : ℕ → Rows) (f : ℕ)
    (hans : r₂.vals =
      (answers Q (stAt Q f) f (Johnson.Prover.Send.held (fun _ _ _ => 0) f Q V) (seedsOf Q r₁)).map .answer)
    (k : ℕ) (hk : k < Q.sent.size) (x : Oracle)
    (hx : d'.st.oracles[d.st.oracles.size + k]? = some x) :
    (∀ w : Words GE, AllSay rdE d'.st x.sampleRows.toList (Johnson.Prover.Send.held w d.st.oracles.size Q V)) ∧
      ∀ r ∈ x.sampleRows.toList, NamesOne r (d.st.oracles.size + k) := by
  obtain ⟨hasks, -, rfl⟩ := (decideSend_iff Q owed d d' r₁ r₂ ids).1 h
  refine ⟨fun w => ?_, names_new Q d _ _ k hk x hx⟩
  have hans' : r₂.vals = (answers Q (OnBytes.Slice.stSent d.st Q.sent) d.st.oracles.size
      (Johnson.Prover.Send.held w d.st.oracles.size Q V) (seedsOf Q r₁)).map .answer := by
    rw [hans, answers_any_first Q f V, ← answers_any_first Q d.st.oracles.size V,
      part_answers Q d hasks.2.1 w V]
  exact Johnson.Prover.Send.send_says Q d r₁ r₂ w V hans' k x hk hx

/-- `SameMsgs` keeps the number of messages. -/
theorem count_of_same_messages {A B : Statement} (h : SameMsgs A B) :
    B.oracles.size = A.oracles.size := by
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

/-- A list, cut at a member. -/
theorem list_cut_at {α : Type} {l : List α} {m : ℕ} {b : α} (h : l[m]? = some b) :
    l = l.take m ++ b :: l.drop (m + 1) := by
  obtain ⟨hm, e⟩ := List.getElem?_eq_some_iff.1 h
  have t := List.take_append_drop m l
  rw [List.drop_eq_getElem_cons hm, e] at t
  exact t.symm

/-- **THE LAW: A CHAIN's FOLD, CUT AT A SENDING.** bs: the chain's blocks. m: the sending's number among them. a: the
state in front of it; s': the state behind it; e: the fold's end. roundOfSeeds: how many rounds the blocks in front of
the sending have. hans: of the rounds that the fold is handed, the one behind the seeds' round holds the sender's
answers at the rows V. Then message k of the sending stands at the fold's
end, sampled; its sample rows name it alone and say their claims of the held words, whatever words lie beneath.
SPEAKS OF ANSWERS, WHICH HANG ON THE PADS. -/
theorem after_sending_says (bs : List (Block FirstState Claim)) (Q : Par)
    (b₀ : Block FirstState Claim) (m : ℕ) (hb : bs[m]? = some b₀)
    (hr : b₀.rounds = VerifiableInference.Desc.K1.rounds Q) (hS : Named Q b₀)
    (hkeep : ∀ b ∈ bs.drop (m + 1), Decides (By SmpStay st₁) b) (ft : ℕ)
    {s e : FirstState} {rs r : List Fmt.RoundView} {cols c : List OpenedColumn}
    (h : foldBlocks ft bs s rs cols = .ok (e, r, c)) (V : ℕ → Rows) (f : ℕ) (roundOfSeeds : ℕ)
    (hround : roundOfSeeds = ((bs.take m).flatMap (·.rounds)).length)
    (hans : ∀ ρ₁ ρ₂ : Fmt.RoundView, rs[roundOfSeeds]? = some ρ₁ → rs[roundOfSeeds + 1]? = some ρ₂ →
      ρ₂.vals = (answers Q (stAt Q f) f (Johnson.Prover.Send.held (fun _ _ _ => 0) f Q V) (seedsOf Q ρ₁)).map .answer)
    (k : ℕ) (hk : k < Q.sent.size) (ha : (shapeAt Q k).answers ≠ 0) :
    ∃ (a s' : FirstState) (r₀ r' : List Fmt.RoundView) (c₀ c' : List OpenedColumn),
      foldBlocks ft (bs.take m) s rs cols = .ok (a, r₀, c₀) ∧
      foldBlocks ft (bs.drop (m + 1)) s' r' c' = .ok (e, r, c) ∧
      (st₁ s').oracles.size = (st₁ a).oracles.size + Q.sent.size ∧
      ∃ x : Oracle, (st₁ e).oracles[(st₁ a).oracles.size + k]? = some x ∧ x.sampled = true ∧
        (∀ q ∈ x.sampleRows.toList, NamesOne q ((st₁ a).oracles.size + k)) ∧
        ∀ w : Words GE, AllSay rdE (st₁ e) x.sampleRows.toList (Johnson.Prover.Send.held w (st₁ a).oracles.size Q V) := by
  subst hround
  have hf := list_cut_at hb
  rw [hf] at h
  obtain ⟨a, r₀, c₀, h₁, h₂⟩ := (VerifiableInference.Desc.foldBlocks_append_ok _ _ _ _ _ _).1 h
  obtain ⟨-, s', n, hstep, hrest⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h₂
  have hfit₀ := (VerifiableInference.Desc.Plain.step_fits hstep).1
  have hfit : VerifiableInference.Desc.roundsFit (VerifiableInference.Desc.K1.rounds Q)
      (List.take b₀.rounds.length r₀) = true := by
    rw [← hr]
    exact hfit₀
  obtain ⟨ρ₁, ρ₂, hR⟩ := two_of_fit _ _ _ hfit
  -- the two rounds, by their numbers in the list that the fold was handed
  have hr₀ := fold_leaves_the_rest ft _ _ _ _ _ _ _ h₁
  obtain ⟨t, ht⟩ := List.take_prefix b₀.rounds.length r₀
  rw [hR] at ht
  have e₀ : rs[((bs.take m).flatMap (·.rounds)).length]? = some ρ₁ := by
    have g : r₀[0]? = some ρ₁ := by
      rw [← ht]
      rfl
    rw [hr₀, List.getElem?_drop] at g
    exact g
  have e₁ : rs[((bs.take m).flatMap (·.rounds)).length + 1]? = some ρ₂ := by
    have g : r₀[1]? = some ρ₂ := by
      rw [← ht]
      rfl
    rw [hr₀, List.getElem?_drop] at g
    exact g
  obtain ⟨gs, hd⟩ := _root_.Desc.K14.Law.step_decides ft b₀ a s' _ c₀ n hstep
  rw [hR] at hd
  obtain ⟨ids, d', hyes, hsame⟩ := hS a s' _ _ gs hd
  have hA : (noDigest ρ₂).vals = (answers Q (stAt Q f) f (Johnson.Prover.Send.held (fun _ _ _ => 0) f Q V)
      (seedsOf Q (noDigest ρ₁))).map .answer := hans ρ₁ ρ₂ e₀ e₁
  obtain ⟨-, -, hd'⟩ := (decideSend_iff Q a.debt _ d' _ _ ids).1 hyes
  obtain ⟨X, hx, hxs⟩ : ∃ X : Oracle,
      d'.st.oracles[(st₁ a).oracles.size + k]? = some X ∧ X.sampled = true :=
    ⟨_, by rw [hd']; exact Johnson.Prover.Send.behind_at Q _ _ _ k hk,
      (Johnson.Prover.Send.wr_sampled _ _ _ _ _ ha).2.1⟩
  obtain ⟨hsay, hnames⟩ := sending_says Q a.debt _ d' _ _ ids hyes V f hA k hk X hx
  have hsz : (st₁ s').oracles.size = (st₁ a).oracles.size + Q.sent.size := by
    rw [count_of_same_messages hsame, hd', Johnson.Prover.Send.size_sent]
    show ((st₁ a).oracles ++ Q.sent.map _).size = _
    rw [Array.size_append, Array.size_map]
  have e₂ := hsame.2 ((st₁ a).oracles.size + k)
  rw [hx] at e₂
  obtain ⟨y, hy, ey⟩ := Option.map_eq_some_iff.1 e₂
  have ey₁ : y.sampled = X.sampled := congrArg (fun p => p.2.1) ey
  have ey₂ : y.sampleRows = X.sampleRows := congrArg (fun p => p.2.2) ey
  have hstay : SmpStay (st₁ s') (st₁ e) :=
    VerifiableInference.Desc.Keeps.foldBlocks_keeps (By SmpStay st₁)
      (fun _ => SmpStay.refl _) (fun _ _ _ p q => p.trans q) ft _ hkeep s' _ _ _ hrest
  have hys : y.sampled = true := ey₁.trans hxs
  obtain ⟨z, hz, -, hzs, hzr⟩ := hstay.2 _ y hy hys
  have back : ∀ q ∈ z.sampleRows.toList, q ∈ X.sampleRows.toList := fun q hq => by
    rw [← ey₂, ← hzr]
    exact hq
  refine ⟨a, s', r₀, _, c₀, _, h₁, hrest, hsz, z, hz, hzs, fun q hq => hnames q (back q hq),
    fun w q hq => ?_⟩
  exact (says_of_stay hstay hy hys q (hnames q (back q hq)) _).2
    ((says_sameMsgs hsame q _ (hnames q (back q hq)) _).2 (hsay w q (back q hq)))

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.fold_leaves_the_rest
#print axioms ProofFile.Honest.K12.AtKey.says_of_stay
#print axioms ProofFile.Honest.K12.AtKey.says_of_words
#print axioms ProofFile.Honest.K12.AtKey.PlansAlike
#print axioms ProofFile.Honest.K12.AtKey.held_of_alike
#print axioms ProofFile.Honest.K12.AtKey.answers_of_alike
#print axioms ProofFile.Honest.K12.AtKey.sending_says
#print axioms ProofFile.Honest.K12.AtKey.count_of_same_messages
#print axioms ProofFile.Honest.K12.AtKey.list_cut_at
#print axioms ProofFile.Honest.K12.AtKey.after_sending_says
