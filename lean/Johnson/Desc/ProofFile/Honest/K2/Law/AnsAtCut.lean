-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/AnsAtCut.lean: the kind "the code switch" (K2): THE SHARED
SENDING's LAW ON A SAMPLE's ANSWERS (`ans_at_entry`, Honest/K1/Law/SendAtBlock.lean, of other
authors) AT A BLOCK WHOSE SECOND ROUND HOLDS MORE THAN A SENDING's. That law asks that the block's
yes holds the sending's decision at the block's own two rounds, and that these fit the sending's
rounds. A switch's second round also draws positions: wherever its numbers state one or more, as the
kind's own test on the plan asks, it cannot fit them, for the sending's second round draws none; and
what is known of a switch's yes stands at that round cut to the sending's answers (`cutTo`,
Johnson/Desc/K1/Law/SendP4.lean). Here the law is had all the same, at the switch's own rounds. Four
statements with their proofs; no definition.

  `decideSend_vals`  the sending's decision reads of its second round what it shows, alone
  `fit_trimmed`      a switch's two rounds that fit, the second without its draws, fit the
                     sending's rounds; and the second shows as many items as the sending has answers
  `block_at_cut`     THE HELPER BLOCK: there is a block of the sending's make that says, at the
                     one state and the trimmed rounds, what the given block says at its own
  `ans_at_cut`       THE END

By: `ans_at_entry`, called at `block_at_cut`'s block. Its end names the two records alone: so the
helper is not in it. `block_at_cut` stands by itself so that other laws of the shared sending whose
ends name no block can be called the same way. THE HELPER IS A WRAPPER, NOT A STEP OF THE ARGUMENT:
`ans_at_entry`'s binders ask for a block; what it draws from the block is one fact on the sending's
decision. Stated from that fact, the law would need no helper: we have seen no such form.
`items_give` (Johnson/Desc/K2/Honest/Returns/ItemsFit.lean): what a switch's rounds that fit give.
Kin, not called: `fits_send` (Johnson/Desc/K14/Honest/ChainWitness.lean): the sending's rounds fit
at a written first round of its own; the steps of `fit_trimmed`'s proof on the sending's two entries
go as its · `answers_tied` (ItemsFit.lean): the count of answers in the cut round.
`seeds_at_numbers` (Honest/K2/Law/SeedsOfDraw.lean) asks h₁ and h₂ too, and that file says from what
they follow.

Limits. EVERY PREMISE IS A PREMISE. hS: the sentence on the block's yes at the cut round, AT THE ONE
STATE s AT WHICH THE LAW SPEAKS: shown of no block here. (A switch takes what it sends off the
state: at all states the sentence need not hold of one sending.) hB, hC, hok, hans: `ans_at_entry`'s
own. `fit_trimmed` asks three public equations between the switch's numbers and the sending's: shown
of no plan here. SPEAKS OF ANSWERS, as `ans_at_entry` does. The helper block's test on its state and
its rounds is decided classically: it is a tool of the proof and is run nowhere. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.SendAtBlock
import Johnson.Desc.K2.Honest.Returns.ItemsFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2)
open VerifiableInference.Desc.K1 (IsSend Booked SameMsgs condPort sampledAt shapesOf decideSend
  smpAt cutTo seedEntry answerEntry)
open VerifiableInference.Desc.K2.Honest.Returns (items_give)
open Johnson.Prover.Send (answers)

variable {Cl : Type}

/-- **The sending's decision reads of its second round what it shows, alone.** -/
theorem decideSend_vals {Lt : Type} (P : K1.Par) (owed : Option Nat) (d : DState Lt)
    (r₁ a b : Fmt.RoundView) (h : a.vals = b.vals) :
    decideSend P owed d [r₁, a] = decideSend P owed d [r₁, b] := by
  obtain ⟨va, da⟩ := a
  obtain ⟨vb, db⟩ := b
  obtain rfl : va = vb := h
  rfl

/-- **A switch's rounds that fit, the second without its draws, fit the sending's.** h₁, h₂, hA: the
switch's numbers of drawn elements, of those that must not be 0, and of answers are the sending's.
-/
theorem fit_trimmed (P : K1.Par) (q : P2) (h₁ : q.seeds = P.seeds * (P.coordinates + 1))
    (h₂ : q.nonZero = P.seeds) (hA : P.answers = q.answers) {r₁ r₂ : Fmt.RoundView}
    (h : roundsFit (First.K2.rounds q) [r₁, r₂] = true) :
    roundsFit (K1.rounds P) [r₁, ⟨r₂.vals, ⟨[], [], [], none⟩⟩] = true ∧
      r₂.vals.length = P.answers := by
  obtain ⟨-, v1, v2, -, -, -⟩ := items_give q r₁ r₂ h
  simp only [First.K2.rounds, roundsFit, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, e1⟩, p1⟩, t1⟩, a5⟩, a6⟩, n1⟩, -⟩ := h
  have i1 : (Fmt.DeclaredRound.items { entry := seedEntry P }).filter (· != .root) = [] := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, seedEntry]
  have i2 : (Fmt.DeclaredRound.items { entry := answerEntry P }).filter (· != .root) =
      List.replicate P.answers .answer := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, answerEntry]
  have m1 : drawsMarkedNonzeroHaveNonzeroWords { entry := seedEntry P } r₁ = true := by
    rw [h₁, h₂] at n1
    exact n1
  have m2 : drawsMarkedNonzeroHaveNonzeroWords { entry := answerEntry P } ⟨r₂.vals, ⟨[], [], [], none⟩⟩ = true := by
    obtain ⟨k, hk⟩ : ∃ k, Fmt.kindOf (answerEntry P).name = some k := by
      show ∃ k, Fmt.kindOf "SEND answer" = some k
      exact Option.isSome_iff_exists.1 (by decide)
    unfold drawsMarkedNonzeroHaveNonzeroWords
    rw [hk, Option.any_some]
    simp
  refine ⟨?_, ?_⟩
  · simp only [VerifiableInference.Desc.K1.rounds, roundsFit, Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, p1⟩, t1⟩, a5⟩, a6⟩, m1⟩,
      ⟨⟨⟨⟨⟨⟨?_, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, m2⟩, ?_⟩
    · rw [i1, v1]
      rfl
    · show (r₁.drawn.elems.length == P.seeds * (P.coordinates + 1)) = true
      rw [← h₁]
      exact e1
    · rw [i2, hA]
      exact beq_iff_eq.2 v2
    · first | rfl | trivial
  · have e := congrArg List.length v2
    rw [List.length_map, List.length_replicate] at e
    rw [e, hA]

/-- **THE HELPER BLOCK.** hS: AT THE ONE STATE s, a yes of b holds the sending's decision at the
second round cut to the sending's answers. b': says, at the state s, the first round and the second
without its draws, what b says there at its own two rounds; it refuses elsewhere. So b' is a block
of the shared sending's make, though b's yes at another state may hold another sending's. -/
theorem block_at_cut (P : K1.Par) {b : Block S Cl}
    {s : S}
    (hS : ∀ s' r₁ r₂ gs, b.decide s [r₁, r₂] gs = .ok s' →
      ∃ (Lt : Type) (d d' : DState Lt) (owed : Option Nat) (ids : Array Nat),
        decideSend P owed d [r₁, cutTo P r₂] = .ok (ids, d') ∧ SameMsgs d'.st s'.st ∧
          s'.st.oracles.size = d'.st.oracles.size)
    {s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : b.decide s [r₁, r₂] gs = .ok s') (hl : r₂.vals.length = P.answers) :
    ∃ b' : Block S Cl, IsSend P (fun s : S => s.st) b' ∧
      b'.decide s [r₁, ⟨r₂.vals, ⟨[], [], [], none⟩⟩] gs = .ok s' := by
  classical
  have hv : (⟨r₂.vals, ⟨[], [], [], none⟩⟩ : Fmt.RoundView).vals = (cutTo P r₂).vals :=
    (List.take_of_length_le (Nat.le_of_eq hl)).symm
  let b' : Block S Cl :=
    { b with decide := fun t rs g =>
        if t = s ∧ rs = [r₁, ⟨r₂.vals, ⟨[], [], [], none⟩⟩] then b.decide t [r₁, r₂] g
        else .error "" }
  have hS' : IsSend P (fun s : S => s.st) b' := by
    intro t t' a₁ a₂ g h
    by_cases e : t = s ∧ [a₁, a₂] = [r₁, (⟨r₂.vals, ⟨[], [], [], none⟩⟩ : Fmt.RoundView)]
    · have h' : b.decide t [r₁, r₂] g = .ok t' := by
        have h2 : (if t = s ∧ [a₁, a₂] = [r₁, (⟨r₂.vals, ⟨[], [], [], none⟩⟩ : Fmt.RoundView)] then
            b.decide t [r₁, r₂] g else .error "") = .ok t' := h
        rwa [if_pos e] at h2
      rw [e.1] at h'
      obtain ⟨Lt, d, d', owed, ids, hy, hs, hz⟩ := hS _ _ _ _ h'
      rw [e.2]
      exact ⟨Lt, d, d', owed, ids, (decideSend_vals P owed d r₁ _ _ hv).trans hy, hs, hz⟩
    · have h2 : (if t = s ∧ [a₁, a₂] = [r₁, (⟨r₂.vals, ⟨[], [], [], none⟩⟩ : Fmt.RoundView)] then
          b.decide t [r₁, r₂] g else .error "") = .ok t' := h
      rw [if_neg e] at h2
      cases h2
  have hd' : b'.decide s [r₁, ⟨r₂.vals, ⟨[], [], [], none⟩⟩] gs = .ok s' := by
    show (if s = s ∧ [r₁, (⟨r₂.vals, ⟨[], [], [], none⟩⟩ : Fmt.RoundView)] =
        [r₁, ⟨r₂.vals, ⟨[], [], [], none⟩⟩] then
      b.decide s [r₁, r₂] gs else .error "") = .ok s'
    rw [if_pos ⟨rfl, rfl⟩]
    exact hd
  exact ⟨b', hS', hd'⟩

/-- **THE SAMPLE's ANSWERS BEHIND A BLOCK WHOSE YES HOLDS THE SENDING's AT THE CUT ROUND.** hS: that
sentence, at the one state s. hfit, hl: what `fit_trimmed` gives. The other letters and the end are
`ans_at_entry`'s. -/
theorem ans_at_cut (P : K1.Par) (rad : ℕ → ℕ) (hC : condPort P rad = true) {b : Block S Cl}
    {s : S}
    (hS : ∀ s' r₁ r₂ gs, b.decide s [r₁, r₂] gs = .ok s' →
      ∃ (Lt : Type) (d d' : DState Lt) (owed : Option Nat) (ids : Array Nat),
        decideSend P owed d [r₁, cutTo P r₂] = .ok (ids, d') ∧ SameMsgs d'.st s'.st ∧
          s'.st.oracles.size = d'.st.oracles.size)
    {s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : b.decide s [r₁, r₂] gs = .ok s')
    (hB : Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (hfit : roundsFit (K1.rounds P) [r₁, ⟨r₂.vals, ⟨[], [], [], none⟩⟩] = true)
    (hl : r₂.vals.length = P.answers)
    (hok : (r₁.drawn.elems.all fun x =>
      x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true)
    (V : ℕ → Johnson.Prover.Send.Rows)
    (hans : r₂.vals = (answers P (K1.stAt P s.st.oracles.size) s.st.oracles.size
      (Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size P V)
      (K1.seedsOf P r₁)).map .answer)
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) (p : OracleShape × ℕ)
    (hp : p.1 = K1.shapeAt P k) :
    ∃ z : (portOmZ P.codes p.1 p.2).Smp,
      smpAt P.codes p.1 p.2 s'.st (s.st.oracles.size + k.val) = some z ∧
        (portOmZ P.codes p.1 p.2).Z.val z.1
          (fun j => Johnson.Prover.Send.held (fun _ _ _ => 0) s.st.oracles.size P V
            (s.st.oracles.size + k.val) (partZ P.codes p.1 j) (locZ P.codes p.1 j)) = z.2 := by
  obtain ⟨b', hS', hd'⟩ := block_at_cut P hS hd hl
  exact K1.ans_at_entry P rad hC hS' hd' hB hfit hok V hans k hk p hp

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.decideSend_vals
#print axioms ProofFile.Honest.K2.Law.fit_trimmed
#print axioms ProofFile.Honest.K2.Law.block_at_cut
#print axioms ProofFile.Honest.K2.Law.ans_at_cut
