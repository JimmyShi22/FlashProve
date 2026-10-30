-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingWordsJob.lean: the job's rows at the stretches that a
later part is lent are message 0 of the switch's lot, where the book's entries agree.

  own_tie              the first message's cut of the part's own coins is the owner's cut
  lendPart_of_handed   what handed hands is what the frame lends
  carryRows_at_lent    the statement

By what. carryRows_of_laid (ClosingWordsRows.lean), carried_tie, cut_cut_zero (ClosingWordsCoins.lean).

Hypotheses. hH, hV: the switch's part is handed c, its rows return V. hT: the later part q at a₂ is
lent cT at the same chain's coins. hlen, hsame: the part's carried entries and q's first ones name
the same owner, start and count. hown: q's next entry is the switch's first message: at its address,
from 0, at its count. h1: the sending has at least two messages.

Limits. The book's entries are premises. They are public, and no test on this pair of parts is
written yet. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingWordsRows
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingWordsCoins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K2.Law (SwitchCoins)

variable {W₀ Rc Xi Tr V' W' X' : Type} {Bk : ProverCoinCounts}

/-- The first message's cut of the part's own coins is the owner's cut. -/
theorem own_tie {d t n n' : Due} {L : Cs d} {c₁ : Cs t} {c' : Cs n} {x : Cs n'}
    (h1 : L.cut ⟨0, 0⟩ t = some c₁) (h2 : c₁.cut ⟨0, 0⟩ n = some c')
    (h3 : L.cut ⟨0, 0⟩ n' = some x) (e : n = n') :
    (⟨n, c'⟩ : K2.Stretch) = asK2 n' (stretchOf x) := by
  subst e
  rw [asK2_stretchOf, cut_cut_zero h1 h2 h3]
  rfl

/-- What handed hands is what the frame lends. -/
theorem lendPart_of_handed {ch : ℕ} {p : K2.SwitchPlace} {k : Coins Bk}
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (h : K2.handed ch p k = some c) :
    lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) =
        .ok c := by
  unfold K2.handed at h
  cases e : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) with
  | error _ =>
    rw [e] at h
    cases h
  | ok c' =>
    rw [e] at h
    obtain rfl := Option.some.inj h
    rfl

/-- **The job's rows at the stretches that a later part is lent are message 0 of the lot.** -/
theorem carryRows_at_lent {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers}
    {closing : K2.Closing} {p : K2.SwitchPlace} {ch : ℕ} {k : Coins Bk} {w : Local W₀ Rc Xi Tr}
    {hd : List Fmt.Drawn} {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    {V : ℕ → Johnson.Prover.Send.Rows}
    (hH : K2.handed ch p k = some c)
    (hV : K2.switchRowsLaid D readers closing p c w hd = .ok V)
    (h1 : 1 < (K2.switchSent p.sizes p.others).size)
    {a₂ : Addr} {q : Part V' W' X'} {cT : q.Coins}
    (hT : lendPart Bk (Bk.rowsOf ch) (k.look ch) a₂ q = .ok cT)
    (hlen : p.front.length ≤ (ProofFile.Honest.carryE Bk ⟨p.place, 0⟩).length)
    (hsame : ∀ n a, n < p.front.length → (ProofFile.Honest.carryE Bk ⟨p.place, 0⟩)[n]? = some a →
      ∃ a', (ProofFile.Honest.carryE Bk a₂)[n]? = some a' ∧ a'.owner = a.owner ∧ a'.start = a.start ∧
        a'.count = a.count)
    {a' : Ahead} (ha : (ProofFile.Honest.carryE Bk a₂)[p.front.length]? = some a')
    (ho : a'.owner = ⟨p.place, 0⟩) (hs : a'.start = ⟨0, 0⟩)
    (hc : a'.count = K2.messageDue p.sizes.codes (shapeL p) none) :
    carryRows D readers closing p w hd (stretches q.carries cT.2.2) = .ok (V 0) := by
  have hl := lendPart_of_handed hH
  have l₁ := lend_of_lendPart_words hl
  have l₂ := lend_of_lendPart_words hT
  have hf : K2.foldAt (K2.switchFresh p.sizes p.others p.foldVars) 0 = none := by
    unfold K2.foldAt K2.switchFresh
    have hne : (K2.switchSent p.sizes p.others).size - 1 ≠ 0 := by omega
    simp [hne]
  refine carryRows_of_laid hV (carried_tie _ p l₁ l₂ hlen hsame) (by omega) hf ?_
  intro c' hcut
  obtain ⟨-, x, hx, ex⟩ := ProofFile.Honest.K12.lend_stretch _ _ _ _ l₂ _ a' ha
  rw [ex]
  have hown := own_of_lendPart_words hl
  rw [ho, hs] at hx
  have hd₀ : K2.dueBefore p.sizes.codes (K2.switchSent p.sizes p.others)
      (K2.switchFresh p.sizes p.others p.foldVars) 0 = ⟨0, 0⟩ := rfl
  rw [hd₀] at hcut
  have e : K2.messageDue p.sizes.codes ((K2.switchSent p.sizes p.others).getD 0 default).shape
      (K2.foldAt (K2.switchFresh p.sizes p.others p.foldVars) 0) = a'.count := by
    rw [hf, hc]
    rfl
  have t := own_tie hown hcut hx e
  rw [t]
  exact congrArg (fun d => asK2 d (stretchOf x)) hc

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.carryRows_at_lent
