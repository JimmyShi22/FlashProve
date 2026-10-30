-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/OwnHandsApart.lean: the kind "the code switch" (K2): TWO
SWITCHES' OWN HANDS ARE DIFFERENT COINS OF THE RUN, AS ONE LAW. What the frame hands a switch's part
as its own (the first component of `handed`, Honest/K2/ScriptLots.lean) is one row of the run's
coins, seen through a lens: a getter and a setter on all the run's coins. Setting that row anew, to
any value, makes that value the switch's own hand, leaves what it carries as it was, and leaves the
own hand of every switch at another place as it was. Three statements with their proofs; no
definition.

  `lent_of_handed`   where `handed` returns, the frame's `lendPart` returned that
  `no_own_entry`     at a book that passes its tests no entry hands a part a run of its own coins
  `own_hands_apart`  THE END

By, of other authors: `fit_of_lent` (Honest/Law/Rule/PartCell.lean) · `RowAt`, `lent_self`
(Honest/Law/Rule/LentAt.lean) · `Cs.cut_zero` (Honest/Law/Rule/RowLens.lean) · `ProverCoinCounts.behind`
(Honest/Law/Rule/Tests.lean). Of ours: `own_of_handed` (Honest/K2/Law/MaskTxt.lean) ·
`handed_public` (Honest/K2/Law/LotsAnswer.lean).

Limits. THE OWN HANDS ALONE. A later switch also CARRIES runs of an earlier switch's coins: these
components of its hand do read the earlier switch's row, and nothing is said of them here
(`lent_known`, Honest/Law/Rule/LentAt.lean, says how far they do). The premises: the book passes its
tests at a description, the description its test on the places, the switch's place is one of the
chain's, and the frame hands the part its coins at one run's coins: shown here at no book. Two parts
at one place are not spoken of: a switch has one part. Inside one hand, that each coin is laid once
is another law's matter (Honest/K2/Law/EveryCoinOnce.lean, not imported). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.PartCell
import Johnson.Desc.ProofFile.Honest.Law.Rule.LentAt
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (FileDescription)

variable {Bk : ProverCoinCounts} {Xf : Type}

/-- Where `handed` returns, the frame's `lendPart` returned that. -/
theorem lent_of_handed {ch : Nat} {p : SwitchPlace} {k : Coins Bk}
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (h : handed ch p k = some c) :
    lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
      (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries) = .ok c := by
  unfold handed at h
  cases hl : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
      (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries) with
  | error _ =>
    rw [hl] at h
    cases h
  | ok c' =>
    rw [hl] at h
    exact congrArg Except.ok (Option.some.inj h)

/-- At a book that passes its tests no entry hands a part a run of its own coins. -/
theorem no_own_entry {F : FileDescription Xf} (hb : Bk.word F = none) (a : Addr) :
    ∀ e ∈ Bk.ahead, e.spender = a → e.owner ≠ a := by
  intro e he hs ho
  have t := ProverCoinCounts.behind hb e he
  rw [hs, ho] at t
  simp [Addr.before] at t

/-- **TWO SWITCHES' OWN HANDS ARE DIFFERENT COINS OF THE RUN.** get, put: a lens on the run's coins
that shows the row at p's own address. -/
theorem own_hands_apart {F : FileDescription Xf} (hb : Bk.word F = none) (hp : F.placesOk = true)
    {ch : Nat} (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) {p : SwitchPlace} (ha : p.place ∈ placesAt F ch)
    {k₀ : Coins Bk} {c₀ : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (h₀ : handed ch p k₀ = some c₀) :
    ∃ (get : Coins Bk → Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)))
      (put : Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)) → Coins Bk → Coins Bk),
      RowAt Bk ⟨p.place, 0⟩ ch _ get put ∧
      (∀ k c, handed ch p k = some c → c.1 = get k) ∧
      (∀ x k c, handed ch p k = some c → handed ch p (put x k) = some (x, c.2.1, c.2.2)) ∧
      ∀ p' : SwitchPlace, p'.place ≠ p.place → ∀ x k c', handed ch p' k = some c' →
        ∃ c'', handed ch p' (put x k) = some c'' ∧ c''.1 = c'.1 := by
  obtain ⟨gp, R⟩ := (fit_of_lent hb hp hch ha (lent_of_handed h₀)).row
  refine ⟨gp.1, gp.2, R, ?_, ?_, ?_⟩
  · intro k c h
    have e := own_of_handed ch p k c h
    unfold K1.lentCut at e
    rw [R.self ch (Or.inl rfl) k] at e
    exact (Option.some.inj ((Cs.cut_zero (gp.1 k)).symm.trans e)).symm
  · intro x k c h
    have e := lent_self R (Bk.rowsOf ch) (no_own_entry hb _) x k
    rw [lent_of_handed h] at e
    unfold handed
    rw [e]
    rfl
  · intro p' hne x k c' h'
    have hs : (handed ch p' (gp.2 x k)).isSome = true := by
      rw [handed_public ch p' (gp.2 x k) k, h']
      rfl
    obtain ⟨c'', h''⟩ := Option.isSome_iff_exists.1 hs
    refine ⟨c'', h'', ?_⟩
    have e' := own_of_handed ch p' k c' h'
    have e'' := own_of_handed ch p' (gp.2 x k) c'' h''
    unfold K1.lentCut at e' e''
    rw [R.other x k ch ⟨p'.place, 0⟩ (fun e => hne (congrArg Addr.place e)), e'] at e''
    exact (Option.some.inj e'').symm

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.lent_of_handed
#print axioms ProofFile.Honest.K2.Law.no_own_entry
#print axioms ProofFile.Honest.K2.Law.own_hands_apart
