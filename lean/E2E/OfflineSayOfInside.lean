-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineSayOfInside.lean: THE ONE CLAUSE OF TRUTH in the condition at a proximity test's second part (`SaysInFront`,
E2E/OfflineSayAtRun.lean), CARRIED FROM IN FRONT OF THE TEST TO BEHIND ITS FIRST PART: where a chain's invariant A holds in
front of the test and gives that clause there, the clause holds at the state behind the first part's rounds, at
its front cut back and at the blocks that the frame hands the second part as carried. General in the job, its
plain rows, the chain, the book, the list of halves, the face and the invariant.

  `says_of_inside`           at the plain half
  `says_of_inside_guarded`   at the half behind the guard on the field, wherever A holds the field being some

Asked of the letter rows (hrows): it reads of the coins all but the second part's own.

Limits. `InsideOf` (Johnson/Desc/ProofFile/Honest/Law/Inside.lean) and "the clause wherever A holds" are premises: no
member of either is given here: the law moves the sentence and proves nothing of it. The sentence reads the input
and the carried coins. Nothing on any property.
-/
import E2E.OfflineTestAsksGuarded
import E2E.OfflineSayAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc (Block)

variable {S Cl V W X Pb : Type}

/-- **The clause behind the first part, from the clause in front of the test.** -/
theorem says_of_inside {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain : ℕ} {hs : List (Placed V W X)}
    {b : Block S Cl} (J : TestJob W X) (rows : W → Front X → TestCoins → PlainRows)
    (hrows : ∀ w fr (c : (restPart J : Part V W X).Coins),
      rows w fr (restCoins J c) = rows w fr (carriedCoins J (stretches _ c.2.2)))
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (P : FirstPartPublic J s next rest)
    (hlaid : b.rounds.zip b.oracles = J.laid) (hor : b.oracles.length = b.rounds.length)
    (hhalf : (hs.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J))
    {A : Coins Bk → S → Mid W X → Env → Prop} {k : Coins Bk} {m : Mid W X} {E : Env}
    (hin : InsideOf φ Bk chain hs b A (firstLen J.p.nums.stages) k m E)
    (hA : ∀ st m₀ E₀ (c : RowCoins [(firstPart J : Part V W X), restPart J]), A k st m₀ E₀ →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) b.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c →
      SaysInFront J m₀.st.input (frontOf m₀) (rows m₀.st.input (frontOf m₀) (restCoins J c.2.1)))
    (ca : CsAll (restPart J : Part V W X).carries)
    (hca : carriedAt Bk k chain ⟨b.place, 1⟩ (restPart J : Part V W X) = .ok ca) :
    SaysInFront J m.st.input (restFront J m)
      (rows m.st.input (restFront J m) (carriedCoins J (stretches _ ca))) := by
  obtain ⟨st, m₀, E₀, c, h0, hc, hi, hfr, -⟩ := behind_first_part J s next rest P hlaid hor hhalf hin
  obtain rfl : c.2.1.2.2 = ca :=
    Except.ok.inj ((carried_of_lent k chain b.place _ _ c hc).symm.trans hca)
  have h := hA st m₀ E₀ c h0 hc
  rw [hrows, ← hi, ← hfr] at h
  exact h

/-- **The same where the test's half stands behind the guard on the field.** -/
theorem says_of_inside_guarded {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain : ℕ} {hs : List (Placed V W X)}
    {b : Block S Cl} (J : TestJob W X) (rows : W → Front X → TestCoins → PlainRows)
    (hrows : ∀ w fr (c : (restPart J : Part V W X).Coins),
      rows w fr (restCoins J c) = rows w fr (carriedCoins J (stretches _ c.2.2)))
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (P : FirstPartPublic J s next rest)
    (hlaid : b.rounds.zip b.oracles = J.laid) (hor : b.oracles.length = b.rounds.length)
    (hhalf : (hs.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J).needsField)
    {A : Coins Bk → S → Mid W X → Env → Prop}
    (hopen : ∀ k s m E, A k s m E → m.opened.isSome = true) {k : Coins Bk} {m : Mid W X} {E : Env}
    (hin : InsideOf φ Bk chain hs b A (firstLen J.p.nums.stages) k m E)
    (hA : ∀ st m₀ E₀ (c : RowCoins [(firstPart J : Part V W X), restPart J]), A k st m₀ E₀ →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) b.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c →
      SaysInFront J m₀.st.input (frontOf m₀) (rows m₀.st.input (frontOf m₀) (restCoins J c.2.1)))
    (ca : CsAll (restPart J : Part V W X).carries)
    (hca : carriedAt Bk k chain ⟨b.place, 1⟩ (restPart J : Part V W X) = .ok ca) :
    SaysInFront J m.st.input (restFront J m)
      (rows m.st.input (restFront J m) (carriedCoins J (stretches _ ca))) := by
  obtain ⟨st, m₀, E₀, c, h0, hc, hi, hfr, -⟩ :=
    behind_first_guarded J s next rest P hlaid hor hhalf hopen hin
  obtain rfl : c.2.1.2.2 = ca :=
    Except.ok.inj ((carried_of_lent k chain b.place _ _ c hc).symm.trans hca)
  have h := hA st m₀ E₀ c h0 hc
  rw [hrows, ← hi, ← hfr] at h
  exact h

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.says_of_inside
#print axioms AtPublicFiles.OfflineRows.says_of_inside_guarded
