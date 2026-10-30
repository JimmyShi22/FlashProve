-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WSays.lean: the clause `saysAt` of `StandAtW` (WAccepted.lean),
from what the items of the last chain say at the border in front of its test.

  `SaysOwe`        what `SaysAt` asks of a state and of words, each under its name
  `SaysLeft`, `owe_of_says`   what stays of it where the statement is tidy
  `saysAt_own`     `SaysAt` at the job's state on entry, from `SaysOwe`: `saysAt_of_items`
                   (E2E/ItemLaws.lean)

The clauses of `SaysOwe`. `order`: the statement is in order: the letter `order` of a last chain's
thread. `kinds`: no open row is marked as a sample row. `rows`: the item: `rows_at_two` (LotWJoint.lean) pays it at the words `wordsAtOwn`. `samples`: the own
group's
members' stored sample rows say of the words: the three pins. `tied`: on the members' tables the
words are those that the job's plain rows make (`WordsTied`, K12/SaysOfMet.lean): what the first
chain's and the shared chain's sendings sent.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: it stands behind `Thr`.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAccepted
import Johnson.Desc.ProofFile.Honest.Thread.Last
import Johnson.Desc.ProofFile.Honest.K12.SaysOfMet
import E2E.ItemLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (Group)
open OnBytes.Slice (rdE GE)
open OnBytes.Means (AllSay OpenKinds OpenSays InOrder Words layoutOf sampleItem rowAt_iff)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Last (ItemL MeaningL)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.Light.ItemLaws (saysAt_of_items openSays_of_rows)

/-- **What `SaysAt` asks of a state and of words.** -/
structure SaysOwe {W X : Type} (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins) (s : S₃)
    (m : Words GE) : Prop where
  order : OnBytes.Means.InOrder s.st
  kinds : OpenKinds s.st
  rows : ∀ G, s.st.groups[s.loc.own]? = some G → AllSay rdE s.st G.rows.toList m
  samples : ∀ G, s.st.groups[s.loc.own]? = some G → sampleItem rdE s.st G.members.toList m
  tied : ∀ G, (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? = some G →
    WordsTied (A.rec₀ w fr).st (A.rec₀ w fr).g G m (layoutOf (A.rec₀ w fr).st G)
      (plainMany A w fr C)

/-- **What stays of `SaysOwe`** where the statement is tidy. -/
structure SaysLeft {W X : Type} (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins) (s : S₃)
    (m : Words GE) : Prop where
  rows : ∀ G, s.st.groups[s.loc.own]? = some G → AllSay rdE s.st G.rows.toList m
  samples : ∀ G, s.st.groups[s.loc.own]? = some G → sampleItem rdE s.st G.members.toList m
  tied : ∀ G, (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? = some G →
    WordsTied (A.rec₀ w fr).st (A.rec₀ w fr).g G m (layoutOf (A.rec₀ w fr).st G)
      (plainMany A w fr C)

/-- `SaysOwe` from what stays. -/
theorem owe_of_says {W X : Type} {A : ManyJob W X} {w : W} {fr : Front X} {C : TestCoins} {s : S₃}
    {m : Words GE} (hT : OnBytes.Means.Tidy s.st) (h : SaysLeft A w fr C s m) :
    SaysOwe A w fr C s m :=
  ⟨hT.inOrder, hT.kinds, h.rows, h.samples, h.tied⟩

/-- **`SaysAt` at the job's state on entry.** -/
theorem saysAt_own {W X : Type} (A : ManyJob W X) (w : W) (fr : Front X) (C : TestCoins) {s : S₃}
    {m : Words GE} (hE : enterOwn s = .ok (A.rec₀ w fr)) (h : SaysOwe A w fr C s m) :
    SaysAt A w fr C := by
  have e : A.rec₀ w fr = { st := s.st, book := s.book, roots := s.roots, g := s.loc.own
                           pass := .nothing, mask := s.loc.mask } := (Except.ok.inj hE).symm
  have hst : (A.rec₀ w fr).st = s.st := by rw [e]
  have hg : (A.rec₀ w fr).g = s.loc.own := by rw [e]
  refine saysAt_of_items A w fr C m (by rw [hst]; exact h.order) (by rw [hst]; exact h.kinds) ?_ ?_
    h.tied
  · intro i
    rw [hst, hg]
    cases hG : s.st.groups[s.loc.own]? with
    | none =>
      intro r hr
      obtain ⟨G, hG', -⟩ := rowAt_iff.1 hr
      rw [hG] at hG'
      cases hG'
    | some G => exact openSays_of_rows rdE s.st m s.loc.own G hG (h.rows G hG) i
  · intro G hG
    rw [hst]
    rw [hst, hg] at hG
    exact h.samples G hG

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.SaysOwe
#print axioms ProofFile.Honest.K12.AtFile.SaysLeft
#print axioms ProofFile.Honest.K12.AtFile.owe_of_says
#print axioms ProofFile.Honest.K12.AtFile.saysAt_own
