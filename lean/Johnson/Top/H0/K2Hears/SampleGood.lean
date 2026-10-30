-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/SampleGood.lean: the code switch: AN INVARIANT OF THE RECORD: EVERY
STORED SAMPLE ROW IS THE PROGRAM's Send.form AT SOME SEED; a yes of the kind's decision keeps it,
and makes it at the new messages.

  SampleGood St   every message of the statement that has a stored sample row has, for some list of
                  seeds, just the rows RowsAre (SentRows.lean): as many as its shape has answers,
                  number i being Send.form at seed number i with some element as its target
  sampleGood_kept  at a yes (Whole.lean's AtYes): SampleGood of the front's statement gives
                  SampleGood of the record behind
  sampleGood_congr  SampleGood hangs on a statement's codes and messages alone
  front_tables    the front that the text makes of a record has the record's codes and messages, at
                  all three sorts of place
  SampleGoodKept, sampleGood_yes  a closed proposition and its proof: a yes of decideWith sendByL8
                  keeps SampleGood, record to record
Why. The typed switch carries a kept member's OLD sample rows (sample_held_at, in
Johnson/Top/H/SwitchHeldPush.lean, a file of this project that this one does not import, reads such
a row as the library's, under the premise «a record's stored sample row is Send.form at a seed»).
That row was laid by an EARLIER sending. So the premise is an invariant along the chain.
LIMITS. K2's share alone: that the other kinds keep it, and that it holds at the chain's start (no
message: trivially), is not typed here. The seeds stand under a «there is»: which seeds is SentRows'
and SeedBehind's matter. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.Whole
import Johnson.Top.H0.K2Hears.SentRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (switchNotices sendByL8)

/-- **Every stored sample row is Send.form at some seed.** -/
def SampleGood (St : Statement) : Prop :=
  ∀ (o : Nat) (x : OnBytes.Oracle), St.oracles[o]? = some x → x.sampleRows.size ≠ 0 →
    ∃ seeds, RowsAre St.codes x.shape o seeds x.sampleRows

/-- **A yes keeps it, and makes it at the new messages.** -/
theorem sampleGood_kept {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (h : SampleGood x.st) : SampleGood s'.st := by
  intro o xo hxo hsz
  have T := A.same.trans A.tables
  have hcod : s'.st.codes = x.st.codes := T.codes.trans A.sent.codes
  have hsh := T.shape o
  have hsm := T.samples o
  rw [hxo] at hsh hsm
  simp only [Option.map_some] at hsh hsm
  rw [hcod]
  by_cases ho : o < x.st.oracles.size
  · rw [A.sent.old o ho] at hsh hsm
    obtain ⟨x0, hx0, e1⟩ := Option.map_eq_some_iff.1 hsh.symm
    obtain ⟨x1, hx1, e2⟩ := Option.map_eq_some_iff.1 hsm.symm
    rw [hx0] at hx1
    obtain rfl := Option.some.inj hx1
    rw [← e1, ← e2]
    exact h o x0 hx0 (by rw [e2]; exact hsz)
  · obtain ⟨i, rfl⟩ : ∃ i, o = x.st.oracles.size + i := ⟨o - x.st.oracles.size, by omega⟩
    obtain ⟨bits, answers, seeds, -, -, hall, hnone⟩ := sent_rows A.sentBy
    rw [A.sent.shape i] at hsh
    obtain ⟨n, hn, e1⟩ := Option.map_eq_some_iff.1 hsh.symm
    by_cases ha : n.shape.answers = 0
    · rw [hnone i n hn ha] at hsm
      have e2 := Option.some.inj hsm
      rw [e2] at hsz
      exact absurd rfl hsz
    · obtain ⟨-, rws, hr, hR⟩ := hall i n hn ha
      rw [hr] at hsm
      have e2 := Option.some.inj hsm
      rw [← e1, e2]
      exact ⟨seeds, hR⟩

/-- **The front has the record's codes and messages.** -/
theorem front_tables {p : P2} {s : S} {x : _root_.Tw.K2.Front} (h : frontAt p s = some x) :
    x.st.codes = s.st.codes ∧ x.st.oracles = s.st.oracles := by
  unfold frontAt at h
  split at h
  · unfold _root_.Tw.K2.firstFront at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · dsimp only at h
          split at h
          · cases h
          · rename_i S' g hg
            simp only [Except.toOption, Option.some.injEq] at h
            subst h
            unfold _root_.Tw.K2.newGroupG at hg
            split at hg
            · rename_i g' d hd
              cases hg
              unfold VerifiableInference.Desc.Ground.newGroupP at hd
              split at hd
              · cases hd
                exact ⟨rfl, rfl⟩
              · cases hd
            · cases hg
        · cases h
        · cases h
  · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, rfl⟩
  · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, rfl⟩
  · cases h

theorem sampleGood_congr {S S' : Statement} (hc : S'.codes = S.codes) (ho : S'.oracles = S.oracles)
    (h : SampleGood S) : SampleGood S' := by
  intro o x hx hs
  rw [hc]
  rw [ho] at hx
  exact h o x hx hs

/-- **As one closed proposition: a yes of the kind's own decision keeps the invariant, record to
record.** -/
def SampleGoodKept : Prop := ∀ p s r₁ r₂ gs s', decideWith sendByL8 p s [r₁, r₂] gs = .ok s' →
  SampleGood s.st → SampleGood s'.st

theorem sampleGood_yes : SampleGoodKept := fun p s r₁ r₂ gs s' h hg => by
  obtain ⟨x, y, S3, Y, rows, G, c, A⟩ := yes_whole p s r₁ r₂ gs s' h
  obtain ⟨e1, e2⟩ := front_tables A.front
  exact sampleGood_kept A (sampleGood_congr e1 e2 hg)

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.sampleGood_yes
#print axioms VerifiableInference.Desc.First.K2.sampleGood_kept
