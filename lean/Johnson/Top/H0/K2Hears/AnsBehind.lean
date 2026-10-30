-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/AnsBehind.lean: the code switch: THE TARGET OF THE SAMPLE ROW THAT
THE RECORD BEHIND HOLDS FOR NEW MESSAGE NUMBER i IS ROUND 2's ITEM NUMBER i, AN ANSWER, READ.

SeedBehind.lean has the rows' coefficients (formsAt); here their targets (ansAt).
  answers_at   what the ground's answersOf reads at number i is the round's item number i, an answer
  ans_behind   at a yes of the kind's decision (Whole.lean's AtYes), if the sending's first N
               notices have one answer each: for i < N: round 2's item number i is an answer x, and
               ansAt at the record BEHIND, at the message n0 + i, is the constant readE (E.ofTriple
               x)
By SentTargets.lean's sent_targets, SentRows.lean's sent_rows (there is a row number 0) and the
stored rows' staying.
LIMITS. One answer a message, and only for a first stretch of the notices all of which are sampled.
No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.SeedBehind
import Johnson.Top.H0.K2Hears.SentTargets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model OnBytes.Slice Desc.Plain
open _root_.Tw.K2 (switchNotices sendByL8)

theorem answers_at {r : Fmt.RoundView} {an : List E} (h : answersOf r = some an) (i : Nat) (e : E)
    (hi : an[i]? = some e) : ∃ x, r.vals[i]? = some (.answer x) ∧ e = E.ofTriple x := by
  unfold answersOf at h
  obtain ⟨k1, k2⟩ := OnBytes.Slice.list_mapM_inv _ _ _ h
  have hlt : i < r.vals.length := by
    rw [← k1]
    exact (List.getElem?_eq_some_iff.1 hi).1
  have g := k2 i hlt
  rw [hi] at g
  rw [List.getElem?_eq_getElem hlt]
  cases hv : r.vals[i] with
  | answer x =>
    rw [hv] at g
    exact ⟨x, rfl, (Option.some.inj g).symm⟩
  | _ =>
    rw [hv] at g
    cases g

/-- **The record behind holds round 2's answers as the stored rows' targets.** -/
theorem ans_behind {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (N : Nat)
    (hN : ∀ i, i < N → ∃ n, (switchNotices x.T x.others)[i]? = some n ∧ n.shape.answers = 1)
    (i : Nat) (hi : i < N) :
    ∃ t, r₂.vals[i]? = some (.answer t) ∧
      ansAt s'.st (x.st.oracles.size + i) = some fun _ => readE (E.ofTriple t) := by
  obtain ⟨need, an, han, hall⟩ := sent_targets A.sentBy N hN
  obtain ⟨rws, hr, ht⟩ := hall i hi
  obtain ⟨n, hn, h1⟩ := hN i hi
  obtain ⟨bits, answers, seeds, _, _, hrows, _⟩ := sent_rows A.sentBy
  obtain ⟨-, rws', hr', hsz, -⟩ := hrows i n hn (by omega)
  rw [hr] at hr'
  obtain rfl := Option.some.inj hr'
  have h0 : 0 < rws.size := by omega
  rw [Array.getElem?_eq_getElem h0] at ht
  obtain ⟨t, hv, he⟩ := answers_at han i rws[0].target ht.symm
  have hv' : r₂.vals[i]? = some (.answer t) := by
    have hv2 : (r₂.vals.take need)[i]? = some (.answer t) := hv
    by_cases hin : i < need
    · rw [List.getElem?_take_of_lt hin] at hv2
      exact hv2
    · rw [List.getElem?_take_eq_none (by omega)] at hv2
      cases hv2
  refine ⟨t, hv', ?_⟩
  have hst : (s'.st.oracles[x.st.oracles.size + i]?).map (·.sampleRows) = some rws :=
    (A.tables.samples _).trans ((A.same.samples _).trans hr)
  obtain ⟨xo, hxo, hxr⟩ := Option.map_eq_some_iff.1 hst
  unfold ansAt
  rw [hxo]
  simp only [Option.bind_some]
  rw [hxr, Array.getElem?_eq_getElem h0]
  simp only [Option.map_some]
  rw [he]

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.ans_behind
