-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnSamples.lean: the second premise of `say_at_entry` behind the last chain's first member: the members' sample rows hold of the
chain's words: those of older members as they did in front, those of Omega's copy as Omega's held through the shared chain's end.

  `names_of_rowOn`: a row on one message names it alone.
  `samples_behind`.

What stays open. h1, h2: the items at the start: srow 0, srow 2 of the first chain, and the shared chain's sample sentence on Omega.
Nothing on soundness, completeness, hiding or binding.
-/
import Johnson.Desc.Third.Law.RowsOfEarlierMessages
import Johnson.Desc.Third.Law.Renamed
import Johnson.Desc.Key.RowsCarry
import E2E.KeyLastExchangeW
import E2E.KeyLastWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Means
open OnBytes.Slice (GE rdE)
open VerifiableInference.Desc.Third (S₃ P₁₄ Border)
open VerifiableInference.Desc.Third.Law (old_says says_renamed tableSize_same)
open VerifiableInference.Desc.Later (Carries)

/-- **A row on one message names it alone.** -/
theorem names_of_rowOn {S : Statement} {o : Nat} {r : OnBytes.Row} (h : RowOn S o r) : ∀ z ∈ r.oracles, z = o := by
  intro z hz
  have hin : RowIn S ({ code := 0, members := #[o] } : Group) r := h.isIn (by simp)
  have hm := VerifiableInference.Desc.Key.rowIn_names_members hin z hz
  simpa using hm

/-- **Behind the member: the sample rows.** ms: the older members. -/
theorem samples_behind (p : P₁₄) (s s' : S₃) (h : VerifiableInference.Desc.Third.Law.Says p s s')
    (hk : Carries s.st s'.st) (ms : List Nat) (m mSh : Words GE) (b : Border) (hb : s.loc.border = some b)
    (hI : InOrder s.st) (hIb : InOrder b.shared.st) (hc : b.shared.st.codes = s.st.codes)
    (hm : ∀ o ∈ ms, o < s.st.oracles.size)
    (h1 : ∀ o ∈ ms, ∀ x : Oracle, s.st.oracles[o]? = some x → ∀ r ∈ x.sampleRows.toList, Says rdE s.st r m)
    (h2 : ∀ y : Oracle, b.shared.st.oracles[b.shared.omega]? = some y → ∀ r ∈ y.sampleRows.toList,
      Says rdE b.shared.st r mSh)
    (hw : ∀ pt i, m s.st.oracles.size pt i = mSh b.shared.omega pt i) :
    ∀ o, (o ∈ ms ∨ o = s.st.oracles.size) → ∀ x : Oracle, s'.st.oracles[o]? = some x →
      ∀ r ∈ x.sampleRows.toList, Says rdE s'.st r m := by
  obtain ⟨x₀, y, G, dot, hb', hl, hy, hsmp, hsz, hnew, -, -, -, -, -, hcod, hold, -, -⟩ := h
  obtain rfl : b = x₀ := Option.some.inj (hb.symm.trans hb')
  intro o ho x hx r hr
  rcases ho with ho | rfl
  · have hlt := hm o ho
    rw [hold o hlt] at hx
    refine (old_says rdE s s' hk r (fun z hz => ?_) m).2 (h1 o ho x hx r hr)
    rw [names_of_rowOn (hI.samples o x hx r hr) z hz]
    exact hlt
  · rw [hnew] at hx
    obtain rfl := Option.some.inj hx
    simp only [Array.toList_map, List.mem_map] at hr
    obtain ⟨u, hu, rfl⟩ := hr
    have hlt : b.shared.omega < b.shared.st.oracles.size := (Array.getElem?_eq_some_iff.1 hy).1
    have hn : s.st.oracles.size < s'.st.oracles.size := by omega
    exact (says_renamed rdE b.shared.st s'.st u b.shared.omega s.st.oracles.size hlt hn
      (names_of_rowOn (hIb.samples _ y hy u hu))
      (tableSize_same b.shared.st s'.st _ _ y _ hy hnew rfl (by rw [hcod, hc])) mSh m hw).2 (h2 y hy u hu)

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.names_of_rowOn
#print axioms AtPublicFiles.KeyLastChain.samples_behind
