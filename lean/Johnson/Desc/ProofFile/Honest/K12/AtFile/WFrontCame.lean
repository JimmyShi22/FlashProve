-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontCame.lean: the clause "the mask has come" of the door's
test, at the shape on entry to the last chain's own test, from the start's yes, the block's yes and
four facts on the mask's message at the first chain's last statement.

  cameB_at_own   the statement: the mask on entry is id, and cameB says yes there

What it pays by itself: the mask's message is not sampled and counts no answer (the start's numbersOk),
and it is no member of the own group (a member is sampled; the new member is a new number).
Premises on the message x at number id: its shape's three numbers, and that it is not spent. Premise on
the statement: every member is sampled.

Limits.
- These four facts are not shown here at any chain's end.
- Nothing on the rest of the door's test. Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontAsks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open OnBytes.Means (SampledMembers)
open VerifiableInference.Desc.Ground.Sh (stSh grpSh orcSh orc_get grp_get)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut batchLinearConstraintsSecondPart start₃E numbersOk)
open VerifiableInference.Desc.Third.Law (laid_k14Second start₃E_inv start₃_inv firstOutFrom_inv)
open ProofFile.Honest.Sh (cameB testSh)

/-- What the start tests of the mask's message. -/
theorem mask_of_start {codes : Codes} {S : Params.LinShape} {st₁ : Statement} {book₁ : TreeBook}
    {roots₁ w₁ own₁ : ℕ} {pile₁ : List TensorRow} {o : SharedOut} {s₀ : S₃} {id : ℕ}
    (h₀ : start₃E codes S st₁ book₁ roots₁ w₁ own₁ (some id) pile₁ o = .ok s₀)
    {x : OnBytes.Oracle} (hx : st₁.oracles[id]? = some x) :
    x.sampled = false ∧ x.shape.answers = 0 := by
  obtain ⟨f, hf, -⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h₀
  obtain ⟨hn, ef, -, -, em, -⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  unfold numbersOk at hn
  rw [em, ef] at hn
  split at hn
  · simp only [Bool.and_eq_true] at hn
    have h2 : (match st₁.oracles[id]? with
      | some y => !y.sampled && y.shape.answers == 0
      | none => false) = true := hn.2
    rw [hx] at h2
    simpa using h2
  · cases hn

/-- **The mask has come**, on the shape on entry to the own test. -/
theorem cameB_at_own {Cl : Type} (p : P₁₄) {codes : Codes} {S : Params.LinShape} {st₁ : Statement}
    {book₁ : TreeBook} {roots₁ w₁ own₁ : ℕ} {pile₁ : List TensorRow} {o : SharedOut} {s₀ s : S₃}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {t : T12} {id : ℕ}
    (h₀ : start₃E codes S st₁ book₁ roots₁ w₁ own₁ (some id) pile₁ o = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s) (h₂ : enterOwn s = .ok t)
    (hM : SampledMembers st₁) {cur : Fmt.M1.Stage} {i : ℕ × ℕ} {x : OnBytes.Oracle}
    (hx : st₁.oracles[id]? = some x) (m0 : x.shape.mainRows = 0)
    (m1 : x.shape.maskRows = 2 ^ cur.h) (m2 : x.shape.maskCode = i.2)
    (m3 : x.spentAsMask = false) :
    t.mask = some id ∧ cameB cur (testSh t).core t.g i id = true := by
  obtain ⟨f, hf, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h₀
  obtain ⟨-, ef, -, eo, em, -⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  obtain ⟨-, -, e0⟩ := start₃_inv _ _ _ _ hst
  have es₀ : s₀.st = st₁ := by rw [e0]; exact ef
  have hun := mask_of_start h₀ hx
  obtain ⟨b, y, G, dot, L⟩ := laid_k14Second p s₀ s rs gs h₁
  have hlt : id < s₀.st.oracles.size := by
    rw [es₀]
    exact (Array.getElem?_eq_some_iff.1 hx).1
  have hx' : s.st.oracles[id]? = some x := by
    rw [L.old id hlt, es₀]
    exact hx
  have et : t = { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
                  mask := s.loc.mask } := (Except.ok.inj h₂).symm
  have hl : s.loc.own = s₀.loc.own := by rw [L.loc]
  have hnot : id ∉ G.members.toList := by
    intro hm
    obtain ⟨x', hx'', hs⟩ := hM _ G (by rw [← es₀]; exact L.group) id hm
    obtain rfl := Option.some.inj (hx''.symm.trans hx)
    rw [hun.1] at hs
    cases hs
  have hpos : (G.members.filter (· < s₀.st.oracles.size)).size ≤ G.members.toList.length := by
    rw [Array.length_toList]
    exact Array.size_filter_le
  have hnot' : id ∉ (G.members.insertIdxIfInBounds
      (G.members.filter (· < s₀.st.oracles.size)).size s₀.st.oracles.size).toList := by
    rw [OnBytes.Means.toList_insertIdxIfInBounds]
    intro hm
    rcases (List.mem_insertIdx hpos).1 hm with e | hm'
    · omega
    · exact hnot hm'
  have gg : (testSh t).core.st.groups[t.g]? = some (grpSh { G with
      members := G.members.insertIdxIfInBounds (G.members.filter (· < s₀.st.oracles.size)).size
        s₀.st.oracles.size
      kept := G.kept.insertIdxIfInBounds (G.members.filter (· < s₀.st.oracles.size)).size false
      rows := G.rows.push dot }) := by
    rw [et]
    show (stSh s.st).groups[s.loc.own]? = _
    rw [grp_get, hl, L.group']
    rfl
  have oo : (testSh t).core.st.oracles[id]? = some (orcSh x) := by
    rw [et]
    show (stSh s.st).oracles[id]? = _
    rw [orc_get, hx']
    rfl
  refine ⟨by
    rw [et, L.loc]
    show s₀.loc.mask = _
    rw [e0]
    exact em, ?_⟩
  unfold cameB
  rw [gg, oo]
  have hc : (grpSh { G with
      members := G.members.insertIdxIfInBounds (G.members.filter (· < s₀.st.oracles.size)).size
        s₀.st.oracles.size
      kept := G.kept.insertIdxIfInBounds (G.members.filter (· < s₀.st.oracles.size)).size false
      rows := G.rows.push dot }).members.contains id = false := by
    show (G.members.insertIdxIfInBounds (G.members.filter (· < s₀.st.oracles.size)).size
      s₀.st.oracles.size).toList.contains id = false
    simpa using hnot'
  simp only [VerifiableInference.Desc.Ground.has, Option.map_some, Option.getD_some, Option.any_some,
    orcSh, hc, m0, m1, m2, m3, hun.1, hun.2]
  simp

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.cameB_at_own
