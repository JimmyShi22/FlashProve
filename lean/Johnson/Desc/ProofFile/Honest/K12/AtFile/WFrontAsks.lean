-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontAsks.lean: the three tests that read the rows, on entry
to the last chain's own test, from what the two earlier chains hand over, the start's yes and the yes
of the block "K14, second part".

  plainRow_renamed     a plain row under another number is plain
  membersPlain_at_own  the members of the own group behind the block: those that were there, and Omega,
                       whose sample rows are copied from the shared chain's end
  denseRows_at_own     every row that the test takes in is dense
  rows_at_own          the clauses tidy, dense and claims of a stand (OwnStand, WStand.lean)

Premises of rows_at_own, each by name.
- hT, hI: the first chain's last statement is tidy, the shared chain's last statement is in order.
- hA, hO: the sentences OpenRowsPass and OpenOrd at the first chain's last statement.
- hM, hΩ: the sample rows of the own group's members at the first chain's last statement, and of Omega
  at the shared chain's end, are plain.
WFrontEnd.lean pays them from the two chains' folds.

Limits.
- These are statements on records, not on a run of a prover.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontClaims
import Johnson.Desc.ProofFile.Honest.K12.AtFile.DenseAtOwn
import Johnson.Desc.Third.Law.Laid
import Johnson.Desc.Tidy.Third

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open OnBytes.Slice.ProxRun (DenseRow)
open OnBytes.Means (Tidy InOrder)
open VerifiableInference.Desc.Ground.Sh (stTidyB)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut batchLinearConstraintsSecondPart start₃E)
open VerifiableInference.Desc.Third.Law (laid_k14Second start₃E_st k14Second_tidy start₃E_border)
open Johnson.AtFull.Shape (OpenOrd)
open ProofFile.Honest.Sh (claimsB)

/-- A plain row under another number is plain. -/
theorem plainRow_renamed {r : OnBytes.Row} (h : PlainRow r) (o : ℕ) : PlainRow (r.renamed o) := by
  refine ⟨fun t ht => ?_, fun f hf => ?_⟩
  · simp only [Row.renamed, Array.toList_map, List.mem_map] at ht
    obtain ⟨t', ht', rfl⟩ := ht
    exact h.1 t' ht'
  · simp only [Row.renamed, Array.toList_map, List.mem_map] at hf
    obtain ⟨f', hf', rfl⟩ := hf
    exact h.2 f' hf'

/-- **The sample rows of the own group's members behind the block.** -/
theorem membersPlain_at_own {Cl : Type} (p : P₁₄) {s₀ s : S₃} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s)
    (hM : ∀ G, s₀.st.groups[s₀.loc.own]? = some G → ∀ o ∈ G.members.toList,
      ∀ x : OnBytes.Oracle, s₀.st.oracles[o]? = some x → ∀ r ∈ x.sampleRows.toList, PlainRow r)
    (hΩ : ∀ b y, s₀.loc.border = some b → b.shared.st.oracles[b.shared.omega]? = some y →
      ∀ r ∈ y.sampleRows.toList, PlainRow r) {G' : Group}
    (hG : s.st.groups[s₀.loc.own]? = some G') :
    ∀ o ∈ G'.members.toList, ∀ x : OnBytes.Oracle, s.st.oracles[o]? = some x →
      ∀ r ∈ x.sampleRows.toList, PlainRow r := by
  obtain ⟨b, y, G, dot, L⟩ := laid_k14Second p s₀ s rs gs h₁
  rw [L.group'] at hG
  obtain rfl := Option.some.inj hG
  intro o ho x hx r hr
  have hpos : (G.members.filter (· < s₀.st.oracles.size)).size ≤ G.members.toList.length := by
    rw [Array.length_toList]
    exact Array.size_filter_le
  have ho' : o ∈ (G.members.insertIdxIfInBounds
      (G.members.filter (· < s₀.st.oracles.size)).size s₀.st.oracles.size).toList := ho
  rw [OnBytes.Means.toList_insertIdxIfInBounds] at ho'
  by_cases e : o = s₀.st.oracles.size
  · subst e
    rw [L.copy] at hx
    obtain rfl := Option.some.inj hx
    simp only [Array.toList_map, List.mem_map] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    exact plainRow_renamed (hΩ b y L.border L.there r' hr') _
  · rcases (List.mem_insertIdx hpos).1 ho' with e' | hm
    · exact absurd e' e
    · have hlt : o < s₀.st.oracles.size := by
        obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.1 hx
        rw [L.size] at hlt
        omega
      rw [L.old o hlt] at hx
      exact hM G L.group o hm x hx r hr

/-- **Every row that the own test takes in is dense.** -/
theorem denseRows_at_own {Cl : Type} (p : P₁₄) {s₀ s : S₃} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {t : T12}
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s) (h₂ : enterOwn s = .ok t)
    (hO : OpenOrd s₀.st)
    (hM : ∀ G, s₀.st.groups[s₀.loc.own]? = some G → ∀ o ∈ G.members.toList,
      ∀ x : OnBytes.Oracle, s₀.st.oracles[o]? = some x → ∀ r ∈ x.sampleRows.toList, PlainRow r)
    (hΩ : ∀ b y, s₀.loc.border = some b → b.shared.st.oracles[b.shared.omega]? = some y →
      ∀ r ∈ y.sampleRows.toList, PlainRow r) :
    ∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, DenseRow r := by
  obtain ⟨b, y, G₀, dot, L⟩ := laid_k14Second p s₀ s rs gs h₁
  have et : t = { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
                  mask := s.loc.mask } := (Except.ok.inj h₂).symm
  subst et
  intro G hG
  have hl : s.loc.own = s₀.loc.own := by rw [L.loc]
  have hG' : s.st.groups[s₀.loc.own]? = some G := by
    rw [← hl]
    exact hG
  exact dense_of_members (ord_second p s₀ s rs gs h₁ hO) hG
    (membersPlain_at_own p h₁ hM hΩ hG')

/-- **The three tests that read the rows, on entry to the last chain's own test.** The statement is
tidy, the rows taken in are dense, the open rows pass: the clauses tidy, dense and claims of a stand. -/
theorem rows_at_own {Cl : Type} (p : P₁₄) {codes : Codes} {S : Params.LinShape} {st₁ : Statement}
    {book₁ : TreeBook} {roots₁ w₁ own₁ : ℕ} {mask₁ : Option ℕ} {pile₁ : List TensorRow}
    {o : SharedOut} {s₀ s : S₃} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {t : T12}
    (h₀ : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s) (h₂ : enterOwn s = .ok t)
    (hT : Tidy st₁) (hI : InOrder o.st) (hA : OpenRowsPass st₁) (hO : OpenOrd st₁)
    (hM : ∀ G, s₀.st.groups[s₀.loc.own]? = some G → ∀ m ∈ G.members.toList,
      ∀ x : OnBytes.Oracle, s₀.st.oracles[m]? = some x → ∀ r ∈ x.sampleRows.toList, PlainRow r)
    (hΩ : ∀ y, o.st.oracles[o.omega]? = some y → ∀ r ∈ y.sampleRows.toList, PlainRow r) :
    stTidyB t.st = true ∧
      (∀ G, t.st.groups[t.g]? = some G → ∀ r ∈ (runRows t.st G).toList, DenseRow r) ∧
      claimsB t = true := by
  have e₀ : s₀.st = st₁ := start₃E_st _ _ _ _ _ _ _ _ _ _ _ h₀
  obtain ⟨g, hb⟩ := start₃E_border _ _ _ _ _ _ _ _ _ _ _ h₀
  have et : t = { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
                  mask := s.loc.mask } := (Except.ok.inj h₂).symm
  have hTs : Tidy s.st := k14Second_tidy p s₀ s rs gs h₁
    (fun x hx => by
      rw [hb] at hx
      rw [← Option.some.inj hx]
      exact hI) (by rw [e₀]; exact hT)
  refine ⟨?_, ?_, ?_⟩
  · rw [et]
    exact VerifiableInference.Desc.Ground.Sh.tidy_mark hTs
  · exact denseRows_at_own p h₁ h₂ (by rw [e₀]; exact hO) hM fun b y hb' hy => by
      rw [hb] at hb'
      obtain rfl := Option.some.inj hb'
      exact hΩ y hy
  · exact claimsB_at_own p h₁ h₂ (by rw [e₀]; exact hA)

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.plainRow_renamed
#print axioms ProofFile.Honest.K12.AtFile.membersPlain_at_own
#print axioms ProofFile.Honest.K12.AtFile.denseRows_at_own
#print axioms ProofFile.Honest.K12.AtFile.rows_at_own
