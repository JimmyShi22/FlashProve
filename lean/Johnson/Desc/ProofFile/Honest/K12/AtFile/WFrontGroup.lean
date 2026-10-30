-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontGroup.lean: the front's list of clauses on the own group
(frontL), on entry to the last chain's own test.

  OwnMembersFit    what stays named: each member's count of sample rows and its pad, and the trees of
                   the members and of the mask
  frontL_of_parts  the clauses, one by one, at any statement, group and mask
  frontL_at_own    the clauses at the own group, from OwnMembersFit, Tidy and MembersFacts at the first
                   chain's last statement, InOrder at the shared chain's, and two facts on the mask's
                   message: that it is there, and that it is not spent

Limits.
- OwnMembersFit is a premise here.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontCame
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontMembers
import Johnson.Desc.Tidy.Third

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open OnBytes.Means (Tidy InOrder SampledMembers)
open VerifiableInference.Desc.Ground (ok on)
open VerifiableInference.Desc.K12 (T12 frontL)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut batchLinearConstraintsSecondPart start₃E numbersOk)
open VerifiableInference.Desc.Third.Law (laid_k14Second start₃E_inv start₃_inv firstOutFrom_inv
  k14Second_tidy)

/-- What stays named of the front's clauses on the own group. -/
structure OwnMembersFit (S : Statement) (B : TreeBook) (G : Group) (mask : Option ℕ) : Prop where
  counts : ∀ o ∈ G.members.toList, ∀ y : OnBytes.Oracle, S.oracles[o]? = some y →
    y.sampleRows.size = y.shape.answers
  pads : ∀ o ∈ G.members.toList, ∀ y : OnBytes.Oracle, S.oracles[o]? = some y →
    ∃ l, VerifiableInference.Desc.Own.padMade S.codes y.shape = some l ∧
      y.pad = l.map fun p => (p.part, p.index)
  trees : ∀ o ∈ G.members.toList ++ mask.toList, ∃ (q : ℕ × ℕ) (T : OnBytes.Tree),
    B.place[o]? = some q ∧ B.trees[q.1]? = some T ∧ (T.oneList = false ∨ T.lists = 0)

/-- **The front's clauses, clause by clause**, at a group and a mask that are not under test. -/
theorem frontL_of_parts {T : Statement} {B : TreeBook} {g id : ℕ} {G : Group} {x : OnBytes.Oracle}
    (hG : T.groups[g]? = some G) (hr : G.inRun = false) (hne : G.members.isEmpty = false)
    (hk : G.kept.size = G.members.size) (hrise : G.members.toList.Pairwise (· < ·))
    (hs : ∀ o ∈ G.members.toList, ∃ y : OnBytes.Oracle, T.oracles[o]? = some y ∧ y.sampled = true)
    (hknow : ∀ o ∈ G.members.toList, ∀ y : OnBytes.Oracle, T.oracles[o]? = some y → g ∈ y.groups)
    (hkind : ∀ row ∈ G.rows.toList, row.kind ≠ .sample) (hfit : OwnMembersFit T B G (some id))
    (hx : T.oracles[id]? = some x) (m1 : x.sampled = false) (m2 : x.shape.answers = 0)
    (m3 : x.spentAsMask = false) (m4 : id ∉ G.members.toList)
    (hstep : T.oracles.size = B.place.size) : ok (frontL T B g (some id)) = true := by
  simp only [ok, frontL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, hG, hx, on,
    Option.map_some, Option.getD_some, Option.isSome_some, Option.bind_some, Option.toList_some]
  have allMem : ∀ (f : ℕ → Bool), (∀ o ∈ G.members.toList, f o = true) → G.members.all f = true :=
    fun f h => Array.all_eq_true_iff_forall_mem.2 fun o ho => h o (Array.mem_toList_iff.2 ho)
  refine ⟨trivial, by simp [hr], by simp [hne], by simp [hk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp,
    by simp [m1], by simp [m2], by simp [m3], ?_, by simp [hstep], ?_, ?_⟩
  · refine List.all_eq_true.2 fun i hi => ?_
    have hi' : i + 1 < G.members.size := by
      have := List.mem_range.1 hi
      omega
    have hp := List.pairwise_iff_getElem.1 hrise i (i + 1) (by simpa using (by omega))
      (by simpa using hi') (by omega)
    simp only [decide_eq_true_eq]
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hi']
    simpa using hp
  · refine allMem _ fun o ho => ?_
    obtain ⟨y, hy, -⟩ := hs o ho
    simp [hy]
  · refine allMem _ fun o ho => ?_
    obtain ⟨y, hy, hm⟩ := hs o ho
    simp [hy, hm]
  · refine allMem _ fun o ho => ?_
    obtain ⟨y, hy, -⟩ := hs o ho
    simp [hy, hknow o ho y hy]
  · refine allMem _ fun o ho => ?_
    obtain ⟨y, hy, -⟩ := hs o ho
    simp [hy, hfit.counts o ho y hy]
  · refine allMem _ fun o ho => ?_
    obtain ⟨y, hy, -⟩ := hs o ho
    obtain ⟨l, hl, e⟩ := hfit.pads o ho y hy
    simp [hy, hl, e]
  · refine Array.all_eq_true_iff_forall_mem.2 fun row hrow => ?_
    have := hkind row (Array.mem_toList_iff.2 hrow)
    simpa using this
  · have : id ∉ G.members := fun hm => m4 (Array.mem_toList_iff.2 hm)
    simpa using this
  · refine List.all_eq_true.2 fun o ho => ?_
    obtain ⟨q, T', hq, hT', -⟩ := hfit.trees o ho
    simp [hq, hT']
  · refine List.all_eq_true.2 fun o ho => ?_
    obtain ⟨q, T', hq, hT', hl⟩ := hfit.trees o ho
    rcases hl with hl | hl <;> simp [hq, hT', hl]

/-- **The front's clauses at the own group.** -/
theorem frontL_at_own {Cl : Type} (p : P₁₄) {codes : Codes} {S : Params.LinShape} {st₁ : Statement}
    {book₁ : TreeBook} {roots₁ w₁ own₁ : ℕ} {pile₁ : List TensorRow} {o : SharedOut} {s₀ s : S₃}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {t : T12} {id : ℕ}
    (h₀ : start₃E codes S st₁ book₁ roots₁ w₁ own₁ (some id) pile₁ o = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s) (h₂ : enterOwn s = .ok t)
    (hT : Tidy st₁) (hI : InOrder o.st) (hF : MembersFacts st₁) {x : OnBytes.Oracle}
    (hx : st₁.oracles[id]? = some x) (m3 : x.spentAsMask = false)
    (hfit : ∀ G, t.st.groups[t.g]? = some G → OwnMembersFit t.st t.book G t.mask) :
    ok (frontL t.st t.book t.g t.mask) = true := by
  obtain ⟨f, hf, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h₀
  obtain ⟨-, ef, -, eo, em, -⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  obtain ⟨-, -, e0⟩ := start₃_inv _ _ _ _ hst
  have es₀ : s₀.st = st₁ := by rw [e0]; exact ef
  obtain ⟨g₀, hb⟩ := VerifiableInference.Desc.Third.Law.start₃E_border _ _ _ _ _ _ _ _ _ _ _ h₀
  have hun := mask_of_start h₀ hx
  obtain ⟨b, y, G, dot, L⟩ := laid_k14Second p s₀ s rs gs h₁
  have hTs : Tidy s.st := k14Second_tidy p s₀ s rs gs h₁
    (fun z hz => by
      rw [hb] at hz
      rw [← Option.some.inj hz]
      exact hI) (by rw [es₀]; exact hT)
  have hFs : MembersFacts s.st := membersFacts_second p s₀ s rs gs h₁ (by rw [es₀]; exact hF)
  have et : t = { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
                  mask := s.loc.mask } := (Except.ok.inj h₂).symm
  have hl : s.loc.own = s₀.loc.own := by rw [L.loc]
  have hm : s.loc.mask = some id := by
    rw [L.loc]
    show s₀.loc.mask = _
    rw [e0]
    exact em
  have hlt : id < s₀.st.oracles.size := by
    rw [es₀]
    exact (Array.getElem?_eq_some_iff.1 hx).1
  have hxs : s.st.oracles[id]? = some x := by
    rw [L.old id hlt, es₀]
    exact hx
  have hGs := L.group'
  rw [← hl] at hGs
  subst et
  have hfit' := hfit _ hGs
  simp only [hm] at hfit'
  have hpos : (G.members.filter (· < s₀.st.oracles.size)).size ≤ G.members.toList.length := by
    rw [Array.length_toList]
    exact Array.size_filter_le
  have hins : ∀ a, a ∈ (G.members.insertIdxIfInBounds
      (G.members.filter (· < s₀.st.oracles.size)).size s₀.st.oracles.size).toList ↔
      a = s₀.st.oracles.size ∨ a ∈ G.members.toList := by
    intro a
    rw [OnBytes.Means.toList_insertIdxIfInBounds, List.mem_insertIdx hpos]
  have hgood := hTs.inOrder.groups _ _ hGs
  obtain ⟨hrise, hknow⟩ := hFs.2 _ _ hGs
  have hnot : id ∉ G.members.toList := by
    intro hmem
    obtain ⟨x', hx'', hs⟩ := hF.1 _ G (by rw [← es₀]; exact L.group) id hmem
    obtain rfl := Option.some.inj (hx''.symm.trans hx)
    rw [hun.1] at hs
    cases hs
  show ok (frontL s.st s.book s.loc.own s.loc.mask) = true
  rw [hm]
  refine frontL_of_parts hGs L.notBegun ?_ hgood.marks hrise (hFs.1 _ _ hGs) hknow
    (fun row hrow => hTs.kinds _ _ hGs row hrow) hfit' hxs hun.1 hun.2 m3 ?_ ?_
  · by_contra hc
    have hm₀ : s₀.st.oracles.size ∈ (G.members.insertIdxIfInBounds
        (G.members.filter (· < s₀.st.oracles.size)).size s₀.st.oracles.size).toList :=
      (hins _).2 (Or.inl rfl)
    have he : (G.members.insertIdxIfInBounds
        (G.members.filter (· < s₀.st.oracles.size)).size s₀.st.oracles.size).isEmpty = true := by
      simpa using hc
    rw [Array.isEmpty_iff] at he
    rw [he] at hm₀
    cases hm₀
  · intro hmem
    rcases (hins id).1 hmem with e | hm'
    · omega
    · exact hnot hm'
  · rw [L.size, L.places, L.step]

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.frontL_of_parts
#print axioms ProofFile.Honest.K12.AtFile.frontL_at_own
