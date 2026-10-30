-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontOwnGroup.lean: the own group behind the text after W's
commitment: its codes, no test begun, no member kept, one row.

  FreshOwn         a group with these codes, not begun, no kept mark set, no row
  join_fresh, joinAll_fresh   a joining keeps it
  rows_group       behind the text the own group is so, with the row (Eval) on it
  rows_w_apart     W is no message of the claim's masks

Limits.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontOwn
import Johnson.Desc.Key.Laid.RowsLaid
import Fmt.Rules6Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.K13 (St rows)
open VerifiableInference.Desc.K13.Honest (joinP_inv newGroupP_inv)

/-- A group with these codes, not begun, no kept mark set, no row. -/
structure FreshOwn (G : Group) (c z : ℕ) : Prop where
  code : G.code = c
  maskCode : G.maskCode = z
  inRun : G.inRun = false
  kept : ∀ k ∈ G.kept.toList, k = false
  rows : G.rows = #[]

/-- **A joining that keeps no main rows keeps it.** -/
theorem join_fresh {d d' : St} {g o c z : ℕ} (h : VerifiableInference.Desc.Ground.joinP d g o false = some d')
    (hf : ∀ G, d.st.groups[g]? = some G → FreshOwn G c z) :
    ∀ G, d'.st.groups[g]? = some G → FreshOwn G c z := by
  obtain ⟨G₀, hG₀, -, e⟩ := joinP_inv h
  intro G hG
  have hG' : (d.st.groups.modify g fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G₀.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G₀.members.filter (· < o)).size false })[g]? = some G := by
    rw [e] at hG
    exact hG
  rw [Array.getElem?_modify, if_pos rfl, hG₀] at hG'
  obtain rfl := Option.some.inj hG'
  have f := hf G₀ hG₀
  refine ⟨f.code, f.maskCode, f.inRun, fun k hk => ?_, f.rows⟩
  have hk' : k ∈ (G₀.kept.insertIdxIfInBounds (G₀.members.filter (· < o)).size false).toList := hk
  rw [OnBytes.Means.toList_insertIdxIfInBounds] at hk'
  by_cases c₁ : (G₀.members.filter (· < o)).size ≤ G₀.kept.toList.length
  · rcases (List.mem_insertIdx c₁).1 hk' with rfl | hm
    · rfl
    · exact f.kept k hm
  · rw [List.insertIdx_of_length_lt (by omega)] at hk'
    exact f.kept k hk'

theorem joinAll_fresh {g c z : ℕ} : ∀ (l : List ℕ) (d d' : St),
    VerifiableInference.Desc.K13.joinAll g l d = .ok d' →
    (∀ G, d.st.groups[g]? = some G → FreshOwn G c z) →
    ∀ G, d'.st.groups[g]? = some G → FreshOwn G c z
  | [], d, d', h, hf => by
    obtain rfl : d = d' := Except.ok.inj h
    exact hf
  | o :: l, d, d', h, hf => by
    simp only [VerifiableInference.Desc.K13.joinAll, VerifiableInference.Desc.K13.Law.bind_ok,
      VerifiableInference.Desc.K13.Law.there_ok] at h
    obtain ⟨d₁, h1, h2⟩ := h
    exact joinAll_fresh l d₁ d' h2 (join_fresh h1 hf)

/-- **Behind the text the own group has its codes, no test begun, no kept mark, and one row.** -/
theorem rows_group {Sh : Params.LinShape} {claim : LinClaim} {ids : Array ℕ} {d : St}
    {o : LinFirst × St} (h : rows Sh claim ids d = .ok o) (hsp : Sh.ownSplitNeeded = false) :
    ∃ (G : Group) (row : OnBytes.Row), o.2.st.groups[o.1.own]? = some G ∧
      G.code = Sh.w.code ∧ G.maskCode = Sh.ownMaskCode ∧ G.inRun = false ∧
      (∀ k ∈ G.kept.toList, k = false) ∧ G.rows = #[row] ∧ row.kind = .plain := by
  simp only [VerifiableInference.Desc.K13.Law.rows_is, VerifiableInference.Desc.K13.Law.bind_ok,
    VerifiableInference.Desc.K13.Law.there_ok, VerifiableInference.Desc.K13.Law.pure_ok] at h
  obtain ⟨w, _, b, hb, d₁, h1, d₂, h2, split, _, d₃, h3, mask, _, row, hrow, d₄, h4, rfl⟩ := h
  obtain ⟨e1, e2⟩ := newGroupP_inv hb
  have B0 : ∀ G, b.2.st.groups[b.1]? = some G → FreshOwn G Sh.w.code Sh.ownMaskCode := by
    intro G hG
    rw [e1, e2] at hG
    have hG' : (d.st.groups.push { code := Sh.w.code, maskCode := Sh.ownMaskCode })[d.st.groups.size]? =
        some G := hG
    rw [Array.getElem?_push_eq] at hG'
    obtain rfl := Option.some.inj hG'
    exact ⟨rfl, rfl, rfl, (fun k hk => by cases hk), rfl⟩
  have B1 := joinAll_fresh _ _ _ h1 B0
  have B2 := join_fresh h2 B1
  rw [if_neg (by simp [hsp])] at h3
  obtain rfl := Option.some.inj h3
  obtain ⟨G, hG, -, e4⟩ := VerifiableInference.Desc.K13.Law.addRows_one h4
  have f := B2 G hG
  refine ⟨{ G with rows := G.rows.push row }, row, ?_, f.code, f.maskCode, f.inRun, f.kept, ?_, ?_⟩
  · show d₄.st.groups[b.1]? = _
    rw [e4]
    show (d₂.st.groups.modify b.1 fun G => { G with rows := G.rows.push row })[b.1]? = _
    rw [Array.getElem?_modify, if_pos rfl, hG]
    rfl
  · show G.rows.push row = #[row]
    rw [f.rows]
    rfl
  · exact VerifiableInference.Desc.Key.LaidW.evalRow_plain _ _ _ _ _ hrow

/-- **W is no message of the claim's masks**: these joined first, and no message joins twice. -/
theorem rows_w_apart {Sh : Params.LinShape} {claim : LinClaim} {ids : Array ℕ} {d : St}
    {o : LinFirst × St} (h : rows Sh claim ids d = .ok o) :
    ∀ m ∈ claim.masks.toList, m.oracle ≠ o.1.w := by
  simp only [VerifiableInference.Desc.K13.Law.rows_is, VerifiableInference.Desc.K13.Law.bind_ok,
    VerifiableInference.Desc.K13.Law.there_ok, VerifiableInference.Desc.K13.Law.pure_ok] at h
  obtain ⟨w, _, b, hb, d₁, h1, d₂, h2, split, _, d₃, h3, mask, _, row, hrow, d₄, h4, rfl⟩ := h
  obtain ⟨e1, e2⟩ := newGroupP_inv hb
  have B0 : VerifiableInference.Desc.K13.Honest.OwnLaid d.st b.2.st b.1 fun _ => False := by
    rw [e1, e2]
    exact VerifiableInference.Desc.K13.Honest.OwnLaid.start d.st _ _
  have B1 := VerifiableInference.Desc.K13.Honest.joinAll_ownLaid _ _ _ _ B0 h1
  obtain ⟨G, hG, hnot, -⟩ := joinP_inv h2
  obtain ⟨G', hG', hiff⟩ := B1.own
  obtain rfl := Option.some.inj (hG.symm.trans hG')
  intro m hm e
  have hin : m.oracle ∈ listOfT (claim.masks.toList.map (·.oracle)) := by
    rw [listOfT_eq, Fmt.listOf_mem _ _]
    exact List.mem_map.2 ⟨m, hm, rfl⟩
  have hmem := (hiff m.oracle).2 (Or.inl hin)
  have e' : m.oracle = w := e
  rw [e'] at hmem
  have hc : G.members.contains w = true := by
    rw [Array.contains_iff_mem] 
    exact Array.mem_toList_iff.1 hmem
  rw [hc] at hnot
  cases hnot

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.rows_w_apart
#print axioms ProofFile.Honest.K12.AtFile.rows_group
