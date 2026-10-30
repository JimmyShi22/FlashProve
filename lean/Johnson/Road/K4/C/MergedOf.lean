-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/MergedOf.lean: CONDITIONAL.

What is here. Each end value of the batched sumcheck that stands for a weight claim, as the honest
side makes it, reads as the sum that the verifier's claim of that number speaks of (`claimVal`,
Johnson/Road/FormsKeysWm.lean) in a matrix W for which OpensAt holds. W is any matrix here; the
statements that call this one lay for it the matrix of the weights in the honest side's input, each
word read into the field. Three pieces: the honest end values panel by panel (`stack_ends_are`,
Johnson/Road/K4/C/StackTrue.lean); the library's `ends_of_claims` (Johnson/Road/FormsKeysWv.lean),
read at the claims' own sums; and that every claim's number lies in one panel's stretch
(`walk_cover`, over the library's WalkL, Johnson/Road/K4/WalkV0.lean). OpensAt is what joins the
first to the second.

  `sum_zero_from`   a sum whose terms are 0 from n on equals the sum of its first n terms.
  `mem_of_forall₂`   a member of the first of two lists that are related member by member has a
      partner in the second.
  `walk_cover`   every number that a walk passes lies in one panel's stretch.
  `OpensAt SD lay W cl`   the hypothesis: the library's vector of a claim, at a place of its panel,
      is the reading of the honest table's entry; 0 beyond the panel's rows and columns. In a panel
      with the selector one claim has all rows, and a place is row times 2 ^ wy plus column; in a
      panel without it each row is a claim of its own (number v0 + i), and a place is the column
      alone.
  `merged_of_opens`   the end values read as the claims' sums.

Not shown here. THAT THE HONEST SIDE's OPEN TABLES READ AS THE LIBRARY's VECTORS OF THE VERIFIER's
WEIGHT CLAIMS, PANEL BY PANEL (OpensAt): a hypothesis HERE;
Johnson/Desc/ProofFile/Honest/K4/Law/W/OpensOfUnits.lean has it from the same law claim by claim and
PanelUnits, and Johnson/Road/K4/C/UnitsOfClaim.lean has PanelUnits from the layout; no member of it
is evaluated in Lean. It can hold only where the extents in the weights' layout are at most the
panels' (the widths of the query heads and of the feed-forward parts, the number of experts). That
the function which makes the batched sumcheck's data returns, that its end values are there, that rs
has as many entries as the plan has rounds of that sumcheck (hr), that the verifier's list of weight
claims returns at the challenges rs and the point p.rt, that the weights' layout is one that wsLayOf
returns for a model with routed experts, with the two widths d and fe of the layer sub-proof's shape
(hd, hfe): hypotheses. That all of these hold together: no example is known. Nothing on soundness,
on completeness or on any other property. No property is claimed.
-/
import Johnson.Road.K4.C.StackTrue
import Johnson.Road.K4.C.StackSidesOf
import Johnson.Road.K4.C.TriPlain
import Johnson.Road.FormsKeysWv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (SBlk ClaimEnv placePanels)
open OnBytes.Road.K4 (WalkL incV panelsT_walked panelsA_walked walk_placed)
open OnBytes.Desc.First.K4.Honest

/-- A sum whose terms are 0 from n on equals the sum of its first n terms. -/
theorem sum_zero_from {K : Type} [AddCommMonoid K] (f : ℕ → K) {n N : ℕ} (h : n ≤ N) :
    ∑ i ∈ range N, (if i < n then f i else 0) = ∑ i ∈ range n, f i := by
  rw [← Finset.sum_subset (Finset.range_mono h) (fun i _ hi => by
    rw [if_neg (by simpa using hi)])]
  exact Finset.sum_congr rfl fun i hi => by rw [if_pos (Finset.mem_range.mp hi)]

/-- A member of the first of two lists that are related member by member has a partner in the
second. -/
theorem mem_of_forall₂ {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons r t, a, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact ⟨_, List.mem_cons_self, r⟩
    · obtain ⟨b, hb, rb⟩ := mem_of_forall₂ t a h'
      exact ⟨b, List.mem_cons_of_mem _ hb, rb⟩

/-- **Every number that a walk passes lies in one panel's stretch.** -/
theorem walk_cover : ∀ (l : List SBlk) (n n' a : ℕ), WalkL n l n' → n ≤ a → a < n' →
    ∃ b ∈ l, ∃ v0, b.v0 = some v0 ∧
      ((b.tri = true ∧ a = v0) ∨ (b.tri = false ∧ ∃ i, i < b.ni ∧ a = v0 + i))
  | [], n, n', a, h, h1, h2 => by
    have e : n = n' := h
    omega
  | b :: l, n, n', a, h, h1, h2 => by
    obtain ⟨hb0, hl⟩ : (∀ v0, b.v0 = some v0 → v0 = n) ∧ WalkL (n + incV b) l n' := h
    by_cases c : a < n + incV b
    · cases hv : b.v0 with
      | none =>
        have e0 : incV b = 0 := by
          unfold incV
          rw [hv]
        omega
      | some v0 =>
        have e := hb0 v0 hv
        have hinc : incV b = if b.tri = true then 1 else b.ni := by
          unfold incV
          rw [hv]
        refine ⟨b, List.mem_cons_self, v0, hv, ?_⟩
        by_cases ht : b.tri = true
        · rw [hinc, if_pos ht] at c
          exact Or.inl ⟨ht, by omega⟩
        · rw [hinc, if_neg ht] at c
          exact Or.inr ⟨by simpa using ht, a - n, by omega, by omega⟩
    · obtain ⟨b', hb', r⟩ := walk_cover l (n + incV b) n' a hl (by omega) h2
      exact ⟨b', List.mem_cons_of_mem _ hb', r⟩

/-- **The honest side's open tables read as the library's vectors of the claims, panel by panel.**
This defines a hypothesis; the definition claims nothing. -/
def OpensAt (SD : StackData) (lay : WsLay) (W : Wm Cb.Gl.E) (cl : List WsClaim) : Prop :=
  ∀ b ∈ SD.bl.toList, ∀ v0, b.v0 = some v0 →
    (b.tri = true → ∀ i, i < 2 ^ (b.w - b.wy) → ∀ yv, yv < 2 ^ b.wy →
      wvOf Reading.gl lay W cl v0 (i * 2 ^ b.wy + yv) =
        if i < b.ni then
          (if yv < b.ny then Reading.gl.val (at2 (SD.F.getD v0 #[]) (SD.S.kkOf v0) i yv) else 0)
        else 0) ∧
    (b.tri = false → ∀ i, i < b.ni → ∀ yv, yv < 2 ^ b.wy →
      wvOf Reading.gl lay W cl (v0 + i) yv =
        if yv < b.ny then
          Reading.gl.val (at2 (SD.F.getD (v0 + i) #[]) (SD.S.kkOf (v0 + i)) 0 yv)
        else 0)

/-- **THE END VALUES THAT STAND FOR THE WEIGHT CLAIMS READ AS THE CLAIMS' SUMS.** CONDITIONAL: on
every hypothesis named. -/
theorem merged_of_opens {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) {rs : Array E} (hr : rs.size = Q.hp.lamS)
    {l : List E} (he : SD.endsAt rs = some l) {cl : List WsClaim}
    (hcl : ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).weightClaims SD.S.TS = some cl)
    {s : WsShape} {lk : ℕ} (hl : wsLayOf s true lk = .ok Q.P.wsLay) (hd : s.d = SD.S.v.y.h.d)
    (hfe : s.fe = SD.S.v.y.h.fe) (W : Wm Cb.Gl.E) (hO : OpensAt SD Q.P.wsLay W cl) :
    ∀ a x, cl[a]? = some x →
      valsOf Reading.gl (l.toArray.extract (2 + SD.nVirt) l.toArray.size) a =
        claimVal Reading.gl Q.P.wsLay W x := by
  obtain ⟨pans, hp, ebl, hnext⟩ := stack_panels_at h
  have hS := (stack_open h).1
  have hQ : SD.S.Q = Q := (sides_fields hS).1
  obtain ⟨_, _, _, cv, cw⟩ := sides_claims hS
  have hN : pans.nextV = SD.S.opens.size := by simpa using hnext
  have hv : (sidesEnv SD.S shownT).v = ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).v :=
    cv.symm
  have hlen := (claims_of_panels _ _ hv SD.S.TS hp hcl).1
  have EC := ends_of_claims Reading.gl _ _ hv SD.S.TS hp hcl
    (s := s) (lk := lk) (by show wsLayOf s true lk = .ok SD.S.ce.wsLay; rw [cw]; exact hl)
    (by show s.d = SD.S.ce.v.y.h.d; rw [cv]; exact hd)
    (by show s.fe = SD.S.ce.v.y.h.fe; rw [cv]; exact hfe) W
    (vv := fun a => ((cl[a]?).map (claimVal Reading.gl SD.S.ce.wsLay W)).getD 0)
    (fun a x hx => by
      show ((cl[a]?).map (claimVal Reading.gl SD.S.ce.wsLay W)).getD 0 = _
      rw [hx]
      rfl)
  have EA := stack_ends_are h he
  have PF := stack_panelsFit h
  have hW : WalkL 0 SD.bl.toList SD.S.opens.size := by
    rw [ebl, ← hN]
    exact walk_placed (placed_f2 pans.bl) (panelsT_walked hp (panelsA_walked rfl))
  intro a x hx
  have ha : a < SD.S.opens.size := by
    rw [← hN, hlen]
    exact (List.getElem?_eq_some_iff.mp hx).1
  obtain ⟨b, hb, v0, h0, hc⟩ := walk_cover _ 0 _ a hW (Nat.zero_le _) ha
  obtain ⟨b₀, hb₀, o, rfl⟩ := mem_of_forall₂ (placed_f2 pans.bl) b (by rw [← ebl]; exact hb)
  have Fb := PF.each _ hb
  rw [hQ] at Fb
  have hwl : b₀.w ≤ rs.size := by
    rw [hr]
    exact (Nat.pow_le_pow_iff_right (by decide)).mp (Nat.le_trans (Nat.le_add_left _ _) Fb.top)
  have hxv : claimVal Reading.gl Q.P.wsLay W x =
      ((cl[a]?).map (claimVal Reading.gl SD.S.ce.wsLay W)).getD 0 := by
    rw [hx, cw]
    rfl
  rw [hxv]
  have f1 : b₀.wy ≤ b₀.w := Fb.wy_le
  have f2 : b₀.ny ≤ 2 ^ b₀.wy := Fb.ny_le
  have f3 : b₀.ni ≤ 2 ^ (b₀.w - b₀.wy) := Fb.ni_le
  rcases hc with ⟨ht, rfl⟩ | ⟨ht, i, hi, rfl⟩
  · refine ((EA _ hb).tv ht a h0).trans (Eq.trans ?_ ((EC b₀ hb₀).1 a ht h0).symm)
    unfold gsum eiK eyK
    dsimp only
    rw [← sum_zero_from _ f3]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    by_cases ci : i < b₀.ni
    · rw [if_pos ci, Finset.mul_sum, ← sum_zero_from _ f2]
      refine Finset.sum_congr rfl fun yv hy => ?_
      have hy' := Finset.mem_range.mp hy
      have q := (hO _ hb a h0).1 ht i hi' yv hy'
      dsimp only at q
      rw [cw, q, if_pos ci]
      by_cases cy : yv < b₀.ny
      · rw [if_pos cy, if_pos cy, eqLow_value Reading.gl rs hwl hi',
          eqLow_value Reading.gl rs (Nat.le_trans f1 hwl) (by rw [Nat.sub_zero]; exact hy')]
        ring
      · rw [if_neg cy, if_neg cy, mul_zero]
    · rw [if_neg ci]
      refine (Finset.sum_eq_zero fun yv hy => ?_).symm
      have q := (hO _ hb a h0).1 ht i hi' yv (Finset.mem_range.mp hy)
      dsimp only at q
      rw [cw, q, if_neg ci, mul_zero]
  · refine ((EA _ hb).pv ht v0 h0 i hi).trans (Eq.trans ?_ ((EC b₀ hb₀).2 v0 i ht h0 hi).symm)
    unfold eyK
    dsimp only
    rw [← sum_zero_from _ f2]
    refine Finset.sum_congr rfl fun yv hy => ?_
    have hy' := Finset.mem_range.mp hy
    have q := (hO _ hb v0 h0).2 ht i hi yv hy'
    dsimp only at q
    rw [cw, q]
    by_cases cy : yv < b₀.ny
    · rw [if_pos cy, if_pos cy,
        eqLow_value Reading.gl rs (Nat.le_trans f1 hwl) (by rw [Nat.sub_zero]; exact hy')]
    · rw [if_neg cy, if_neg cy, mul_zero]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.sum_zero_from
#print axioms OnBytes.Road.K4.C.mem_of_forall₂
#print axioms OnBytes.Road.K4.C.walk_cover
#print axioms OnBytes.Road.K4.C.merged_of_opens
