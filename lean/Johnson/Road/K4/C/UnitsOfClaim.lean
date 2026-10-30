-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/UnitsOfClaim.lean: CONDITIONAL.

What is here. At every panel of the batched sumcheck that has weight claims, the units of the
weights' layout that these claims name: each is found; it has the group "e" just where the panel has
the selector; there the bits of an index of its group "kk" are the bits of the panel's column; the
extent of "kk" is at most the panel's number of columns, the extent of "e" at most its number of
rows (`panel_units`). That is, in its letters, the hypothesis PanelUnits of
Johnson/Desc/ProofFile/Honest/K4/Law/W/OpensOfUnits.lean. The road: the library's `claims_of_panels`
(Johnson/Road/FormsKeysFold.lean) says from which segment a panel and its claims come; its
`claim_inv`, `groups_found`, `unit_found`, `kk_first`, `sizes_kind0`
(Johnson/Road/FormsKeysClaim.lean, FormsKeysWv.lean, FormsKeysWvB.lean) say which unit a claim names
and what its groups are; the panels' numbers are read off the verifier's own text.

  `extR u n`   the extent of the group named n of the unit u; 0 if there is none.
  `sizes_three`, `sizes_found`   the extents of the groups of an asked unit with routed experts; a
      found unit's extents are an asked unit's.
  `claimUnit_two`, `claimUnit_last`, `claimUnit_three`   the unit of a claim, by the three shapes of
      a unit.
  `claimUnit_routed`, `kkSize_acc`   the same by a segment's name; the extent of "kk" against the
      panel's columns.
  `panelA_ny`, `panelT_QK_ny`, `triStep_nums`   a panel's columns and rows.
  `panel_units`   the whole.

Not shown here. That the function which makes the batched sumcheck's data returns, that the
verifier's list of weight claims returns: hypotheses. That the weights' layout is one that wsLayOf
returns for a model with routed experts (hl); that its widths d and fe are the layer sub-proof's
(hd, hfe); FOUR PUBLIC INEQUALITIES between the two shapes: s.dq ≤ y.dq, s.f ≤ h.f, s.fe ≤ h.f, s.NE
≤ h.NE: hypotheses; no statement here ties the weights' layout to the layer sub-proof's. That all of
these hold together: no example is known; none is evaluated in Lean. Nothing on soundness, on
completeness or on any other property. No property is claimed.
-/
import Johnson.Road.K4.C.MergedOf
import Johnson.Road.FormsKeysWvB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (SBlk ClaimEnv Panels PanelEnv isAcc panelA panelT)
open OnBytes.Desc.First.K4.Honest

/-- The extent of the group named n of the unit u; 0 if there is none. -/
def extR (u : WsUnit) (n : String) : ℕ := ((u.g.find? fun g => g.name == n).map (·.R)).getD 0

/-- The extents of the groups of an asked unit with routed experts. -/
theorem sizes_three {s' : WsShape} {l : ℕ} {a : AskW} (ha : a ∈ layerAsks s' l)
    (hX : a.X = 7 ∨ a.X = 8 ∨ a.X = 10) :
    a.g.map (·.R) =
      [if a.X = 10 then s'.fe else s'.d, s'.NE, if a.X = 10 then s'.d else s'.fe] := by
  unfold layerAsks at ha
  by_cases hm : s'.moe.getD l false = true
  · rw [if_pos hm] at ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e | e | e | e | e | e | e | e | e <;> subst e <;>
      first | rfl | (exfalso; simp at hX)
  · rw [if_neg hm] at ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e | e | e | e | e <;> subst e <;> first | rfl | (exfalso; simp at hX)

/-- A found unit's extents are those of a unit that a layer asks for. -/
theorem sizes_found {s : WsShape} {lk : ℕ} {lay : WsLay} (h : wsLayOf s true lk = .ok lay)
    {X l ui : ℕ} {u : WsUnit} (h1 : lay.unitOf X l = some ui) (h2 : lay.U[ui]? = some u)
    (hX : X ≤ 11) :
    ∃ a l', a ∈ layerAsks (shapeOf s true) l' ∧ a.X = X ∧ a.l = l ∧
      u.g.map (·.R) = a.g.map (·.R) := by
  obtain ⟨-, a, ha, o, e, eX, el⟩ := unit_found h h1 h2
  obtain ⟨l', hl'⟩ := ask_of_layer ha (by rw [eX]; exact hX)
  refine ⟨a, l', hl', eX, el, ?_⟩
  rw [e]
  exact sizes_placeP a.g lk 0

variable {c : ClaimEnv} {s : WsShape} {lk : ℕ}

/-- **The unit of a claim of a kind with the groups kk and x.** -/
theorem claimUnit_two (hl : wsLayOf s true lk = .ok c.wsLay) {X lam : ℕ}
    {fac : WsGrp → Option WsFac} {x : WsClaim} (hcl : c.claim X lam fac = some x)
    (hg : groupsOf X = [("kk", 'E'), ("x", 'E')]) (hX : X ≤ 11) :
    ∃ u, c.wsLay.U[x.ui]? = some u ∧ hasE u.g = false ∧
      extR u "kk" = kkSize (shapeOf s true) (c.v.lay lam) X := by
  obtain ⟨u, h1, h2, -⟩ := claim_inv hcl
  have hgr := groups_found hl h1 h2 hX
  rw [hg] at hgr
  obtain ⟨g1, g2, hu, e1, e2⟩ := map_two hgr
  have n1 : g1.name = "kk" := congrArg Prod.fst e1
  have n2 : g2.name = "x" := congrArg Prod.fst e2
  have hX0 : X ≠ 0 := by
    rintro rfl
    exact absurd (congrArg List.length hg) (by decide)
  obtain ⟨a, l', hl', eX, el, hs⟩ := sizes_found hl h1 h2 hX
  obtain ⟨k1, k2⟩ := kk_first hl'
  have hR : (u.g.map (·.R)).head? = some (kkSize (shapeOf s true) (c.v.lay lam) X) := by
    rw [hs, ← eX, ← el, k1]
    exact k2 (by rw [eX]; exact hX0)
  rw [hu] at hR
  have hR1 : g1.R = kkSize (shapeOf s true) (c.v.lay lam) X := Option.some.inj hR
  refine ⟨u, h2, ?_, ?_⟩
  · rw [hu]
    exact hasE_two n1 n2
  · unfold extR
    rw [hu, List.find?_cons_of_pos (by rw [n1]; rfl)]
    exact hR1

/-- **The unit of a claim of kind 0**: the groups hd, cd, kk. -/
theorem claimUnit_last (hl : wsLayOf s true lk = .ok c.wsLay) {lam : ℕ}
    {fac : WsGrp → Option WsFac} {x : WsClaim} (hcl : c.claim 0 lam fac = some x) :
    ∃ u, c.wsLay.U[x.ui]? = some u ∧ hasE u.g = false ∧ extR u "kk" = s.d := by
  obtain ⟨u, h1, h2, -⟩ := claim_inv hcl
  have hgr := groups_found hl h1 h2 (Nat.zero_le _)
  obtain ⟨g1, g2, g3, hu, e1, e2, e3⟩ :=
    map_three (a := ("hd", 'A')) (b := ("cd", 'A')) (c := ("kk", 'E')) hgr
  have n1 : g1.name = "hd" := congrArg Prod.fst e1
  have n2 : g2.name = "cd" := congrArg Prod.fst e2
  have n3 : g3.name = "kk" := congrArg Prod.fst e3
  obtain ⟨a, l', hl', eX, -, hs⟩ := sizes_found hl h1 h2 (Nat.zero_le _)
  rw [sizes_kind0 hl' eX, hu] at hs
  have hR3 : g3.R = s.d := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hs
    exact hs.2.2
  refine ⟨u, h2, ?_, ?_⟩
  · rw [hu]
    exact hasE_last n1 n2 n3
  · unfold extR
    rw [hu, List.find?_cons_of_neg (by rw [n1]; decide),
      List.find?_cons_of_neg (by rw [n2]; decide), List.find?_cons_of_pos (by rw [n3]; rfl)]
    exact hR3

/-- **The unit of a claim of a kind with routed experts**: the groups kk, e, x. -/
theorem claimUnit_three (hl : wsLayOf s true lk = .ok c.wsLay) {X lam : ℕ}
    {fac : WsGrp → Option WsFac} {x : WsClaim} (hcl : c.claim X lam fac = some x)
    (hX : X = 7 ∨ X = 8 ∨ X = 10) :
    ∃ u, c.wsLay.U[x.ui]? = some u ∧ hasE u.g = true ∧
      wkOf u.g = ceilLog2 (if X = 10 then s.fe else s.d) ∧
      extR u "kk" = (if X = 10 then s.fe else s.d) ∧ extR u "e" = s.NE := by
  obtain ⟨u, h1, h2, -⟩ := claim_inv hcl
  have hX11 : X ≤ 11 := by omega
  have hgr := groups_found hl h1 h2 hX11
  have eg : groupsOf X = [("kk", 'E'), ("e", 'E'), ("x", 'E')] := by
    unfold groupsOf
    rw [if_neg (by omega), if_pos hX]
  rw [eg] at hgr
  obtain ⟨g1, g2, g3, hu, e1, e2, e3⟩ := map_three hgr
  have n1 : g1.name = "kk" := congrArg Prod.fst e1
  have n2 : g2.name = "e" := congrArg Prod.fst e2
  have n3 : g3.name = "x" := congrArg Prod.fst e3
  obtain ⟨a, l', hl', eX, -, hs⟩ := sizes_found hl h1 h2 hX11
  rw [sizes_three hl' (by rw [eX]; exact hX), hu, eX] at hs
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hs
  have hR1 : g1.R = if X = 10 then s.fe else s.d := hs.1
  have hR2 : g2.R = s.NE := hs.2.1
  refine ⟨u, h2, ?_, ?_, ?_, ?_⟩
  · rw [hu]
    exact hasE_three n1 n2 n3
  · rw [hu, wkOf_three n1, hR1]
  · unfold extR
    rw [hu, List.find?_cons_of_pos (by rw [n1]; rfl)]
    exact hR1
  · unfold extR
    rw [hu, List.find?_cons_of_neg (by rw [n1]; decide),
      List.find?_cons_of_pos (by rw [n2]; rfl)]
    exact hR2

/-- The same by the segment's name. -/
theorem claimUnit_routed (hl : wsLayOf s true lk = .ok c.wsLay) {sn : String}
    (hs : sn = "G" ∨ sn = "U" ∨ sn = "D") {lam : ℕ} {fac : WsGrp → Option WsFac} {x : WsClaim}
    (hcl : c.claim (if sn == "G" then 7 else if sn == "U" then 8 else 10) lam fac = some x) :
    ∃ u, c.wsLay.U[x.ui]? = some u ∧ hasE u.g = true ∧
      wkOf u.g = ceilLog2 (if sn == "D" then s.fe else s.d) ∧
      extR u "kk" = (if sn == "D" then s.fe else s.d) ∧ extR u "e" = s.NE := by
  rcases hs with rfl | rfl | rfl
  · exact claimUnit_three hl hcl (Or.inl rfl)
  · exact claimUnit_three hl hcl (Or.inr (Or.inl rfl))
  · exact claimUnit_three hl hcl (Or.inr (Or.inr rfl))

/-- The extent of "kk" at a segment of the lookup's join, against the panel's columns. -/
theorem kkSize_acc {l : ℕ} {sn : String} (m1 m2 : Bool) (ha : isAcc sn = true) {d dq f : ℕ}
    (hd : s.d = d) (hdq : s.dq ≤ dq) (hf : s.f ≤ f) (hfe : s.fe ≤ f) :
    kkSize (shapeOf s true) l
      (if sn == "G" then (if m1 then 5 else 3) else if sn == "U" then (if m2 then 6 else 4)
      else if sn == "V" then 1 else if sn == "O" then 2 else if sn == "D" then 9 else 11) ≤
      (if sn == "O" then dq else if sn == "D" then f else d) := by
  rcases (isAcc_iff sn).mp ha with rfl | rfl | rfl | rfl | rfl | rfl
  · cases m1 <;> exact Nat.le_of_eq hd
  · cases m2 <;> exact Nat.le_of_eq hd
  · exact Nat.le_of_eq hd
  · exact hdq
  · show (if (shapeOf s true).moe.getD l false = true then s.fe else s.f) ≤ f
    split
    · exact hfe
    · exact hf
  · exact Nat.le_of_eq hd

/-- The columns of a panel of the lookup's join. -/
theorem panelA_ny (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (st : Panels) {b : SBlk}
    (h : isAcc sn = true) (hb : (panelA p ec el sn st).bl = st.bl.push b) :
    b.ny = (if sn == "O" then p.v.y.dq else if sn == "D" then p.v.y.h.f else p.v.y.h.d) := by
  rcases (isAcc_iff sn).mp h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact congrArg SBlk.ny (push_inj hb).symm

/-- The columns of the panel of the queries' and keys' segment. -/
theorem panelT_QK_ny (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (st st' : Panels)
    {b : SBlk} (hs : sn = "QK") (h : panelT p ec el sn st = some st')
    (hb : st'.bl = st.bl.push b) : b.ny = p.v.y.h.d := by
  subst hs
  rw [panelT_QK_eq] at h
  cases h
  exact congrArg SBlk.ny (push_inj hb).symm

/-- The columns and rows of a panel with the selector. -/
theorem triStep_nums {p : PanelEnv} {ec : E} {el : Array E} {sn : String} {st st' : Panels}
    {lm : ℕ} {b : SBlk} (h : triStep p ec el sn st lm = some st') (hb : st'.bl = st.bl.push b) :
    b.ny = (if sn == "D" then p.v.y.h.fe else p.v.y.h.d) ∧ b.ni = p.v.y.h.NE := by
  simp only [triStep] at h
  split_ifs at h ⊢ <;> first
    | (cases h; obtain rfl := push_inj hb; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_some h; cases h; obtain rfl := push_inj hb; exact ⟨rfl, rfl⟩)

/-- **AT EACH PANEL, THE CLAIMS' UNITS.** CONDITIONAL: on every hypothesis named. -/
theorem panel_units {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData}
    (h : stackData Q w p shownT = some SD) {rs : Array E} {cl : List WsClaim}
    (hcl : ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).weightClaims SD.S.TS = some cl)
    {s : WsShape} {lk : ℕ} (hl : wsLayOf s true lk = .ok Q.P.wsLay) (hd : s.d = SD.S.v.y.h.d)
    (hfe : s.fe = SD.S.v.y.h.fe) (hdq : s.dq ≤ SD.S.v.y.dq) (hf : s.f ≤ SD.S.v.y.h.f)
    (hfef : s.fe ≤ SD.S.v.y.h.f) (hNE : s.NE ≤ SD.S.v.y.h.NE) :
    ∀ b ∈ SD.bl.toList, ∀ v0, b.v0 = some v0 →
      (b.tri = true → ∃ x u, cl[v0]? = some x ∧ Q.P.wsLay.U[x.ui]? = some u ∧
        hasE u.g = true ∧ wkOf u.g = b.wy ∧ extR u "kk" ≤ b.ny ∧ extR u "e" ≤ b.ni) ∧
      (b.tri = false → ∀ i, i < b.ni → ∃ x u, cl[v0 + i]? = some x ∧
        Q.P.wsLay.U[x.ui]? = some u ∧ hasE u.g = false ∧ extR u "kk" ≤ b.ny) := by
  obtain ⟨pans, hp, ebl, _⟩ := stack_panels_at h
  have hS := (stack_open h).1
  obtain ⟨_, _, _, cv, cw⟩ := sides_claims hS
  have hv : (sidesEnv SD.S shownT).v = ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).v :=
    cv.symm
  have hl' : wsLayOf s true lk =
      .ok ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).wsLay := by
    show wsLayOf s true lk = .ok SD.S.ce.wsLay
    rw [cw]
    exact hl
  have G := (claims_of_panels _ _ hv SD.S.TS hp hcl).2
  intro b hb v0 h0
  obtain ⟨b₀, hb₀, o, rfl⟩ := mem_of_forall₂ (placed_f2 pans.bl) b (by rw [← ebl]; exact hb)
  refine ⟨fun ht => ?_, fun ht i hi => ?_⟩
  · obtain ⟨q, -, g, -, lm, st, st', l, h3, hname, hlm, -, hstep, hbl, hclT, hlen, hat⟩ :=
      (G b₀ hb₀ v0 h0).2 ht
    obtain ⟨-, hatr⟩ := claimsT_routed_at _ g.name (hv ▸ h3) hname hclT
    have hlm' : lm < l.length := by omega
    have e2 : l[lm]? = some l[lm] := List.getElem?_eq_getElem hlm'
    obtain ⟨u, hu, hE, hwk, hkk, he⟩ :=
      claimUnit_routed hl' hname ((hatr lm hlm').symm.trans e2)
    obtain ⟨hwy, _⟩ := triStep_wy hstep hbl
    obtain ⟨hny, hni⟩ := triStep_nums hstep hbl
    refine ⟨l[lm], u, hat.trans e2, by rw [← cw]; exact hu, hE, ?_, ?_, ?_⟩
    · show wkOf u.g = b₀.wy
      rw [hwk, hwy, hd, hfe]
      rfl
    · show extR u "kk" ≤ b₀.ny
      rw [hkk, hny, hd, hfe]
      exact Nat.le_refl _
    · show extR u "e" ≤ b₀.ni
      rw [he, hni]
      exact hNE
  · rcases (G b₀ hb₀ v0 h0).1 ht with ⟨q, -, g, -, st, l, hacc, -, hbl, hclA, hlen, hat⟩ |
      ⟨q, -, g, -, st, st', l, hname, -, hpt, hbl, hclT, hlen, hat⟩
    · have hi' : i < l.length := by
        rw [hlen]
        exact hi
      have e2 : l[i]? = some l[i] := List.getElem?_eq_getElem hi'
      obtain ⟨k1, k2⟩ := kindA_groups g.name
        (({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).v.isMoe
          (if g.name == "LR" then 2 * i + 1 else i))
        (({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).v.isMoe
          (if g.name == "LR" then 2 * i + 1 else i)) hacc
      obtain ⟨u, hu, hE, hkk⟩ :=
        claimUnit_two hl' ((claimsA_at _ g.name hclA hacc i hi').symm.trans e2) k1 k2
      refine ⟨l[i], u, (hat i hi).trans e2, by rw [← cw]; exact hu, hE, ?_⟩
      show extR u "kk" ≤ b₀.ny
      rw [hkk, panelA_ny _ _ _ _ st hacc hbl]
      exact kkSize_acc _ _ hacc hd hdq hf hfef
    · have hi' : i < l.length := by
        rw [hlen]
        exact hi
      have e2 : l[i]? = some l[i] := List.getElem?_eq_getElem hi'
      rw [hname] at hclT
      obtain ⟨-, AH, lfc, -, hatq⟩ := claimsT_QK_at _ hclT
      obtain ⟨u, hu, hE, hkk⟩ := claimUnit_last hl' ((hatq i hi').symm.trans e2)
      refine ⟨l[i], u, (hat i hi).trans e2, by rw [← cw]; exact hu, hE, ?_⟩
      show extR u "kk" ≤ b₀.ny
      rw [hkk, panelT_QK_ny _ _ _ _ st st' hname hpt hbl, hd]
      exact Nat.le_refl _

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.sizes_three
#print axioms OnBytes.Road.K4.C.sizes_found
#print axioms OnBytes.Road.K4.C.claimUnit_two
#print axioms OnBytes.Road.K4.C.claimUnit_last
#print axioms OnBytes.Road.K4.C.claimUnit_three
#print axioms OnBytes.Road.K4.C.claimUnit_routed
#print axioms OnBytes.Road.K4.C.kkSize_acc
#print axioms OnBytes.Road.K4.C.panelA_ny
#print axioms OnBytes.Road.K4.C.panelT_QK_ny
#print axioms OnBytes.Road.K4.C.triStep_nums
#print axioms OnBytes.Road.K4.C.panel_units
