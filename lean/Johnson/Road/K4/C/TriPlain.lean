-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TriPlain.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side, the second token
sumcheck: the unit of the weight claim of a panel with the selector has no group named "cd". The
verifier's lists of panels and of weight claims are in step (the library's claims_of_panels,
claimsT_routed_at, Johnson/Road/FormsKeysFold.lean): the claim of such a panel is on a unit of kind
7, 8 or 10; and the groups of such a unit are named kk, e, x (the library's groups_found,
Johnson/Road/FormsKeysWv.lean). Statements and proofs.

  `sides_claims`   what Sides.of lays besides: the list of weight claims and their tables.
  `no_cd`          a unit of kind 7, 8 or 10 has no group named "cd".
  **`tri_cd`**       the extent of the group "cd" is 0 at the claim of every panel with the
                   selector.

Not shown here. That the honest side's functions return anywhere: no example is known. THAT THE
LAYOUT OF THE WEIGHTS IS ONE THAT THE VERIFIER's FUNCTION wsLayOf RETURNS, for a model with
mixtures of experts (hws), is a hypothesis: at a free layout the statement can be false. Public
data alone.
No property is claimed.
-/
import Johnson.Road.K4.C.StackPanelsAt
import Johnson.Road.K4.C.RowMaps
import Johnson.Road.FormsKeysFold
import Johnson.Road.FormsKeysWv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (SBlk ClaimEnv placePanels panelsA panelsT)
open OnBytes.Desc.First.K4.Honest

variable {Q : K4Pub} {w : K4In} {p : Pts} {S : Sides}

/-- **What Sides.of lays besides**: the verifier's list of weight claims returns, and the claims'
tables are made of it, claim by claim. -/
theorem sides_claims (h : Sides.of Q w p = some S) :
    ∃ cls, S.ce.weightClaims S.TS = some cls ∧
      cls.toArray.mapM (openOf Q.P.wsLay w.w (Q.g * Q.P.y.Lam)) = some S.opens ∧
      S.ce.v = S.v ∧ S.ce.wsLay = Q.P.wsLay := by
  unfold Sides.of at h
  obtain ⟨v, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨TS, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨Z, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨cls, hc, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨x, lfc⟩, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨opens, ho, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨gl, gr⟩, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ends, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := Option.some.inj h
  exact ⟨cls, hc, ho, rfl, rfl⟩

/-- A unit of kind 7, 8 or 10 of a layout that wsLayOf returns has no group named "cd". -/
theorem no_cd {s : WsShape} {lk : ℕ} {lay : WsLay} (hws : wsLayOf s true lk = .ok lay)
    {X l ui : ℕ} {u : WsUnit} (h1 : lay.unitOf X l = some ui) (h2 : lay.U[ui]? = some u)
    (hX : X = 7 ∨ X = 8 ∨ X = 10) : (u.g.find? fun G => G.name == "cd") = none := by
  have e := groups_found hws h1 h2 (by omega)
  have eg : groupsOf X = [("kk", 'E'), ("e", 'E'), ("x", 'E')] := by
    unfold groupsOf
    rw [if_neg (by omega), if_pos hX]
  rw [eg] at e
  rw [List.find?_eq_none]
  intro G hG
  have hm : (G.name, G.cls) ∈ [("kk", 'E'), ("e", 'E'), ("x", 'E')] := by
    rw [← e]
    exact List.mem_map_of_mem (f := fun y : WsGrp => (y.name, y.cls)) hG
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨e1, _⟩ | ⟨e1, _⟩ | ⟨e1, _⟩ <;> rw [e1] <;> decide

/-- **AT THE CLAIM OF EVERY PANEL WITH THE SELECTOR THE EXTENT OF THE GROUP "cd" IS 0.** sh: any
values in the place of those that the second token sumcheck has shown. CONDITIONAL: on hws, h and
hx. -/
theorem tri_cd {s : WsShape} {lk : ℕ} (hws : wsLayOf s true lk = .ok Q.P.wsLay)
    (h : Sides.of Q w p = some S) {sh : Array E} {x : Array SBlk × ℕ}
    (hx : S.panels sh = some x) :
    ∀ b ∈ x.1.toList, b.tri = true → ∀ v0, b.v0 = some v0 → (S.opens.getD v0 {}).cd = 0 := by
  obtain ⟨cls, hc, ho, hv, hl⟩ := sides_claims h
  unfold Sides.panels at hx
  obtain ⟨pans, hp, hx⟩ := Option.bind_eq_some_iff.1 hx
  dsimp only at hx
  by_cases hn : (pans.nextV != S.opens.size) = true
  · rw [if_pos hn] at hx
    simp at hx
  · rw [if_neg hn] at hx
    obtain ⟨_, _, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain rfl := Option.some.inj hx
    intro b hb ht v0 h0
    obtain ⟨b0, hb0, o, rfl⟩ := placed_from pans.bl b hb
    obtain ⟨q, _, g, _, lm, _, _, l, h3, hname, hlm, _, _, _, hcl, hlen, hat⟩ :=
      ((claims_of_panels _ S.ce hv.symm S.TS hp hc).2 b0 hb0 v0 h0).2 ht
    have h3' : S.ce.v.y.h.p3 = true := by
      rw [hv]
      exact h3
    obtain ⟨_, hall⟩ := claimsT_routed_at S.ce g.name h3' hname hcl
    have hlm' : lm < l.length := by
      rw [hlen]
      exact hlm
    have hcl0 := hall lm hlm'
    rw [List.getElem?_eq_getElem hlm'] at hcl0 hat
    generalize l[lm] = cl0 at hcl0 hat
    have hcl1 := hcl0.symm
    unfold ClaimEnv.claim at hcl1
    obtain ⟨ui, hui, hcl1⟩ := Option.bind_eq_some_iff.1 hcl1
    obtain ⟨u, hu, hcl1⟩ := Option.bind_eq_some_iff.1 hcl1
    obtain ⟨f, _, hcl1⟩ := Option.bind_eq_some_iff.1 hcl1
    obtain rfl := Option.some.inj hcl1
    rw [hl] at hui hu
    have hX : (if (g.name == "G") = true then 7 else if (g.name == "U") = true then 8 else 10) = 7 ∨
        (if (g.name == "G") = true then 7 else if (g.name == "U") = true then 8 else 10) = 8 ∨
        (if (g.name == "G") = true then 7 else if (g.name == "U") = true then 8 else 10) = 10 := by
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have hnone := no_cd hws hui hu hX
    obtain ⟨y, hy, hg⟩ := amapM_get ho (i := v0) (x := { ui := ui, f := f })
      (by rw [List.getElem?_toArray]; exact hat)
    rw [Array.getD_eq_getD_getElem?, hg, Option.getD_some]
    unfold openOf at hy
    obtain ⟨u', hu', hy⟩ := Option.bind_eq_some_iff.1 hy
    obtain rfl : u = u' := Option.some.inj (hu.symm.trans hu')
    dsimp only at hy
    split_ifs at hy
    · obtain ⟨_, hbad, _⟩ := Option.bind_eq_some_iff.1 hy
      cases hbad
    · obtain ⟨_, _, hy⟩ := Option.bind_eq_some_iff.1 hy
      obtain ⟨tab, _, hy⟩ := Option.bind_eq_some_iff.1 hy
      obtain rfl := Option.some.inj hy
      show (((u.g.find? fun G => G.name == "cd").map (·.R)).getD 0) = 0
      rw [hnone]
      rfl

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.sides_claims
#print axioms OnBytes.Road.K4.C.no_cd
#print axioms OnBytes.Road.K4.C.tri_cd
