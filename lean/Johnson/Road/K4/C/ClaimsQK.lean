-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ClaimsQK.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the weight claims: THE CLAIMS OF THE
SEGMENT QK RETURN, one for each layer of the group, each on a unit of the layout of the weights and
with the sizes that the layout asks (claimsT at QK, OnBytes/Model/LayerPanels.lean). First the
weights of the heads return (headWeights): some call holds QK, its point has a head's coordinates,
the tensors q and kx are in the list, and each head lies in its tensor. Then the rule for the
factors of the unit of queries and keys: 64 weights of heads, one entry for each coordinate within
a head, and the factor on the place's bits. One definition of a hypothesis; statements and proofs.
General in the sizes.

  `QkRd c s`           what headWeights reads, and that the weights' shape has twice the half,
                       rounded down, of a head's width.
  `headFeat_there`, `cutLast_there`   a head lies in its tensor; a point's last coordinates.
  **`headWeights_some`** the weights of the heads are there.
  `rule_zero`          the rule for the factors.
  **`claimsT_QK`**       the claims.

Not shown here. That the hypotheses hold at any plan: no example is shown here. WHO HAS THE TWO
BUNDLES: ClaimRdOf.lean (claimRd_of, qkRd_of), AT THE BLANK STRUCTURE ALONE, where every challenge
and coordinate is 0; at a structure with sampled challenges no statement has them. AT A LAYOUT OF
THE WEIGHTS THAT wsLayOf RETURNS FOR A MODEL WITH ROUTED EXPERTS. ClaimRd also asks: that the dense
width is twice an expert's (f = 2 fe); switch p3 on; each routed layer's number in the group; five
sizes at least one. Public data alone: whether a claim IS THERE and how long its parts are; nothing
on its elements.
No property is claimed.
-/
import Johnson.Road.K4.C.ClaimsWalk
import Johnson.Road.K4.C.JoinReturn
import Johnson.Road.FormsKeysQK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env ClaimEnv Ten)
open Inst.Model (Params)

/-- **What headWeights reads**, and that the weights' shape has twice the half, rounded down, of a
head's width (dhe). This defines a hypothesis; the definition claims nothing. -/
structure QkRd (c : ClaimEnv) (s : WsShape) : Prop where
  seg : ∃ q cd sg, c.v.callOf "QK" = some (q, cd, sg) ∧ c.v.y.ldh ≤ (c.v.zj q cd.lJ).size
  tq : ∃ t : Ten, c.v.y.T_ "q" = some t ∧ t.J = c.v.y.h.H * c.v.y.h.dh
  tk : ∃ t : Ten, c.v.y.T_ "kx" = some t ∧ t.J = c.v.y.h.Gk * c.v.y.h.dh
  dh0 : 0 < c.v.y.h.dh
  dhe : s.dh = 2 * (c.v.y.h.dh / 2)

/-- A head lies in its tensor. -/
theorem headFeat_there {X : TenAt} {n hd dh : ℕ} (hJ : X.J = n * dh) (h0 : 0 < dh) (hh : hd < n) :
    ((headFeat X hd dh).toOption).isSome = true := by
  unfold headFeat
  have c1 : (dh == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have c2 : (X.J % dh != 0) = false := by
    rw [hJ, Nat.mul_mod_left]
    rfl
  have c3 : decide (hd ≥ X.J / dh) = false := by
    rw [decide_eq_false_iff_not, hJ, Nat.mul_div_cancel _ h0]
    omega
  rw [c1, c2, c3]
  rfl

variable {c : ClaimEnv} {s : WsShape} {P : Params} {lk : ℕ}

/-- Cutting the last k coordinates off a point that has them. -/
theorem cutLast_there {z : Array E} {k : ℕ} (h : k ≤ z.size) :
    (cutLast z k).toOption = some (z.extract 0 (z.size - k), z.extract (z.size - k) z.size) := by
  unfold cutLast
  rw [if_neg (by omega)]
  rfl

/-- **THE WEIGHTS OF THE HEADS ARE THERE**, and the first array has 64 entries. Of QkRd the clause
dhe is not spent here. -/
theorem headWeights_some (Q : QkRd c s) :
    ∃ AH lfc, c.headWeights = some (AH, lfc) ∧ AH.size = 64 := by
  obtain ⟨q, cd, sg, hc, hz⟩ := Q.seg
  obtain ⟨tq, htq, jq⟩ := Q.tq
  obtain ⟨tk, htk, jk⟩ := Q.tk
  have hr : (c.headWeights).isSome = true := by
    unfold ClaimEnv.headWeights
    refine bind_at hc ?_
    dsimp only
    refine bind_at (cutLast_there hz) ?_
    dsimp only
    refine bind_at htq ?_
    refine bind_at htk ?_
    refine bind_there (foldlM_there _ (fun hd hhd a => ?_) _) fun _ => rfl
    have hhd' := List.mem_range.mp hhd
    by_cases hH : hd < c.v.y.h.H
    · rw [if_pos hH]
      exact bind_there (headFeat_there (X := tq.place) jq Q.dh0 hH) fun _ => rfl
    · rw [if_neg hH]
      refine bind_there ?_ fun _ => rfl
      rw [Option.isSome_map]
      exact headFeat_there (X := tk.place) jk Q.dh0 (by omega)
  obtain ⟨p, hp⟩ := some_of hr
  obtain ⟨AH, lfc⟩ := p
  obtain ⟨-, -, -, -, h64, -⟩ := headWeights_entries c hc hp
  exact ⟨AH, lfc, hp, h64⟩

/-- **The rule for the factors of the unit of queries and keys.** -/
theorem rule_zero {AH kap : Array E} {wy Rc Rk : ℕ} (hA : AH.size = 64) (hkap : kap.size = Rc)
    (hk0 : 0 < Rk) (hk : Rk ≤ 2 ^ wy) (hrs : wy ≤ c.rs.size) {G : WsGrp}
    (hm : (G.name, G.R, G.cls) ∈ [("hd", 64, 'A'), ("cd", Rc, 'A'), ("kk", Rk, 'E')])
    (hok : GrpOK G) :
    ∃ f, (if G.name == "hd" then some ({ AV := AH } : WsFac)
      else if G.name == "cd" then some { AV := kap } else c.facRs G 0 wy) = some f ∧
      f.fits G = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨n, r, e⟩ | ⟨n, r, e⟩ | ⟨n, r, e⟩
  · have hn : (G.name == "hd") = true := by
      rw [n]
      rfl
    rw [if_pos hn]
    refine ⟨_, rfl, ?_⟩
    unfold WsFac.fits
    rw [e, r]
    show ((AH.size == 64 && (#[] : Array E).isEmpty) && (#[] : Array E).isEmpty) = true
    rw [hA]
    rfl
  · have hn : ¬ (G.name == "hd") = true := by
      rw [n]
      decide
    have hn2 : (G.name == "cd") = true := by
      rw [n]
      rfl
    rw [if_neg hn, if_pos hn2]
    refine ⟨_, rfl, ?_⟩
    unfold WsFac.fits
    rw [e, r]
    show ((kap.size == Rc && (#[] : Array E).isEmpty) && (#[] : Array E).isEmpty) = true
    rw [hkap, beq_self_eq_true]
    rfl
  · have hn : ¬ (G.name == "hd") = true := by
      rw [n]
      decide
    have hn2 : ¬ (G.name == "cd") = true := by
      rw [n]
      decide
    rw [if_neg hn, if_neg hn2]
    exact rs_rule hok e (by rw [r]; exact hk0) (by rw [r]; exact hk) (by omega)

/-- **THE CLAIMS OF THE SEGMENT QK RETURN**, one good claim for each layer of the group.
CONDITIONAL: on R and Q. -/
theorem claimsT_QK (R : ClaimRd c s P lk) (Q : QkRd c s) :
    RetCl c.wsLay (c.claimsT "QK") c.v.y.Lam := by
  obtain ⟨⟨d0, -, -, -, -, -⟩, ⟨dle, -, -, -, -, -⟩, -⟩ := sizes_rd R
  obtain ⟨AH, lfc, hw, h64⟩ := headWeights_some Q
  rw [claimsT_QK_eq, hw]
  have h := retCl_mapM (lay := c.wsLay)
    (f := fun lam => c.claim 0 lam fun G =>
      if G.name == "hd" then some ({ AV := AH } : WsFac)
      else if G.name == "cd" then some { AV := c.ropeFactor (eqTab c.rt) lfc lam }
      else c.facRs G 0 (ceilLog2 c.v.y.h.d))
    (List.range c.v.y.Lam) fun i hi => by
    have hi' := List.mem_range.mp hi
    have hX : (kindsOf (c.v.lay i))[0]? = some 0 := by
      unfold kindsOf
      split_ifs <;> rfl
    exact claim_some R.Z R.hlw (R.lays i hi') hX fun a ha eX G hG hok =>
      rule_zero (Rc := s.dh) (Rk := s.d) h64
        (by rw [ropeFactor_size, Q.dhe]) d0 dle R.bd (by
          have h1 := grp_in_ask ha hG
          rw [eX] at h1
          exact h1) hok
  rw [List.length_range] at h
  exact h

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.headFeat_there
#print axioms OnBytes.Road.K4.C.cutLast_there
#print axioms OnBytes.Road.K4.C.headWeights_some
#print axioms OnBytes.Road.K4.C.rule_zero
#print axioms OnBytes.Road.K4.C.claimsT_QK
