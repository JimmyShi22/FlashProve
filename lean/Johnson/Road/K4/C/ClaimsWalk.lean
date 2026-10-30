-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ClaimsWalk.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the weight claims: SEGMENT BY SEGMENT THE
LIST OF CLAIMS RETURNS, one claim for each layer of the group (LR and the routed products: one for
each layer with routed experts), each on a unit of the layout of the weights and with the sizes that
the layout asks: the six segments of the first walk (claimsA at G, U, V, O, D, LR) and the three
routed products of the second (claimsT at G, U, D; OnBytes/Model/LayerPanels.lean). By the kit's
claimA_one and claimT_one (ClaimsKit.lean), at the kind of unit that the layer has: an even layer of
the group is dense, an odd one a mixture of experts. Statements and proofs. General in the sizes.

  `kinds_even`, `kinds_odd`, `isMoe_odd`, `isMoe_even`, `sizes_rd`   steps.
  `claimsA_G`, `claimsA_U`, `claimsA_V`, `claimsA_O`, `claimsA_D`, `claimsA_LR`   the first walk.
  `claimsT_G`, `claimsT_U`, `claimsT_D`   the routed products.

Not shown here. That the hypothesis ClaimRd holds at any plan: no example is shown here. WHO HAS
ClaimRd: ClaimRdOf.lean (claimRd_of), AT THE BLANK STRUCTURE ALONE, where every challenge and
coordinate is 0; at a structure with sampled challenges no statement has it. AT A LAYOUT OF THE
WEIGHTS THAT wsLayOf RETURNS FOR A MODEL WITH ROUTED EXPERTS. ClaimRd also asks: that the dense
width is twice an expert's (f = 2 fe); switch p3 on; each routed layer's number in the group; five
sizes at least one. The claims of the segment QK and the embedding's claim are not here. Public data
alone: whether a claim IS THERE and how long its parts are; nothing on its elements.
No property is claimed.
-/
import Johnson.Road.K4.C.ClaimsKit
import Johnson.Road.FormsKeysFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env ClaimEnv)
open Inst.Model (Params)

variable {c : ClaimEnv} {s : WsShape} {P : Params} {lk : ℕ}

/-- The kinds of the units of an even layer. -/
theorem kinds_even {l : ℕ} (h : ¬ l % 2 = 1) : kindsOf l = [0, 1, 2, 3, 4, 9] := by
  unfold kindsOf
  rw [if_neg h]

/-- The kinds of the units of an odd layer. -/
theorem kinds_odd {l : ℕ} (h : l % 2 = 1) : kindsOf l = [0, 1, 2, 5, 6, 7, 8, 9, 10, 11] := by
  unfold kindsOf
  rw [if_pos h]

/-- Whether a layer of the group has routed experts. -/
theorem isMoe_odd (R : ClaimRd c s P lk) {i : ℕ} (h : i % 2 = 1) : c.v.isMoe i = true := by
  unfold Env.isMoe
  rw [R.p3, h]
  rfl

/-- The like at an even layer. -/
theorem isMoe_even (R : ClaimRd c s P lk) {i : ℕ} (h : ¬ i % 2 = 1) : c.v.isMoe i = false := by
  unfold Env.isMoe
  have h0 : i % 2 = 0 := by omega
  rw [R.p3, h0]
  rfl

/-- The sizes of the weights' shape: each at least one, each at most two to the bits that its
factor is given, each within its segment. -/
theorem sizes_rd (R : ClaimRd c s P lk) :
    (0 < s.d ∧ 0 < s.dq ∧ 0 < s.dkv ∧ 0 < s.f ∧ 0 < s.fe ∧ 0 < s.NE) ∧
    (s.d ≤ 2 ^ ceilLog2 c.v.y.h.d ∧ s.dq ≤ 2 ^ ceilLog2 c.v.y.dq ∧
      s.f ≤ 2 ^ ceilLog2 c.v.y.h.f ∧ s.fe ≤ 2 ^ ceilLog2 c.v.y.h.f ∧
      s.fe ≤ 2 ^ ceilLog2 c.v.y.h.fe ∧ s.NE ≤ 2 ^ ceilLog2 (max c.v.y.h.NE 1)) ∧
    (0 + s.d ≤ c.v.y.h.d ∧ 0 + s.dkv ≤ c.v.y.dkv ∧ 0 + s.f ≤ c.v.y.h.f ∧
      0 + s.fe ≤ c.v.y.h.f ∧ 0 + s.NE ≤ c.v.y.h.NE ∧ c.v.y.h.fe + s.fe ≤ c.v.y.h.f) := by
  have hfe := R.fe0
  have hff := R.ffe
  rw [R.d, R.dq, R.dkv, R.f, R.fe, R.NE]
  refine ⟨⟨R.d0, R.dq0, R.dkv0, by omega, R.fe0, R.NE0⟩,
    ⟨le_pow_ceil _, le_pow_ceil _, le_pow_ceil _, Nat.le_trans (by omega) (le_pow_ceil _),
      le_pow_ceil _, Nat.le_trans (Nat.le_max_left _ _) (le_pow_ceil _)⟩,
    ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩⟩

/-- **The claims of the segment G in the first walk.** -/
theorem claimsA_G (R : ClaimRd c s P lk) : RetCl c.wsLay (c.claimsA "G") c.v.y.Lam := by
  obtain ⟨⟨d0, dq0, dkv0, f0, fe0, NE0⟩, ⟨dle, dqle, fle, fef, fele, NEle⟩,
    ⟨wd, wdkv, wf, wfe, wNE, wfe2⟩⟩ := sizes_rd R
  rw [claimsA_eq c "G" rfl]
  have h := retCl_mapM (lay := c.wsLay)
    (f := fun i => c.claim (if c.v.isMoe i then 5 else 3) i fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else c.facEw G "G" 0)
    (List.range c.v.y.Lam) fun i hi => by
    have hi' := List.mem_range.mp hi
    by_cases hp : i % 2 = 1
    · have hl : c.v.lay i % 2 = 1 := by
        rw [R.par]
        exact hp
      dsimp only
      rw [isMoe_odd R hp]
      exact claimA_one R (k := 3) (Rk := s.d) (Rx := s.fe) hi' (by rw [kinds_odd hl]; rfl) rfl
        R.sG d0 fe0 dle R.bd wfe
    · have hl : ¬ c.v.lay i % 2 = 1 := by
        rw [R.par]
        exact hp
      dsimp only
      rw [isMoe_even R hp]
      exact claimA_one R (k := 3) (Rk := s.d) (Rx := s.f) hi' (by rw [kinds_even hl]; rfl) rfl
        R.sG d0 f0 dle R.bd wf
  rw [List.length_range] at h
  exact h

/-- **The claims of the segment U in the first walk.** -/
theorem claimsA_U (R : ClaimRd c s P lk) : RetCl c.wsLay (c.claimsA "U") c.v.y.Lam := by
  obtain ⟨⟨d0, dq0, dkv0, f0, fe0, NE0⟩, ⟨dle, dqle, fle, fef, fele, NEle⟩,
    ⟨wd, wdkv, wf, wfe, wNE, wfe2⟩⟩ := sizes_rd R
  rw [claimsA_eq c "U" rfl]
  have h := retCl_mapM (lay := c.wsLay)
    (f := fun i => c.claim (if c.v.isMoe i then 6 else 4) i fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else c.facEw G "U" 0)
    (List.range c.v.y.Lam) fun i hi => by
    have hi' := List.mem_range.mp hi
    by_cases hp : i % 2 = 1
    · have hl : c.v.lay i % 2 = 1 := by
        rw [R.par]
        exact hp
      dsimp only
      rw [isMoe_odd R hp]
      exact claimA_one R (k := 4) (Rk := s.d) (Rx := s.fe) hi' (by rw [kinds_odd hl]; rfl) rfl
        R.sU d0 fe0 dle R.bd wfe
    · have hl : ¬ c.v.lay i % 2 = 1 := by
        rw [R.par]
        exact hp
      dsimp only
      rw [isMoe_even R hp]
      exact claimA_one R (k := 4) (Rk := s.d) (Rx := s.f) hi' (by rw [kinds_even hl]; rfl) rfl
        R.sU d0 f0 dle R.bd wf
  rw [List.length_range] at h
  exact h

/-- **The claims of the segment V.** -/
theorem claimsA_V (R : ClaimRd c s P lk) : RetCl c.wsLay (c.claimsA "V") c.v.y.Lam := by
  obtain ⟨⟨d0, dq0, dkv0, f0, fe0, NE0⟩, ⟨dle, dqle, fle, fef, fele, NEle⟩,
    ⟨wd, wdkv, wf, wfe, wNE, wfe2⟩⟩ := sizes_rd R
  rw [claimsA_eq c "V" rfl]
  have h := retCl_mapM (lay := c.wsLay)
    (f := fun i => c.claim 1 i fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else c.facEw G "V" 0)
    (List.range c.v.y.Lam) fun i hi => by
    have hi' := List.mem_range.mp hi
    by_cases hp : i % 2 = 1
    · have hl : c.v.lay i % 2 = 1 := by
        rw [R.par]
        exact hp
      exact claimA_one R (k := 1) (Rk := s.d) (Rx := s.dkv) hi' (by rw [kinds_odd hl]; rfl) rfl
        R.sV d0 dkv0 dle R.bd wdkv
    · have hl : ¬ c.v.lay i % 2 = 1 := by
        rw [R.par]
        exact hp
      exact claimA_one R (k := 1) (Rk := s.d) (Rx := s.dkv) hi' (by rw [kinds_even hl]; rfl) rfl
        R.sV d0 dkv0 dle R.bd wdkv
  rw [List.length_range] at h
  exact h

/-- **The claims of the segment O.** -/
theorem claimsA_O (R : ClaimRd c s P lk) : RetCl c.wsLay (c.claimsA "O") c.v.y.Lam := by
  obtain ⟨⟨d0, dq0, dkv0, f0, fe0, NE0⟩, ⟨dle, dqle, fle, fef, fele, NEle⟩,
    ⟨wd, wdkv, wf, wfe, wNE, wfe2⟩⟩ := sizes_rd R
  rw [claimsA_eq c "O" rfl]
  have h := retCl_mapM (lay := c.wsLay)
    (f := fun i => c.claim 2 i fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.dq)
      else c.facEw G "O" 0)
    (List.range c.v.y.Lam) fun i hi => by
    have hi' := List.mem_range.mp hi
    by_cases hp : i % 2 = 1
    · have hl : c.v.lay i % 2 = 1 := by
        rw [R.par]
        exact hp
      exact claimA_one R (k := 2) (Rk := s.dq) (Rx := s.d) hi' (by rw [kinds_odd hl]; rfl) rfl
        R.sO dq0 d0 dqle R.bdq wd
    · have hl : ¬ c.v.lay i % 2 = 1 := by
        rw [R.par]
        exact hp
      exact claimA_one R (k := 2) (Rk := s.dq) (Rx := s.d) hi' (by rw [kinds_even hl]; rfl) rfl
        R.sO dq0 d0 dqle R.bdq wd
  rw [List.length_range] at h
  exact h

/-- **The claims of the segment D in the first walk.** -/
theorem claimsA_D (R : ClaimRd c s P lk) : RetCl c.wsLay (c.claimsA "D") c.v.y.Lam := by
  obtain ⟨⟨d0, dq0, dkv0, f0, fe0, NE0⟩, ⟨dle, dqle, fle, fef, fele, NEle⟩,
    ⟨wd, wdkv, wf, wfe, wNE, wfe2⟩⟩ := sizes_rd R
  rw [claimsA_eq c "D" rfl]
  have h := retCl_mapM (lay := c.wsLay)
    (f := fun i => c.claim 9 i fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.f)
      else c.facEw G "D" 0)
    (List.range c.v.y.Lam) fun i hi => by
    have hi' := List.mem_range.mp hi
    by_cases hp : i % 2 = 1
    · have hl : c.v.lay i % 2 = 1 := by
        rw [R.par]
        exact hp
      have e9 : askRs (shapeOf s true) (c.v.lay i) 9 =
          [("kk", s.fe, 'E'), ("x", s.d, 'E')] := by
        have e : askRs (shapeOf s true) (c.v.lay i) 9 = [("kk",
            if (shapeOf s true).moe.getD (c.v.lay i) false = true then s.fe else s.f, 'E'),
            ("x", s.d, 'E')] := rfl
        rw [e, moe_at R (R.lays i hi')]
        rw [hl]
        rfl
      exact claimA_one R (k := 7) hi' (by rw [kinds_odd hl]; rfl) e9 R.sD fe0 d0 fef R.bf wd
    · have hl : ¬ c.v.lay i % 2 = 1 := by
        rw [R.par]
        exact hp
      have e9 : askRs (shapeOf s true) (c.v.lay i) 9 =
          [("kk", s.f, 'E'), ("x", s.d, 'E')] := by
        have e : askRs (shapeOf s true) (c.v.lay i) 9 = [("kk",
            if (shapeOf s true).moe.getD (c.v.lay i) false = true then s.fe else s.f, 'E'),
            ("x", s.d, 'E')] := rfl
        rw [e, moe_at R (R.lays i hi')]
        have h0 : c.v.lay i % 2 = 0 := by omega
        rw [h0]
        rfl
      exact claimA_one R (k := 5) hi' (by rw [kinds_even hl]; rfl) e9 R.sD f0 d0 fle R.bf wd
  rw [List.length_range] at h
  exact h

/-- **The claims of the segment LR.** -/
theorem claimsA_LR (R : ClaimRd c s P lk) : RetCl c.wsLay (c.claimsA "LR") c.v.y.LamM := by
  obtain ⟨⟨d0, dq0, dkv0, f0, fe0, NE0⟩, ⟨dle, dqle, fle, fef, fele, NEle⟩,
    ⟨wd, wdkv, wf, wfe, wNE, wfe2⟩⟩ := sizes_rd R
  rw [claimsA_eq c "LR" rfl]
  have h := retCl_mapM (lay := c.wsLay)
    (f := fun i => c.claim 11 (2 * i + 1) fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else c.facEw G "LR" 0)
    (List.range c.v.y.LamM) fun i hi => by
    have hi' := R.odd i (List.mem_range.mp hi)
    have hl : c.v.lay (2 * i + 1) % 2 = 1 := by
      rw [R.par]
      omega
    exact claimA_one R (k := 9) (Rk := s.d) (Rx := s.NE) hi' (by rw [kinds_odd hl]; rfl) rfl R.sLR
      d0 NE0 dle R.bd wNE
  rw [List.length_range] at h
  exact h

/-- **The claims of the routed product G.** -/
theorem claimsT_G (R : ClaimRd c s P lk) : RetCl c.wsLay (c.claimsT "G") c.v.y.LamM := by
  obtain ⟨⟨d0, dq0, dkv0, f0, fe0, NE0⟩, ⟨dle, dqle, fle, fef, fele, NEle⟩,
    ⟨wd, wdkv, wf, wfe, wNE, wfe2⟩⟩ := sizes_rd R
  rw [claimsT_routed_eq c "G" R.p3 (Or.inl rfl)]
  have h := retCl_mapM (lay := c.wsLay)
    (f := fun lm => c.claim 7 (2 * lm + 1) fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else if G.name == "e" then c.facRs G (ceilLog2 c.v.y.h.d) (ceilLog2 (max c.v.y.h.NE 1))
      else c.facEw G "G" c.v.y.h.fe)
    (List.range c.v.y.LamM) fun i hi => by
    have hi' := R.odd i (List.mem_range.mp hi)
    have hl : c.v.lay (2 * i + 1) % 2 = 1 := by
      rw [R.par]
      omega
    exact claimT_one R (k := 5) (Rk := s.d) (Re := s.NE) (Rx := s.fe) hi'
      (by rw [kinds_odd hl]; rfl) rfl R.sG d0 NE0 fe0 dle NEle R.bde wfe2
  rw [List.length_range] at h
  exact h

/-- **The claims of the routed product U.** -/
theorem claimsT_U (R : ClaimRd c s P lk) : RetCl c.wsLay (c.claimsT "U") c.v.y.LamM := by
  obtain ⟨⟨d0, dq0, dkv0, f0, fe0, NE0⟩, ⟨dle, dqle, fle, fef, fele, NEle⟩,
    ⟨wd, wdkv, wf, wfe, wNE, wfe2⟩⟩ := sizes_rd R
  rw [claimsT_routed_eq c "U" R.p3 (Or.inr (Or.inl rfl))]
  have h := retCl_mapM (lay := c.wsLay)
    (f := fun lm => c.claim 8 (2 * lm + 1) fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else if G.name == "e" then c.facRs G (ceilLog2 c.v.y.h.d) (ceilLog2 (max c.v.y.h.NE 1))
      else c.facEw G "U" c.v.y.h.fe)
    (List.range c.v.y.LamM) fun i hi => by
    have hi' := R.odd i (List.mem_range.mp hi)
    have hl : c.v.lay (2 * i + 1) % 2 = 1 := by
      rw [R.par]
      omega
    exact claimT_one R (k := 6) (Rk := s.d) (Re := s.NE) (Rx := s.fe) hi'
      (by rw [kinds_odd hl]; rfl) rfl R.sU d0 NE0 fe0 dle NEle R.bde wfe2
  rw [List.length_range] at h
  exact h

/-- **The claims of the routed product D.** -/
theorem claimsT_D (R : ClaimRd c s P lk) : RetCl c.wsLay (c.claimsT "D") c.v.y.LamM := by
  obtain ⟨⟨d0, dq0, dkv0, f0, fe0, NE0⟩, ⟨dle, dqle, fle, fef, fele, NEle⟩,
    ⟨wd, wdkv, wf, wfe, wNE, wfe2⟩⟩ := sizes_rd R
  rw [claimsT_routed_eq c "D" R.p3 (Or.inr (Or.inr rfl))]
  have h := retCl_mapM (lay := c.wsLay)
    (f := fun lm => c.claim 10 (2 * lm + 1) fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.fe)
      else if G.name == "e" then c.facRs G (ceilLog2 c.v.y.h.fe) (ceilLog2 (max c.v.y.h.NE 1))
      else c.facEw G "D" 0)
    (List.range c.v.y.LamM) fun i hi => by
    have hi' := R.odd i (List.mem_range.mp hi)
    have hl : c.v.lay (2 * i + 1) % 2 = 1 := by
      rw [R.par]
      omega
    exact claimT_one R (k := 8) (Rk := s.fe) (Re := s.NE) (Rx := s.d) hi'
      (by rw [kinds_odd hl]; rfl) rfl R.sD fe0 NE0 d0 fele NEle R.bfe wd
  rw [List.length_range] at h
  exact h

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.kinds_even
#print axioms OnBytes.Road.K4.C.kinds_odd
#print axioms OnBytes.Road.K4.C.isMoe_odd
#print axioms OnBytes.Road.K4.C.isMoe_even
#print axioms OnBytes.Road.K4.C.sizes_rd
#print axioms OnBytes.Road.K4.C.claimsA_G
#print axioms OnBytes.Road.K4.C.claimsA_U
#print axioms OnBytes.Road.K4.C.claimsA_V
#print axioms OnBytes.Road.K4.C.claimsA_O
#print axioms OnBytes.Road.K4.C.claimsA_D
#print axioms OnBytes.Road.K4.C.claimsA_LR
#print axioms OnBytes.Road.K4.C.claimsT_G
#print axioms OnBytes.Road.K4.C.claimsT_U
#print axioms OnBytes.Road.K4.C.claimsT_D
