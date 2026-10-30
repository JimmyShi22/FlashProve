-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ClaimsKit.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the weight claims: the kit for «the list of
claims of a segment returns, and each claim passes the merge's two tests on a claim». The
verifier's two rules for a claim's factors (OnBytes/Model/LayerPanels.lean: claimsA's, on the groups
kk and x; claimsT's for a routed product, on kk, e and x) return fitting factors on each group of
the asked unit; so one claim of either kind returns and is good (claimA_one, claimT_one), by
claim_some (ClaimReturn.lean) over facRs_some and facEw_some (FacsReturn.lean). Four definitions of
hypotheses; statements and proofs. General in the sizes.

  `SegRd c sn W`    some call holds segment sn, with W entries, its columns in the call, the call's
                    point has its column coordinates, and the call has room for W columns.
  `GoodCl`, `RetCl` a claim that passes the two tests; a list of n such claims is returned.
  `ClaimRd`         the layout of the weights, its ties to the layers' shape, the bits, the
                    segments; and what the limits below name.
  `le_pow_ceil`, `rs_rule`, `ew_rule`, `rule_two`, `rule_three`, `retCl_mapM`, `moe_at`   steps.
  **`claimA_one`**, **`claimT_one`**   one claim.

Not shown here. That the hypotheses hold at any plan or layout of the weights: no example is shown
here. WHO HAS ClaimRd: ClaimRdOf.lean (claimRd_of), AT THE BLANK STRUCTURE ALONE, where every
challenge and coordinate is 0; at a structure with sampled challenges no statement has it. AT A
LAYOUT OF THE WEIGHTS THAT wsLayOf RETURNS FOR A MODEL WITH ROUTED EXPERTS. ClaimRd also asks: that
the dense width is twice an expert's (f = 2 fe); switch p3 on; each routed layer's number in the
group; five sizes at least one. The unit of queries and keys (kind 0) and the embedding's are not
here. Public data alone: whether a claim IS THERE and how long its parts are; nothing on its
elements.
No property is claimed.
-/
import Johnson.Road.K4.C.FacsReturn
import Johnson.Road.K4.C.ClaimReturn
import Johnson.Road.K4.C.AskGroups
import Johnson.Road.FormsKeysPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv)
open Inst.Model (Params)

/-- **Some call holds segment sn**, with W entries; its columns lie in the call; the call's point
has its column coordinates; the call has room for W columns. This defines a hypothesis; the
definition claims nothing. -/
def SegRd (c : ClaimEnv) (sn : String) (W : ℕ) : Prop :=
  ∃ q cd sg, c.v.callOf sn = some (q, cd, sg) ∧ sg.pos.size = W ∧
    (∀ j ∈ sg.pos.toList, j < 2 ^ cd.lJ) ∧ (c.v.zj q cd.lJ).size = cd.lJ ∧ W ≤ 2 ^ cd.lJ

/-- A claim on a unit of the layout, with the sizes that the layout asks. This defines a
hypothesis; the definition claims nothing. -/
def GoodCl (lay : WsLay) (cl : WsClaim) : Prop :=
  cl.ui < lay.U.size ∧ (wsClaimShape lay cl).isOk = true

/-- A list of n good claims is returned. This defines a hypothesis; the definition claims
nothing. -/
def RetCl (lay : WsLay) (x : Option (List WsClaim)) (n : ℕ) : Prop :=
  ∃ l, x = some l ∧ l.length = n ∧ ∀ cl ∈ l, GoodCl lay cl

/-- A number is at most two to its rounded-up logarithm. -/
theorem le_pow_ceil (n : ℕ) : n ≤ 2 ^ ceilLog2 n := by
  rw [ceilLog2_eq_clog]
  exact Nat.le_pow_clog (by norm_num) n

/-- The factor on the place's bits, from a group whose numbers fit. -/
theorem rs_rule {c : ClaimEnv} {G : WsGrp} {lo0 w : ℕ} (hok : GrpOK G) (hE : G.cls = 'E')
    (h0 : 0 < G.R) (hle : G.R ≤ 2 ^ w) (hrs : lo0 + w ≤ c.rs.size) :
    ∃ f, c.facRs G lo0 w = some f ∧ f.fits G = true :=
  facRs_some hE (grpE hok hE) h0 hle hrs

/-- The factor on a segment's entries, from a group whose numbers fit. -/
theorem ew_rule {c : ClaimEnv} {G : WsGrp} {sn : String} {x0 W : ℕ} (Sg : SegRd c sn W)
    (hok : GrpOK G) (hE : G.cls = 'E') (h0 : 0 < G.R) (hx : x0 + G.R ≤ W) :
    ∃ f, c.facEw G sn x0 = some f ∧ f.fits G = true := by
  obtain ⟨q, cd, sg, hc, hs, hJ, hz, hW⟩ := Sg
  have hR := grpE hok hE
  exact facEw_some hc hE hR (grp_bits hR h0 (by omega)).1 (by rw [hs]; exact hx) hJ hz

/-- **The rule of the first walk's claims**, on a unit with the groups kk and x. -/
theorem rule_two {c : ClaimEnv} {sn : String} {wy x0 W Rk Rx : ℕ} (Sg : SegRd c sn W)
    (hk0 : 0 < Rk) (hx0 : 0 < Rx) (hk : Rk ≤ 2 ^ wy) (hrs : wy ≤ c.rs.size) (hx : x0 + Rx ≤ W)
    {G : WsGrp} (hm : (G.name, G.R, G.cls) ∈ [("kk", Rk, 'E'), ("x", Rx, 'E')]) (hok : GrpOK G) :
    ∃ f, (if G.name == "kk" then c.facRs G 0 wy else c.facEw G sn x0) = some f ∧
      f.fits G = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨n, r, e⟩ | ⟨n, r, e⟩
  · have hn : (G.name == "kk") = true := by
      rw [n]
      rfl
    rw [if_pos hn]
    exact rs_rule hok e (by rw [r]; exact hk0) (by rw [r]; exact hk) (by omega)
  · have hn : ¬ (G.name == "kk") = true := by
      rw [n]
      decide
    rw [if_neg hn]
    exact ew_rule Sg hok e (by rw [r]; exact hx0) (by rw [r]; exact hx)

/-- **The rule of a routed product's claims**, on a unit with the groups kk, e and x. -/
theorem rule_three {c : ClaimEnv} {sn : String} {wk we x0 W Rk Re Rx : ℕ} (Sg : SegRd c sn W)
    (hk0 : 0 < Rk) (he0 : 0 < Re) (hx0 : 0 < Rx) (hk : Rk ≤ 2 ^ wk) (he : Re ≤ 2 ^ we)
    (hrs : wk + we ≤ c.rs.size) (hx : x0 + Rx ≤ W) {G : WsGrp}
    (hm : (G.name, G.R, G.cls) ∈ [("kk", Rk, 'E'), ("e", Re, 'E'), ("x", Rx, 'E')])
    (hok : GrpOK G) :
    ∃ f, (if G.name == "kk" then c.facRs G 0 wk
      else if G.name == "e" then c.facRs G wk we else c.facEw G sn x0) = some f ∧
      f.fits G = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨n, r, e⟩ | ⟨n, r, e⟩ | ⟨n, r, e⟩
  · have hn : (G.name == "kk") = true := by
      rw [n]
      rfl
    rw [if_pos hn]
    exact rs_rule hok e (by rw [r]; exact hk0) (by rw [r]; exact hk) (by omega)
  · have hn : ¬ (G.name == "kk") = true := by
      rw [n]
      decide
    have hn2 : (G.name == "e") = true := by
      rw [n]
      rfl
    rw [if_neg hn, if_pos hn2]
    exact rs_rule hok e (by rw [r]; exact he0) (by rw [r]; exact he) hrs
  · have hn : ¬ (G.name == "kk") = true := by
      rw [n]
      decide
    have hn2 : ¬ (G.name == "e") = true := by
      rw [n]
      decide
    rw [if_neg hn, if_neg hn2]
    exact ew_rule Sg hok e (by rw [r]; exact hx0) (by rw [r]; exact hx)

/-- Good claims, member by member: the list of them is returned. -/
theorem retCl_mapM {α : Type} {lay : WsLay} {f : α → Option WsClaim} : ∀ (l : List α),
    (∀ a ∈ l, ∃ cl, f a = some cl ∧ GoodCl lay cl) → RetCl lay (l.mapM f) l.length
  | [], _ => ⟨[], rfl, rfl, fun _ h => by cases h⟩
  | a :: l, h => by
    obtain ⟨cl, h1, g1⟩ := h a List.mem_cons_self
    obtain ⟨r, h2, h3, h4⟩ := retCl_mapM l fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨cl :: r, ?_, ?_, fun x hx => ?_⟩
    · rw [List.mapM_cons, h1, h2]
      rfl
    · rw [List.length_cons, List.length_cons, h3]
    · rcases List.mem_cons.mp hx with e | hx
      · rw [e]
        exact g1
      · exact h4 x hx

/-- **The layout of the weights, its ties to the layers' shape, the bits, the segments.** lays: the
group's layers are layers of the model. par: a layer's number in the model is odd just where its
number in the group is. p3: the switch is on. odd: each routed layer's number lies in the group. d0
to NE0: five sizes are at least one. ffe: the dense width is twice an expert's. This defines a
hypothesis; the definition claims nothing. -/
structure ClaimRd (c : ClaimEnv) (s : WsShape) (P : Params) (lk : ℕ) : Prop where
  Z : SizedW s P
  hlw : wsLayOf s true lk = .ok c.wsLay
  p3 : c.v.y.h.p3 = true
  lays : ∀ lam, lam < c.v.y.Lam → c.v.lay lam < P.layers
  par : ∀ lam, c.v.lay lam % 2 = lam % 2
  odd : ∀ i, i < c.v.y.LamM → 2 * i + 1 < c.v.y.Lam
  d : s.d = c.v.y.h.d
  dq : s.dq = c.v.y.dq
  dkv : s.dkv = c.v.y.dkv
  f : s.f = c.v.y.h.f
  fe : s.fe = c.v.y.h.fe
  NE : s.NE = c.v.y.h.NE
  d0 : 0 < c.v.y.h.d
  dq0 : 0 < c.v.y.dq
  dkv0 : 0 < c.v.y.dkv
  fe0 : 0 < c.v.y.h.fe
  NE0 : 0 < c.v.y.h.NE
  ffe : c.v.y.h.f = 2 * c.v.y.h.fe
  bd : ceilLog2 c.v.y.h.d ≤ c.rs.size
  bdq : ceilLog2 c.v.y.dq ≤ c.rs.size
  bf : ceilLog2 c.v.y.h.f ≤ c.rs.size
  bde : ceilLog2 c.v.y.h.d + ceilLog2 (max c.v.y.h.NE 1) ≤ c.rs.size
  bfe : ceilLog2 c.v.y.h.fe + ceilLog2 (max c.v.y.h.NE 1) ≤ c.rs.size
  sG : SegRd c "G" c.v.y.h.f
  sU : SegRd c "U" c.v.y.h.f
  sV : SegRd c "V" c.v.y.dkv
  sO : SegRd c "O" c.v.y.h.d
  sD : SegRd c "D" c.v.y.h.d
  sLR : SegRd c "LR" c.v.y.h.NE

variable {c : ClaimEnv} {s : WsShape} {P : Params} {lk : ℕ}

/-- Which layers of the model are mixtures of experts, in the shape for which the layout is
built. -/
theorem moe_at (R : ClaimRd c s P lk) {l : ℕ} (hl : l < P.layers) :
    (shapeOf s true).moe.getD l false = (l % 2 == 1) := by
  obtain ⟨-, -, -, B⟩ := wsLayOf_units R.hlw
  have hL : (shapeOf s true).L = P.layers := R.Z.L
  rw [B.moe l (by rw [hL]; exact hl)]
  rfl

/-- **One claim of the first walk returns and is good.** -/
theorem claimA_one (R : ClaimRd c s P lk) {sn : String} {lam X k wy W Rk Rx : ℕ}
    (hl : lam < c.v.y.Lam) (hX : (kindsOf (c.v.lay lam))[k]? = some X)
    (hask : askRs (shapeOf s true) (c.v.lay lam) X = [("kk", Rk, 'E'), ("x", Rx, 'E')])
    (Sg : SegRd c sn W) (hk0 : 0 < Rk) (hx0 : 0 < Rx) (hk : Rk ≤ 2 ^ wy)
    (hrs : wy ≤ c.rs.size) (hx : 0 + Rx ≤ W) :
    ∃ cl, c.claim X lam (fun G => if G.name == "kk" then c.facRs G 0 wy
      else c.facEw G sn 0) = some cl ∧ GoodCl c.wsLay cl :=
  claim_some R.Z R.hlw (R.lays lam hl) hX fun a ha eX G hG hok =>
    rule_two Sg hk0 hx0 hk hrs hx (by
      have h1 := grp_in_ask ha hG
      rw [eX, hask] at h1
      exact h1) hok

/-- **One claim of a routed product returns and is good.** -/
theorem claimT_one (R : ClaimRd c s P lk) {sn : String} {lam X k wk we x0 W Rk Re Rx : ℕ}
    (hl : lam < c.v.y.Lam) (hX : (kindsOf (c.v.lay lam))[k]? = some X)
    (hask : askRs (shapeOf s true) (c.v.lay lam) X =
      [("kk", Rk, 'E'), ("e", Re, 'E'), ("x", Rx, 'E')])
    (Sg : SegRd c sn W) (hk0 : 0 < Rk) (he0 : 0 < Re) (hx0 : 0 < Rx) (hk : Rk ≤ 2 ^ wk)
    (he : Re ≤ 2 ^ we) (hrs : wk + we ≤ c.rs.size) (hx : x0 + Rx ≤ W) :
    ∃ cl, c.claim X lam (fun G => if G.name == "kk" then c.facRs G 0 wk
      else if G.name == "e" then c.facRs G wk we else c.facEw G sn x0) = some cl ∧
      GoodCl c.wsLay cl :=
  claim_some R.Z R.hlw (R.lays lam hl) hX fun a ha eX G hG hok =>
    rule_three Sg hk0 he0 hx0 hk he hrs hx (by
      have h1 := grp_in_ask ha hG
      rw [eX, hask] at h1
      exact h1) hok

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.le_pow_ceil
#print axioms OnBytes.Road.K4.C.rs_rule
#print axioms OnBytes.Road.K4.C.ew_rule
#print axioms OnBytes.Road.K4.C.rule_two
#print axioms OnBytes.Road.K4.C.rule_three
#print axioms OnBytes.Road.K4.C.retCl_mapM
#print axioms OnBytes.Road.K4.C.moe_at
#print axioms OnBytes.Road.K4.C.claimA_one
#print axioms OnBytes.Road.K4.C.claimT_one
