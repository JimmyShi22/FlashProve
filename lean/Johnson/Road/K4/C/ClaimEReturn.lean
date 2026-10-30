-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ClaimEReturn.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the weight claims: THE EMBEDDING's CLAIM
RETURNS (claimE, OnBytes/Model/LayerPanels.lean), on a unit of the layout of the weights and with
the sizes that the layout asks. Its unit is the one that the layout adds behind the layers' units
(kind 12), with a group for the vocabulary and a group for the stream's width; the factor on the
first has an entry for each token of the vocabulary, the factor on the second is read off an
equality table of the point's coordinates. Three definitions; statements and proofs. General in the
sizes.

  `bind_eq_at`, `psi_size`   a step in Option; the factor on the vocabulary has V entries.
  `psiOf`, `embRule`, `ask12`   the factor on the vocabulary; the rule for the factors; what the
                    layout is asked to add.
  `unit12_there`    the embedding's unit is found, with its two groups.
  **`claimE_ret`**   the claim.

Not shown here. That the hypotheses hold at any plan: no example is shown here. AT A LAYOUT OF THE
WEIGHTS THAT wsLayOf RETURNS FOR A MODEL WITH ROUTED EXPERTS. Public data alone: whether the claim
IS THERE and how long its parts are; nothing on its elements. No property is claimed.
-/
import Johnson.Road.K4.C.ClaimsKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv)

/-- A step in Option at a known value. -/
theorem bind_eq_at {α β : Type} {x : Option α} {f : α → Option β} {a : α} {b : β} (e : x = some a)
    (h : f a = some b) : (x >>= f) = some b := by
  subst e
  exact h

/-- The factor on the vocabulary has V entries. -/
theorem psi_size (V : ℕ) (tokv : Array ℕ) (et : Array E) : ∀ (l : List ℕ) (a : Array E),
    a.size = V → (l.foldl (fun (a : Array E) t =>
      a.modify (tokv.getD t 0) fun x => addE x (et.getD t zeroE)) a).size = V
  | [], _, h => h
  | t :: l, a, h => by
    rw [List.foldl_cons]
    exact psi_size V tokv et l _ (by rw [Array.size_modify]; exact h)

/-- The factor on the vocabulary: each token's id gets the weight of its positions. The verifier's
text, where it has no name (the library names the same function embPsi,
OnBytes/Tie/Pv/Lay/EmbClaim.lean). -/
def psiOf (V T : ℕ) (tokv : Array ℕ) (et : Array E) : Array E :=
  (List.range T).foldl
    (fun (a : Array E) t => a.modify (tokv.getD t 0) fun x => addE x (et.getD t zeroE))
    (Array.replicate V zeroE)

/-- The rule for the factors of the embedding's claim. pnt: the coordinates of the feature; tok:
those of the token. The verifier's text, where it has no name. -/
def embRule (lPd T V : ℕ) (tokv : Array ℕ) (pnt tok : Array E) (G : WsGrp) : Option WsFac :=
  if G.name == "v" then some { AV := psiOf V T tokv (eqTab tok) }
  else if G.z > lPd then none
  else do
    let HV ← (Array.range G.o).mapM fun hi => (eqTab (pnt.extract 0 (lPd - G.z)))[hi]?
    pure { pt := (Array.range G.z).map fun i => pnt.getD (lPd - G.z + i) zeroE, HV := HV }

/-- What the layout is asked to add for the embedding. -/
def ask12 (s : WsShape) : AskW := ⟨12, s.L, 4, [WsLay.A_ "v" s.V, WsLay.E_ "x" s.d true]⟩

/-- **The embedding's unit is found**: its number is a unit's, its groups' numbers fit each other,
and each group is the vocabulary's or the stream's width's. -/
theorem unit12_there {s : WsShape} {lk : ℕ} {lay : WsLay} (h : wsLayOf s true lk = .ok lay) :
    ∃ ui u, lay.unitOf 12 s.L = some ui ∧ lay.U[ui]? = some u ∧ (∀ G ∈ u.g, GrpOK G) ∧
      ∀ G ∈ u.g, (G.name, G.R, G.cls) ∈ [("v", s.V, 'A'), ("x", s.d, 'E')] := by
  have hm : ask12 (shapeOf s true) ∈ allAsks (shapeOf s true) := by
    unfold allAsks
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hm
  obtain ⟨-, h2, -, -⟩ := wsLayOf_units h
  obtain ⟨o, hU⟩ : ∃ o, lay.U[n]? = some (unitP lk o (ask12 (shapeOf s true))) :=
    ⟨_, by rw [← Array.getElem?_toList, h2]; exact unitsFrom_get lk _ 0 _ _ hn⟩
  refine ⟨n, _, unitOf_ask h hn, hU,
    ((unitOK_of_layout h).2 _ (Array.mem_of_getElem? hU)).1.grp, fun G hG => ?_⟩
  have h3 := List.mem_map_of_mem (f := fun y : WsGrp => (y.name, y.R, y.cls)) hG
  have h4 : (placeP [WsLay.A_ "v" (shapeOf s true).V, WsLay.E_ "x" (shapeOf s true).d true]
      lk 0).map (fun y => (y.name, y.R, y.cls)) = [("v", s.V, 'A'), ("x", s.d, 'E')] := by
    rw [placed_three]
    rfl
  rw [← h4]
  exact h3

/-- **THE EMBEDDING's CLAIM RETURNS AND IS GOOD.** CONDITIONAL: on the layout of the weights (hlw)
and its ties to the layers' shape (hL, hd); on T tokens below V, the vocabulary's size in the
weights' shape; on the sizes of the two parts of the point (hZE, htk); and on the bits of the
stream's width (hlPd, hls). -/
theorem claimE_ret {c : ClaimEnv} {s : WsShape} {lk : ℕ} (hlw : wsLayOf s true lk = .ok c.wsLay)
    (hL : s.L = c.v.y.h.L) (hd : s.d = c.v.y.h.d) (d0 : 0 < c.v.y.h.d)
    (hlPd : c.v.y.lPd = ceilLog2 c.v.y.h.d) (hls : c.v.y.ls ≤ c.v.y.lPd) {ZE tkh : Array E}
    {tokv : Array ℕ} (hT : tokv.size = c.v.y.T) (hV : ∀ t ∈ tokv.toList, t < s.V)
    (hZE : ZE.size = c.v.y.ls + c.v.y.h.lt) (htk : tkh.size = c.v.y.lPd - c.v.y.ls) :
    ∃ cl, c.claimE ZE tkh s.V tokv = some cl ∧ GoodCl c.wsLay cl := by
  obtain ⟨ui, u, h1, h2, hok, hg⟩ := unit12_there hlw
  rw [hL] at h1
  have hc0 : (tokv.size != c.v.y.T || tokv.any (· ≥ s.V)) = false := by
    rw [Bool.or_eq_false_iff]
    refine ⟨by rw [hT]; simp, ?_⟩
    rw [Array.any_eq_false']
    intro t ht
    have := hV t (Array.mem_toList_iff.mpr ht)
    simp
    omega
  have hcut : (cutLast ZE c.v.y.h.lt).toOption =
      some (ZE.extract 0 (ZE.size - c.v.y.h.lt), ZE.extract (ZE.size - c.v.y.h.lt) ZE.size) := by
    unfold cutLast
    rw [if_neg (by omega)]
    rfl
  have hpn : (tkh ++ ZE.extract 0 (ZE.size - c.v.y.h.lt)).size = c.v.y.lPd := by
    rw [Array.size_append, Array.size_extract, htk]
    omega
  obtain ⟨fs, f1, f2, f3⟩ := mapM_fits (fac := embRule c.v.y.lPd c.v.y.T s.V tokv
      (tkh ++ ZE.extract 0 (ZE.size - c.v.y.h.lt)) (ZE.extract (ZE.size - c.v.y.h.lt) ZE.size))
      u.g fun G hG => by
    unfold embRule
    have hm := hg G hG
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨n, r, e⟩ | ⟨n, r, e⟩
    · have hn : (G.name == "v") = true := by
        rw [n]
        rfl
      rw [if_pos hn]
      refine ⟨_, rfl, ?_⟩
      unfold WsFac.fits
      rw [e, r]
      show (((psiOf s.V c.v.y.T tokv _).size == s.V && (#[] : Array E).isEmpty) &&
        (#[] : Array E).isEmpty) = true
      unfold psiOf
      rw [psi_size s.V tokv _ _ _ Array.size_replicate, beq_self_eq_true]
      rfl
    · have hn : ¬ (G.name == "v") = true := by
        rw [n]
        decide
      have hR := grpE (hok G hG) e
      obtain ⟨hz, ho⟩ := grp_bits (w := c.v.y.lPd) hR (by rw [r, hd]; exact d0)
        (by rw [r, hd, hlPd]; exact le_pow_ceil _)
      have hsz : (eqTab ((tkh ++ ZE.extract 0 (ZE.size - c.v.y.h.lt)).extract 0
          (c.v.y.lPd - G.z))).size = 2 ^ (c.v.y.lPd - G.z) := by
        rw [eqTab_size, Array.size_extract, hpn, Nat.min_eq_left (Nat.sub_le _ _), Nat.sub_zero]
      obtain ⟨HV, hHV, hs⟩ := range_get_some (eqTab ((tkh ++
        ZE.extract 0 (ZE.size - c.v.y.h.lt)).extract 0 (c.v.y.lPd - G.z))) (n := G.o)
        (by rw [hsz]; exact ho)
      rw [if_neg hn, if_neg (by omega), hHV]
      refine ⟨_, rfl, ?_⟩
      unfold WsFac.fits
      rw [e]
      show ((HV.size == G.o && ((Array.range G.z).map _).size == G.z) &&
        (#[] : Array E).isEmpty) = true
      rw [hs, Array.size_map, Array.size_range]
      simp
  refine ⟨{ ui := ui, f := fs }, ?_, (Array.getElem?_eq_some_iff.mp h2).1, ?_⟩
  · unfold ClaimEnv.claimE
    dsimp only
    rw [hc0, if_neg Bool.false_ne_true]
    refine bind_eq_at (a := PUnit.unit) rfl ?_
    refine bind_eq_at h1 ?_
    refine bind_eq_at h2 ?_
    refine bind_eq_at hcut ?_
    dsimp only
    exact bind_eq_at f1 rfl
  · unfold wsClaimShape
    show (match c.wsLay.U[ui]? with
      | none => throw "internal-claim-unit"
      | some u =>
        if (fs.length == u.g.length && ((fs.zip u.g).all fun y => y.1.fits y.2)) = true then
          pure ()
        else throw "internal-claim-factors" : Except String Unit).isOk = true
    rw [h2]
    show (if (fs.length == u.g.length && ((fs.zip u.g).all fun y => y.1.fits y.2)) = true then
      pure () else throw "internal-claim-factors" : Except String Unit).isOk = true
    rw [f2, f3, beq_self_eq_true]
    rfl

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.bind_eq_at
#print axioms OnBytes.Road.K4.C.psi_size
#print axioms OnBytes.Road.K4.C.unit12_there
#print axioms OnBytes.Road.K4.C.claimE_ret
