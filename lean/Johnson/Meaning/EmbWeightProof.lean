-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/EmbWeightProof.lean: the proofs of the two statements of
Johnson/Meaning/EmbWeight.lean, after the pattern of claimVal_head
(Johnson/Road/HeadWeight.lean:221).

The steps. claimE_inv: what a claim that claimE returns is made of. psi_value: the factor on the
vocabulary in closed form: entry v adds up the positions' weights over the positions with token v.
facE_at: the factor on the features weighs feature j with entry j of the table of equality weights
of the whole point tkh ++ low. emb_unit, units_emb: the verifier's and the library's unit. Then
claimVal_Tn_of_layout (Johnson/Road/FormsKeysTnP.lean) and two identities on sums (sum_blocks,
sum_side). EmbNums.blocks_le: the number of blocks is at most 2^(lPd - ls).
-/
import Johnson.Meaning.EmbWeight

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.Emb

open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv Lay)
open Inst.Model (ppref TClaim entryW)
open Inst.Model.Layout (kRef units uEmb uH layerUnits first place)
open Inst.Model.FFSeg (embR)

/-! ## What claimE returns -/

/-- The factor on the vocabulary: each token's id gets the weight of its positions. -/
def psiOf (V : ℕ) (tokv : Array ℕ) (et : Array E) (n : ℕ) : Array E :=
  (List.range n).foldl
    (fun (a : Array E) t => a.modify (tokv.getD t 0) fun x => addE x (et.getD t zeroE))
    (Array.replicate V zeroE)

/-- The factor that claimE makes for a group. -/
def facE (lPd : ℕ) (pnt psi : Array E) (G : WsGrp) : Option WsFac :=
  if G.name == "v" then some ({ AV := psi } : WsFac)
  else if G.z > lPd then none
  else do
    let e := eqTab (pnt.extract 0 (lPd - G.z))
    let HV ← (Array.range G.o).mapM fun hi => e[hi]?
    pure { pt := (Array.range G.z).map fun i => pnt.getD (lPd - G.z + i) zeroE, HV }

/-- What a claim that claimE returns is made of. -/
theorem claimE_inv {c : ClaimEnv} {ZE tkh : Array E} {V : ℕ} {tokv : Array ℕ} {cl : WsClaim}
    (h : c.claimE ZE tkh V tokv = some cl) :
    tokv.size = c.v.y.T ∧ (∀ t, t < tokv.size → tokv.getD t 0 < V) ∧
    ∃ u p, c.wsLay.unitOf 12 c.v.y.h.L = some cl.ui ∧ c.wsLay.U[cl.ui]? = some u ∧
      (cutLast ZE c.v.y.h.lt).toOption = some p ∧
      u.g.mapM (facE c.v.y.lPd (tkh ++ p.1) (psiOf V tokv (eqTab p.2) c.v.y.T)) = some cl.f := by
  unfold ClaimEnv.claimE at h
  dsimp only at h
  by_cases hc : (tokv.size != c.v.y.T || tokv.any (· ≥ V)) = true
  · rw [if_pos hc] at h
    cases h
  rw [if_neg hc] at h
  rw [Bool.not_eq_true] at hc
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨ui, h1, h⟩ := bind_some h
  obtain ⟨u, h2, h⟩ := bind_some h
  obtain ⟨⟨low, tok⟩, h3, h⟩ := bind_some h
  obtain ⟨f, h4, h⟩ := bind_some h
  cases h
  rw [Bool.or_eq_false_iff] at hc
  refine ⟨by simpa using hc.1, fun t ht => ?_, u, (low, tok), h1, h2, h3, h4⟩
  have h5 := hc.2
  rw [Array.any_eq_false] at h5
  have h6 := h5 t ht
  simp only [ge_iff_le, decide_eq_true_eq, not_le] at h6
  simpa [Array.getD, ht] using h6

/-! ## The factor on the vocabulary -/

section Factors

variable {K : Type} [Field K] (ρ : Reading K)

/-- Its length, and its entries in closed form. -/
theorem psi_value (V : ℕ) (tokv : Array ℕ) (et : Array E) {v : ℕ} (hv : v < V) : ∀ n : ℕ,
    (psiOf V tokv et n).size = V ∧
    ρ.val ((psiOf V tokv et n).getD v zeroE) =
      ∑ t ∈ range n, if tokv.getD t 0 = v then ρ.val (et.getD t zeroE) else 0
  | 0 => ⟨by simp [psiOf], by simp [psiOf, Array.getD, hv, ρ.zero]⟩
  | n + 1 => by
    obtain ⟨i1, i2⟩ := psi_value V tokv et hv n
    have e : psiOf V tokv et (n + 1) =
        (psiOf V tokv et n).modify (tokv.getD n 0) fun x => addE x (et.getD n zeroE) := by
      unfold psiOf
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [e]
    refine ⟨Array.size_modify.trans i1, ?_⟩
    rw [Finset.sum_range_succ, ← i2]
    by_cases h2 : tokv.getD n 0 = v
    · rw [if_pos h2, h2, Hd.getD_modify_self _ _ (by rw [i1]; exact hv), ρ.add]
    · rw [if_neg h2, add_zero, Hd.getD_modify_ne _ _ h2 (by rw [i1]; exact hv)]

/-! ## The factor on the features -/

/-- The factor on a group of class 'E' that is not named "v" weighs index v with entry v of the
table of equality weights of the whole point. -/
theorem facE_at {lPd : ℕ} {pnt psi : Array E} {G : WsGrp} (hn : (G.name == "v") = false)
    (hE : (G.cls == 'E') = true) (hp : pnt.size = lPd) {X : WsFac}
    (h : facE lPd pnt psi G = some X) (v : ℕ) (hv : v < G.o * 2 ^ G.z) :
    facAt ρ X G v = ρ.val ((eqTab pnt).getD v zeroE) := by
  unfold facE at h
  rw [hn] at h
  simp only [Bool.false_eq_true, if_false] at h
  by_cases hz : G.z > lPd
  · rw [if_pos hz] at h
    cases h
  rw [if_neg hz] at h
  have hz' : G.z ≤ lPd := by omega
  obtain ⟨HV, hm, h3⟩ := bind_some h
  cases h3
  rw [Array.mapM_eq_mapM_toList, Array.toList_range] at hm
  obtain ⟨l, hl, hHV⟩ := map_some hm
  subst hHV
  have hpos : 0 < 2 ^ G.z := by positivity
  have hhi : v / 2 ^ G.z < G.o := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    exact hv
  have hr : v % 2 ^ G.z < 2 ^ G.z := Nat.mod_lt _ hpos
  have hsplit : 2 ^ G.z * (v / 2 ^ G.z) + v % 2 ^ G.z = v := Nat.div_add_mod v (2 ^ G.z)
  obtain ⟨b, hb, hf⟩ := (list_mapM_some _ _ l hl).2 (v / 2 ^ G.z) (v / 2 ^ G.z) (by simp [hhi])
  have hHVb : (l.toArray).getD (v / 2 ^ G.z) zeroE = b := getD_of_some (by simpa using hb) zeroE
  have hbe := getD_of_some hf zeroE
  have hzs : (pnt.extract 0 (lPd - G.z)).size = lPd - G.z := by
    rw [Array.size_extract]
    omega
  have hlt : v / 2 ^ G.z < 2 ^ (lPd - G.z) := by
    have h1 : v / 2 ^ G.z < (eqTab (pnt.extract 0 (lPd - G.z))).size := by
      by_contra hh
      rw [Array.getElem?_eq_none (by omega)] at hf
      cases hf
    rw [eqTab_size, hzs] at h1
    exact h1
  have hs := eqTab_split ρ pnt (pnt.extract 0 (lPd - G.z)) hp hz' hzs
    (fun j hj => Hd.getD_cut pnt (by omega) hj zeroE) hlt hr
  rw [hsplit] at hs
  rw [hs]
  unfold facAt
  rw [if_pos hE, hHVb, ← hbe]
  congr 1
  refine eqN_congr' _ _ (fun j hj => ?_) _
  unfold pt
  rw [Nat.zero_add, getD_map_lt _ _ (by simpa using hj) zeroE 0]
  simp [Array.getD, hj]

end Factors

/-! ## The embedding's unit -/

/-- What the layout of W asks for the embedding: kind 12, four digits, the vocabulary's index
written out, the features' index with its high bits first. It is the last member but one of allAsks
(Johnson/Road/FormsKeysWLay.lean). -/
def askE (S : WsShape) : AskW := ⟨12, S.L, 4, [WsLay.A_ "v" S.V, WsLay.E_ "x" S.d true]⟩

/-- The last unit but one of a layout that the verifier builds is the embedding's. -/
theorem emb_unit {s : WsShape} {p3 : Bool} {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s p3 lk = .ok lay) :
    ∃ o, lay.U[lay.U.size - 2]? = some (unitP lk o (askE (shapeOf s p3))) := by
  obtain ⟨_, h2, _, _⟩ := wsLayOf_units h
  generalize shapeOf s p3 = S at h2 ⊢
  have hlen : lay.U.size = ((List.range S.L).flatMap (layerAsks S)).length + 2 := by
    rw [← Array.length_toList, h2, unitsFrom_length]
    unfold allAsks
    rw [List.length_append]
    rfl
  have ha : (allAsks S)[((List.range S.L).flatMap (layerAsks S)).length]? = some (askE S) := by
    unfold allAsks
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  refine ⟨0 + (((allAsks S).take (((List.range S.L).flatMap (layerAsks S)).length)).map
    (rowsP lk)).sum, ?_⟩
  rw [hlen, Nat.add_sub_cancel, ← Array.getElem?_toList, h2]
  exact unitsFrom_get lk _ 0 _ _ ha

/-- The library's number of the embedding's unit. -/
theorem first_emb : first ppref ppref.layers = 384 := by
  have h := Inst.Model.Head.first_layers
  omega

/-- The library's list has the embedding at that number. -/
theorem units_emb : (units ppref)[384]? = some (uEmb ppref) := by
  have hl := Hd.units_layers
  unfold units
  rw [List.getElem?_append_right (le_of_eq hl), hl]
  rfl

/-- WHICH TABLE IS THE EMBEDDING's. -/
theorem embTable : Spec.embTable := by
  intro c s Z hl hL ZE tkh V tokv cl h
  obtain ⟨-, -, u, p, h1, -, -, -⟩ := claimE_inv h
  rw [hL, (unitOf_eq Z hl).2.1] at h1
  have hui : cl.ui = first ppref ppref.layers := (Option.some.inj h1).symm
  have hU : (units ppref)[cl.ui]? = some (uEmb ppref) := by
    rw [hui, first_emb]
    exact units_emb
  obtain ⟨-, -, -, hall⟩ := layout_eq Z hl
  obtain ⟨u', hu', -, hnl, -, -, -, -, -, hcell⟩ := hall cl.ui _ hU
  exact ⟨hui, hU, u', hu', hnl, hcell⟩

/-! ## An identity on sums -/

section Sums

variable {K : Type} [Field K]

/-- A sum over n blocks of m. -/
theorem sum_blocks (m : ℕ) (f : ℕ → K) : ∀ n : ℕ,
    ∑ j ∈ range (n * m), f j = ∑ kh ∈ range n, ∑ r ∈ range m, f (kh * m + r)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, sum_range_add, sum_blocks m f n, sum_range_succ]

/-- V entries of the vocabulary, nb blocks of 2^ls features, 2^lt positions. psi v adds up the
weights e of the positions with the token v; the weight w of a feature is its block's times its
place's in the block. The sum over the vocabulary and the features of psi v w j A v j is the sum
over blocks, places and positions of the weights times A at the position's token. -/
theorem sum_side (V nb ls lt : ℕ) (tok : ℕ → ℕ) (htok : ∀ p, p < 2 ^ lt → tok p < V)
    (psi w wk el e : ℕ → K) (A emb : ℕ → ℕ → K)
    (hpsi : ∀ v, v < V → psi v = ∑ t ∈ range (2 ^ lt), if tok t = v then e t else 0)
    (hw : ∀ kh, kh < nb → ∀ r, r < 2 ^ ls → w (kh * 2 ^ ls + r) = wk kh * el r)
    (hemb : ∀ v, v < V → ∀ j, j < nb * 2 ^ ls → emb v j = A v j) :
    ∑ v ∈ range V, ∑ j ∈ range (nb * 2 ^ ls), psi v * w j * A v j =
      ∑ kh ∈ range nb, wk kh * ∑ r ∈ range (2 ^ ls), el r *
        ∑ p ∈ range (2 ^ lt), e p * emb (tok p) (kh * 2 ^ ls + r) := by
  have hG : ∀ j, ∑ v ∈ range V, psi v * A v j = ∑ p ∈ range (2 ^ lt), e p * A (tok p) j := by
    intro j
    rw [sum_congr rfl fun v hv => by rw [hpsi v (mem_range.mp hv), sum_mul]]
    rw [sum_comm]
    refine sum_congr rfl fun t ht => ?_
    rw [sum_eq_single (tok t)]
    · rw [if_pos rfl]
    · intro v _ hne
      rw [if_neg (fun h => hne h.symm), zero_mul]
    · intro hn
      exact absurd (mem_range.mpr (htok t (mem_range.mp ht))) hn
  rw [sum_comm, sum_blocks]
  refine sum_congr rfl fun kh hkh => ?_
  rw [mul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hkh' := mem_range.mp hkh
  have hr' := mem_range.mp hr
  have hj : kh * 2 ^ ls + r < nb * 2 ^ ls := by
    have h1 : (kh + 1) * 2 ^ ls ≤ nb * 2 ^ ls := Nat.mul_le_mul_right _ hkh'
    rw [Nat.succ_mul] at h1
    omega
  have e1 : ∑ v ∈ range V, psi v * w (kh * 2 ^ ls + r) * A v (kh * 2 ^ ls + r) =
      w (kh * 2 ^ ls + r) * ∑ v ∈ range V, psi v * A v (kh * 2 ^ ls + r) := by
    rw [mul_sum]
    exact sum_congr rfl fun v _ => by ring
  rw [e1, hG, hw kh hkh' r hr', mul_assoc]
  congr 2
  exact sum_congr rfl fun p hp => by rw [hemb _ (htok p (mem_range.mp hp)) _ hj]

end Sums

/-! ## The law -/

/-- An entry of an array's tail. -/
theorem getD_from {α : Type} (z : Array α) {a j : ℕ} (hj : a + j < z.size) (d : α) :
    (z.extract a z.size).getD j d = z.getD (a + j) d := by
  have h1 : j < z.size - a := by omega
  simp [Array.getD, hj, h1]

/-- An entry of the first of two arrays. -/
theorem getD_left {α : Type} (a b : Array α) {j : ℕ} (hj : j < a.size) (d : α) :
    (a ++ b).getD j d = a.getD j d := by
  have h1 : j < a.size + b.size := by omega
  simp [Array.getD, hj, h1, Array.getElem_append_left]

/-- An entry of the second. -/
theorem getD_right {α : Type} (a b : Array α) (i : ℕ) (d : α) :
    (a ++ b).getD (a.size + i) d = b.getD i d := by
  by_cases h : i < b.size
  · simp [Array.getD, h, Array.getElem_append_right]
  · simp [Array.getD, h]

/-- The low bits and the odd part of the library's width. -/
theorem x_5120 : (WsLay.E_ "x" 5120 true).z = 10 ∧ (WsLay.E_ "x" 5120 true).o = 5 :=
  ⟨rfl, rfl⟩

/-- The two factors of a claim on the embedding's unit, with the vector on the vocabulary and the
point as letters. -/
theorem facs_emb {K : Type} [Field K] (ρ : Reading K) {S : WsShape} (hd : S.d = 5120) {o lPd : ℕ}
    {pnt psi : Array E} (hpnt : pnt.size = lPd) {Fs : List WsFac}
    (h4 : (unitP kRef o (askE S)).g.mapM (facE lPd pnt psi) = some Fs) :
    FacsAre ρ (Fs.zip (unitP kRef o (askE S)).g)
      [fun v => ρ.val (psi.getD v zeroE), fun j => ρ.val ((eqTab pnt).getD j zeroE)] := by
  have hg : (unitP kRef o (askE S)).g =
      [yP (WsLay.A_ "v" S.V) kRef 0,
       yP (WsLay.E_ "x" 5120 true) (kRef - tP (WsLay.A_ "v" S.V) kRef)
        (0 + tP (WsLay.A_ "v" S.V) kRef)] := by
    rw [← hd]
    rfl
  rw [hg] at h4 ⊢
  refine facs_two h4 (fun X hX v _ => ?_) (fun X hX v hv => ?_)
  · have e1 : X = { AV := psi } := by
      have hn1 : ((yP (WsLay.A_ "v" S.V) kRef 0).name == "v") = true := by
        show (("v" : String) == "v") = true
        decide
      unfold facE at hX
      rw [if_pos hn1] at hX
      exact (Option.some.inj hX).symm
    subst e1
    rfl
  · have hn2 : ((yP (WsLay.E_ "x" 5120 true) (kRef - tP (WsLay.A_ "v" S.V) kRef)
        (0 + tP (WsLay.A_ "v" S.V) kRef)).name == "v") = false := by
      show (("x" : String) == "v") = false
      decide
    have hv' : v < 5 * 2 ^ 10 := hv
    exact facE_at ρ hn2 rfl hpnt hX v hv'

/-- THE LAW: hE of emb_side | emb_field. -/
theorem embWeight : Spec.embWeight := by
  intro K _ ρ c s Z hl N ZE tkh tokv cl hZ hk h M
  obtain ⟨hsz, htok, u, ⟨low, tok⟩, h1, h2, h3, h4⟩ := claimE_inv h
  obtain ⟨-, hp⟩ := cutLast_some h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
  have hcut : ZE.size - c.v.y.h.lt = c.v.y.ls := by omega
  rw [hcut] at h4
  simp only at h4
  -- the unit
  rw [N.L, (unitOf_eq Z hl).2.1] at h1
  have hui : cl.ui = first ppref ppref.layers := (Option.some.inj h1).symm
  have hU : (units ppref)[cl.ui]? = some (uEmb ppref) := by
    rw [hui, first_emb]
    exact units_emb
  obtain ⟨-, hsize, -, -⟩ := layout_eq Z hl
  have hsize' : c.wsLay.U.size = 386 := hsize.trans Hd.units_head.1
  obtain ⟨o, hu⟩ := emb_unit hl
  have e384 : c.wsLay.U.size - 2 = 384 := by omega
  rw [e384, ← first_emb, ← hui, h2] at hu
  have eu := Option.some.inj hu
  have hd : (shapeOf s true).d = 5120 := Z.d
  -- the point
  have hlow : (ZE.extract 0 c.v.y.ls).size = c.v.y.ls := by
    rw [Array.size_extract]
    omega
  have htk : (ZE.extract c.v.y.ls ZE.size).size = c.v.y.h.lt := by
    rw [Array.size_extract]
    omega
  have hpnt : (tkh ++ ZE.extract 0 c.v.y.ls).size = c.v.y.lPd := by
    rw [Array.size_append, hlow, hk]
    have := N.ls
    omega
  -- the factor on the vocabulary, then as a letter
  have hΨ : ∀ v, v < ppref.V →
      ρ.val ((psiOf ppref.V tokv (eqTab (ZE.extract c.v.y.ls ZE.size)) c.v.y.T).getD v zeroE) =
        ∑ t ∈ range c.v.y.T, if tokv.getD t 0 = v then
          ρ.val ((eqTab (ZE.extract c.v.y.ls ZE.size)).getD t zeroE) else 0 :=
    fun v hv => (psi_value ρ ppref.V tokv _ hv c.v.y.T).2
  generalize psiOf ppref.V tokv (eqTab (ZE.extract c.v.y.ls ZE.size)) c.v.y.T = Ψ at h4 hΨ
  -- the factors
  have key : claimVal ρ c.wsLay M cl = (⟨cl.ui, uEmb ppref,
      [fun v => ρ.val (Ψ.getD v zeroE),
       fun j => ρ.val ((eqTab (tkh ++ ZE.extract 0 c.v.y.ls)).getD j zeroE)]⟩ :
        TClaim K).Tn ppref kRef M := by
    refine claimVal_Tn_of_layout ρ Z hl M hU fun u' hu' => ?_
    rw [h2] at hu'
    have e' := Option.some.inj hu'
    subst e'
    refine ⟨(list_mapM_some _ _ _ h4).1, ?_⟩
    subst eu
    exact facs_emb ρ hd hpnt h4
  have hb : c.v.y.h.d / c.v.y.S2 * 2 ^ c.v.y.ls = ppref.d := N.blocks.trans N.d
  have fin := sum_side ppref.V (c.v.y.h.d / c.v.y.S2) c.v.y.ls c.v.y.h.lt (fun p => tokv.getD p 0)
    (fun p hp => htok p (by rw [hsz, N.T]; exact hp))
    (fun v => ρ.val (Ψ.getD v zeroE))
    (fun j => ρ.val ((eqTab (tkh ++ ZE.extract 0 c.v.y.ls)).getD j zeroE))
    (fun kh => ρ.val ((eqTab tkh).getD kh zeroE))
    (Blocks.eqN c.v.y.ls 0 (pt ρ ZE))
    (Blocks.eqN c.v.y.h.lt 0 fun j => pt ρ ZE (c.v.y.ls + j))
    (fun v j => entryW ppref kRef M cl.ui (uEmb ppref) [v, j])
    (embR ppref kRef M) (fun v hv => ?_) (fun kh hkh r hr => ?_) (fun v hv j hj => ?_)
  · rw [hb] at fin
    unfold Rows.EmbWeight Rows.embSide Blocks.ext
    rw [key, TClaim.Tn_two ppref kRef M cl.ui (uEmb ppref) ⟨ppref.V, .whole⟩ ⟨ppref.d, .high⟩ rfl]
    exact fin
  · show ρ.val (Ψ.getD v zeroE) = ∑ t ∈ range (2 ^ c.v.y.h.lt), if tokv.getD t 0 = v then
      Blocks.eqN c.v.y.h.lt 0 (fun j => pt ρ ZE (c.v.y.ls + j)) t else 0
    rw [hΨ v hv, N.T]
    refine sum_congr rfl fun t ht => ?_
    rw [eqTab_value ρ _ t (by rw [htk]; exact mem_range.mp ht), htk]
    rw [eqN_congr' c.v.y.h.lt 0 (a' := fun j => pt ρ ZE (c.v.y.ls + j)) (fun j hj => ?_) t]
    unfold pt
    rw [getD_from ZE (by omega) zeroE]
  · show ρ.val ((eqTab (tkh ++ ZE.extract 0 c.v.y.ls)).getD (kh * 2 ^ c.v.y.ls + r) zeroE) =
      ρ.val ((eqTab tkh).getD kh zeroE) * Blocks.eqN c.v.y.ls 0 (pt ρ ZE) r
    have hQ : kh < 2 ^ (c.v.y.lPd - c.v.y.ls) := by
      have h5 : (kh + 1) * 2 ^ c.v.y.ls ≤ c.v.y.h.d / c.v.y.S2 * 2 ^ c.v.y.ls :=
        Nat.mul_le_mul_right _ hkh
      have h6 : 2 ^ c.v.y.lPd = 2 ^ (c.v.y.lPd - c.v.y.ls) * 2 ^ c.v.y.ls := by
        rw [← pow_add, Nat.sub_add_cancel N.ls]
      have h7 := N.cap
      rw [← N.blocks, h6] at h7
      exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_right (h5.trans h7) (by positivity))
    have hs := eqTab_split ρ (tkh ++ ZE.extract 0 c.v.y.ls) tkh hpnt N.ls hk
      (fun j hj => (getD_left tkh _ (by omega) zeroE).symm) hQ hr
    rw [Nat.mul_comm, hs]
    congr 1
    refine eqN_congr' _ _ (fun j hj => ?_) _
    unfold pt
    rw [← hk, getD_right tkh _ _ zeroE, Hd.getD_cut ZE (by omega) (by omega) zeroE]
  · rw [hb] at hj
    rw [hui]
    unfold embR Inst.Model.FFSeg.matR
    rw [if_pos ⟨hv, hj⟩]
    rfl

/-- The blocks' numbers have at most lPd - ls bits. -/
theorem EmbNums.blocks_le {y : Lay} (N : EmbNums y) : y.h.d / y.S2 ≤ 2 ^ (y.lPd - y.ls) := by
  have h6 : 2 ^ y.lPd = 2 ^ (y.lPd - y.ls) * 2 ^ y.ls := by
    rw [← pow_add, Nat.sub_add_cancel N.ls]
  have h7 := N.cap
  rw [← N.blocks, h6] at h7
  exact Nat.le_of_mul_le_mul_right h7 (by positivity)

#print axioms EmbNums.blocks_le
#print axioms claimE_inv
#print axioms psi_value
#print axioms facE_at
#print axioms facs_emb
#print axioms sum_side
#print axioms embTable
#print axioms embWeight

end Meaning.Emb
