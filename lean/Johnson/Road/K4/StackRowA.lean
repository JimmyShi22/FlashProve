-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackRowA.lean: the first side of the library's summand of the batched sumcheck, on
values of its end values, is the verifier's element of the field for the A side at these values.

The library's first side is a sum over its parts' names (IA, Cb/Pv/Lay/At/InnerGeo.lean): the form
part, with the coefficient 1, and one part for each panel whose first factor is a never-sent vector
(D, and Dr l for each layer with routed experts), with a public coefficient
(Cb/Pv/Lay/At/Pieces.lean, Inner.lean). The verifier's AsAt (Johnson/Road/FormsKeysEnd.lean) is the
form part's value plus what each placed panel adds (dEnd). Here the two are compared panel by panel.
For Dr l the library has one weight for each row of the panel and the verifier one weight for all:
the library's does not read the row (Pan.wt, Inst/Model/FF/Objects.lean).

Main names:
  `cAP`, `sideA_c`, `sideA_c0`: the library's coefficient of a panel's part, by the panel alone; the
    form part's is 1.
  `GeoA`, `geoA_of`: the verifier's weights of a panel's place and rows are the library's equality
    weights; from the panel's bits and place, by geo_sb and geo_sbei
    (Johnson/Road/K4/StackRowB.lean).
  `pair_A`, `as_list`: what one panel adds to As; what the panels of a list add.
  `sumIA`, `dr_lt`: tools.
  `as_typed`: the first side's sum is AsAt.
Limits. PREMISES: EndFields and GeoA of each pair of the placed list and pans D; StackTies; that the
weight of claim 0 reads 1; NE = nx; that the form part's value is a0 and the value at the part of a
panel is h1 at the number of the panel's never-sent vector. An identity: nothing on a run, on
soundness or on hiding.


-/
import Johnson.Road.K4.StackRowB
import Johnson.Road.K4.EndFields
import Johnson.Road.K4.StackTyped

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (Reading World eqIndexOK)
open OnBytes.Model.Layer (Lay SBlk)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Pan pans wc call)
open Cb.Pv.Lay.At (InnPar0 isVirt nP kS wrow cntA IA IB wid_eq)
open Cb.Pv.Lay.End.Sig (pans_nodup)
open Blocks (eqN)

variable {K : Type} [Field K] [Fintype K] [scl : Scl]

/-- The library's coefficient of the part of a panel on the first side. -/
noncomputable def cAP (P : InnPar0 K) (st : P.St) (zp : Fin (kS P.D) → K) (pn : Pan) : K :=
  ∑ e ∈ range (if pn.three then pn.nr P.D else 1), P.κA st pn e *
    eqN (kS P.D - (if pn.three then pn.wcol P.D else pn.wid P.D)) 0 (Blocks.nat zp)
      ((if pn.three then nP P.D pn * 2 ^ wrow P.D pn else nP P.D pn) + e)

theorem sideA_c (P : InnPar0 K) (st : P.St) (zp : Fin (kS P.D) → K)
    (i : Σ p : {p : Pan // p ∈ pans P.D}, Fin (cntA p.1)) :
    P.sideA.side.c (.inr i) st zp = cAP P st zp i.1.1 := rfl

theorem sideA_c0 (P : InnPar0 K) (st : P.St) (zp : Fin (kS P.D) → K) :
    P.sideA.side.c (.inl ()) st zp = 1 := by
  show ∑ e ∈ range 1, (1 : K) * eqN (kS P.D - kS P.D) 0 (Blocks.nat zp) (0 + e) = 1
  rw [sum_range_one, Nat.sub_self, one_mul]
  unfold Blocks.eqN
  rw [range_zero, prod_empty]

/-- The verifier's weights of a panel's place, and of its place and a row, are the library's
equality weights at the point Z. -/
structure GeoA (ρ : Reading K) (rs : Array E) (lam : ℕ) (D : Dim) (Z : ℕ → K) (b : SBlk)
    (pn : Pan) : Prop where
  sb : sbK ρ rs lam b = eqN (lam - pn.wid D) 0 Z (nP D pn)
  sbei : ∀ e, e < pn.nr D → sbK ρ rs lam b * eiK ρ rs b e =
    eqN (lam - pn.wcol D) 0 Z (nP D pn * 2 ^ wrow D pn + e)

omit [Fintype K] scl in
/-- GeoA from the panel's bits and place. hz: the point reads as the challenges turned round. -/
theorem geoA_of {ρ : Reading K} {rs : Array E} {D : Dim} {b : SBlk} {pn : Pan}
    (bw : b.w = pn.wid D) (bwy : b.wy = pn.wcol D) (off : b.off / 2 ^ b.w = nP D pn)
    (ok : eqIndexOK (rs.extract b.w (kS D)) (b.off / 2 ^ b.w) = true) (hl : kS D ≤ rs.size)
    (zp : Fin (kS D) → K) (hz : ∀ j, j < kS D → Blocks.nat zp j = zR ρ rs (kS D) j)
    (hp : pn ∈ pans D) : GeoA ρ rs (kS D) D (Blocks.nat zp) b pn := by
  have hwl : pn.wid D ≤ kS D := by
    rw [Cb.Pv.Lay.At.kS_eq]
    exact Cb.Pv.Lay.At.wid_le D hp
  have cz : ∀ m c, m ≤ kS D → eqN m 0 (zR ρ rs (kS D)) c = eqN m 0 (Blocks.nat zp) c :=
    fun m c hm => eqN_congr' _ _ (fun j hj => by
      rw [Nat.zero_add]
      exact (hz j (Nat.lt_of_lt_of_le hj hm)).symm) c
  have hwy : b.wy ≤ b.w := by
    rw [bw, bwy, wid_eq]
    exact Nat.le_add_left _ _
  have hwr : b.w - b.wy = wrow D pn := by
    rw [bw, bwy, wid_eq, Nat.add_sub_cancel]
  refine ⟨?_, fun e he => ?_⟩
  · rw [geo_sb ρ hl ok, off, bw, cz _ _ (Nat.sub_le _ _)]
  · have he' : e < 2 ^ (b.w - b.wy) := by
      rw [hwr]
      exact Nat.lt_of_lt_of_le he (Nat.le_pow_clog (by decide) _)
    rw [geo_sbei ρ hl ok hwy (by rw [bw]; exact hwl) he', off, hwr, bwy, cz _ _ (Nat.sub_le _ _)]

omit [Fintype K] scl in
/-- A sum over the names of the first side's parts. G p: what the part of panel p adds. -/
theorem sumIA (D : Dim) (f : IA D → K) (G : Pan → K)
    (hG : ∀ p : {p : Pan // p ∈ pans D}, ∑ i : Fin (cntA p.1), f (.inr ⟨p, i⟩) = G p.1) :
    ∑ j : IA D, f j = f (.inl ()) + ((pans D).map G).sum :=
  sum_pieces (pans_nodup D) cntA f G hG

omit [Fintype K] scl in
/-- A panel Dr l of the library's list belongs to a layer with routed experts. -/
theorem dr_lt {D : Dim} {l : ℕ} (h : Pan.Dr l ∈ pans D) : l < D.ne := by
  simpa [pans] using h

variable {P : InnPar0 K} {st : P.St} {ρ : Reading K} {W : World K} {y : Lay} {sh om rs : Array E}
  {z zh : ℕ → K} {zp : Fin (kS P.D) → K}

/-- **What one panel adds to As.** -/
theorem pair_A (T : StackTies P st ρ y sh om z zh) (hom : ρ.val (om.getD 0 zeroE) = 1)
    (hNE : y.h.NE = P.D.nx) (h1 vv : ℕ → K) {b : SBlk} {pn : Pan} (hp : pn ∈ pans P.D)
    (F : EndFields ρ y sh P.D z b pn) (Gm : GeoA ρ rs (kS P.D) P.D (Blocks.nat zp) b pn) :
    (dEnd ρ W y rs (kS P.D) om h1 vv b).2.2.1 =
      if isVirt pn then cAP P st zp pn * h1 ((virtOf pn).getD 0) else 0 := by
  have other : virtOf pn = none → isVirt pn = false →
      (dEnd ρ W y rs (kS P.D) om h1 vv b).2.2.1 =
        if isVirt pn then cAP P st zp pn * h1 ((virtOf pn).getD 0) else 0 := by
    intro hk hv
    have hb : b.virt = none := F.virt.trans hk
    rw [hv, if_neg (by simp)]
    unfold dEnd
    rw [hb]
    cases b.tri <;> cases b.v0 <;> rfl
  cases pn with
  | D =>
    obtain ⟨v0, hv0⟩ := F.v0w rfl
    have ht : b.tri = false := F.tri
    have hk : b.virt = some 0 := F.virt
    have hc : b.claim = 0 := F.claim
    have e1 : (dEnd ρ W y rs (kS P.D) om h1 vv b).2.2.1 =
        sbK ρ rs (kS P.D) b * omK ρ om b * h1 0 := by
      unfold dEnd
      rw [ht, hk, hv0]
    have e2 : omK ρ om b = 1 := by
      unfold omK
      rw [hc, hom]
    have e3 : cAP P st zp .D = eqN (kS P.D - Pan.D.wid P.D) 0 (Blocks.nat zp) (nP P.D .D) := by
      show ∑ e ∈ range 1, (1 : K) *
        eqN (kS P.D - Pan.D.wid P.D) 0 (Blocks.nat zp) (nP P.D .D + e) = _
      rw [sum_range_one, one_mul, Nat.add_zero]
    rw [e1, e2, mul_one, Gm.sb, if_pos (show isVirt Pan.D = true from rfl), e3]
    rfl
  | Dr l =>
    obtain ⟨v0, hv0⟩ := F.v0w rfl
    have ht : b.tri = true := F.tri
    have hk : b.virt = some (1 + l) := F.virt
    have hc : b.claim = 1 := F.claim
    obtain ⟨hec, hwt, hsl⟩ := F.dr l rfl
    have hl : l < P.D.ne := dr_lt hp
    have h3 : st.o3.st = z := T.z3
    have e1 : (dEnd ρ W y rs (kS P.D) om h1 vv b).2.2.1 =
        c1K ρ y rs (kS P.D) om b * h1 (1 + l) := by
      unfold dEnd
      rw [ht, hk, hv0]
    have e2 : omK ρ om b = st.β := by
      unfold omK
      rw [hc, T.x]
    have e3 : cAP P st zp (.Dr l) = c1K ρ y rs (kS P.D) om b := by
      show ∑ e ∈ range P.D.nx, (st.β * wc P.D st.o3.st (call .D) *
          (Pan.Dr l).wt P.D st.o3.st e * P.selV st l e) *
        eqN (kS P.D - (Pan.Dr l).wcol P.D) 0 (Blocks.nat zp)
          (nP P.D (.Dr l) * 2 ^ wrow P.D (.Dr l) + e) = _
      unfold c1K
      rw [e2, hec, hwt, hNE, mul_sum, h3]
      refine sum_congr rfl fun e he => ?_
      have he' : e < P.D.nx := mem_range.mp he
      have hs : P.selV st l e = ρ.val (b.sl.getD e zeroE) := by
        unfold InnPar0.selV
        rw [dif_pos ⟨hl, he'⟩, T.sel2 l e ⟨hl, he'⟩, hsl e (by rw [hNE]; exact he')]
        rfl
      have hw : (Pan.Dr l).wt P.D z e = (Pan.Dr l).wt P.D z 0 := rfl
      rw [← Gm.sbei e he', hs, hw]
      ring
    rw [e1, if_pos (show isVirt (Pan.Dr l) = true from rfl), e3]
    rfl
  | G => exact other rfl rfl
  | U => exact other rfl rfl
  | O => exact other rfl rfl
  | V => exact other rfl rfl
  | LR => exact other rfl rfl
  | Gr l => exact other rfl rfl
  | Ur l => exact other rfl rfl
  | N1 => exact other rfl rfl
  | N2 => exact other rfl rfl
  | QK => exact other rfl rfl
  | XR => exact other rfl rfl
  | DD => exact other rfl rfl
  | MR => exact other rfl rfl

/-- What the panels of a list add to As, against a list of panels of the library. The second list is
a letter: nothing is computed on pans D. -/
theorem as_list (T : StackTies P st ρ y sh om z zh) (hom : ρ.val (om.getD 0 zeroE) = 1)
    (hNE : y.h.NE = P.D.nx) (h1 vv : ℕ → K) : ∀ {bl : List SBlk} {L : List Pan},
    (∀ pn ∈ L, pn ∈ pans P.D) →
    List.Forall₂ (fun b pn => EndFields ρ y sh P.D z b pn ∧
      GeoA ρ rs (kS P.D) P.D (Blocks.nat zp) b pn) bl L →
    (bl.map fun b => (dEnd ρ W y rs (kS P.D) om h1 vv b).2.2.1).sum =
      (L.map fun pn => if isVirt pn then cAP P st zp pn * h1 ((virtOf pn).getD 0) else 0).sum
  | _, _, _, .nil => rfl
  | _, _, hm, .cons h t => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
      pair_A T hom hNE h1 vv (hm _ List.mem_cons_self) h.1 h.2,
      as_list T hom hNE h1 vv (fun pn hp => hm pn (List.mem_cons_of_mem _ hp)) t]

/-- **The first side's sum is the verifier's element of the field for the A side.** v: values of the
end values; a0, h1: the form part's and the never-sent vectors' values in the verifier's letters. -/
theorem as_typed (T : StackTies P st ρ y sh om z zh) (hom : ρ.val (om.getD 0 zeroE) = 1)
    (hNE : y.h.NE = P.D.nx) (h1 vv : ℕ → K) (a0 : K) {bl : List SBlk}
    (F2 : List.Forall₂ (fun b pn => EndFields ρ y sh P.D z b pn ∧
      GeoA ρ rs (kS P.D) P.D (Blocks.nat zp) b pn) bl (pans P.D))
    (v : IA P.D ⊕ IB P.D → K) (ha0 : v (.inl (.inl ())) = a0)
    (hv : ∀ i : (Σ p : {p : Pan // p ∈ pans P.D}, Fin (cntA p.1)),
      v (.inl (.inr i)) = h1 ((virtOf i.1.1).getD 0)) :
    ∑ i : IA P.D, P.sideA.side.c i st zp * v (.inl i) =
      AsAt ρ W y rs (kS P.D) om h1 vv a0 bl := by
  have hg : ∀ p : {p : Pan // p ∈ pans P.D},
      ∑ c : Fin (cntA p.1), P.sideA.side.c (.inr ⟨p, c⟩) st zp * v (.inl (.inr ⟨p, c⟩)) =
        if isVirt p.1 then cAP P st zp p.1 * h1 ((virtOf p.1).getD 0) else 0 := by
    intro p
    have e : ∀ c : Fin (cntA p.1),
        P.sideA.side.c (.inr ⟨p, c⟩) st zp * v (.inl (.inr ⟨p, c⟩)) =
          cAP P st zp p.1 * h1 ((virtOf p.1).getD 0) := fun c => by
      rw [hv ⟨p, c⟩, sideA_c]
    rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    unfold cntA
    by_cases hvp : isVirt p.1 = true
    · rw [if_pos hvp, if_pos hvp, one_smul]
    · rw [if_neg hvp, if_neg hvp, zero_smul]
  unfold AsAt
  rw [sumIA P.D (fun i => P.sideA.side.c i st zp * v (.inl i))
    (fun pn => if isVirt pn then cAP P st zp pn * h1 ((virtOf pn).getD 0) else 0) hg,
    sideA_c0, one_mul, ha0]
  congr 1
  exact (as_list T hom hNE h1 vv (fun _ hp => hp) F2).symm

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sideA_c
#print axioms OnBytes.Road.K4.sideA_c0
#print axioms OnBytes.Road.K4.geoA_of
#print axioms OnBytes.Road.K4.sumIA
#print axioms OnBytes.Road.K4.dr_lt
#print axioms OnBytes.Road.K4.pair_A
#print axioms OnBytes.Road.K4.as_list
#print axioms OnBytes.Road.K4.as_typed
