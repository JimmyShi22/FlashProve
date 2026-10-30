-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoJoinOut.lean.
The lookup of a sub-proof: the end of its key side, in the record of end values.

The typed verifier of a sub-proof's lookup puts out a masked claim on the joint key vector.
OnBytes/Tie/Pv/Lookup/Forest/FoOut.lean says what that claim's weights, mask form and target are, in
the fields of the record of end values (Fo.endsOf): the point (zx, zy), the form cEndF with the
constant cEndC, alpha, theta. This file turns that claim into the plain form Fo.joinK
(OnBytes/Tie/Pv/Lookup/Port/FoJoin.lean), which is written after the byte-level verifier's routine
Forest.join, at the same fields.

States:
  lvGo_len, keys_len, ordK_len, pntK_len: the key side's point has as many coordinates as a key's
    number has bits.
  ends_zx_len, ends_zy_len, ends_zk: the lengths of the record's two cuts of the point; each call's
    point in the record is the verifier's cut of them.
  holds_congr: whether a masked claim holds depends on its point through the weights alone.
  join_ends: for every out-statement x whose state, weights, mask form and target are as
    OnBytes/Tie/Pv/Lookup/Forest/FoOut.lean
    says:
    the masked claim on the keys holds if and only if the value of joinK's form, at the record's
      theta, alpha, zy, cEndF, cEndC and the caller's forms KF, is 0.
Premises of join_ends: FoNums.ok h = true; the four clauses on x (each is a clause of Fo.OutIs);
KFokAt at the record's points and at the reading at which the claim is said.
The lengths and ends_zk stand under FoNums.ok h = true (ordK_len: 10 ≤ dT; ends_zk: c < NC).
Does not say: that the caller's forms meet KFokAt; that the form which Forest.join returns has
joinK's value (join_val, OnBytes/Tie/Pv/Lookup/Forest/FoJoinRun.lean, says that).

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinAt
import OnBytes.Tie.Pv.Lookup.Forest.FoOut
import OnBytes.Tie.Pv.Lookup.Forest.FoTies

set_option autoImplicit false

namespace Fo
open TwV FoNums Finset OnBytes.Model OnBytes.Ends Cb Cb.LdLkp Cb.Fo Tw3

/-! ### The point's length -/
section
variable {K : Type} [CommRing K]

theorem lvGo_len (o : ℕ → List ℕ) : ∀ (c l : ℕ) (tg : K) (pt : List K) (rs : Rounds K),
    (lvGo o c l tg pt rs).1.length = c
  | 0, _, _, _, _ => rfl
  | c + 1, l, tg, pt, rs => by
    unfold lvGo
    simp only [List.length_cons]
    rw [lvGo_len o c]

theorem keys_len {P : Type} (N : Nums P K) (rs : Rounds K) : (traceOfFlat N rs).keys.length =
    N.v' + 1 :=
  lvGo_len N.oK (N.v' + 1) 0 _ _ _

theorem ordK_len (h : FoNums.Sh) (hd : 10 ≤ h.dT) (k : ℕ) : (ordK h k).length = k := by
  rw [← asList_forOK h hd k]
  simp [E3.asList]

theorem pntK_len (h : FoNums.Sh) (H : FoNums.ok h = true) (lm jLK : ℕ) (rs : Rounds K) :
    (pntK (forN h lm jLK rs) (forTrace h lm jLK rs)).length = h.dT + h.rK := by
  have hk : (forTrace h lm jLK rs).keys.reverse.length = FoNums.v' h + 1 := by
    rw [List.length_reverse]
    exact keys_len (forN h lm jLK rs) _
  have hv : h.dT + h.rK = FoNums.v' h + 1 := ok_v H
  unfold pntK
  cases hr : (forTrace h lm jLK rs).keys.reverse with
  | nil => rw [hr] at hk; simp at hk
  | cons s rest =>
    rw [hr, List.length_cons] at hk
    show (byVar ((forN h lm jLK rs).oK rest.length) s.1.xs ++ [s.2]).length = _
    rw [List.length_append, List.length_singleton]
    have e : (byVar ((forN h lm jLK rs).oK rest.length) s.1.xs).length = rest.length := by
      unfold byVar
      rw [List.length_map, List.length_range]
      exact ordK_len h (ok_parts H).1.1 _
    rw [e, hv]
    omega

variable (h : FoNums.Sh) (H : FoNums.ok h = true) (lm jLK : ℕ) (rs : Rounds K)
include H

theorem ends_zx_len : (endsOf h lm jLK rs).zx.length = h.dT := by
  show ((pntK (forN h lm jLK rs) (forTrace h lm jLK rs)).drop h.rK).reverse.length = _
  rw [List.length_reverse, List.length_drop, pntK_len h H]
  omega

theorem ends_zy_len : (endsOf h lm jLK rs).zy.length = h.rK := by
  show ((pntK (forN h lm jLK rs) (forTrace h lm jLK rs)).take h.rK).reverse.length = _
  rw [List.length_reverse, List.length_take, pntK_len h H]
  omega

/-- A call's point in the record is the verifier's cut of the record's two lists. -/
theorem ends_zk (c : ℕ) (hc : c < h.NC) :
    (endsOf h lm jLK rs).zk.getD c [] = zk h.rK (io h c) (endsOf h lm jLK rs).zx
        (endsOf h lm jLK rs).zy := by
  have hio : io h c ≤ h.rK := (ok_prem H).le c hc
  have hp := pntK_len h H lm jLK rs
  have e := zk_coord h.dT h.rK (io h c) hio (pntK (forN h lm jLK rs) (forTrace h lm jLK rs)) hp
  rw [zx_coord h.dT h.rK _ hp, zy_coord h.dT h.rK _ hp] at e
  show ((List.range h.NC).map fun c => ((pntK (forN h lm jLK rs) (forTrace h lm jLK rs)).drop
      h.rK ++
    (pntK (forN h lm jLK rs) (forTrace h lm jLK rs)).take (io h c)).reverse).getD c [] = _
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]
  exact e.symm

end

/-! ### A claim's point enters through the weights alone -/
section
variable {E N : Type} [Field E] [Fintype N]

theorem holds_congr (c c' : MCl E N) (k : ℕ) (f : ℕ → E) (μ : N → E)
    (hw : ∀ X < 2 ^ k, Blocks.eqN k 0 c.pt X = Blocks.eqN k 0 c'.pt X) (hm : c.mf = c'.mf)
        (ht : c.tg = c'.tg) :
    c.Holds k f μ ↔ c'.Holds k f μ := by
  unfold MCl.Holds Blocks.ext
  rw [hm, ht, Finset.sum_congr rfl fun X hX => by rw [hw X (Finset.mem_range.mp hX)]]

/-- A list as a point. -/
def ptL (ρ : List E) : ℕ → E := fun t => ρ.getD t 0

theorem rho_ptL (ρ : List E) : rhoP ρ.length (ptL ρ) = ρ := by
  unfold rhoP ptL
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]

end

/-! ### The join, in the record's fields -/
section
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

theorem join_ends (h : FoNums.Sh) (H : FoNums.ok h = true) (L : Lay E St₀ J₀) (lm jLK : ℕ)
    (ι : Pl → Option J₀) (rs : Rounds E)
    (st : St₀) (x : TX (St₀ × E) E (Option J₀))
    (h1 : x.1 = (st, (endsOf h lm jLK rs).theta))
    (h4 : ∀ X < 2 ^ (FoNums.v' h + 1), Blocks.eqN (FoNums.v' h + 1) 0 x.2.1.pt X =
      TwV.eqN ((endsOf h lm jLK rs).zy.reverse ++ (endsOf h lm jLK rs).zx.reverse) X)
    (h5 : ∀ j, x.2.1.mf j = dense (mapL ι (endsOf h lm jLK rs).cEndF) j)
    (h6 : x.2.1.tg = (endsOf h lm jLK rs).alpha - (endsOf h lm jLK rs).cEndC)
    (KF : ℕ → AffK (Option J₀) E) (μ : Option J₀ → E)
    (hKF : KFokAt h (forK E L st) (fun c => (endsOf h lm jLK rs).zk.getD c []) KF μ) :
    x.2.1.Holds ((forA E h L).v' + 1) ((forA E h L).key x.1 μ) μ ↔
      AffK.val (joinK h (endsOf h lm jLK rs).theta (endsOf h lm jLK rs).alpha
          (eK h (endsOf h lm jLK rs).zy)
        (endsOf h lm jLK rs).zy KF (mapL ι (endsOf h lm jLK rs).cEndF, (endsOf h lm jLK rs).cEndC))
            μ = 0 := by
  have hx := ends_zx_len h H lm jLK rs
  have hy := ends_zy_len h H lm jLK rs
  have hv : FoNums.v' h + 1 = h.dT + h.rK := (ok_v H).symm
  have hlen : ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy).length = h.dT + h.rK := by
    rw [List.length_append, hx, hy]
  -- the claim with the record's lists as its point
  have hrho : rhoP (h.dT + h.rK) (ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy)) =
      (endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy := by
    rw [← hlen]; exact rho_ptL _
  have hc := holds_congr x.2.1 ⟨ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy), x.2.1.mf,
      x.2.1.tg⟩
    (FoNums.v' h + 1) ((forA E h L).key x.1 μ) μ (fun X hX => by
      rw [h4 X hX, hv]
      have e := eqN_top (ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy)) 0 (h.dT + h.rK) X
      simp only [Nat.zero_add] at e
      rw [← e]
      have e2 : ((List.range (h.dT + h.rK)).map fun i =>
          ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy) i) =
          (endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy := hrho
      rw [e2, List.reverse_append]) rfl rfl
  have hzx : zxOf h (⟨ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy), x.2.1.mf, x.2.1.tg⟩
      : MCl E (Option J₀)) =
      (endsOf h lm jLK rs).zx := by
    unfold zxOf zx
    rw [hrho, ← hx, List.take_left']
    rfl
  have hzy : zyOf h (⟨ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy), x.2.1.mf, x.2.1.tg⟩
      : MCl E (Option J₀)) =
      (endsOf h lm jLK rs).zy := by
    unfold zyOf zy
    rw [hrho, ← hx, List.drop_left']
    rfl
  have hKF' : KFokAt h (forK E L st)
      (zkOf h (⟨ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy), x.2.1.mf, x.2.1.tg⟩ : MCl
          E (Option J₀))) KF μ := by
    intro c hcN
    rw [hKF c hcN]
    show extL _ ((endsOf h lm jLK rs).zk.getD c []) = _
    rw [ends_zk h H lm jLK rs c hcN]
    unfold zkOf
    rw [hzx, hzy]
  have hCE : CEok (⟨ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy), x.2.1.mf, x.2.1.tg⟩ :
      MCl E (Option J₀))
      (endsOf h lm jLK rs).alpha (mapL ι (endsOf h lm jLK rs).cEndF, (endsOf h lm jLK rs).cEndC) :=
          by
    intro ν
    unfold AffK.val
    simp only [h5, h6]
    rw [dense_val]
    ring
  have hj := join_form (ok_prem H) (forK E L st) (endsOf h lm jLK rs).theta
      (endsOf h lm jLK rs).alpha
    (⟨ptL ((endsOf h lm jLK rs).zx ++ (endsOf h lm jLK rs).zy), x.2.1.mf, x.2.1.tg⟩ : MCl E
        (Option J₀)) KF _ μ hKF' hCE
  rw [hzy] at hj
  rw [← hj]
  have hk : (forA E h L).key x.1 μ = jointKey h (forK E L st μ) (endsOf h lm jLK rs).theta := by
    rw [h1]; exact forA_key E h L H st _ μ
  rw [← hk]
  have hvv : h.v = FoNums.v' h + 1 := ok_v H
  rw [hvv]
  exact hc

end
end Fo
