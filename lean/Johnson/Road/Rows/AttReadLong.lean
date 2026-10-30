-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttReadLong.lean: the forms xl and plane of the attention sub-proof, as sums of
entries of the matrices; and the sizes of a shape that these sums need.

Main definitions: Sizes (equations and tests on the numbers of a shape), hiOf (the weights that xl
applies to the entries of its table), planeFirst (the first place of a plane).
Main theorems.
 - sizes_of_shape, sizes_of_hid: the verifier's functions shape and shapeHid return a shape with
   these sizes.
 - long_read: an entry of a table on blocks of features, as a sum over the features of the block and
   the tokens.
 - xl_value, overG_value, plane_value: what the forms are worth. The weights on the right are the
   verifier's own arrays, read in the field. The entries stand at the addresses featCell and asCell
   of Johnson/Road/Lane5AttDef.lean.

Every theorem on a form begins "if the routine returns". Nothing is said about probabilities or
about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttReadLaws
import Johnson.Road.FormsKeysPoint
import Johnson.Road.Lane5AttNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Fork SubM HFun HTailF2 TenAt tenCell eqTab blockRows)
open OnBytes.Attention (Shape Heard)
open OnBytes.Road.Hd (Ok ok_pure ok_bind ok_lift mustAs_ok ok_uEnt colsOf rdW)

variable {K : Type} [Field K]

/-! ## The sizes of a shape -/

/-- Equations and tests on the numbers of a shape. Public. -/
structure Sizes (S : Shape) : Prop where
  /-- the heads of keys and values -/
  G : S.G = 2 ^ S.cf.lgk
  /-- the tokens -/
  T : S.T = 2 ^ S.cf.lt
  /-- the side of a tile -/
  B : S.B = 2 ^ S.cf.lB
  /-- the tiles along a side -/
  nT : S.nT = 2 ^ S.lnT
  /-- the slot rows -/
  hP : S.hP = 2 ^ S.lnT / 2
  /-- a block has the rows of 2^ls features -/
  la : S.cf.la = S.ls + S.cf.lt
  /-- a head's features are whole blocks -/
  ls : S.ls ≤ S.cf.ldh
  /-- a column of ao holds whole blocks -/
  wcO : S.cf.wcO % 2 ^ S.ls = 0
  /-- a column of qa holds whole blocks -/
  wcQ : S.cf.wcQ % 2 ^ S.ls = 0
  /-- a plane on the diagonal holds whole columns of as -/
  lmS : S.cf.lmS ≤ S.nD
  /-- there are at least four tiles along a side -/
  lnT : 2 ≤ S.lnT

/-- What shape returns has these sizes. -/
theorem sizes_of_shape {cf : Attention.Cfg} {S : Shape} (h : Attention.shape cf = Except.ok S) :
    Sizes S := by
  unfold Attention.shape at h
  obtain ⟨e1, h⟩ := L5.refuse_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨e4, h⟩ := L5.refuse_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨Tt, -, h⟩ := L5.bind_ok h
  obtain ⟨e7, h⟩ := L5.refuse_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨_, -, h⟩ := L5.bind_ok h
  obtain ⟨_, -, h⟩ := L5.bind_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨e13, h⟩ := L5.refuse_ok h
  obtain ⟨-, h⟩ := L5.refuse_ok h
  obtain ⟨calls, -, h⟩ := L5.bind_ok h
  have e := Except.ok.inj h
  subst e
  simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at e1 e4 e7 e13
  have a0 := of_decide_eq_false e1.2
  have a1 := of_decide_eq_false e4.1.1
  have a2 := of_decide_eq_false e4.1.2
  have a3 := of_decide_eq_false e7.1
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, e13.1.2, e13.2, ?_, ?_⟩
  · show cf.la = cf.la - cf.lt + cf.lt
    omega
  · show cf.la - cf.lt ≤ cf.ldh
    omega
  · show cf.lmS ≤ Attention.nDOf cf
    omega
  · show 2 ≤ cf.lt - cf.lB
    omega

/-- The same for a shape that shapeHid returns. -/
theorem sizes_of_hid {lid : ℕ} {cf : Attention.Cfg} {S : Shape} {fs : Model.Forest.Shape}
    (h : Attention.shapeHid lid cf = Except.ok (S, fs)) : Sizes S := by
  unfold Attention.shapeHid at h
  obtain ⟨A, hA, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  obtain ⟨_, _, h⟩ := L5.bind_ok h
  have e := (Prod.mk.inj (Except.ok.inj h)).1
  have P := sizes_of_shape hA
  subst e
  exact ⟨P.G, P.T, P.B, P.nT, P.hP, P.la, P.ls, P.wcO, P.wcQ, P.lmS, P.lnT⟩

/-- The equations of Johnson/Road/Lane5AttNum.lean, for a shape that shapeHid returns. -/
theorem norm_of_hid {lid : ℕ} {cf : Attention.Cfg} {S : Shape} {fs : Model.Forest.Shape}
    (h : Attention.shapeHid lid cf = Except.ok (S, fs)) : L5.Norm S := by
  obtain ⟨A, hA⟩ := L5.shape_of_hid h
  exact L5.norm_of_shaped (L5.shaped_of_hid h) (L5.tested_of_shape hA).1 (L5.tested_of_shape hA).2

/-! ## Numbers -/

/-- A number with a low part below P, divided by P times w. -/
theorem block_div {P : ℕ} (hP : 0 < P) (w b c : ℕ) (hc : c < P) :
    (b * P + c) / (P * w) = b / w := by
  rw [← Nat.div_div_eq_div_mul, Nat.mul_comm b P, Nat.mul_add_div hP, Nat.div_eq_of_lt hc,
    Nat.add_zero]

/-- The same number modulo P times w. -/
theorem block_mod {P : ℕ} (hP : 0 < P) (w b c : ℕ) (hc : c < P) :
    (b * P + c) % (P * w) = b % w * P + c := by
  rw [Nat.mod_mul, Nat.mul_comm b P, Nat.mul_add_mod, Nat.mod_eq_of_lt hc, Nat.mul_add_div hP,
    Nat.div_eq_of_lt hc, Nat.add_zero, Nat.add_comm, Nat.mul_comm]

/-- The weights of the limbs read as the powers of 256. -/
theorem limb_value {ρ : Reading K} (hρ : Numerals ρ) {nl l : ℕ} (hl : l < nl) :
    ρ.val ((Attention.limbWeights nl).getD l zeroE) = (256 : K) ^ l := by
  unfold Attention.limbWeights
  rw [getD_map_lt (Array.range nl) _ (by simpa using hl) zeroE 0, hρ.ofNat]
  simp [Array.getD, hl]

/-- What cutLast returns. -/
theorem cutLast_ok {z : Array E} {k : ℕ} {c : Array E × Array E}
    (h : Model.cutLast z k = .ok c) :
    k ≤ z.size ∧ c = (z.extract 0 (z.size - k), z.extract (z.size - k) z.size) := by
  unfold Model.cutLast at h
  split at h
  · cases h
  · exact ⟨by omega, (Except.ok.inj h).symm⟩

/-- What headFeat returns. -/
theorem headFeat_ok {X : TenAt} {hd dh j : ℕ} (h : Model.headFeat X hd dh = .ok j) :
    j = hd * dh := by
  unfold Model.headFeat at h
  split at h
  · cases h
  · exact (Except.ok.inj h).symm

section Forms

variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-! ## A table on blocks of features -/

/-- Entry b of a table on blocks of features: a sum over the 2^ls features of block b and over the
tokens. wc: the features of a column of the matrix. -/
theorem long_read (A : AttAt ρ W tl K3 M h lid cf fs) (Z : Sizes h.S) {t mat wc : ℕ}
    {low tok : Array E} (Tb : TabAt tl h t mat (2 ^ h.S.cf.la) (blockRows low tok))
    (hm : mat < tl.NM) (hM : (tl.mats.getD mat {}).m = wc * h.S.T) (hwc : wc % 2 ^ h.S.ls = 0)
    (hlow : low.size = 2 ^ h.S.ls) (htok : tok.size = h.S.T) {b : ℕ}
    (hb : b < (h.t.tabLen.lookup t).getD 0) :
    rdW W h.iU3 K3 (t + b) = ∑ c ∈ range (2 ^ h.S.ls), ∑ i ∈ range h.S.T,
      ρ.val (low.getD c zeroE) * ρ.val (tok.getD i zeroE) *
        mAt M (L5.featCell h.S mat wc (b * 2 ^ h.S.ls + c) i) := by
  have hP : 0 < 2 ^ h.S.ls := Nat.two_pow_pos _
  have hT : 0 < h.S.T := by rw [Z.T]; exact Nat.two_pow_pos _
  have hla : 2 ^ h.S.cf.la = 2 ^ h.S.ls * h.S.T := by rw [Z.la, pow_add, Z.T]
  obtain ⟨wb, hwb⟩ := Nat.dvd_of_mod_eq_zero hwc
  have hn : (tl.mats.getD mat {}).m / 2 ^ h.S.cf.la = wb := by
    rw [hM, hla, hwb, show 2 ^ h.S.ls * wb * h.S.T = wb * (2 ^ h.S.ls * h.S.T) by ring]
    exact Nat.mul_div_cancel _ (Nat.mul_pos hP hT)
  rw [tab_read A Tb hm (Nat.ne_of_gt (Nat.two_pow_pos _)) hb, hn, hla, Alg.sum_range_mul_add]
  refine sum_congr rfl fun c hc => sum_congr rfl fun i hi => ?_
  have e := blockRows_getD low tok (r := c) (i := i) (by rw [hlow]; exact mem_range.mp hc)
    (by rw [htok]; exact mem_range.mp hi)
  rw [htok] at e
  rw [e, ρ.mul]
  show _ * M mat _ _ = _ * M mat ((b * 2 ^ h.S.ls + c) % wc * h.S.T + i)
    ((b * 2 ^ h.S.ls + c) / wc)
  rw [hwb, block_div hP wb b c (mem_range.mp hc), block_mod hP wb b c (mem_range.mp hc),
    show b % wb * (2 ^ h.S.ls * h.S.T) + (c * h.S.T + i) =
      (b % wb * 2 ^ h.S.ls + c) * h.S.T + i by ring]

/-! ## xl -/

/-- The weights that xl applies to the entries of its table: the equality weights of the point zc on
the features of a head, cut to ldh coordinates, without its last ls. -/
def hiOf (S : Shape) (zc : Array E) : Array E :=
  eqTab ((zc.extract 0 S.cf.ldh).extract 0 ((zc.extract 0 S.cf.ldh).size - S.ls))

/-- The form xl: a sum over the blocks ch of a head's features, the limbs l, the features c of a
block and the tokens i. -/
theorem xl_value (A : AttAt ρ W tl K3 M h lid cf fs) (Z : Sizes h.S) {F : Fork}
    (hc : Cols F h K3) {t mat wc : ℕ} {X : TenAt} {lam hd : ℕ} {zc low tok : Array E}
    (Tb : TabAt tl h t mat (2 ^ h.S.cf.la) (blockRows low tok))
    (hm : mat < tl.NM) (hM : (tl.mats.getD mat {}).m = wc * h.S.T) (hwc : wc % 2 ^ h.S.ls = 0)
    (hlow : low.size = 2 ^ h.S.ls) (htok : tok.size = h.S.T)
    (hX : ∀ l, 2 ^ h.S.ls ∣ tenCell X l lam (hd * h.S.dh))
    {q : Aff} {G : Fork} {C D : Ctx} (hq : Ok (Attention.xl h t X lam hd zc) F C q G D) :
    G = F ∧ D = C ∧ q.value ρ W =
      ∑ ch ∈ range (hiOf h.S zc).size, ρ.val ((hiOf h.S zc).getD ch zeroE) *
        ∑ l ∈ range X.nl, (256 : K) ^ l *
          ∑ c ∈ range (2 ^ h.S.ls), ∑ i ∈ range h.S.T,
            ρ.val (low.getD c zeroE) * ρ.val (tok.getD i zeroE) *
              mAt M (L5.featCell h.S mat wc
                (tenCell X l lam (hd * h.S.dh) + (ch * 2 ^ h.S.ls + c)) i) := by
  unfold Attention.xl at hq
  dsimp only at hq
  split at hq
  · rename_i cut hcut
    obtain ⟨-, ecut⟩ := cutLast_ok hcut
    split at hq
    · rename_i j0 hj0
      have ej := headFeat_ok hj0
      rw [ecut, ej] at hq
      obtain ⟨e1, e2, -, e3⟩ := weighted_value ρ W _ _ _
        (fun ch => ∑ l ∈ range X.nl, (256 : K) ^ l *
          ∑ c ∈ range (2 ^ h.S.ls), ∑ i ∈ range h.S.T,
            ρ.val (low.getD c zeroE) * ρ.val (tok.getD i zeroE) *
              mAt M (L5.featCell h.S mat wc
                (tenCell X l lam (hd * h.S.dh) + (ch * 2 ^ h.S.ls + c)) i))
        (fun _ => True)
        (by
          intro ch _ x G1 D1 hx
          obtain ⟨a1, a2, -, a3⟩ := weighted_value ρ W _ _ _
            (fun l => ∑ c ∈ range (2 ^ h.S.ls), ∑ i ∈ range h.S.T,
              ρ.val (low.getD c zeroE) * ρ.val (tok.getD i zeroE) *
                mAt M (L5.featCell h.S mat wc
                  (tenCell X l lam (hd * h.S.dh) + (ch * 2 ^ h.S.ls + c)) i))
            (fun _ => True)
            (by
              intro l _ y G2 D2 hy
              obtain ⟨b1, b2, b3, b4⟩ := u3at_value ρ W hy
              refine ⟨b1, b2, trivial, ?_⟩
              have hc' : colsOf F h.iU3 = K3 := hc
              rw [b4, hc', long_read A Z Tb hm hM hwc hlow htok b3]
              refine sum_congr rfl fun c _ => sum_congr rfl fun i _ => ?_
              obtain ⟨u, hu⟩ := hX l
              have e : (tenCell X l lam (hd * h.S.dh) / 2 ^ h.S.ls + ch) * 2 ^ h.S.ls + c =
                  tenCell X l lam (hd * h.S.dh) + (ch * 2 ^ h.S.ls + c) := by
                rw [hu, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
                ring
              rw [e]) hx
          refine ⟨a1, a2, trivial, ?_⟩
          rw [a3]
          exact sum_congr rfl fun l hl => by rw [limb_value A.num (mem_range.mp hl)]) hq
      exact ⟨e1, e2, e3⟩
    · exact absurd hq (refuse_not_ok _ _ _ _ _ _)
  · exact absurd hq (refuse_not_ok _ _ _ _ _ _)

/-! ## overG -/

/-- The form overG: the sum over the heads g of keys and values. -/
theorem overG_value {F : Fork} {C : Ctx} (zg : Array E) (f : ℕ → SubM Aff) (v : ℕ → K)
    (hf : ∀ g < h.S.G, ∀ x G D, Ok (f g) F C x G D → G = F ∧ D = C ∧ x.value ρ W = v g)
    {q : Aff} {G : Fork} {D : Ctx} (hq : Ok (Attention.overG h zg f) F C q G D) :
    G = F ∧ D = C ∧ q.value ρ W =
      ∑ g ∈ range h.S.G, ρ.val ((eqTab (zg.extract 0 h.S.cf.lgk)).getD g zeroE) * v g := by
  unfold Attention.overG at hq
  obtain ⟨e1, e2, -, e3⟩ := weighted_value ρ W _ _ _ v (fun _ => True)
    (fun g hg x G1 D1 hx => by
      obtain ⟨a1, a2, a3⟩ := hf g hg x G1 D1 hx
      exact ⟨a1, a2, trivial, a3⟩) hq
  exact ⟨e1, e2, e3⟩

/-! ## plane -/

/-- The first place of plane x of the pair (lam, a), among the cells of the matrix as. -/
def planeFirst (S : Shape) (x lam a : ℕ) (isD : Bool) : ℕ :=
  (if isD then (5 * S.Lam * S.HA) <<< S.nM else 0) +
    (((x * S.Lam + lam) * S.HA + a) <<< (if isD then S.nD else S.nM))

/-- The form plane: a sum over the columns hi of the plane and the rows lo of a column. -/
theorem plane_value (A : AttAt ρ W tl K3 M h lid cf fs) {F : Fork} (hc : Cols F h K3) {t : ℕ}
    {phi : Array E} (Tb : AsAt h t phi) {x lam a : ℕ} {z : Array E} {isD : Bool}
    {q : Aff} {G : Fork} {C D : Ctx} (hq : Ok (Attention.plane h t x lam a z isD) F C q G D) :
    G = F ∧ D = C ∧ q.value ρ W =
      ∑ hi ∈ range
          (eqTab (z.extract 0 ((if isD then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        ρ.val ((eqTab (z.extract 0 ((if isD then h.S.nD else h.S.nM) - h.S.cf.lmS))).getD hi
          zeroE) *
          ∑ lo ∈ range (2 ^ h.S.cf.lmS), ρ.val (phi.getD lo zeroE) *
            mAt M (L5.asCell h.S
              ((planeFirst h.S x lam a isD >>> h.S.cf.lmS + hi) * 2 ^ h.S.cf.lmS + lo)) := by
  unfold Attention.plane at hq
  dsimp only at hq
  obtain ⟨e1, e2, -, e3⟩ := weighted_value ρ W _ _ _
    (fun hi => ∑ lo ∈ range (2 ^ h.S.cf.lmS), ρ.val (phi.getD lo zeroE) *
      mAt M (L5.asCell h.S
        ((planeFirst h.S x lam a isD >>> h.S.cf.lmS + hi) * 2 ^ h.S.cf.lmS + lo)))
    (fun _ => True)
    (by
      intro hi _ y G2 D2 hy
      obtain ⟨b1, b2, b3, b4⟩ := u3at_value ρ W hy
      refine ⟨b1, b2, trivial, ?_⟩
      have hc' : colsOf F h.iU3 = K3 := hc
      rw [b4, hc', as_read A Tb b3]
      refine sum_congr rfl fun lo hlo => ?_
      have hP : 0 < 2 ^ h.S.cf.lmS := Nat.two_pow_pos _
      have d1 : ∀ n : ℕ, (n * 2 ^ h.S.cf.lmS + lo) / 2 ^ h.S.cf.lmS = n := fun n => by
        rw [Nat.mul_comm, Nat.mul_add_div hP, Nat.div_eq_of_lt (mem_range.mp hlo), Nat.add_zero]
      have d2 : ∀ n : ℕ, (n * 2 ^ h.S.cf.lmS + lo) % 2 ^ h.S.cf.lmS = lo := fun n => by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (mem_range.mp hlo)]
      show _ = _ * M _ _ _
      unfold L5.asCell
      simp only [d1, d2]
      rfl) hq
  exact ⟨e1, e2, e3⟩

end Forms

end OnBytes.Road.Rows
