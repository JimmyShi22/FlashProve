-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgGam.lean: the product parts of the library's key, beside G.lean's gamG.
G.lean is OnBytes/Tie/Pv/Lookup/Ends/G.lean: a file of terms written for these files over the
verifier's records; no function of the verifier returns them.
States: (parts_gamG) for all 34 families: the two product parts of the library's key (term and mat,
Inst/Model/FF/Objects.lean) together are G.lean's gamG at the segment of that name, at every layer
of the group on which the family is present, every entry and every token. (key_segG) So the
library's key is G.lean's segG: with lin_affG (Johnson/Road/Ends/AlgLin.lean) and the library's
key_eq.
Under TiesG (Johnson/Road/Ends/AlgLin.lean) and TiesW: profile 4; the library's value of the
attention output is G.lean's tensor o; three sizes more; an even width of a head; the library's
matrices of a layer of the group are G.lean's weights of the units 0 to 11 (wOfG); the library's
rotary tables are the verifier's ropeC. C, S, valO and w are asked at every i, jj, instance and
token (the layer alone is bounded), also past the tables' ends: they are met by tbG P, wOfG and
cellsOf by definition (Johnson/Road/Ends/AlgWit.lean); Johnson/Road/Ends/AlgKey.lean carries the
result to tables and weights that agree with these on the range.
Does not say: what a form of the verifier's is worth; that a run's reads have their rule values;
that the batched sumcheck or the second token sumcheck proves these products.
-/
import Johnson.Road.Ends.AlgLin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open Finset
open OnBytes.Ends
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr Fam LW key lin term mat present val xS led hh mr Ag Au Av Ad AY
  Aq Ak Y' kG kU kQK isExpL)

section Weights

variable {K : Type} [Field K]

/-- The library's matrices of layer l of the group, read through G.lean's weights. -/
def wOfG (P : Model.Layer.Pub) (g : ℕ) (cell : G.NameG → K) (l : ℕ) : LW K where
  Wq := fun j x => G.wt P cell 0 (g * P.y.Lam + l) [x / P.y.h.dh, x % P.y.h.dh, j]
  Wk := fun j x =>
    G.wt P cell 0 (g * P.y.Lam + l) [(P.y.dq + x) / P.y.h.dh, (P.y.dq + x) % P.y.h.dh, j]
  Wv := fun j x => G.wt P cell 1 (g * P.y.Lam + l) [j, x]
  Wo := fun j x => G.wt P cell 2 (g * P.y.Lam + l) [j, x]
  Wg := fun j x => G.wt P cell (if G.moe P l then 5 else 3) (g * P.y.Lam + l) [j, x]
  Wu := fun j x => G.wt P cell (if G.moe P l then 6 else 4) (g * P.y.Lam + l) [j, x]
  Wd := fun j x => G.wt P cell 9 (g * P.y.Lam + l) [j, x]
  Wr := fun j x => G.wt P cell 11 (g * P.y.Lam + l) [j, x]
  Eg := fun e j x => G.wt P cell 7 (g * P.y.Lam + l) [j, e, x]
  Eu := fun e j x => G.wt P cell 8 (g * P.y.Lam + l) [j, e, x]
  Ed := fun e j x => G.wt P cell 10 (g * P.y.Lam + l) [j, e, x]

end Weights

section Ties

variable {K : Type} [Field K] [scl : Scl]

/-- **What more ties G.lean's products to the library's.** -/
structure TiesW (P : Model.Layer.Pub) (g : ℕ) (cell : G.NameG → K) (D : Dim) (t : Cell → K)
    (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) : Prop where
  /-- the attention output is a tensor -/
  p4 : P.y.h.p4 = true
  /-- the library's value of the attention output is the tensor o -/
  valO : ∀ inst j i : ℕ, val t .o inst j i = G.ten P cell "o" inst j i
  /-- the model's width -/
  d : P.y.h.d = D.d
  /-- the hidden units -/
  f : P.y.h.f = D.f
  /-- the width of a head -/
  ch : P.y.h.dh = D.P.ch
  /-- the width of a head is even -/
  even : D.P.ch % 2 = 0
  /-- the weights, on the layers of the group -/
  w : ∀ lam, lam < D.nl → w lam = wOfG P g cell lam
  /-- the cosines, on the layers of the group -/
  C : ∀ lam, lam < D.nl → ∀ i jj : ℕ,
    tb.C (L0 + lam) i jj = Model.Layer.ropeC P.y.h P.sc P.rope (g * P.y.Lam + lam) i jj false
  /-- the sines -/
  S : ∀ lam, lam < D.nl → ∀ i jj : ℕ,
    tb.S (L0 + lam) i jj = Model.Layer.ropeC P.y.h P.sc P.rope (g * P.y.Lam + lam) i jj true

variable {P : Model.Layer.Pub} {g : ℕ} {cell : G.NameG → K} {D : Dim} {t : Cell → K}
  {tb : Tables} {L0 : ℕ} {w : ℕ → LW K}

/-- Which layers have routed experts. -/
theorem TiesG.moe_eq (T : TiesG P g cell D t) (lam : ℕ) : G.moe P lam = isExpL lam := by
  unfold G.moe isExpL
  rw [T.p3, Bool.true_and]

/-- The library's value of an array without an offset. -/
theorem TiesG.val0 (T : TiesG P g cell D t) (X : Arr) (hX : readsG X = true) (h0 : X.off = 0)
    (inst j i : ℕ) :
    Inst.Model.FFSeg.val t X inst j i = G.ten P cell (arrName X) inst j i := by
  rw [T.val X hX, h0, Int.cast_zero, add_zero]

/-- The product of v. -/
theorem TiesW.Av_eq (T : TiesG P g cell D t) (W : TiesW P g cell D t tb L0 w) {lam : ℕ}
    (hlam : lam < D.nl) (x i : ℕ) :
    Av D t w lam x i = G.sumN P.y.h.d fun k2 =>
      G.ten P cell "a" lam k2 i * G.wt P cell 1 (g * P.y.Lam + lam) [k2, x] := by
  unfold Av
  rw [sumN_eq, W.d, W.w lam hlam]
  refine sum_congr rfl fun j _ => ?_
  rw [T.val0 .a rfl rfl]
  rfl

/-- The product of the attention output. -/
theorem TiesW.Ao_eq (W : TiesW P g cell D t tb L0 w) (T : TiesG P g cell D t) {lam : ℕ}
    (hlam : lam < D.nl) (x i : ℕ) :
    (∑ j ∈ range D.dq, val t .o lam j i * (w lam).Wo j x) = G.sumN P.y.dq fun k2 =>
      G.attO P g cell lam k2 i * G.wt P cell 2 (g * P.y.Lam + lam) [k2, x] := by
  rw [sumN_eq, T.dq, W.w lam hlam]
  refine sum_congr rfl fun j _ => ?_
  unfold G.attO
  rw [W.valO, W.p4, if_pos rfl]
  rfl

/-- The router's product. -/
theorem TiesW.Ar_eq (T : TiesG P g cell D t) (W : TiesW P g cell D t tb L0 w) {lam : ℕ}
    (hlam : lam < D.nl) (x i : ℕ) :
    (∑ j ∈ range D.d, val t .m lam j i * (w lam).Wr j x) = G.sumN P.y.h.d fun k2 =>
      G.ten P cell "m" lam k2 i * G.wt P cell 11 (g * P.y.Lam + lam) [k2, x] := by
  rw [sumN_eq, W.d, W.w lam hlam]
  refine sum_congr rfl fun j _ => ?_
  rw [T.val0 .m rfl rfl]
  rfl

/-- The gate's accumulator. -/
theorem TiesW.Ag_eq (T : TiesG P g cell D t) (W : TiesW P g cell D t tb L0 w) {lam : ℕ}
    (hlam : lam < D.nl) (x i : ℕ) :
    Ag D t w lam x i = if G.routed P lam x then G.accRouted P g cell false lam x i
      else G.accDense P g cell false lam x i := by
  rw [T.routed_eq]
  unfold Ag
  by_cases hr : Inst.Model.FFSeg.routed D lam x = true
  · rw [if_pos hr, if_pos hr]
    show _ = G.sumN P.y.h.NE fun e =>
      G.ten P cell "sel" (lam / 2) e i *
        G.sumN P.y.h.d fun k2 =>
          G.ten P cell "xr" (lam / 2) k2 i *
            G.wt P cell 7 (g * P.y.Lam + lam) [k2, e, x - P.y.h.fe]
    rw [sumN_eq, T.NE, W.w lam hlam]
    refine sum_congr rfl fun e _ => ?_
    rw [sumN_eq, W.d, T.val0 .sel rfl rfl, T.fe]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [T.val0 .xr rfl rfl]
    rfl
  · rw [if_neg hr, if_neg hr]
    show _ = G.sumN P.y.h.d fun k2 =>
      G.ten P cell "m" lam k2 i *
        G.wt P cell (if G.moe P lam then 5 else 3) (g * P.y.Lam + lam) [k2, x]
    rw [sumN_eq, W.d, W.w lam hlam]
    refine sum_congr rfl fun j _ => ?_
    rw [T.val0 .m rfl rfl]
    rfl

/-- The up product's accumulator. -/
theorem TiesW.Au_eq (T : TiesG P g cell D t) (W : TiesW P g cell D t tb L0 w) {lam : ℕ}
    (hlam : lam < D.nl) (x i : ℕ) :
    Au D t w lam x i = if G.routed P lam x then G.accRouted P g cell true lam x i
      else G.accDense P g cell true lam x i := by
  rw [T.routed_eq]
  unfold Au
  by_cases hr : Inst.Model.FFSeg.routed D lam x = true
  · rw [if_pos hr, if_pos hr]
    show _ = G.sumN P.y.h.NE fun e =>
      G.ten P cell "sel" (lam / 2) e i *
        G.sumN P.y.h.d fun k2 =>
          G.ten P cell "xr" (lam / 2) k2 i *
            G.wt P cell 8 (g * P.y.Lam + lam) [k2, e, x - P.y.h.fe]
    rw [sumN_eq, T.NE, W.w lam hlam]
    refine sum_congr rfl fun e _ => ?_
    rw [sumN_eq, W.d, T.val0 .sel rfl rfl, T.fe]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [T.val0 .xr rfl rfl]
    rfl
  · rw [if_neg hr, if_neg hr]
    show _ = G.sumN P.y.h.d fun k2 =>
      G.ten P cell "m" lam k2 i *
        G.wt P cell (if G.moe P lam then 6 else 4) (g * P.y.Lam + lam) [k2, x]
    rw [sumN_eq, W.d, W.w lam hlam]
    refine sum_congr rfl fun j _ => ?_
    rw [T.val0 .m rfl rfl]
    rfl

/-- The gated product. -/
theorem TiesG.hh_eq (T : TiesG P g cell D t) (lam j i : ℕ) :
    hh t lam j i = G.gated P cell lam j i := by
  unfold hh G.gated
  rw [T.val0 .sl rfl rfl, T.val0 .up rfl rfl]
  rfl

/-- The chosen expert's logit. -/
theorem TiesG.mr_eq (T : TiesG P g cell D t) (lam i : ℕ) :
    mr D t (lam / 2) i = G.selLr P cell lam i := by
  unfold mr G.selLr
  rw [sumN_eq, T.NE]
  refine sum_congr rfl fun e _ => ?_
  rw [T.val0 .sel rfl rfl, T.val0 .lr rfl rfl]
  rfl

/-- The norm's reciprocal. -/
theorem TiesG.R_eq (T : TiesG P g cell D t) (ν i : ℕ) :
    Inst.Model.Ledger.R (led t ν i) = G.recip P cell ν i := by
  unfold G.recip
  rw [sumN_eq, T.xl]
  simp only [Inst.Model.Ledger.R, Inst.Model.Ledger.Rlo, Inst.Model.Ledger.Rhi,
    Inst.Model.Ledger.b256, led, G.dig, T.val .D rfl, arrName, Arr.off, sum_range_succ,
    sum_range_zero, beq_self_eq_true, if_true]
  push_cast
  ring

/-- The down product's accumulator, in its two parts. -/
theorem TiesW.Ad_eq (T : TiesG P g cell D t) (W : TiesW P g cell D t tb L0 w) {lam : ℕ}
    (hlam : lam < D.nl) (x i : ℕ) :
    (if isExpL lam then
        (∑ e ∈ range D.nx, val t .sel (lam / 2) e i *
          ∑ j ∈ range D.fe, hh t lam (D.fe + j) i * (w lam).Ed e j x)
      else 0) +
      (∑ j ∈ range (if isExpL lam then D.fe else D.f), hh t lam j i * (w lam).Wd j x) =
    G.accD P g cell lam x i := by
  unfold G.accD
  rw [T.moe_eq, W.w lam hlam, add_comm, sumN_eq, T.fe, W.f]
  congr 1
  · refine sum_congr rfl fun j _ => ?_
    rw [T.hh_eq]
    rfl
  · split_ifs
    · rw [sumN_eq, T.NE]
      refine sum_congr rfl fun e _ => ?_
      rw [sumN_eq, T.val0 .sel rfl rfl]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [T.hh_eq]
      rfl
    · rfl

/-- Queries and keys before the rotation. -/
theorem TiesW.AY_eq (T : TiesG P g cell D t) (W : TiesW P g cell D t tb L0 w) {lam : ℕ}
    (hlam : lam < D.nl) (x i : ℕ) :
    AY D t w lam x i = G.accQK P g cell lam (x / D.P.ch) (x % D.P.ch) i := by
  unfold AY Aq Ak G.accQK
  rw [sumN_eq, W.d, W.w lam hlam]
  split_ifs with hx
  · refine sum_congr rfl fun j _ => ?_
    rw [T.val0 .a rfl rfl, ← W.ch]
    rfl
  · refine sum_congr rfl fun j _ => ?_
    rw [T.val0 .a rfl rfl, ← W.ch]
    show _ * G.wt P cell 0 (g * P.y.Lam + lam)
      [(P.y.dq + (x - D.dq)) / P.y.h.dh, (P.y.dq + (x - D.dq)) % P.y.h.dh, j] = _
    rw [T.dq, Nat.add_sub_cancel' (Nat.le_of_not_lt hx)]
    rfl

omit scl in
/-- The next coordinate of an even coordinate lies in the same head. -/
theorem next_in_head {c x : ℕ} (hc : c % 2 = 0) (hx : x % c % 2 = 0) :
    (x + 1) / c = x / c ∧ (x + 1) % c = x % c + 1 := by
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · subst h0
    simp only [Nat.mod_zero] at hx ⊢
    simp
  · have h1 : x % c < c := Nat.mod_lt x hpos
    have h2 : x % c + 1 < c := by omega
    have h3 : x + 1 = c * (x / c) + (x % c + 1) := by
      have := Nat.div_add_mod x c
      omega
    constructor
    · conv_lhs => rw [h3]
      rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt h2, Nat.add_zero]
    · conv_lhs => rw [h3]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h2]

end Ties

section Main

variable {K : Type} [Field K] [scl : Scl] {P : Model.Layer.Pub} {g : ℕ} {cell : G.NameG → K}
  {D : Dim} {t : Cell → K} {tb : Tables} {L0 : ℕ} {w : ℕ → LW K}

omit scl in
/-- The coordinate before an odd coordinate lies in the same head. -/
theorem prev_in_head {c x : ℕ} (hx : x % c % 2 = 1) :
    (x - 1) / c = x / c ∧ (x - 1) % c = x % c - 1 := by
  rcases Nat.eq_zero_or_pos c with h0 | hpos
  · subst h0
    simp
  · have h1 : x % c < c := Nat.mod_lt x hpos
    have h3 : x - 1 = c * (x / c) + (x % c - 1) := by
      have := Nat.div_add_mod x c
      omega
    have h2 : x % c - 1 < c := by omega
    constructor
    · conv_lhs => rw [h3]
      rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt h2, Nat.add_zero]
    · conv_lhs => rw [h3]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h2]

/-- Entry x of q and k after the rotation. -/
theorem TiesW.Y_eq (T : TiesG P g cell D t) (W : TiesW P g cell D t tb L0 w) {lam : ℕ}
    (hlam : lam < D.nl) (x i : ℕ) : Y' D t tb L0 w lam x i = G.rotQK P g cell lam x i := by
  have hR : G.rotQK P g cell lam x i =
      if (x % P.y.h.dh % 2 == 0) = true then
        ((Model.Layer.ropeC P.y.h P.sc P.rope (g * P.y.Lam + lam) i (x % P.y.h.dh / 2) false : ℤ) :
            K) * G.accQK P g cell lam (x / P.y.h.dh) (x % P.y.h.dh) i -
          ((Model.Layer.ropeC P.y.h P.sc P.rope (g * P.y.Lam + lam) i (x % P.y.h.dh / 2) true : ℤ) :
            K) * G.accQK P g cell lam (x / P.y.h.dh) (x % P.y.h.dh + 1) i
      else
        ((Model.Layer.ropeC P.y.h P.sc P.rope (g * P.y.Lam + lam) i (x % P.y.h.dh / 2) true : ℤ) :
            K) * G.accQK P g cell lam (x / P.y.h.dh) (x % P.y.h.dh - 1) i +
          ((Model.Layer.ropeC P.y.h P.sc P.rope (g * P.y.Lam + lam) i (x % P.y.h.dh / 2) false :
            ℤ) : K) * G.accQK P g cell lam (x / P.y.h.dh) (x % P.y.h.dh) i := rfl
  rw [hR, W.ch]
  unfold Y'
  simp only [W.AY_eq T hlam, W.C lam hlam, W.S lam hlam, beq_iff_eq]
  split_ifs with h
  · rw [(next_in_head W.even h).1, (next_in_head W.even h).2]
  · have h1 : x % D.P.ch % 2 = 1 := by omega
    rw [(prev_in_head h1).1, (prev_in_head h1).2]

/-- **The product parts of the library's key are G.lean's gamG: all 34 families.** -/
theorem TiesW.parts_gamG (T : TiesG P g cell D t) (W : TiesW P g cell D t tb L0 w) (s : Fam)
    (lam x i : ℕ) (hlam : lam < D.nl) (hp : present s lam = true) :
    term D t tb L0 w s lam x i + mat D t w s lam x i = G.gamG P g cell (segName s) lam x i := by
  cases s
  case G =>
    have hR : G.gamG P g cell "G" lam x i = 2 ^ (16 - G.kGU P g false lam x) *
        (if G.routed P lam x then G.accRouted P g cell false lam x i
          else G.accDense P g cell false lam x i) := rfl
    show term D t tb L0 w .G lam x i + mat D t w .G lam x i = G.gamG P g cell "G" lam x i
    rw [hR, ← W.Ag_eq T hlam, T.kGU_false hlam]
    simp only [term, mat, kG, Inst.Model.Site.scl_eq, Inst.Model.Site.dn]
    split_ifs <;> ring
  case U =>
    have hR : G.gamG P g cell "U" lam x i = 2 ^ (16 - G.kGU P g true lam x) *
        (if G.routed P lam x then G.accRouted P g cell true lam x i
          else G.accDense P g cell true lam x i) := rfl
    show term D t tb L0 w .U lam x i + mat D t w .U lam x i = G.gamG P g cell "U" lam x i
    rw [hR, ← W.Au_eq T hlam, T.kGU_true hlam]
    simp only [term, mat, kU, Inst.Model.Site.scl_eq, Inst.Model.Site.dn]
    split_ifs <;> ring
  case V =>
    have hR : G.gamG P g cell "V" lam x i = 2 ^ (16 - G.kL P g lam Model.Layer.Lkv) *
        G.sumN P.y.h.d fun k2 =>
          G.ten P cell "a" lam k2 i * G.wt P cell 1 (g * P.y.Lam + lam) [k2, x] := rfl
    show term D t tb L0 w .V lam x i + mat D t w .V lam x i = G.gamG P g cell "V" lam x i
    rw [hR, ← W.Av_eq T hlam, show G.kL P g lam Model.Layer.Lkv = (D.Pl lam).kv from T.kv lam hlam]
    simp only [term, mat, Inst.Model.Site.scl_eq, Inst.Model.Site.dn, zero_add]
  case O =>
    have hR : G.gamG P g cell "O" lam x i = 2 ^ (16 - G.kL P g lam Model.Layer.Lko) *
        G.sumN P.y.dq fun k2 =>
          G.attO P g cell lam k2 i * G.wt P cell 2 (g * P.y.Lam + lam) [k2, x] := rfl
    show term D t tb L0 w .O lam x i + mat D t w .O lam x i = G.gamG P g cell "O" lam x i
    rw [hR, ← W.Ao_eq T hlam, show G.kL P g lam Model.Layer.Lko = (D.Pl lam).ko from T.ko lam hlam]
    simp only [term, mat, Inst.Model.Site.scl_eq, Inst.Model.Site.dn, zero_add]
  case LR =>
    have hR : G.gamG P g cell "LR" lam x i = 2 ^ (16 - G.kR P g lam) *
        G.sumN P.y.h.d fun k2 =>
          G.ten P cell "m" lam k2 i * G.wt P cell 11 (g * P.y.Lam + lam) [k2, x] := rfl
    show term D t tb L0 w .LR lam x i + mat D t w .LR lam x i = G.gamG P g cell "LR" lam x i
    rw [hR, ← W.Ar_eq T hlam,
      show G.kR P g lam = (D.Pl lam).kr from T.kr lam hlam (odd_of_present rfl hp)]
    simp only [term, mat, Inst.Model.Site.scl_eq, Inst.Model.Site.dn, zero_add]
  case D =>
    have hR : G.gamG P g cell "D" lam x i =
        2 ^ (16 - G.kL P g lam Model.Layer.Lkd) * G.accD P g cell lam x i := rfl
    show term D t tb L0 w .D lam x i + mat D t w .D lam x i = G.gamG P g cell "D" lam x i
    rw [hR, ← W.Ad_eq T hlam, show G.kL P g lam Model.Layer.Lkd = (D.Pl lam).kd from T.kd lam hlam]
    simp only [term, mat, Inst.Model.Site.scl_eq, Inst.Model.Site.dn]
    split_ifs <;> ring
  case N1 =>
    have hR : G.gamG P g cell "N1" lam x i = 2 ^ (16 - G.kL P g lam Model.Layer.LK1) *
        (G.recip P cell (2 * lam) i * G.xs P cell (2 * lam) x i) := rfl
    show term D t tb L0 w .N1 lam x i + mat D t w .N1 lam x i = G.gamG P g cell "N1" lam x i
    rw [hR, show G.kL P g lam Model.Layer.LK1 = (D.Pl lam).n1.K from T.K1 lam hlam,
      Nat.sub_eq_zero_of_le (T.K1le lam hlam), ← T.R_eq,
      ← T.xs _ x i (show 2 * lam ≤ 2 * D.nl by omega)]
    simp only [term, mat]
    ring
  case N2 =>
    have hR : G.gamG P g cell "N2" lam x i = 2 ^ (16 - G.kL P g lam Model.Layer.LK2) *
        (G.recip P cell (2 * lam + 1) i * G.xs P cell (2 * lam + 1) x i) := rfl
    show term D t tb L0 w .N2 lam x i + mat D t w .N2 lam x i = G.gamG P g cell "N2" lam x i
    rw [hR, show G.kL P g lam Model.Layer.LK2 = (D.Pl lam).n2.K from T.K2 lam hlam,
      Nat.sub_eq_zero_of_le (T.K2le lam hlam), ← T.R_eq,
      ← T.xs _ x i (show 2 * lam + 1 ≤ 2 * D.nl by omega)]
    simp only [term, mat]
    ring
  case QK =>
    have hR : G.gamG P g cell "QK" lam x i =
        2 ^ (16 - G.kQK P g lam x) * G.rotQK P g cell lam x i := rfl
    show term D t tb L0 w .QK lam x i + mat D t w .QK lam x i = G.gamG P g cell "QK" lam x i
    rw [hR, ← W.Y_eq T hlam, T.kQK_eq hlam]
    simp only [term, mat, Inst.Model.Site.scl_eq, Inst.Model.Site.dn, add_zero]
  case XR =>
    have hR : G.gamG P g cell "XR" lam x i =
        G.ten P cell "sc" (lam / 2) 0 i * G.ten P cell "m" lam x i := rfl
    show term D t tb L0 w .XR lam x i + mat D t w .XR lam x i = G.gamG P g cell "XR" lam x i
    rw [hR]
    simp only [term, mat, add_zero, T.val0 .sc rfl rfl, T.val0 .m rfl rfl, arrName]
  case DD =>
    have hR : G.gamG P g cell "DD" lam x i = G.selLr P cell lam i := rfl
    show term D t tb L0 w .DD lam x i + mat D t w .DD lam x i = G.gamG P g cell "DD" lam x i
    rw [hR, ← T.mr_eq]
    simp only [term, mat, add_zero]
  case MR =>
    have hR : G.gamG P g cell "MR" lam x i = G.selLr P cell lam i := rfl
    show term D t tb L0 w .MR lam x i + mat D t w .MR lam x i = G.gamG P g cell "MR" lam x i
    rw [hR, ← T.mr_eq]
    simp only [term, mat, add_zero]
  all_goals exact add_zero _

/-- **THE LIBRARY's KEY IS G.lean's segG: all 34 families.** -/
theorem TiesW.key_segG (T : TiesG P g cell D t) (W : TiesW P g cell D t tb L0 w) (s : Fam)
    (lam x i : ℕ) (hlam : lam < D.nl) (hp : present s lam = true) :
    key D t tb L0 w s lam x i = G.segG P g cell (segName s) lam x i := by
  rw [Inst.Model.FFSeg.key_eq, add_assoc, T.lin_affG tb L0 w s lam x i hlam hp,
    W.parts_gamG T s lam x i hlam hp]
  rfl

end Main

#print axioms TiesW.parts_gamG
#print axioms TiesW.key_segG

end OnBytes.Road.Alg
