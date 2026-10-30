-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ClaimRdOf.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the weight claims: WHAT THE CLAIMS READ AT
THE BLANK STRUCTURE IS THERE: the two bundles of hypotheses ClaimRd (ClaimsKit.lean) and QkRd
(ClaimsQK.lean) hold at the structure with every challenge and coordinate 0 (blankClaims,
Johnson/Desc/First/K4/Returns/Pub/ClaimsB.lean). From the layout's return, the switches, profile 4,
the eight lines, the layout of the weights with its ties to the library's sizes, and that the
plan's number of rounds is the function lamSOf of the layout. Statements and proofs. General in the
sizes.

  `pow_le_lamS`     a panel's bits are at most the rounds.
  `sum_bounds`, `bits_lamS`   the five bounds on bits.
  `blank_zk`        a blank point has the lookup's number of coordinates.
  **`claimRd_of`**, **`qkRd_of`**   the two bundles.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. AT A LAYOUT
WHOSE EIGHT LINES OF CALLS ARE THE LIBRARY's, UNDER THE LIBRARY's ELEVEN SWITCHES ALONE, at profile
4, AND A LAYOUT OF THE WEIGHTS THAT wsLayOf RETURNS FOR A MODEL WITH ROUTED EXPERTS. Public data
alone: numbers and sizes; nothing on an element. No property is claimed.
-/
import Johnson.Road.K4.C.SegRdOf
import Johnson.Road.K4.C.ClaimsQK
import Johnson.Road.K4.C.PansBOf
import Johnson.Desc.First.K4.Returns.Pub.ClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Pub HPlan2 layout lamSOf)
open OnBytes.Desc.First.K4.RtPub (blankClaims blankZk zkSize)
open Inst.Model.FFSeg (Dim)

/-- Bits whose power is at most a number are at most that number's rounded-up logarithm. -/
theorem pow_le_lamS {a n : ℕ} (h : 2 ^ a ≤ n) : a ≤ ceilLog2 n :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_trans h (le_pow_ceil n))

/-- Five members of a sum of natural numbers are at most the sum. -/
theorem sum_bounds (B E G W N O Q X d q f j k : ℕ) (p1 : d ≤ B) (p2 : q ≤ E) (p3 : f ≤ G)
    (m1 : 2 * j + k ≤ X) :
    d ≤ 4 * B + E + G + 2 * W + (N + O + 2 * Q + X) ∧
      q ≤ 4 * B + E + G + 2 * W + (N + O + 2 * Q + X) ∧
      f ≤ 4 * B + E + G + 2 * W + (N + O + 2 * Q + X) ∧
      j ≤ 4 * B + E + G + 2 * W + (N + O + 2 * Q + X) ∧
      k ≤ 4 * B + E + G + 2 * W + (N + O + 2 * Q + X) :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- **The five bounds on bits**: the columns of each kind of panel, and with the selector its rows
too, have at most as many bits as the batched sumcheck has rounds. -/
theorem bits_lamS {y : Lay} (h3 : y.h.p3 = true) (hM : 0 < y.LamM) :
    ceilLog2 y.h.d ≤ lamSOf y ∧ ceilLog2 y.dq ≤ lamSOf y ∧ ceilLog2 y.h.f ≤ lamSOf y ∧
      ceilLog2 y.h.d + ceilLog2 (max y.h.NE 1) ≤ lamSOf y ∧
      ceilLog2 y.h.fe + ceilLog2 (max y.h.NE 1) ≤ lamSOf y := by
  rw [ceilLog2_max]
  unfold lamSOf
  dsimp only
  rw [if_pos h3]
  have p : ∀ a b : ℕ, 2 ^ b ≤ 2 ^ (a + b) := fun a b =>
    Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
  have m : ∀ x : ℕ, x ≤ y.LamM * x := fun x => Nat.le_mul_of_pos_left x hM
  have c : ∀ a b : ℕ, 2 ^ (a + b) = 2 ^ (b + a) := fun a b => by rw [Nat.add_comm]
  have p1 := p (ceilLog2 y.Lam) (ceilLog2 y.h.d)
  have p2 := p (ceilLog2 y.Lam) (ceilLog2 y.dq)
  have p3 := p (ceilLog2 y.Lam) (ceilLog2 y.h.f)
  have m1 := m (2 * 2 ^ (ceilLog2 y.h.NE + ceilLog2 y.h.d) +
    2 ^ (ceilLog2 y.h.NE + ceilLog2 y.h.fe))
  have c1 := c (ceilLog2 y.h.d) (ceilLog2 y.h.NE)
  have c2 := c (ceilLog2 y.h.fe) (ceilLog2 y.h.NE)
  obtain ⟨t1, t2, t3, t4, t5⟩ := sum_bounds (2 ^ (ceilLog2 y.Lam + ceilLog2 y.h.d))
    (2 ^ (ceilLog2 y.Lam + ceilLog2 y.dq)) (2 ^ (ceilLog2 y.Lam + ceilLog2 y.h.f))
    (2 ^ ceilLog2 y.Lam) (2 ^ (ceilLog2 y.LamM + ceilLog2 y.h.d)) (2 ^ ceilLog2 y.LamM)
    (2 ^ (ceilLog2 y.LamM + ceilLog2 y.h.NE))
    (y.LamM * (2 * 2 ^ (ceilLog2 y.h.NE + ceilLog2 y.h.d) +
      2 ^ (ceilLog2 y.h.NE + ceilLog2 y.h.fe)))
    (2 ^ ceilLog2 y.h.d) (2 ^ ceilLog2 y.dq) (2 ^ ceilLog2 y.h.f)
    (2 ^ (ceilLog2 y.h.NE + ceilLog2 y.h.d)) (2 ^ (ceilLog2 y.h.NE + ceilLog2 y.h.fe)) p1 p2 p3 m1
  exact ⟨pow_le_lamS t1, pow_le_lamS t2, pow_le_lamS t3, pow_le_lamS (by rw [c1]; exact t4),
    pow_le_lamS (by rw [c2]; exact t5)⟩

/-- A blank point has the lookup's number of coordinates. -/
theorem blank_zk {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {P : Pub}
    (hy : layout h pc = .ok P.y) {q : ℕ} (hq : q < P.y.calls.size) :
    ((blankZk P).getD q #[]).size = ((P.y.fo.calls[q]?).map (·.n)).getD 0 := by
  obtain ⟨-, e1, e2⟩ := fo_of_layout hy
  unfold blankZk
  rw [getD_range_map _ _ _ _ (by rw [e1, e2]; exact hq), Array.size_replicate]
  rfl

variable {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {P : Pub} {hp : HPlan2}
  {g : ℕ} {s : WsShape} {D : Dim} {lk : ℕ}

/-- **WHAT THE CLAIMS READ AT THE BLANK STRUCTURE IS THERE.** CONDITIONAL: on the layout's return,
the switches, profile 4, a group of the layout, the eight lines, the ties of the sizes (Z, Zw,
hsL), the layout of the weights (hlw) and the plan's rounds (h1). -/
theorem claimRd_of (hy : layout h pc = .ok P.y) (S : Switches h) (h4 : h.p4 = true)
    (hg : g < P.y.NGr) (hN : LinesAre P.y) (Z : Sized h D) (Zw : SizedW s D.P) (hsL : s.L = h.L)
    (hlw : wsLayOf s true lk = .ok P.wsLay) (h1 : hp.lamS = lamSOf P.y) :
    ClaimRd (blankClaims P hp g) s D.P lk := by
  have A := admitted_of_layout hy S.p3
  have L := A.laid
  have es := A.shape
  subst es
  obtain ⟨-, -, -, B⟩ := wsLayOf_units hlw
  have f5 : WsLay.inWords s.d = true ∧ WsLay.inWords s.dh = true ∧ WsLay.inWords s.dkv = true ∧
      WsLay.inWords s.dq = true ∧ WsLay.inWords s.f = true := by simpa using B.five
  obtain ⟨wd, -, wkv, wq, wf⟩ := f5
  obtain ⟨k, hk⟩ : ∃ k, P.y.h.ll = k + 1 := ⟨P.y.h.ll - 1, by have := L.ll; omega⟩
  have e2 : 2 ^ P.y.h.ll = 2 * 2 ^ k := by rw [hk, Nat.pow_succ, Nat.mul_comm]
  have hkp := Nat.two_pow_pos k
  have hM : 0 < P.y.LamM := by
    rw [L.LamM, e2]
    omega
  have td : s.d = P.y.h.d := Zw.d.trans Z.d
  have tdq : s.dq = P.y.dq := by rw [Zw.dq, Z.nq, Z.ch, L.dq]
  have tdkv : s.dkv = P.y.dkv := by rw [Zw.dkv, Z.nkv, Z.ch, L.dkv]
  have tf : s.f = P.y.h.f := Zw.f.trans Z.f
  have tfe : s.fe = P.y.h.fe := Zw.fe.trans Z.fe
  have tNE : s.NE = P.y.h.NE := Zw.NE.trans Z.nexp
  have hf0 : 0 < P.y.h.f := tf ▸ (lt_of_inWords wf).1
  have hNE0 : 0 < P.y.h.NE := by
    have a3 := S.p3
    unfold OnBytes.Model.Layer.Shape.p3 at a3
    unfold OnBytes.Model.Layer.Shape.p4 at h4
    have e4 : P.y.h.prof = 4 := by simpa using h4
    rw [e4] at a3
    simpa using a3
  obtain ⟨b1, b2, b3, b4, b5⟩ := bits_lamS (y := P.y) S.p3 hM
  have hrs : (blankClaims P hp g).rs.size = lamSOf P.y := by
    show (Array.replicate hp.lamS zeroE).size = _
    rw [Array.size_replicate, h1]
  have hzk : ∀ q, q < (blankClaims P hp g).v.y.calls.size →
      ((blankClaims P hp g).v.zk.getD q #[]).size =
        (((blankClaims P hp g).v.y.fo.calls[q]?).map (·.n)).getD 0 := fun q hq => blank_zk hy hq
  have Sg := segRd_of (c := blankClaims P hp g) hy S hN hzk
  exact {
    Z := Zw
    hlw := hlw
    p3 := S.p3
    lays := fun lam hl => by
      have hl' : lam < 2 ^ P.y.h.ll := by
        rw [← L.Lam]
        exact hl
      have hg' : g + 1 ≤ P.y.h.L / 2 ^ P.y.h.ll := by
        rw [← A.NGr]
        exact hg
      have h5 := Nat.le_trans (Nat.mul_le_mul_right (2 ^ P.y.h.ll) hg')
        (Nat.div_mul_le_self _ _)
      rw [Nat.succ_mul] at h5
      show g * P.y.Lam + lam < D.P.layers
      rw [← Zw.L, hsL, L.Lam]
      omega
    par := fun lam => by
      show (g * P.y.Lam + lam) % 2 = lam % 2
      rw [L.Lam, e2, Nat.mul_left_comm, Nat.mul_add_mod]
    odd := fun i hi => by
      have hi' : i < 2 ^ P.y.h.ll / 2 := by
        rw [← L.LamM]
        exact hi
      show 2 * i + 1 < P.y.Lam
      rw [L.Lam]
      omega
    d := td
    dq := tdq
    dkv := tdkv
    f := tf
    fe := tfe
    NE := tNE
    d0 := td ▸ (lt_of_inWords wd).1
    dq0 := tdq ▸ (lt_of_inWords wq).1
    dkv0 := tdkv ▸ (lt_of_inWords wkv).1
    fe0 := by
      have := L.ffe
      show 0 < P.y.h.fe
      omega
    NE0 := hNE0
    ffe := L.ffe
    bd := by rw [hrs]; exact b1
    bdq := by rw [hrs]; exact b2
    bf := by rw [hrs]; exact b3
    bde := by rw [hrs]; exact b4
    bfe := by rw [hrs]; exact b5
    sG := Sg .G
    sU := Sg .U
    sV := by
      have h6 : SegRd (blankClaims P hp g) "V" (P.y.h.Gk * P.y.h.dh) := Sg .V
      rw [← L.dkv] at h6
      exact h6
    sO := Sg .O
    sD := Sg .D
    sLR := Sg .LR }

/-- **WHAT THE WEIGHTS OF THE HEADS READ AT THE BLANK STRUCTURE IS THERE.** CONDITIONAL: on the
layout's return, the switches, the eight lines and the ties of the sizes (Z, Zw). -/
theorem qkRd_of (hy : layout h pc = .ok P.y) (S : Switches h) (hN : LinesAre P.y)
    (Z : Sized h D) (Zw : SizedW s D.P) : QkRd (blankClaims P hp g) s := by
  have A := admitted_of_layout hy S.p3
  have L := A.laid
  have Hh := headsLaid_of_layout hy
  have es := A.shape
  subst es
  have hzk : ∀ q, q < (blankClaims P hp g).v.y.calls.size →
      ((blankClaims P hp g).v.zk.getD q #[]).size =
        (((blankClaims P hp g).v.y.fo.calls[q]?).map (·.n)).getD 0 := fun q hq => blank_zk hy hq
  obtain ⟨q, cd, sg, hc, -, -, hz, hW⟩ := segRd_of (c := blankClaims P hp g) hy S hN hzk .QK
  have hdh0 : 0 < P.y.h.dh := by
    rw [Hh.pow]
    exact Nat.two_pow_pos _
  obtain ⟨tq, htq, -, -, -, jq, -⟩ := ten_of L S .q (Or.inl rfl)
  obtain ⟨tk, htk, -, -, -, jk, -⟩ := ten_of L S .kx (Or.inl rfl)
  exact {
    seg := ⟨q, cd, sg, hc, by
      rw [hz]
      have hW' : P.y.h.H * P.y.h.dh + P.y.h.Gk * P.y.h.dh ≤ 2 ^ cd.lJ := hW
      have hH : 1 ≤ P.y.h.H := Nat.pos_of_ne_zero A.H0
      have h7 : P.y.h.dh ≤ P.y.h.H * P.y.h.dh := Nat.le_mul_of_pos_left _ hH
      have h8 : 2 ^ P.y.ldh ≤ 2 ^ cd.lJ := by
        rw [← Hh.pow]
        omega
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h8⟩
    tq := ⟨tq, htq, jq⟩
    tk := ⟨tk, htk, jk⟩
    dh0 := hdh0
    dhe := by
      obtain ⟨k, hk⟩ : ∃ k, P.y.ldh = k + 1 := ⟨P.y.ldh - 1, by have := Hh.two; omega⟩
      show s.dh = 2 * (P.y.h.dh / 2)
      rw [Zw.dh, Z.ch, Hh.pow, hk, Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num),
        Nat.mul_comm] }

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.pow_le_lamS
#print axioms OnBytes.Road.K4.C.sum_bounds
#print axioms OnBytes.Road.K4.C.bits_lamS
#print axioms OnBytes.Road.K4.C.blank_zk
#print axioms OnBytes.Road.K4.C.claimRd_of
#print axioms OnBytes.Road.K4.C.qkRd_of
