-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PiecesTie.lean: kind K5: at every shape that the verifier's own
shapeHid returns at the usual call list: for each of the seven families of looked-up values: the
pieces of its list in its call are one for each pair, in the order of the pairs ("piece b is pair
b"), and each piece's weight, read, is the library's wp.

Main names:
  `KeyPt ρ fs key c p`: the key point of call c has the call's number of coordinates and, read, is
    the library's zC c p.z. A premise: the lookup's kind's to pay (zk_eq_zC,
    Johnson/Road/Lane5ZkZc.lean, says it of the array that the lookup's text lays, at one reading).
  `FamAt S q s f`: the conclusion for one family: for every key point with KeyPt:
    PiecesAll S (pieces (callAt S q) key s), and the weights.
  `fam_tie`: the general step, from how the call's pieces are laid.
  `seven_of_hid`: all seven: (0, rm, m1) (0, rd, d1) (1, fm, m2) (1, fd, d2) (2, wl, w3) (2, ix, x3)
    (3, wh, f4).
Premises of seven_of_hid: shapeHid lid cf = ok (S, fs); UsualCalls cf (a public test on the
configuration: usualB, Johnson/Road/Lane5AttLaid.lean).
Used: four_of_hid, FourCalls, famAt, dim_nums, shaped_of_hid, tests_of_hid, calls_of_hid, a_eq_n,
laidA_of_hid; PiecesFam.lean.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Lane5KvAll
import Johnson.Desc.First.Att.Claims.PiecesFam

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.L5 (famAt callAt FourCalls UsualCalls)
open Inst.Model.AttSeg (Pub Fam wp)

variable {Kf : Type} [Field Kf]

/-- The key point of call c, read, is the library's. -/
structure KeyPt (ρ : Reading Kf) (fs : Model.Forest.Shape) (key : Array E) (c : Fin 4)
    (p : Pub Kf) : Prop where
  size : key.size = (L5.callsOf fs).a c
  read : ∀ t < (L5.callsOf fs).a c, pt ρ key t = (L5.callsOf fs).zC c p.z t

/-- One family: piece b is pair b, and the weights are the library's. -/
def FamAt (ρ : Reading Kf) (S : Shape) (fs : Model.Forest.Shape) (p : Pub Kf) (q : Fin 4)
    (s : Attention.Seg) (f : Fam) : Prop :=
  ∀ key : Array E, KeyPt ρ fs key q p →
    PiecesAll S (pieces (callAt S q.val) key s) ∧
      ∀ b < S.NP, ρ.val ((pieces (callAt S q.val) key s).getD b default).wp =
        wp (L5.dimOf S) (L5.callsOf fs) p.z f b

/-- The general step. -/
theorem fam_tie (ρ : Reading Kf) {S : Shape} {fs : Model.Forest.Shape} (p : Pub Kf) {q : Fin 4}
    {s : Attention.Seg} {f : Fam} {A B : List Attention.Piece} {HA l base n : ℕ}
    (hq : f.call = q) (hp : (callAt S q.val).pcs.toList = A ++ famAt s HA l base n ++ B)
    (hA : ∀ pc ∈ A, (pc.seg == s) = false) (hB : ∀ pc ∈ B, (pc.seg == s) = false)
    (hHA : S.HA = HA) (hn : n = S.NP) (hl : f.l (L5.dimOf S) = l)
    (hb : base = 2 ^ l * f.nu0 (L5.dimOf S))
    (ha : (L5.callsOf fs).a q = (callAt S q.val).call.n) : FamAt ρ S fs p q s f := by
  intro key K
  rw [pieces_fam hp hA hB key]
  refine ⟨piecesAll_fam S key hHA hn, fun b hb' => ?_⟩
  rw [val_wp_fam ρ HA l base n _ (v := (L5.callsOf fs).zC q p.z) (K.size.trans ha)
    (fun t ht => K.read t (by rw [ha]; omega)) (by rw [hb]; exact Dvd.intro _ rfl)
    (by rw [hn]; exact hb'), hb, Nat.mul_div_cancel_left _ (Nat.two_pow_pos l)]
  unfold wp
  rw [hq, hl, ha]

theorem fam_other {s s' : Attention.Seg} (h : (s' == s) = false) (HA c base n : ℕ) :
    ∀ pc ∈ famAt s' HA c base n, (pc.seg == s) = false := by
  intro pc hpc
  unfold famAt at hpc
  obtain ⟨b, _, rfl⟩ := List.mem_map.1 hpc
  exact h

/-- **All seven families, at what shapeHid returns at the usual call list.** -/
theorem seven_of_hid (ρ : Reading Kf) {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Model.Forest.Shape}
    (hid : shapeHid lid cf = Except.ok (S, fs)) (U : UsualCalls cf) (p : Pub Kf) :
    FamAt ρ S fs p 0 .rm .m1 ∧ FamAt ρ S fs p 0 .rd .d1 ∧ FamAt ρ S fs p 1 .fm .m2 ∧
      FamAt ρ S fs p 1 .fd .d2 ∧ FamAt ρ S fs p 2 .wl .w3 ∧ FamAt ρ S fs p 2 .ix .x3 ∧
      FamAt ρ S fs p 3 .wh .f4 := by
  have Fo := L5.four_of_hid hid U
  have P := L5.shaped_of_hid hid
  obtain ⟨hlt, hpos⟩ := L5.tests_of_hid hid
  obtain ⟨hnb, hM, hD, hW, hX, h4⟩ := L5.dim_nums P hlt
  have La := L5.laidA_of_hid hid U
  have ha : ∀ q : Fin 4, (L5.callsOf fs).a q = (callAt S q.val).call.n :=
    fun q => L5.a_eq_n (L5.calls_of_hid hid) La.isCall q
  have hNP : 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) = S.NP := by
    show _ = S.Lam * S.HA
    rw [P.Lam, P.HA]
  have hnb' : (L5.dimOf S).nb = 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) := hnb
  have hMD : nDOf cf ≤ nMOf cf := by
    unfold nDOf nMOf
    omega
  have hWX : segBits cf .ix ≤ segBits cf .wl := by
    show cf.lgk + cf.lt ≤ 1 + cf.lgk + cf.lt + cf.ldh
    omega
  have bD : 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ nMOf cf =
      2 ^ nDOf cf * ((L5.dimOf S).nb * 2 ^ ((L5.dimOf S).lM - (L5.dimOf S).lD)) := by
    rw [hnb', hM, hD]
    have e : (2 : ℕ) ^ nMOf cf = 2 ^ nDOf cf * 2 ^ (nMOf cf - nDOf cf) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e]
    ring
  have bX : 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 2 ^ segBits cf .wl =
      2 ^ segBits cf .ix * ((L5.dimOf S).nb * 2 ^ ((L5.dimOf S).lW - (L5.dimOf S).lX)) := by
    rw [hnb', hW, hX]
    have e : (2 : ℕ) ^ segBits cf .wl =
        2 ^ segBits cf .ix * 2 ^ (segBits cf .wl - segBits cf .ix) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fam_tie ρ p (A := []) rfl (by rw [List.nil_append]; exact Fo.p0) (by simp)
      (fam_other rfl _ _ _ _) P.HA hNP hM (by simp [Fam.nu0]) (ha 0)
  · exact fam_tie ρ p (B := []) rfl (by rw [List.append_nil]; exact Fo.p0)
      (fam_other rfl _ _ _ _) (by simp) P.HA hNP hD bD (ha 0)
  · exact fam_tie ρ p (A := []) rfl (by rw [List.nil_append]; exact Fo.p1) (by simp)
      (fam_other rfl _ _ _ _) P.HA hNP hM (by simp [Fam.nu0]) (ha 1)
  · exact fam_tie ρ p (B := []) rfl (by rw [List.append_nil]; exact Fo.p1)
      (fam_other rfl _ _ _ _) (by simp) P.HA hNP hD bD (ha 1)
  · exact fam_tie ρ p (A := []) rfl (by rw [List.nil_append]; exact Fo.p2) (by simp)
      (fam_other rfl _ _ _ _) P.HA hNP hW (by simp [Fam.nu0]) (ha 2)
  · exact fam_tie ρ p (B := []) rfl (by rw [List.append_nil]; exact Fo.p2)
      (fam_other rfl _ _ _ _) (by simp) P.HA hNP hX bX (ha 2)
  · exact fam_tie ρ p (A := []) (B := []) rfl
      (by rw [List.nil_append, List.append_nil]; exact Fo.p3) (by simp) (by simp) P.HA hNP h4
      (by simp [Fam.nu0]) (ha 3)

end K5Law

#print axioms K5Law.seven_of_hid
