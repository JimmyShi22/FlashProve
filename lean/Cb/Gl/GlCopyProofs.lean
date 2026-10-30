-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gl/GlCopyProofs.lean: the proofs of the statements of Cb/Gl/GlCopy.lean (copied rows over
p = 2^64 - 2^32 + 1).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

A copied row: a short Reed-Solomon code whose codewords are written out c times as one long word
(`rsCp a b k msg r`, for a ≤ b ≤ 32, with c = 2^(b - a)).
Two small facts carry all, with c = 2^(b - a): for a ≤ b ≤ 32 the long point `pts b j` to the power
c is the short point `pts a (cpDn a b j)`, at the position modulo the short length (`cp_pts_pow`); a
polynomial in X^c is a polynomial of degree at most c k whose other coefficients are 0
(`cp_sum_spread`). Laws, transparency, distance: the generic lemmas on families
(Cb/Ld/LdRelRepProofs.lean). Hiding: from the native family's, position by position. Nothing assumed
beyond the hypotheses of the statements and whatever the arguments hold as proofs.
-/
import Cb.Gl.GlCopy
import Cb.Ld.LdRelSubProofs
import Cb.Gen.CodeProofs

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks

theorem cp_root_pow {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 32) : root b ^ 2 ^ (b - a) = root a := by
  unfold root
  rw [← pow_mul, ← pow_add]
  congr 2
  omega

theorem cp_pts_pow {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 32) (j : Fin (2 ^ b)) :
    pts b j ^ 2 ^ (b - a) = pts a (cpDn a b j) := by
  have h1 : root a ^ 2 ^ a = 1 := by
    have h0 := pow_orderOf_eq_one (root a)
    rwa [gl_root_order a (le_trans hab hb)] at h0
  show (root b ^ (j : ℕ)) ^ 2 ^ (b - a) = root a ^ ((j : ℕ) % 2 ^ a)
  rw [← pow_mul, mul_comm, pow_mul, cp_root_pow hab hb, pow_eq_pow_mod _ h1]

/-- where the coefficient i goes -/
def cpUp (c k : ℕ) (i : Fin (k + 1)) : Fin (c * k + 1) :=
  ⟨c * (i : ℕ), Nat.lt_succ_of_le (Nat.mul_le_mul_left c (Nat.le_of_lt_succ i.2))⟩

theorem cpUp_inj {c : ℕ} (hc : 0 < c) (k : ℕ) : Function.Injective (cpUp c k) := fun _ _ h =>
  Fin.ext (Nat.eq_of_mul_eq_mul_left hc (congrArg Fin.val h))

theorem cp_sum_spread {K : Type} [CommSemiring K] {c : ℕ} (hc : 0 < c) (k : ℕ)
    (v : Fin (k + 1) → K) (x : K) :
    ∑ i' : Fin (c * k + 1), x ^ (i' : ℕ) * Function.extend (cpUp c k) v 0 i' =
      ∑ i : Fin (k + 1), x ^ (c * (i : ℕ)) * v i := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (cpUp c k))) (fun i' _ hi' => by
    rw [Function.extend_apply' _ _ _
        (fun ⟨i, hi⟩ => hi' (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩))]
    exact mul_zero _)]
  rw [Finset.sum_image fun i _ i' _ h => cpUp_inj hc k h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(cpUp_inj hc k).extend_apply]
  rfl

theorem cp_lt {a b k : ℕ} (hab : a ≤ b) (hk : k < 2 ^ a) : 2 ^ (b - a) * k < 2 ^ b := by
  have h : 2 ^ b = 2 ^ (b - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel hab]
  rw [h]
  exact Nat.mul_lt_mul_of_pos_left hk (pow_pos (by norm_num) _)

theorem glCp_enc : Spec.glCp_enc := by
  intro a b k msg r hab hb m ρ j
  show ∑ i : Fin (k + 1),
      algebraMap F E (pts b j ^ (2 ^ (b - a) * (i : ℕ))) * (rsCp a b k msg r).fm m ρ i =
    ∑ i : Fin (k + 1), algebraMap F E (pts a (cpDn a b j) ^ (i : ℕ)) * (rs a k msg r 0 0).fm m ρ i
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_mul, cp_pts_pow hab hb]
  rfl

theorem glCp_dist : Spec.glCp_dist := by
  intro a b k msg r hab hb hk v hv
  have hc : 0 < 2 ^ (b - a) := pow_pos (by norm_num) _
  have hne : Function.extend (cpUp (2 ^ (b - a)) k) v 0 ≠ 0 := by
    intro h0
    apply hv
    funext i
    have := congrFun h0 (cpUp (2 ^ (b - a)) k i)
    rwa [(cpUp_inj hc k).extend_apply] at this
  have hl := gl_rs_dist b (2 ^ (b - a) * k) 0 0 0 0 hb (cp_lt hab hk) _ hne
  refine le_trans hl (le_of_eq (cnt_congr fun j => ?_))
  have e1 : (rs b (2 ^ (b - a) * k) 0 0 0 0).G.mulVec
        (Function.extend (cpUp (2 ^ (b - a)) k) v 0) j =
      (rsCp a b k msg r).G.mulVec v j :=
    cp_sum_spread hc k v (pts b j)
  exact Iff.of_eq (congrArg (fun z => z ≠ 0) e1)

theorem glCp_code : Spec.glCp_code := by
  rintro P _ C d t ⟨A, _, _, a, b, k, msg, r, pos, mult, R, _, _, rfl, hab, hb, hk, hp, hE, hd, ht⟩
  have hdist : ∀ i, HasDist (grpCp a b k msg r i).G (grpCp a b k msg r i).d := fun i =>
    glCp_dist _ _ _ _ _ (hab i) (hb i) (hk i)
  have hpos : ∀ i, 0 < (grpCp a b k msg r i).d := fun i => Nat.sub_pos_of_lt (cp_lt (hab i) (hk i))
  have hl := ldr_laws F E A _ (⟨P, pos, mult⟩ : Reading (grpCp a b k msg r)) R hp hdist hpos
  refine ⟨hl, ldr_transparent F E A _ _ R, hl.loc, ldr_dist F E A _ _ R d hE hp hdist hd, ?_⟩
  -- hiding, from the native family's
  classical
  have hn := (gl_ld A a k msg r (fun i => le_trans (hab i) (hb i)) hk hp
      (⟨P, fun i x => cpDn (a i) (b i) (pos i x), mult⟩ : Reading (grp a k msg r)) R).2.2.1
    t ht
  refine (hides_iff_equiv _ ((⟨P, pos, mult⟩ : Reading (grpCp a b k msg r)).ld E R).Nn _).2
    fun S hS m m' => ?_
  obtain ⟨X, hX, hSX⟩ := hS
  let φ : (Σ i, Fin (2 ^ b i)) → Σ i, Fin (2 ^ a i) := fun q => ⟨q.1, cpDn (a q.1) (b q.1) q.2⟩
  have hS' : ((⟨P, fun i x => cpDn (a i) (b i) (pos i x), mult⟩ : Reading (grp a k msg r)).ld
        E R).budT
      t (Finset.image φ S) := by
    refine ⟨X, hX, fun q' hq' => ?_⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hq'
    obtain ⟨x, hx, hqx⟩ := Finset.mem_biUnion.1 (hSX hq)
    refine Finset.mem_biUnion.2
      ⟨x, hx, Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_singleton.2 ?_⟩⟩
    have h2 : q.2 = pos q.1 x := Finset.mem_singleton.1 (Finset.mem_sigma.1 hqx).2
    show cpDn (a q.1) (b q.1) q.2 = cpDn (a q.1) (b q.1) (pos q.1 x)
    rw [h2]
  obtain ⟨e, he⟩ := (hides_iff_equiv _
      ((⟨P, fun i x => cpDn (a i) (b i) (pos i x), mult⟩ : Reading (grp a k msg r)).ld E R).Nn _).1
    hn (Finset.image φ S) hS' m m'
  refine ⟨e, fun ρ q hq => ?_⟩
  have h1 := he ρ (φ q) (Finset.mem_image_of_mem φ hq)
  have h2 := eq_of_heq (Sigma.mk.inj h1).2
  refine congrArg (Sigma.mk q) (funext fun s => ?_)
  have h3 := congrFun h2 s
  exact (glCp_enc _ _ _ _ _ (hab q.1) (hb q.1) _ _ q.2).trans
    (h3.trans (glCp_enc _ _ _ _ _ (hab q.1) (hb q.1) _ _ q.2).symm)

theorem glCp_mono : Spec.glCp_mono := by
  rintro P _ C d t d' t'
    ⟨A, iA, dA, a, b, k, msg, r, pos, mult, R, fR, dR, hC, hab, hb, hk, hp, hE, hd, ht⟩ h1 h2
  exact ⟨A, iA, dA, a, b, k, msg, r, pos, mult, R, fR, dR, hC, hab, hb, hk, hp, hE,
    fun i => le_trans h1 (hd i), fun i => le_trans h2 (ht i)⟩

theorem glCp_atPos : Spec.glCp_atPos := by
  rintro P P' _ _ C d t pos' m
    ⟨A, iA, dA, a, b, k, msg, r, pos, mult, R, fR, dR, rfl, hab, hb, hk, hp, hE, hd, ht⟩ hm hpos
  refine ⟨A, iA, dA, a, b, k, msg, r, fun i x => pos i (pos' x), fun i => m * mult i, R, fR, dR,
    rfl, hab, hb, hk, hp, fun i => ⟨Nat.mul_pos hm (hE i).1, fun y => ?_⟩, fun i => ?_, ht⟩
  · have e := CodeRep.cnt_comp_even pos' m hpos fun z => pos i z = y
    exact e.trans (congrArg (m * ·) ((hE i).2 y))
  · rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left m (hd i)

theorem glCpJ_cp : Spec.glCpJ_cp := by
  rintro P _ C d t e bad
    ⟨A, iA, dA, a, b, k, msg, r, pos, mult, R, fR, dR, hC, hab, hb, -, hk, hp, hE, hd, ht, -, -⟩
  exact ⟨A, iA, dA, a, b, k, msg, r, pos, mult, R, fR, dR, hC, hab, hb, hk, hp, hE, hd, ht⟩

theorem glCpJ_mono : Spec.glCpJ_mono := by
  rintro P _ C d t e bad t'
    ⟨A, iA, dA, a, b, k, msg, r, pos, mult, R, fR, dR, hC, hab, hb, hk0, hk,
      hp, hE, hd, ht, hm, hbd⟩ h2
  exact ⟨A, iA, dA, a, b, k, msg, r, pos, mult, R, fR, dR, hC, hab, hb, hk0, hk, hp, hE, hd,
    fun i => le_trans h2 (ht i), hm, hbd⟩

theorem glCp_sub : Spec.glCp_sub := by
  intro A _ _ a b k msg r P _ pos mult R _ _
  refine ⟨fun α => ⟨α, rfl⟩, fun f' => ⟨f', fun _ _ => rfl⟩, fun m' r' => ?_⟩
  refine ⟨fun n =>
      Function.extend (cpUp (2 ^ (b n.1 - a n.1)) (k n.1))
        ((rsCp (a n.1) (b n.1) (k n.1) (msg n.1) (r n.1)).fm
          (fun j => m' ⟨n.1, (n.2.1, j)⟩) (fun q => r' ⟨n.1, (n.2.1, q)⟩))
        0 n.2.2,
    fun n => Fin.elim0 n.2.2,
    fun x α => ?_⟩
  obtain ⟨i, ρ, u⟩ := α
  have hc : 0 < 2 ^ (b i - a i) := pow_pos (by norm_num) _
  have h := cp_sum_spread hc (k i)
    ((rsCp (a i) (b i) (k i) (msg i) (r i)).fm (fun j => m' ⟨i, (ρ, j)⟩) (fun q => r' ⟨i, (ρ, q)⟩))
    (algebraMap F E (pts (b i) (pos i x)))
  show ∑ i' : Fin (k i + 1),
      algebraMap F E (pts (b i) (pos i x) ^ (2 ^ (b i - a i) * (i' : ℕ))) * _ =
    ∑ i' : Fin (2 ^ (b i - a i) * k i + 1), algebraMap F E (pts (b i) (pos i x) ^ (i' : ℕ)) *
      (rs (b i) (2 ^ (b i - a i) * k i) (2 ^ (b i - a i) * k i + 1) 0 0 0).fm _ _ i'
  simp only [map_pow]
  rw [← h]
  refine Finset.sum_congr rfl fun i' _ => ?_
  congr 1
  show _ = if h : (i' : ℕ) < 2 ^ (b i - a i) * k i + 1 then _ else _
  rw [dif_pos i'.2]
  rfl

end Cb.Gl
