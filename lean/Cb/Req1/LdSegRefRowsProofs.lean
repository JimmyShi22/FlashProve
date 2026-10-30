-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefRowsProofs.lean: the statements of Cb/Req1/LdSegRefRows.lean, proved.

Rows of the range check: Cb/Ld/LdRngProofs.lean (`ldRng_rows`, `ldRng_placed`); the step: proved in
the manner of `ldPeel_base` (Cb/Ld/LdBatPeelProofs.lean), with a verifier that may reject, then
`ldSeg_step` (Cb/Req1/LdSegStep.lean).
What each statement says, and the limits: the head of Cb/Req1/LdSegRefRows.lean.
-/
import Cb.Req1.LdSegRefRows
import Cb.Req1.LdSegRefDigProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR

theorem ldSegRef_ga_sum : Spec.ldSegRef_ga_sum := by
  intro E _ p K v e d c hK
  have h1 : ∑ b ∈ Finset.range (2 ^ v), c b * rngKeys p e d b =
      ∑ b ∈ Finset.range K, c b * rngKeys p e d b := by
    symm
    refine Finset.sum_subset
      (fun b hb => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hb) hK)) fun b _ hb => ?_
    have hb' : ¬ b < K := fun h => hb (Finset.mem_range.2 h)
    unfold rngKeys pad
    rw [if_neg hb', mul_zero]
  rw [h1, ← Fin.sum_univ_eq_sum_range (fun b => c b * rngKeys p e d b) K, ← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun ru _ => ?_
  unfold rngKeys pad
  rw [if_pos (e ru).2]
  beta_reduce
  rw [dif_pos (e ru).2]
  simp

theorem ldSegRef_ga_keys : Spec.ldSegRef_ga_keys := by
  intro E Kc E₀ Wp _ Q x ms pt hK
  show ∑ X ∈ Finset.range (2 ^ (Q.v + 1)), eqN (Q.v + 1) 0 pt X *
      (Q.sh.key x.1 ms.2 (X / 2 ^ Q.v) (X % 2 ^ Q.v) + Q.tag (X / 2 ^ Q.v) * x.2) = _
  have hpos : 0 < 2 ^ Q.v := by positivity
  have e0 : ∑ X ∈ Finset.range (2 ^ (Q.v + 1)), eqN (Q.v + 1) 0 pt X *
        (Q.sh.key x.1 ms.2 (X / 2 ^ Q.v) (X % 2 ^ Q.v) + Q.tag (X / 2 ^ Q.v) * x.2) =
      ∑ X ∈ Finset.range (2 ^ (Q.v + 1)),
          eqN (Q.v + 1) 0 pt X * Q.sh.key x.1 ms.2 (X / 2 ^ Q.v) (X % 2 ^ Q.v) +
        x.2 * ∑ X ∈ Finset.range (2 ^ (Q.v + 1)), eqN (Q.v + 1) 0 pt X * Q.tag (X / 2 ^ Q.v) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun X _ => by ring
  rw [e0]
  congr 1
  have e2 : 2 ^ (Q.v + 1) = 2 ^ Q.v + 2 ^ Q.v := by rw [pow_succ]; ring
  rw [e2, Finset.sum_range_add]
  congr 1
  · rw [← ldSegRef_ga_sum E Q.D.p Q.K Q.v Q.e (Q.dg ms.2).1 (fun b => eqN (Q.v + 1) 0 pt b) hK]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' := Finset.mem_range.1 hb
    rw [Nat.div_eq_of_lt hb', Nat.mod_eq_of_lt hb']
    rfl
  · rw [← ldSegRef_ga_sum E Q.D.p Q.K Q.v Q.e (Q.dg ms.2).2
        (fun b => eqN (Q.v + 1) 0 pt (2 ^ Q.v + b)) hK]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' := Finset.mem_range.1 hb
    have d1 : (2 ^ Q.v + b) / 2 ^ Q.v = 1 := by
      rw [Nat.add_div_left _ hpos, Nat.div_eq_of_lt hb']
    have m1 : (2 ^ Q.v + b) % 2 ^ Q.v = b := by
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt hb']
    rw [d1, m1]
    rfl

theorem ldSegRef_ga_all : Spec.ldSegRef_ga_all := by
  intro E Kc E₀ Wp _ G x y m hR hK hn
  have hp : ∀ {I : Type} [Fintype I] (at' : I → G.Q.T.Ent) (a : I → E),
      ∑ nn, placed at' a nn * G.Q.T.ents m nn = ∑ i, a i * G.Q.T.ents m (at' i) :=
    fun {I} _ at' a => ldRng_placed I G.Q.T.Ent E at' a (G.Q.T.ents m)
  have k1 := ldRng_rows E G.Q.D.St G.Q.T.Ent G.Q.D.p G.Q.D.r.W G.l x.1.1.1 x.1.1.2 (G.Q.T.ents m)
  rw [← hR.pk m, ← hR.rd m] at k1
  -- the claims on the reads
  have k2 : ∀ j,
      (∑ nn, G.sl (.inr (.inl j)) x nn * G.Q.T.ents m nn = G.tg x (.inr (.inl j))) ↔
      G.Q.D.cl.k0 x.1.1.1 j + ∑ k, ∑ c, G.Q.D.cl.cw x.1.1.1 j k c * G.Q.D.r.rd (G.Q.old m) k c +
          ∑ n, G.Q.D.cl.ms x.1.1.1 j n *
            G.Q.D.c.ent (G.Q.D.S.left G.Q.D.N (T := OMsg.Msg) (G.Q.old m)) n =
        G.Q.D.cl.v x.1.1.1 j := by
    intro j
    have e1 : ∑ nn, G.sl (.inr (.inl j)) x nn * G.Q.T.ents m nn =
        ∑ k, ∑ c, G.Q.D.cl.cw x.1.1.1 j k c * G.Q.D.r.rd (G.Q.old m) k c +
          ∑ n, G.Q.D.cl.ms x.1.1.1 j n *
            G.Q.D.c.ent (G.Q.D.S.left G.Q.D.N (T := OMsg.Msg) (G.Q.old m)) n := by
      show ∑ nn, (placed (fun kc : G.Q.D.p.Rd × G.Q.D.p.C => G.l.rd kc.1 kc.2)
              (fun kc => G.Q.D.cl.cw x.1.1.1 j kc.1 kc.2) nn +
            placed G.jAt (G.Q.D.cl.ms x.1.1.1 j) nn) *
          G.Q.T.ents m nn = _
      simp only [add_mul, Finset.sum_add_distrib, hp]
      rw [Fintype.sum_prod_type, hR.rd m]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by rw [hR.je m n]
    rw [e1]
    show _ = G.Q.D.cl.v x.1.1.1 j - G.Q.D.cl.k0 x.1.1.1 j ↔ _
    constructor <;> intro h <;> linear_combination h
  -- the lookup's output claim
  have k3 : (∑ nn, G.sl (.inr (.inr (.inl ()))) x nn * G.Q.T.ents m nn =
        G.tg x (.inr (.inr (.inl ())))) ↔
      x.2.1.Holds G.Q.L.v (G.Q.L.key x.1 (y, m)) (G.ent (y, m)) := by
    have e1 : ∑ nn, G.sl (.inr (.inr (.inl ()))) x nn * G.Q.T.ents m nn =
        ∑ ru : G.Q.D.p.Row × G.Q.D.p.U,
            eqN (G.Q.v + 1) 0 x.2.1.pt (G.Q.e ru) * (G.Q.dg m).1 ru.1 ru.2 +
          ∑ ru : G.Q.D.p.Row × G.Q.D.p.U,
            eqN (G.Q.v + 1) 0 x.2.1.pt (2 ^ G.Q.v + G.Q.e ru) * (G.Q.dg m).2 ru.1 ru.2 +
          ∑ i, x.2.1.mf i * G.ent (y, m) i := by
      show ∑ nn, (placed (fun ru : G.Q.D.p.Row × G.Q.D.p.U => G.l.lo ru.1 ru.2)
              (fun ru => eqN (G.Q.v + 1) 0 x.2.1.pt (G.Q.e ru)) nn +
            placed (fun ru : G.Q.D.p.Row × G.Q.D.p.U => G.l.hi ru.1 ru.2)
              (fun ru => eqN (G.Q.v + 1) 0 x.2.1.pt (2 ^ G.Q.v + G.Q.e ru)) nn +
            placed G.nAt x.2.1.mf nn) *
          G.Q.T.ents m nn = _
      simp only [add_mul, Finset.sum_add_distrib, hp]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [hR.ne y m i]
    rw [e1]
    unfold MCl.Holds
    rw [ldSegRef_ga_keys E Kc _ _ G.Q x.1 (y, m) x.2.1.pt hK]
    show _ = x.2.1.tg -
          x.1.2 * ∑ X ∈ Finset.range (2 ^ (G.Q.v + 1)),
              eqN (G.Q.v + 1) 0 x.2.1.pt X * G.Q.tag (X / 2 ^ G.Q.v) ↔
      _
    constructor <;> intro h <;> linear_combination h
  -- the recorded rows
  have k4 : (∀ i : Fin G.n,
        ∑ nn, G.sl (.inr (.inr (.inr i))) x nn * G.Q.T.ents m nn = G.tg x (.inr (.inr (.inr i)))) ↔
      RowsHold x.2.2 (G.ent (y, m)) := by
    have e1 : ∀ i : Fin G.n, ∑ nn, G.sl (.inr (.inr (.inr i))) x nn * G.Q.T.ents m nn =
        ∑ t, (x.2.2.getD i G.row0).cf t * G.ent (y, m) t := by
      intro i
      show ∑ nn, placed G.nAt (x.2.2.getD i G.row0).cf nn * G.Q.T.ents m nn = _
      rw [hp]
      exact Finset.sum_congr rfl fun t _ => by rw [hR.ne y m t]
    constructor
    · intro h r hr
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
      have h1 := h ⟨i, by rw [← hn]; exact hi⟩
      rw [e1] at h1
      have h2 : x.2.2.getD i G.row0 = x.2.2[i] := List.getD_eq_getElem _ _ hi
      have h3 : ∑ t, (x.2.2.getD i G.row0).cf t * G.ent (y, m) t = (x.2.2.getD i G.row0).tg := h1
      rw [h2] at h3
      exact h3
    · intro h i
      rw [e1]
      have hi : (i : ℕ) < x.2.2.length := by rw [hn]; exact i.2
      have h2 : x.2.2.getD i G.row0 = x.2.2[(i : ℕ)] := List.getD_eq_getElem _ _ hi
      show ∑ t, (x.2.2.getD i G.row0).cf t * G.ent (y, m) t = (x.2.2.getD i G.row0).tg
      rw [h2]
      exact h _ (List.getElem_mem hi)
  constructor
  · intro h
    exact ⟨k1.2 fun b => h (.inl b),
      fun j => (k2 j).1 (h (.inr (.inl j))),
      k3.1 (h (.inr (.inr (.inl ())))),
      k4.1 fun i => h (.inr (.inr (.inr i)))⟩
  · rintro ⟨h1, h2, h3, h4⟩ (b | j | ⟨⟩ | i)
    · exact k1.1 h1 b
    · exact (k2 j).2 (h2 j)
    · exact k3.2 h3
    · exact k4.2 h4 i

theorem ldSegRef_ga_hyp : Spec.ldSegRef_ga_hyp := by
  intro E Kc E₀ Wp _ _ G St₀ g₀ Ar hR hS hK
  obtain ⟨hid, hfs, _, hcomp, hpair⟩ := extMap_isLocal
  refine ldSeg_step E Kc (G.Q.lkT G.ent G.n) (G.tgt St₀ Ar) _ _ _ _
    ⟨hpair _ _ _ _ _ (hcomp _ _ _ _ _ (hid _) (hfs E₀ G.Q.T.ext).1) (hfs E₀ G.Q.T.ext).2, ?_, ?_,
      fun x w => hS.core _ _, ?_⟩
  · rintro x y w ⟨h1, h2, h3⟩
    obtain ⟨⟨hRows, ⟨hCl, hA⟩, _, _⟩, ⟨hM, hL, _⟩, hlen⟩ := h3
    refine ⟨if_pos hlen, h1, h2, ?_, hS.fw _ _ _ _ hA⟩
    exact (ldSegRef_ga_all E Kc _ _ G x.1 y.1 (G.Q.T.msgs w.1) hR hK hlen).2 ⟨hRows, hCl, hM, hL⟩
  · rintro x y x' ⟨h1, h2⟩ hx
    by_cases hlen : x.1.2.2.length = G.n
    · rw [if_pos hlen] at hx
      rw [← Option.some.inj hx]
      exact ⟨h1, hS.on _ _ h2⟩
    · rw [if_neg hlen] at hx
      exact absurd hx (by simp)
  · rintro x y x' w' ⟨_, h2⟩ hx hB
    by_cases hlen : x.1.2.2.length = G.n
    · rw [if_pos hlen] at hx
      rw [← Option.some.inj hx] at hB
      obtain ⟨hd, hAll, hA⟩ := hB
      obtain ⟨hRows, hCl, hM, hL⟩ :=
        (ldSegRef_ga_all E Kc _ _ G x.1 y.1 (G.Q.T.msgs w'.1) hR hK hlen).1 hAll
      exact ⟨hd, ⟨hRows, hCl, hS.bw _ _ _ _ h2 hA⟩, hM, hL, trivial⟩
    · rw [if_neg hlen] at hx
      exact absurd hx (by simp)

end Cb
