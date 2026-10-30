-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/Group.lean: a group of the sampled messages of a sending, read at common positions, as
a value of the library's record, with what a proximity test asks of it.

Definitions, statements and proofs. A proximity test takes several oracle messages as one word, read
at common long positions, with one radius (`Grp`, Cb/Ld/LdBatSig.lean). In the programs a shorter
word is read at the position modulo its length (`OnBytes.shortPosition`). This file writes such a
group over the signature `sigOf` (Johnson/Pack/PortF.lean) and derives, from conditions on numbers,
what the library's statements on a test below the Johnson radius ask of a group
(Cb/Ld/LdTowerJohn.lean: `ldJohn_bridge`, `ldJohn_run`).
Main names:
  `atPos_laws`, `atPos_dist`: a code read at other long positions keeps its laws; if every old
    position is read at exactly m new ones, its distance is m times the old.
  `modP`, `cnt_modP`: the position modulo 2^a, of 2^A positions; every value is taken 2^(A - a)
    times.
  `near_modP`, `near_modP_lt`: for every code at 2^a positions that is read modulo 2^a at 2^A common
    positions: words within e common positions are within e / 2^(A - a) of the code's own; so a
    joint radius e < (e₀ + 1) 2^(A - a) implies the radius e₀. No group is named.
  `grpOf cs l mem A e`: the group of the members that `mem` names, at 2^A common positions, with
    the joint radius e.
  `grp_laws`, `grp_dist`: every member as read in the group has the laws, and the distance d if d ≤
    2^(A - a) times the member's own.
  `grp_list`: below the Johnson radius the group's complex has lists of at most `listMax (2^A) d e`.
  `grp_fits`: the joint radius implies each member's own (`Grp.Fits`), if e ≤ 2^(A - a) e_a + (2^(A
    - a) - 1) for every member.
Limits: of what `ldJohn_run` asks, the group's part alone is shown here (laws, distance, the Johnson
radius, `Grp.Fits`); its conditions on the zero-evader and on the test (`D.Z.OK`, `D.T.OK`) are not
touched. One sending's signature: a group with members from several sendings is a group over their
sum, which is not written here. In the programs a group may also hold messages that are not sampled
(masks that are sent ahead of the round that uses them); these are in no `sigOf`, so a group of the
programs is in general no `grpOf`. Of a group without a member (`mem` false of every name) the
conditions on members are empty, and `grp_list` and `grp_fits` say nothing. Which messages the
programs put in one group, and at which radius, is not said. Nothing on the test itself, on the
honest prover or on hiding.
-/
import Johnson.Pack.Check
import Cb.Ld.LdTowerJohn
import Cb.Ref.GlRefCodeSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open Cb Cb.Ood Iop IOR Prob OnBytes.Slice

section Gen
variable {E P P' : Type} [Field E] (C : LdCode E P) (pos : P' → P)

theorem atPos_laws (h : C.Laws) : (C.atPos pos).Laws :=
  ⟨h.encLin,
    ⟨fun f g => funext fun x => congrFun (h.tLin.map_add f g) (pos x),
      fun c f => funext fun x => congrFun (h.tLin.map_smul c f) (pos x)⟩,
    h.inj, fun f g x hx => h.loc f g (pos x) hx⟩

theorem atPos_dist [Fintype P] [Fintype P'] (m : ℕ) (hm : ∀ y, cnt (fun x => pos x = y) = m)
    (d : ℕ) (h : C.Dist d) : (C.atPos pos).Dist (m * d) := by
  intro mm r hne
  show m * d ≤ cnt fun x => C.T (C.enc mm r) (pos x) ≠ 0
  rw [CodeRep.cnt_comp_even pos m hm fun y => C.T (C.enc mm r) y ≠ 0]
  exact Nat.mul_le_mul_left _ (h mm r hne)

end Gen

/-- The position modulo 2^a. -/
def modP (a A : ℕ) (x : Fin (2 ^ A)) : Fin (2 ^ a) :=
  ⟨x.val % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem cnt_modP (a A : ℕ) (h : a ≤ A) (y : Fin (2 ^ a)) :
    cnt (fun x : Fin (2 ^ A) => modP a A x = y) = 2 ^ (A - a) := by
  rw [cnt_congr (fun x : Fin (2 ^ A) => (Fin.ext_iff : modP a A x = y ↔ _)),
    ← Nat.pow_div h (by decide)]
  exact CodeRep.cnt_mod (Nat.pow_dvd_pow 2 h) y

/-- A member that is read modulo its own length: two native words that differ at no more than e of
the 2^A common positions differ at no more than e / 2^(A - a) of the member's own. For every code
at 2^a positions; no group is named. -/
theorem near_modP (a A : ℕ) (h : a ≤ A) (C : LdCode GE (Fin (2 ^ a))) (e : ℕ) (f g : C.Word)
    (hn : (C.atPos (modP a A)).Near e f g) : C.Near (e / 2 ^ (A - a)) f g := by
  have hp : 0 < 2 ^ (A - a) := Nat.two_pow_pos _
  refine Cb.Gl.Bld.bld_near_atPos _ _ C (modP a A) _ _ hp (cnt_modP a A h) f g (le_trans hn ?_)
  have h1 := Nat.div_add_mod e (2 ^ (A - a))
  have h2 := Nat.mod_lt e hp
  omega

/-- The same, as a condition on the joint radius: e < (e₀ + 1) 2^(A - a) gives the radius e₀. -/
theorem near_modP_lt (a A : ℕ) (h : a ≤ A) (C : LdCode GE (Fin (2 ^ a))) (e e₀ : ℕ)
    (he : e < (e₀ + 1) * 2 ^ (A - a)) (f g : C.Word)
    (hn : (C.atPos (modP a A)).Near e f g) : C.Near e₀ f g :=
  le_trans (near_modP a A h C e f g hn)
    (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 he))

section Grp
variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (mem : Fin l.length → Prop) [DecidablePred mem] (A e : ℕ)

/-- The group of the members that `mem` names, at 2^A common positions, with the radius e. -/
def grpOf : Grp (sigOf cs l) where
  P := Fin (2 ^ A)
  mem := mem
  pos := fun a x => modP (aOf cs (l.get a.1).1) A x
  e := e

variable (hA : ∀ i, mem i → aOf cs (l.get i).1 ≤ A)

theorem grp_laws (hc : ∀ i, mem i → CodeOK cs (l.get i).1) (a : (grpOf cs l mem A e).A) :
    (((sigOf cs l).om a.1).C.atPos ((grpOf cs l mem A e).pos a)).Laws :=
  atPos_laws _ _ (port_laws cs (l.get a.1).1 (hc a.1 a.2))

include hA in
theorem grp_dist (hc : ∀ i, mem i → CodeOK cs (l.get i).1) (d : ℕ)
    (hd : ∀ i, mem i → d ≤ 2 ^ (A - aOf cs (l.get i).1) * dOf cs (l.get i).1)
    (a : (grpOf cs l mem A e).A) :
    (((sigOf cs l).om a.1).C.atPos ((grpOf cs l mem A e).pos a)).Dist d :=
  dist_mono _ (hd a.1 a.2)
    (atPos_dist (portCode cs (l.get a.1).1) (modP (aOf cs (l.get a.1).1) A) _
      (cnt_modP _ _ (hA a.1 a.2)) _
      (port_dist cs _ (hc a.1 a.2) _ (pbase_dOf cs _ (hc a.1 a.2)).d1
        (pbase_dOf cs _ (hc a.1 a.2)).d2))

include hA in
theorem grp_list (hc : ∀ i, mem i → CodeOK cs (l.get i).1) (d : ℕ)
    (hd : ∀ i, mem i → d ≤ 2 ^ (A - aOf cs (l.get i).1) * dOf cs (l.get i).1)
    (hJ : InJohnson (2 ^ A) d e) :
    (grpOf cs l mem A e).C.ListAt e (listMax (2 ^ A) d e) := by
  have h := ldJohn_bridge GE (sigOf cs l) (grpOf cs l mem A e) d (grp_laws cs l mem A e hc)
    (grp_dist cs l mem A e hA hc d hd)
  rw [show Fintype.card (grpOf cs l mem A e).P = 2 ^ A from Fintype.card_fin _] at h
  exact h hJ

include hA in
theorem grp_fits
    (he : ∀ i, mem i → e ≤ 2 ^ (A - aOf cs (l.get i).1) * (l.get i).2 +
      (2 ^ (A - aOf cs (l.get i).1) - 1)) : (grpOf cs l mem A e).Fits := by
  intro a f g hn
  exact Cb.Gl.Bld.bld_near_atPos _ _ (portCode cs (l.get a.1).1)
    (modP (aOf cs (l.get a.1).1) A) _ (l.get a.1).2 (Nat.two_pow_pos _)
    (cnt_modP _ _ (hA a.1 a.2)) f g (le_trans hn (he a.1 a.2))

end Grp
end Johnson.Pack

#print axioms Johnson.Pack.atPos_dist
#print axioms Johnson.Pack.near_modP
#print axioms Johnson.Pack.near_modP_lt
#print axioms Johnson.Pack.grp_dist
#print axioms Johnson.Pack.grp_list
#print axioms Johnson.Pack.grp_fits
