-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Ent/CdCodes.lean: laws and distances of the codes of Cb/Ent/CdLink.lean.

Main names:
  `rsCode`, `genOf_eq_GE`, `hasDist_rsCode`, `hasDist_genOf`: the generator matrix is that of the
    library's `Code.RS.code` at the points `ptOf`; its distance is 2^a - (r + l) + 1.
  `ldOf_laws`, `ldOf_dist`, `ldRep_laws`, `ldRep_dist`: the library's laws (`LdCode.Laws`) and
    distances (`LdCode.Dist`) of a code read at its own length and of a repeated code.
  `memb_laws_of`, `memb_dist_of`, `memb_evades`: the same for a folded row's oracle message, and
    that its sample tells different messages apart at all but its own count of seeds.

Limits: for a ≤ 32 and r + l ≤ 2^a. Nothing on lists or on counts of exceptional points:
CdCounts.lean. Nothing on an honest prover.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ent.CdPoints

set_option autoImplicit false

namespace Cb.Ent
open Cb

/-- The library's Reed-Solomon code at the format's points, over the base field: 2^a positions
and r + l coefficients. All coefficients count as the message here, because a table format names
the places of its message itself. The three further parameters of `Code.RS.code` are read by no
statement of this file and are 0. -/
def rsCode (C : RsPar) : Code.Enc GF :=
  Code.RS.code (ptOf C.a) (C.r + C.l) (C.r + C.l) 0 0 0

/-- The format's generator matrix is that of the library's code, read over the extension field.
Both have the image of z^k at the position with the point z and the coefficient number k. -/
theorem genOf_eq_GE (C : RsPar) : genOf C = (rsCode C).GE GE := by
  funext x k
  rfl

/-- The library's code at the format's points has the distance 2^a - (r + l) + 1 over the base
field, since the points are different. -/
theorem hasDist_rsCode (C : RsPar) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) :
    Blocks.HasDist (rsCode C).G (2 ^ C.a - (C.r + C.l) + 1) :=
  Code.RS.code_dist (ptOf_inj C.a ha) hk

/-- Distance. Over the extension field, the word of a polynomial other than 0 with r + l
coefficients is not 0 at 2^a - (r + l) + 1 positions or more. -/
theorem hasDist_genOf (C : RsPar) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) :
    Blocks.HasDist (genOf C) (2 ^ C.a - (C.r + C.l) + 1) := by
  have h : Blocks.HasDist ((rsCode C).GE GE) (2 ^ C.a - (C.r + C.l) + 1) :=
    Blocks.HasDist.map (E := GE) (hasDist_rsCode C ha hk)
  rwa [← genOf_eq_GE] at h

end Cb.Ent

namespace Cb.Ent
open Cb Prob

/-- A position of the code itself is read at that position. -/
theorem posIn_self (C : RsPar) (x : Fin (2 ^ C.a)) : posIn C x = x :=
  Fin.ext (Nat.mod_eq_of_lt x.isLt)

/-- The encoder is the generator matrix, applied to the tail's entries followed by the
message's. -/
theorem ldOf_enc (C : RsPar) (a : ℕ) (m : Fin C.l → GE) (r : Fin C.r → GE)
    (p : Fin (2 ^ C.a)) (s : Unit) :
    (ldOf C a).enc m r p s = (genOf C).mulVec (Fin.append r m) p := by
  show (∑ q, genOf C p (Fin.castAdd C.l q) * r q) + ∑ j, genOf C p (Fin.natAdd C.r j) * m j
    = ∑ k, genOf C p k * Fin.append r m k
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- If the list of coefficients is 0, so are the message and the tail. -/
theorem append_eq_zero {l r : ℕ} {m : Fin l → GE} {t : Fin r → GE}
    (h : Fin.append t m = 0) : m = 0 ∧ t = 0 := by
  constructor
  · funext j
    have hj := congrFun h (Fin.natAdd r j)
    rwa [Fin.append_right] at hj
  · funext q
    have hq := congrFun h (Fin.castAdd l q)
    rwa [Fin.append_left] at hq

/-- The encoder is linear in (message, tail). -/
theorem ldOf_encLin (C : RsPar) (a : ℕ) :
    IsLinearMap GE fun w : (Fin C.l → GE) × (Fin C.r → GE) => (ldOf C a).enc w.1 w.2 where
  map_add u w := by
    funext p s
    show (∑ q, genOf C p (Fin.castAdd C.l q) * (u.2 q + w.2 q))
        + ∑ j, genOf C p (Fin.natAdd C.r j) * (u.1 j + w.1 j)
      = ((∑ q, genOf C p (Fin.castAdd C.l q) * u.2 q)
          + ∑ j, genOf C p (Fin.natAdd C.r j) * u.1 j)
        + ((∑ q, genOf C p (Fin.castAdd C.l q) * w.2 q)
          + ∑ j, genOf C p (Fin.natAdd C.r j) * w.1 j)
    simp only [mul_add, Finset.sum_add_distrib]
    exact add_add_add_comm _ _ _ _
  map_smul c u := by
    funext p s
    show (∑ q, genOf C p (Fin.castAdd C.l q) * (c * u.2 q))
        + ∑ j, genOf C p (Fin.natAdd C.r j) * (c * u.1 j)
      = c * ((∑ q, genOf C p (Fin.castAdd C.l q) * u.2 q)
          + ∑ j, genOf C p (Fin.natAdd C.r j) * u.1 j)
    simp only [mul_add, Finset.mul_sum, mul_left_comm c]

/-- The laws, at any number 2^a of positions of the group. -/
theorem ldOf_laws (C : RsPar) (a : ℕ) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) :
    (ldOf C a).Laws where
  encLin := ldOf_encLin C a
  tLin := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  inj m r h := by
    have hinj : Function.Injective (genOf C).mulVec :=
      (hasDist_genOf C ha hk).injective (Nat.succ_pos _)
    have h0 : (genOf C).mulVec (Fin.append r m) = (genOf C).mulVec 0 := by
      funext p
      rw [← ldOf_enc C a m r p (), h, Matrix.mulVec_zero]
      rfl
    exact append_eq_zero (hinj h0)
  loc f g x h := by
    funext s
    show f (posIn C x) () = g (posIn C x) ()
    rw [h (posIn C x) (Finset.mem_singleton_self _)]

/-- The distance, at the code's own positions. -/
theorem ldOf_dist (C : RsPar) (ha : C.a ≤ 32) (hk : C.r + C.l ≤ 2 ^ C.a) :
    (ldOf C C.a).Dist (2 ^ C.a - (C.r + C.l) + 1) := by
  intro m r hmr
  have hv : Fin.append r m ≠ 0 := fun h => hmr (append_eq_zero h)
  refine (hasDist_genOf C ha hk (Fin.append r m) hv).trans (cnt_mono fun x hx h0 => hx ?_)
  have h1 : (ldOf C C.a).enc m r (posIn C x) () = 0 := congrFun h0 ()
  rwa [ldOf_enc, posIn_self] at h1

/-- A symbol of a repeated code word is the symbol of the code's own word at the position modulo the
code's length. -/
theorem ldRep_enc (C : RsPar) (a : ℕ) (m : Fin C.l → GE) (r : Fin C.r → GE)
    (p : Fin (2 ^ a)) (s : Unit) :
    (ldRep C a).enc m r p s = (ldOf C C.a).enc m r (posIn C p) () := rfl

/-- A position of the code, as a position of a group that is at least as long. -/
def upIn (C : RsPar) {a : ℕ} (h : C.a ≤ a) (y : Fin (2 ^ C.a)) : Fin (2 ^ a) :=
  ⟨y.val, lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) h)⟩

/-- Modulo the code's length it is the position from which it was made. -/
theorem posIn_upIn (C : RsPar) {a : ℕ} (h : C.a ≤ a) (y : Fin (2 ^ C.a)) :
    posIn C (upIn C h y) = y :=
  Fin.ext (Nat.mod_eq_of_lt y.isLt)

/-- Exactly 2^(a - C.a) positions of the group are equal to a given position of the code modulo the
code's length. -/
theorem cnt_posIn (C : RsPar) {a : ℕ} (h : C.a ≤ a) (y : Fin (2 ^ C.a)) :
    cnt (fun x : Fin (2 ^ a) => posIn C x = y) = 2 ^ (a - C.a) := by
  rw [cnt_congr (fun x : Fin (2 ^ a) => (Fin.ext_iff : posIn C x = y ↔ _)),
    ← Nat.pow_div h (by decide)]
  exact CodeRep.cnt_mod (Nat.pow_dvd_pow 2 h) y

/-- The laws of the repeated code, at a group that is at least as long as the code (C.a ≤ a), if
C.a ≤ 32 and the code has room for C.r + C.l symbols (C.r + C.l ≤ 2^C.a). -/
theorem ldRep_laws (C : RsPar) (a : ℕ) (hle : C.a ≤ a) (ha : C.a ≤ 32)
    (hk : C.r + C.l ≤ 2 ^ C.a) : (ldRep C a).Laws where
  encLin :=
    { map_add := fun u w => by
        funext p s
        exact congrFun (congrFun ((ldOf_encLin C C.a).map_add u w) (posIn C p)) ()
      map_smul := fun c u => by
        funext p s
        exact congrFun (congrFun ((ldOf_encLin C C.a).map_smul c u) (posIn C p)) () }
  tLin := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  inj m r h := by
    refine (ldOf_laws C C.a ha hk).inj m r ?_
    funext y s
    have h1 : (ldRep C a).enc m r (upIn C hle y) () = 0 := congrFun (congrFun h (upIn C hle y)) ()
    rw [ldRep_enc, posIn_upIn] at h1
    exact h1
  loc f g x h := by
    funext s
    show f x () = g x ()
    rw [h x (Finset.mem_singleton_self _)]

/-- The distance of the repeated code: 2^C.a - (C.r + C.l) + 1, times the 2^(a - C.a) copies. The
first number is the one that `ldOf_dist` gives for the code at its own positions. Under the
hypotheses of `ldRep_laws`: C.a ≤ a, C.a ≤ 32, and room for C.r + C.l symbols. -/
theorem ldRep_dist (C : RsPar) (a : ℕ) (hle : C.a ≤ a) (ha : C.a ≤ 32)
    (hk : C.r + C.l ≤ 2 ^ C.a) :
    (ldRep C a).Dist (2 ^ (a - C.a) * (2 ^ C.a - (C.r + C.l) + 1)) := by
  intro m r hmr
  have key : ∀ x : Fin (2 ^ a), (ldOf C C.a).T ((ldOf C C.a).enc m r) (posIn C x) ≠ 0 →
      (ldRep C a).T ((ldRep C a).enc m r) x ≠ 0 := by
    intro x hx h
    refine hx (funext fun s => ?_)
    have h1 : (ldRep C a).enc m r x () = 0 := congrFun h ()
    show (ldOf C C.a).enc m r (posIn C (posIn C x)) () = 0
    rw [posIn_self]
    exact h1
  refine (Nat.mul_le_mul_left _ (ldOf_dist C ha hk m r hmr)).trans (le_trans (le_of_eq ?_)
    (cnt_mono key))
  exact (CodeRep.cnt_comp_even (posIn C) (2 ^ (a - C.a)) (cnt_posIn C hle)
    fun y => (ldOf C C.a).T ((ldOf C C.a).enc m r) y ≠ 0).symm

end Cb.Ent

namespace Cb.Ent
open Iop Prob Hiop Blocks Cb Cb.Ood

/-- The interleaving with no row keeps the laws, whatever the code. -/
theorem il_empty_laws {E P : Type} [Field E] (C : LdCode E P) : (C.il Empty).Laws where
  encLin := ⟨fun _ _ => funext fun _ => funext fun s => s.1.elim,
    fun _ _ => funext fun _ => funext fun s => s.1.elim⟩
  tLin := ⟨fun _ _ => funext fun _ => funext fun s => s.1.elim,
    fun _ _ => funext fun _ => funext fun s => s.1.elim⟩
  inj := fun _ _ _ => ⟨funext fun j => j.1.elim, funext fun q => q.1.elim⟩
  loc := fun _ _ _ _ => funext fun s => s.1.elim

/-- The interleaving with no row has every distance: its one code word is 0. -/
theorem il_empty_dist {E P : Type} [Field E] [Finite P] (C : LdCode E P) (d : ℕ) :
    (C.il Empty).Dist d :=
  fun _ _ h => absurd ⟨funext fun j => j.1.elim, funext fun q => q.1.elim⟩ h

/-- The message's code keeps the laws, if one row under the code C does. -/
theorem memb_laws_of (S : Sz) (hL : (ldOf S.P.C S.P.C.a).Laws) : S.memb.Cm.Laws :=
  ld_laws_pair GE (Fin (2 ^ S.P.C.a)) _ _
    (ld_laws_il GE (Fin (2 ^ S.P.C.a)) (ldOf S.P.C S.P.C.a) (Fin S.P.R) hL)
    (il_empty_laws (ldRep S.P.Z S.P.C.a))

/-- The message's code has the distance of one row under the code C. -/
theorem memb_dist_of (S : Sz) (d : ℕ) (hD : (ldOf S.P.C S.P.C.a).Dist d) : S.memb.Cm.Dist d :=
  ld_dist_pair GE (Fin (2 ^ S.P.C.a)) _ _ d
    (ld_dist_il GE (Fin (2 ^ S.P.C.a)) (ldOf S.P.C S.P.C.a) (Fin S.P.R) d hD)
    (il_empty_dist (ldRep S.P.Z S.P.C.a) d)

/-- Take a standard oracle message in which different data have different corners and the map of
the pad's factors into the field is injective. If m and m' are different messages in the list of
the same word, then the seeds at which the sample answers alike on m and m' number at most the
sample's own count `Z.err`. -/
theorem stdM_evades_of {E P : Type} [Fintype P] [Field E] [Fintype E] (M : StdM E P)
    (hp : Function.Injective M.plc) (hb : Function.Injective M.b) : M.om.Evades :=
  sig_evades_of_okOn E M.om _
    (ood_okOn_comap E (M.Dt ⊕ Unit) M.Cm.J M.Z₀ M.place.symm (PadInF E)
      (ood_okOn_pad E E M.μ M.Dt Unit M.B _ _ _ hp hb std_padBasis.1))
    fun _ _ _ _ _ _ => ⟨_, rfl⟩

/-- The same for a folded row's message, from the fact on the corners. -/
theorem memb_evades_of (S : Sz) (hp : Function.Injective S.memb.plc) : S.memb.om.Evades :=
  stdM_evades_of S.memb hp Units.val_injective

/-- Different messages in the list of the same word get the same answers from the sample at no more
seeds than the sample's own count `Z.err`, if the rows and the places of a row have room among the
digits of the cube. -/
theorem memb_evades (S : Sz) (hR : S.P.R ≤ 2 ^ S.P.aR) (hl : S.P.C.l ≤ 2 ^ S.P.aP) :
    S.memb.om.Evades :=
  memb_evades_of S (memb_plc_inj S hR hl)

end Cb.Ent
