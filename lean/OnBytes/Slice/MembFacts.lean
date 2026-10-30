-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/MembFacts.lean: a folded row's oracle message keeps the laws and the distance of the
code C, and its sample tells two messages of a list apart.

The link at the sizes of an entry file (OnBytes/Slice/LinkAt.lean) sends each folded row as one
oracle message, `Sz.memb`: R rows under the code C side by side, beside them an interleaving with no
row at all, and a sample with a pad. Among what the library's soundness theorem for the link asks
of such a message are the facts above. This file proves them from the laws and the distance of the
code C and from the fact that different entries of the message have different corners of the cube.

How. An interleaving with no row has one word only, so it keeps every law and has every distance.
The library carries laws and distance from one row to R rows and to two codes side by side.
For the sample, the library's own proof for a standard oracle message is repeated with the two
hypotheses that it uses.

Main theorems.
 `il_empty_laws`, `il_empty_dist`   the interleaving with no row keeps the laws, at any distance.
 `memb_laws`, `memb_dist`   the message's code keeps the laws and the distance of the code C.

 `stdM_evades_of` the fact on the sample for every standard oracle message, from two injections.
 `memb_evades`    the fact on the sample for a folded row's message.

Not claimed. Nothing on hiding: no statement here speaks of what a reader of a few positions learns.
No bound on lists.
-/
import Cb.Ld.LdRelJohnsonProofs
import OnBytes.Slice.LinkAt
import OnBytes.Slice.LdOfFacts
import OnBytes.Slice.CornersAt

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Hiop Blocks Cb Cb.Ood

/-! ## The interleaving with no row -/

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

/-! ## Laws and distance of a folded row's message -/

/-- The message's code keeps the laws, if one row under the code C does. -/
theorem memb_laws_of (S : Sz) (hL : (ldOf S.P.C S.P.C.a).Laws) : S.memb.Cm.Laws :=
  ld_laws_pair GE (Fin (2 ^ S.P.C.a)) _ _
    (ld_laws_il GE (Fin (2 ^ S.P.C.a)) (ldOf S.P.C S.P.C.a) (Fin S.P.R) hL)
    (il_empty_laws (ldOf S.P.Z S.P.C.a))

/-- The message's code has the distance of one row under the code C. -/
theorem memb_dist_of (S : Sz) (d : ℕ) (hD : (ldOf S.P.C S.P.C.a).Dist d) : S.memb.Cm.Dist d :=
  ld_dist_pair GE (Fin (2 ^ S.P.C.a)) _ _ d
    (ld_dist_il GE (Fin (2 ^ S.P.C.a)) (ldOf S.P.C S.P.C.a) (Fin S.P.R) d hD)
    (il_empty_dist (ldOf S.P.Z S.P.C.a) d)

/-! ## The sample -/

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

/-! ## The same from the sizes alone -/

/-- The message's code keeps the laws. -/
theorem memb_laws (S : Sz) (ha : S.P.C.a ≤ 32) (hk : S.P.C.r + S.P.C.l ≤ 2 ^ S.P.C.a) :
    S.memb.Cm.Laws :=
  memb_laws_of S (ldOf_laws S.P.C S.P.C.a ha hk)

/-- The message's code has the distance of the code C. -/
theorem memb_dist (S : Sz) (ha : S.P.C.a ≤ 32) (hk : S.P.C.r + S.P.C.l ≤ 2 ^ S.P.C.a) :
    S.memb.Cm.Dist (2 ^ S.P.C.a - (S.P.C.r + S.P.C.l) + 1) :=
  memb_dist_of S _ (ldOf_dist S.P.C ha hk)

/-- Different messages in the list of the same word get the same answers from the sample at no more
seeds than the sample's own count `Z.err`, if the rows and the places of a row have room among the
digits of the cube. -/
theorem memb_evades (S : Sz) (hR : S.P.R ≤ 2 ^ S.P.aR) (hl : S.P.C.l ≤ 2 ^ S.P.aP) :
    S.memb.om.Evades :=
  memb_evades_of S (memb_plc_inj S hR hl)

end OnBytes.Slice

#print axioms OnBytes.Slice.memb_laws
#print axioms OnBytes.Slice.memb_dist
#print axioms OnBytes.Slice.memb_evades
