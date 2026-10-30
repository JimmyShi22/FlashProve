-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CoreKnow.lean: the four blocks of the library's link before its closing, each with its
round-by-round knowledge soundness alone.

The library states each block of its link protocol (Cb/Ld/LdLink.lean) as a bundle of several
properties, of which knowledge soundness is one. For the sending, the bundle asks laws of an honest
sender. A theorem about a verifier needs knowledge soundness alone. This file takes it out of the
bundles, or from the library's own separate statement, in one common form: the theorem holds on all
statements, and a statement outside a block's condition counts as having a witness
(`Iop.IOR.Rels.cf`). In that form the blocks can be taken off a written protocol one after another
(OnBytes/Slice/Peel.lean).

Main theorems: `know_gam`, `know_snd`, `know_loc`, `know_phi`. The blocks, with their rounds among
the link's five: `gam`, the fold point (round 1, LINK point); `snd`, the sending of
the two folded rows (rounds 2 and 3, SEND seed and SEND answer); `loc`, the drawn columns (round 4,
LINK); `phi`, the point at which the two folded rows are compared (round 5, LINK phi). The closing
is whatever follows: here, the fourteen rounds of batching and proximity test.
What is asked: for the fold point, a bound on the bad points of the two folds; for the sending, fair
seeds, bounds on the lists, and that two different members of a list have the same answers at no
more than a counted number of seeds; for the locations, nothing; for the point of comparison, that
the layout's places are different vertices of the cube. No honest side.
Not claimed. Nothing on an honest prover, on zero knowledge or on the sizes of the error counts.
-/
import Cb.Ld.LdLinkProofs
import Cb.Ld.LdLinProofsChain
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb

variable {E ι κ J Λ : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Λ]

/-- A value of the record that the library's statement on the locations takes for its budgets of
positions. No block's verifier reads anything of it but the seeds. -/
def sndOf (P : LdLkP E ι κ J Λ) (Sd : P.N.Seeds) : P.Snd where
  Sd := Sd
  dS :=
    { Nn := ⟨Unit, Unit, fun _ _ a => (P.N.om a).sy0, fun _ => none⟩
      upM := fun _ _ _ => 0
      upR := fun _ _ _ => 0
      Mk := Unit
      put := fun _ _ => ()
      rest := fun w => w.2
      w0 := ((fun _ => 0, fun _ => 0), (fun _ _ => 0, fun _ _ => 0)) }
  L := fun _ => 0
  t := fun _ => 0

omit [Nonempty ι] [Fintype Λ] in
/-- The round of the fold point. -/
theorem know_gam (P : LdLkP E ι κ J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (ε₀ ε₁ : ℕ) (hF : P.FoldErr on0 on1 ε₀ ε₁) :
    P.gam.red.Know (fun _ => True) (P.j0 on0 on1).cf.relR (P.j1 on0 on1).cf.relR
      (fun _ _ w => w.2) ((P.errGam ε₀ ε₁, ()) : ℕ × Unit) :=
  (ldk_pieceTr_cf (ldLk_gam P on0 on1 ε₀ ε₁ (fun _ => True) hF)).good.know

omit [Fintype E] [Nonempty ι] [Fintype Λ] in
/-- The two rounds of the sending. -/
theorem know_snd (P : LdLkP E ι κ J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (Sd : P.N.Seeds) (L : P.N.O → ℕ) (hfair : Sd.Fair) (hlist : ∀ a, (P.N.om a).ListLE (L a))
    (hev : ∀ a, (P.N.om a).Evades) :
    (ldSendFam P.N Sd P.X1 P.E0).red.Know (fun _ => True) (P.j1 on0 on1).cf.relR
      (P.j2 on0 on1).cf.relR (fun _ _ w => P.back (P.N.msgs w.1) w.2)
      (ldSendFamErr P.N Sd L, (0, ())) :=
  (knowInto_iff _ _ _ _ _ _ _ _ _ _ _).1
    (ldSendFam_into E P.N Sd Unit P.X1 P.W1 P.W0 P.E0 (P.j1 on0 on1) P.back L hfair hlist hev)

omit [Fintype Λ] in
/-- The round of the locations. -/
theorem know_loc (P : LdLkP E ι κ J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (Sd : P.N.Seeds) :
    P.loc.red.Know (fun _ => True) (P.j2 on0 on1).cf.relR P.j3.cf.relR (fun _ _ w => w)
      ((P.errLoc, ()) : ℕ × Unit) :=
  (ldk_pieceTr_cf (ldLk_loc P on0 on1 (sndOf P Sd))).good.know

omit [Fintype ι] [Nonempty ι] in
/-- The round of the point of comparison. -/
theorem know_phi (P : LdLkP E ι κ J Λ) (hpl : Function.Injective P.D.pl) :
    P.phi.red.Know (fun _ => True) P.j3.cf.relR P.j4.cf.relR (fun _ _ w => w)
      ((P.errPhi, ()) : ℕ × Unit) :=
  (ldk_pieceTr_cf (ldLk_phi P (fun _ => True) hpl)).good.know

end OnBytes.Slice

#print axioms OnBytes.Slice.know_gam
#print axioms OnBytes.Slice.know_snd
#print axioms OnBytes.Slice.know_loc
#print axioms OnBytes.Slice.know_phi
