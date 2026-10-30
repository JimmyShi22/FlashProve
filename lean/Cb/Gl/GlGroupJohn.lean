-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`GlJ` does not ask a radius within half the distance (Cb/Gl/GlLdJ.lean).
Cb/Gl/GlGroupJohn.lean: the first half of a segment's closing (bridge-to-fold), over
p = 2^64 - 2^32 + 1, at a radius below the Johnson radius: list sizes are proved, mutual correlated
agreement comes from the hypothesis `Cb.BCHKS46F F`.



Exactly: the first half of a closing of a request's segment below the Johnson radius, over p: lists
proved, agreement from the one hypothesis BCHKS46F F.


Statements as theorems and proofs: an assembly of Cb/Ld/LdGroupJohn.lean,
Cb/GlVal/GlJohn.lean, Cb/Gl/GlLdJ.lean.
A session's groups are the batch linear test's and the groups of a request's closings. For a group
with a shape whose three codes (base code, mask code, the fresh mask's code) are built from families
of plain Reed-Solomon codes over the prime (`GlJ`: Cb/Gl/GlLdJ.lean), at a joint radius below the
Johnson radius as the codes are read:
  `glGroupJohn_par`: BCHKS46F F → Sh.par.John d G.e t bC bZ bW. Left as hypotheses: challenges are
    distinct, degree at least 2, the packing's law and degrees.
  `glGroupJohn_seg`, `glGroupJohn_isGrp`: BCHKS46F F → the hypotheses of the closing's link
    bridge-to-fold; and `D.IsGrp l` (Cb/Req1/LdReqProtoStd.lean: the clause "fold" of `S.ProtoS`),
    all bounds on lists := listMax |P| d e. Left as hypotheses, beside the above: the shape is in
    order, the held messages' laws, the bridge's evader evades, Fits; every oracle message is a
    member of the group or kept (`hc`); the group has a long position (`[Nonempty G.P]`).

`G8J.kpJ`: the message that is read after the bridge, among the oracle messages `LdGToy.Mem`
(Cb/Ld/LdGroupToy.lean).





Limits: BCHKS46F F ITSELF STAYS A HYPOTHESIS (a statement of Cryptology ePrint Archive 2025/2055
(Theorem 4.6), which gives an outline of a proof). This file does not say that the counts are below
the number of elements of E. It says nothing on the second half of a closing, or on a whole segment
closed at such radii. Not guarded and not said: a reference segment or a request at such a radius:
no instance in this file. This file exhibits no instance of its statements at any radius.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupJohn
import Cb.GlVal.GlGuardJohn

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR Cb.Ood

section
variable {S : Sig E} {G : Grp S} (Sh : GShape G) {d t bC bZ bW : ℕ}

theorem glGroupJohn_par (H : Cb.BCHKS46F F) (hC : GlJ Sh.Cb d 0 G.e bC) (hZ : GlJ Sh.Zb d 0 G.e bZ)
    (hW : GlJ Sh.par.Zw d t G.e bW) (hJ : InJohnson (Fintype.card G.P) d G.e)
    (hi : Function.Injective Sh.val) (hn : 2 ≤ Sh.n) (hp : Sh.par.PackOK) (hq : Sh.par.QwDeg) :
    Sh.par.John d G.e t bC bZ bW :=
  glJ_fold H G.P Sh.par d G.e t bC bZ bW (.il _ hC) hZ hW hJ hi hn hp hq

end

section
variable {B Kc St₀ Wp : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] (Hd : GHeld Sh kp) (Sb : B → Type)
  (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (hc : ∀ o, G.mem o ∨ kp o)
  (dw : S.Wit × Wp) {d t bC bZ bW : ℕ}

theorem glGroupJohn_seg (H : Cb.BCHKS46F F) (hC : GlJ Sh.Cb d 0 G.e bC) (hZb : GlJ Sh.Zb d 0 G.e bZ)
    (hW : GlJ Sh.par.Zw d t G.e bW) (hJ : InJohnson (Fintype.card G.P) d G.e)
    (hi : Function.Injective Sh.val) (hn : 2 ≤ Sh.n) (hp : Sh.par.PackOK) (hq : Sh.par.QwDeg)
    (hS : Sh.OK) (hH : Hd.Laws) (hZ : Z.OK) (hF : G.Fits) :
    (Hd.foldD Sb sl Z A₀).Hyp
      (Hd.link Sb sl Z A₀ hc dw d t (fun _ => listMax (Fintype.card G.P) d G.e) (fun _ => bC)
        (fun _ => bZ) (fun _ => bW) (listMax (Fintype.card G.P) d G.e)) :=
  ldGroupJohn_seg Hd Sb sl Z A₀ hc dw hS hH (glGroupJohn_par Sh H hC hZb hW hJ hi hn hp hq) hZ hF

theorem glGroupJohn_isGrp (H : Cb.BCHKS46F F) (hC : GlJ Sh.Cb d 0 G.e bC)
    (hZb : GlJ Sh.Zb d 0 G.e bZ) (hW : GlJ Sh.par.Zw d t G.e bW)
    (hJ : InJohnson (Fintype.card G.P) d G.e) (hi : Function.Injective Sh.val) (hn : 2 ≤ Sh.n)
    (hp : Sh.par.PackOK) (hq : Sh.par.QwDeg) (hS : Sh.OK) (hH : Hd.Laws) (hZ : Z.OK) (hF : G.Fits) :
    (Hd.foldD Sb sl Z A₀).IsGrp
      (Hd.link Sb sl Z A₀ hc dw d t (fun _ => listMax (Fintype.card G.P) d G.e) (fun _ => bC)
        (fun _ => bZ) (fun _ => bW) (listMax (Fintype.card G.P) d G.e)) :=
  ldGroupJohn_isGrp Hd Sb sl Z A₀ hc dw hS hH (glGroupJohn_par Sh H hC hZb hW hJ hi hn hp hq) hZ hF

end

/-! ## The kept message -/

namespace G8J
open LdGToy (Mem)

/-- read after the bridge: the kept message -/
@[reducible] def kpJ : Mem → Prop := fun o => o = .kep

end G8J

end Cb.Gl
