-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupJohnPack.lean: this file builds the bundle of a whole closing (`GPack`,
Cb/Ld/LdGroupPack.lean) below the Johnson radii, with no hypothesis on lists.

In the words of lean/GLOSSARY.md: closing: the last part of a test, of the link or of a segment.
bundle: In `Cb/Ld/LdGroupPack.lean` and the files that use it, a group with all that a closing needs
(`GPack`, Cb/Ld/LdGroupPack.lean).

Two definitions (`StdM.John`, `GPack.ofJohn`), statements as theorems, proofs: an assembly on
Cb/Ld/LdGroupJohn.lean. Generic: any finite field, any codes read under a transformation. No assumed
theorem.
In `GPack.ofJohn` the group's set of common long positions, `G.P`, is nonempty.

Why: a closing asks bounds on lists at three places: at the stages of the fold, of the group's
complex (both: Cb/Ld/LdGroupJohn.lean), and of each new oracle message at its own radius (the one
sending). All three are theorems below the Johnson radius of the distance as the codes are read,
under the hypotheses of the statements below.

Main names:
  `stdM_ok_john`: a standard oracle message (`StdM`, Cb/Obj/LdObjectToyKit.lean): `M.OK` (`listMax`
    |P| d M.e) t from: laws, distance d, `InJohnson` |P| d M.e, the encoding hides t long positions,
    and the sample's three conditions.
  `stdNew_ok_john`: the new messages of a closing: `V.OK` (`listMax` |Pn| d₂ e₂) t₂, if `InJohnson`
    |Pn| d₂ e₂ and all of them are at one radius e₂, have the distance d₂ and meet the other
    conditions above (`StdM.John d₂ e₂ t₂`).
  `GPack.ofJohn`: the bundle, built from: a group with a shape that meets `Sh.OK`; hc (every oracle
    message is a member or kept); held messages with their laws; `G.Fits`;
    `Sh.par.John d G.e t bC bZ bW`, in which agreement is asked of the shape's codes, whatever the
    number of rows; and the new messages as above.
So all that is proved of closings from a bundle (Cb/Ld/LdGroupPack.lean, Cb/Ld/LdGroupNewRide*.lean,
Cb/Ld/LdGroupNewStd*.lean, Cb/Req1/LdSegRefPack*.lean: S.Proto, S.NumsAt, masks) holds at such
radii.

Notation: `d`, `d₂`: the numbers in `Dist d`, `Dist d₂`; `e₂`: the number in `rad : M.e = e` of
`StdM.John d₂ e₂ t₂`; `bC`, `bZ`, `bW`: the numbers in `MCArows e bC`, `MCArows e bZ`,
`MCArows e bW` of the shape's three codes (`SumPar.John`, Cb/Obj/LdObjectTowerJohn.lean); `t`, `t₂`:
the numbers in `Zk t`, `Zk t₂` (`LdCode.Zk`, Cb/Ld/LdRel.lean).

Limits: this file does not say that any code has `MCArows` beyond a third of the distance (an
instance's matter, below the Johnson radius: `Gl.glAg_rows`, Cb/Gl/GlFinalAg.lean, under
`Gl.AgreeJ`, which is proved nowhere in this library: it follows from the statement on codes
`Cb.BCHKS46At Gl.F Gl.E` (`Cb.Gl.glAg_ofAt`, same file)). Riders: their lists are asked of them as
before. It says nothing on any instance of a whole closing at such radii.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupJohn
import Cb.Ld.LdGroupPack

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

theorem stdM_ok_john {E P : Type} [Fintype P] [Field E] [Fintype E] (M : StdM E P) (d t : ℕ)
    (hL : M.Cm.Laws) (hD : M.Cm.Dist d) (hJ : InJohnson (Fintype.card P) d M.e) (hz : M.Cm.Zk t)
    (hp : Function.Injective M.plc) (hi : Function.Injective M.b) (h0 : ∀ β, M.b β ≠ 0) :
    M.OK (listMax (Fintype.card P) d M.e) t :=
  ⟨hL, ld_list_johnson E P M.Cm d M.e hL hD hJ, hz, hp, hi, h0⟩

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {G : Grp S} {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn] (V : StdNew Hd Pn)

/-- what is asked of one new message, below the Johnson radius -/
structure StdM.John {E P : Type} [Fintype P] [Field E] [Fintype E] (M : StdM E P) (d e t : ℕ) :
    Prop where
  rad  : M.e = e
  laws : M.Cm.Laws
  dist : M.Cm.Dist d
  zk   : M.Cm.Zk t
  plc  : Function.Injective M.plc
  inj  : Function.Injective M.b
  ne0  : ∀ β, M.b β ≠ 0

omit [DecidablePred kp] in
theorem stdNew_ok_john (d₂ e₂ t₂ : ℕ) (hJ : InJohnson (Fintype.card Pn) d₂ e₂)
    (hc : V.Mc.John d₂ e₂ t₂) (hn : ∀ k, (V.Mn k).John d₂ e₂ t₂) :
    V.OK (listMax (Fintype.card Pn) d₂ e₂) t₂ :=
  ⟨hc.rad ▸ stdM_ok_john V.Mc d₂ t₂ hc.laws hc.dist (hc.rad.symm ▸ hJ) hc.zk hc.plc hc.inj hc.ne0,
    fun k =>
      (hn k).rad ▸
        stdM_ok_john (V.Mn k) d₂ t₂ (hn k).laws (hn k).dist ((hn k).rad.symm ▸ hJ) (hn k).zk
          (hn k).plc (hn k).inj (hn k).ne0⟩

theorem ldGroupJohn_cf {d t bC bZ bW : ℕ} (h : Sh.par.John d G.e t bC bZ bW) : Sh.Cf.Laws :=
  ld_laws_pair E G.P _ _ h.lawsC (ld_laws_pair E G.P _ _ h.lawsZ h.lawsW)

/-- The bundle of a closing below the Johnson radii. -/
def GPack.ofJohn [Nonempty G.P] {d t bC bZ bW d₂ e₂ t₂ : ℕ} (hc : ∀ o, G.mem o ∨ kp o) (hS : Sh.OK)
    (hH : Hd.Laws) (h : Sh.par.John d G.e t bC bZ bW) (hF : G.Fits)
    (hJ₂ : InJohnson (Fintype.card Pn) d₂ e₂) (hMc : V.Mc.John d₂ e₂ t₂)
    (hMn : ∀ k, (V.Mn k).John d₂ e₂ t₂) :
    GPack S G.mem kp Hd.cl Pn d G.e t (fun _ => listMax (Fintype.card G.P) d G.e) (fun _ => bC)
      (fun _ => bZ) (fun _ => bW) (listMax (Fintype.card G.P) d G.e)
      (listMax (Fintype.card Pn) d₂ e₂) t₂ where
  G := G
  Sh := Sh
  Hd := Hd
  V := V
  memI := fun _ => Iff.rfl
  clI := fun _ => Iff.rfl
  eI := rfl
  hc := hc
  ok := hS
  held := hH
  hyp := h.hyp
  list := ldGroupJohn_list Sh hS h
  fits := hF
  new := stdNew_ok_john V d₂ e₂ t₂ hJ₂ hMc hMn
  cf := ldGroupJohn_cf h

end
end Cb
