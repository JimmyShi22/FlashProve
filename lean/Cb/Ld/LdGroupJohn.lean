-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupJohn.lean: this file derives bounds on lists from the Johnson bound, for a batching
round and a fold on several oracle messages: the link bridge-to-fold of a group with a shape
(`GShape`, Cb/Ld/LdGroupFold.lean), below the Johnson radius, with no hypothesis on lists, and
agreement asked of the three codes of the shape only, "whatever the number of rows".

In standard terms: a radius e is below the Johnson radius of length n and distance d if n (n - d) <
(n - e)^2 (`InJohnson`, Cb/Gen/JohnsonList.lean); a code with its laws and that distance then has at
most `listMax` n d e codewords within e of any word (`ld_list_johnson`, Cb/Ld/LdRelJohnson.lean).
`MCArows` (Cb/Ld/LdRelRows.lean) is mutual correlated agreement on lines, with a count of
exceptional scalars, for every interleaving of a code.
In `ldGroupJohn_seg`, `ldGroupJohn_isGrp` and `ldGroupJohn_below` the group's set of common long
positions, `G.P`, is nonempty, and every oracle message is a member of the group or kept (hc): the
link `Hd.link ..` takes both.

Statements as theorems, proofs: an assembly of Cb/Ld/LdTowerJohn.lean,
Cb/Obj/LdObjectTowerJohn.lean, Cb/Ld/LdRelRows.lean on Cb/Ld/LdGroupFold.lean,
Cb/Ld/LdGroupSeg.lean. Generic: any finite field, any codes read under a transformation. No assumed
theorem.

Why: a session's groups are the batch linear test's and the groups of a request's closings. A
closing's link (`Hd.link`, Cb/Ld/LdGroupSeg.lean) asks, in `ldGroup_seg` (the same file) and in
`D.IsGrp l` (Cb/Req1/LdReqProtoStd.lean), the fold's own hypotheses `Sh.par.Hyp d e t` (on lists
and, three times, on agreement) and a bound on the lists of the group's complex. Under the
hypotheses named below, this file derives them for a radius `G.e` below the Johnson radius of the
distance d as the codes are read (`InJohnson` |P| d e, Cb/Gen/JohnsonList.lean).

Main names:
  `ldGroupJohn_par`: the fold's record "below Johnson" (Cb/Obj/LdObjectTowerJohn.lean:
    `Sh.par.John d e t bC bZ bW`) from the shape's own three codes: laws, distance d and `MCArows`
    of the base code `Sh.Cb`, of the mask code `Sh.Zb`, of the fresh mask's code; rows (the kept
    slots) cost nothing (`ld_rows_il`). Its other hypotheses are fields of the record: hJ
    (`InJohnson`), hi (the challenges' values are distinct), hn (degree at least 2), hp (`PackOK`),
    hq (`QwDeg`), hz (`Sh.par.Cw.Zk t`).
  `ldGroupJohn_list`: under `Sh.OK` and `Sh.par.John d G.e t bC bZ bW`, the lists of the group's
    complex are a theorem: at most `listMax` |P| d e codewords (through the shape: on the members'
    own codes no premise but `Sh.view.Laws`, a field of `Sh.OK` (`Reshape.Laws`,
    Cb/Ld/LdBatShape.lean); no laws, distance or list is asked of them directly).
  `ldGroupJohn_seg`: so the link's hypotheses, under these two, `Hd.Laws`, `Z.OK` and `G.Fits`.
    `ldGroupJohn_isGrp`: and `D.IsGrp l`, under the hypotheses of `ldGroupJohn_seg`, with all bounds
    on lists := `listMax` |P| d e.
  `ldGroupJohn_below`: the errors against numbers of values, written out, L := `listMax` |P| d e: if
    L · (the bridge's evader's number) ≤ κ |its seeds|, L ≤ κ |challenges| and bC + bZ + bW + L · n
    ≤ κ |challenges|, then the link's errors are `Err.Below` κ (Iop/InteractiveOracleProof.lean).

Limits: this file does not say that any code has `MCArows` beyond a third of the distance (an
instance's matter, below the Johnson radius: Cb/Gl/GlGroupJohn.lean, under `BCHKS46F F`;
`Gl.glAg_rows`, Cb/Gl/GlFinalAg.lean, under `Gl.AgreeJ`, which is proved nowhere in this library: it
follows from the statement on codes `Cb.BCHKS46At Gl.F Gl.E` (`Cb.Gl.glAg_ofAt`, same file)), or
that these errors are small. It says nothing between the Johnson radius and
capacity. It says nothing on the second half of a closing (the one sending asks lists of each new
message at its radius): Cb/Ld/LdGroupJohnPack.lean.


Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupLinkBelow
import Cb.Obj.LdObjectTowerJohn
import Cb.Req1.LdReqProtoStd
import Cb.Ld.LdRelRowsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood
open scoped ENNReal

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {G : Grp S} (Sh : GShape G) (d t bC bZ bW : ℕ)

/-- The fold's record below Johnson, from the shape's three codes.
(not all hypotheses are named here: see the statement below) -/
theorem ldGroupJohn_par (lC : Sh.Cb.Laws) (lZ : Sh.Zb.Laws) (lW : Sh.par.Zw.Laws)
    (dC : Sh.Cb.Dist d) (dZ : Sh.Zb.Dist d) (dW : Sh.par.Zw.Dist d)
    (hJ : InJohnson (Fintype.card G.P) d G.e) (mC : Sh.Cb.MCArows G.e bC)
    (mZ : Sh.Zb.MCArows G.e bZ) (mW : Sh.par.Zw.MCArows G.e bW) (hi : Function.Injective Sh.val)
    (hn : 2 ≤ Sh.n) (hp : Sh.par.PackOK) (hq : Sh.par.QwDeg) (hz : Sh.par.Cw.Zk t) :
    Sh.par.John d G.e t bC bZ bW where
  lawsC := ld_laws_il E G.P _ _ lC
  lawsZ := lZ
  lawsW := lW
  distC := ld_dist_il E G.P _ _ d dC
  distZ := dZ
  distW := dW
  john := hJ
  mcaC := ld_rows_il E G.P _ _ G.e bC mC
  mcaZ := mZ
  mcaW := mW
  inj := hi
  deg := hn
  pack := hp
  qw := hq
  zk := hz

variable {d t bC bZ bW}

/-- The lists of the group's complex: a theorem, under `hS` and `h`. -/
theorem ldGroupJohn_list (hS : Sh.OK) (h : Sh.par.John d G.e t bC bZ bW) :
    G.C.ListAt G.e (listMax (Fintype.card G.P) d G.e) :=
  ldGroup_list E S G Sh G.e _ hS
    (ld_list_johnson E G.P Sh.Cin d G.e
      (ld_laws_pair E G.P _ _ (ld_laws_il E G.P _ _ h.lawsC) (ld_laws_il E G.P _ _ h.lawsZ))
      (ld_dist_pair E G.P _ _ d (ld_dist_il E G.P _ _ d h.distC) (ld_dist_il E G.P _ _ d h.distZ))
      h.john)

end

section
variable {E B Kc St₀ Wp : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S}
  [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] (Hd : GHeld Sh kp)
  (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (hc : ∀ o, G.mem o ∨ kp o)
  (dw : S.Wit × Wp) {d t bC bZ bW : ℕ}

/-- The link bridge-to-fold below the Johnson radius. -/
theorem ldGroupJohn_seg (hS : Sh.OK) (hH : Hd.Laws) (h : Sh.par.John d G.e t bC bZ bW)
    (hZ : Z.OK) (hF : G.Fits) :
    (Hd.foldD Sb sl Z A₀).Hyp
      (Hd.link Sb sl Z A₀ hc dw d t (fun _ => listMax (Fintype.card G.P) d G.e) (fun _ => bC)
        (fun _ => bZ) (fun _ => bW) (listMax (Fintype.card G.P) d G.e)) :=
  ldGroup_seg E B Kc St₀ Wp S G Sh kp Hd Sb sl Z E₀ A₀ hc dw d t _ _ _ _ _ hS hH h.hyp hZ
    (ldGroupJohn_list Sh hS h) hF

theorem ldGroupJohn_isGrp (hS : Sh.OK) (hH : Hd.Laws) (h : Sh.par.John d G.e t bC bZ bW)
    (hZ : Z.OK) (hF : G.Fits) :
    (Hd.foldD Sb sl Z A₀).IsGrp
      (Hd.link Sb sl Z A₀ hc dw d t (fun _ => listMax (Fintype.card G.P) d G.e) (fun _ => bC)
        (fun _ => bZ) (fun _ => bW) (listMax (Fintype.card G.P) d G.e)) :=
  ldReqProtoStd_selfFold E B Kc St₀ Wp S G Sh kp Hd Sb sl Z E₀ A₀ hc dw d t _ _ _ _ _ hS hH h.hyp hZ
    (ldGroupJohn_list Sh hS h) hF

/-- The errors against numbers of values. -/
theorem ldGroupJohn_below (κ : ℝ≥0∞)
    (hb : ((listMax (Fintype.card G.P) d G.e * Z.err : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card Z.D : ℝ≥0∞))
    (h0 : (listMax (Fintype.card G.P) d G.e : ℝ≥0∞) ≤ κ * (Fintype.card Sh.Ch : ℝ≥0∞))
    (hi : ((bC + (bZ + bW) + listMax (Fintype.card G.P) d G.e * Sh.n : ℕ) : ℝ≥0∞) ≤
      κ * (Fintype.card Sh.Ch : ℝ≥0∞)) :
    Err.Below (Hd.link Sb sl Z A₀ hc dw d t (fun _ => listMax (Fintype.card G.P) d G.e)
        (fun _ => bC) (fun _ => bZ) (fun _ => bW) (listMax (Fintype.card G.P) d G.e)).P.err κ :=
  ldGroup_link_below Hd Sb sl Z A₀ hc dw d t _ _ _ _ _ κ hb h0 fun i _ => le_trans (Nat.cast_le.2 (by
    show bC + (if i + 1 ≤ Sh.h then bZ + bW else 0) + listMax (Fintype.card G.P) d G.e * Sh.n ≤
      bC + (bZ + bW) + listMax (Fintype.card G.P) d G.e * Sh.n
    split <;> omega)) hi

end
end Cb
