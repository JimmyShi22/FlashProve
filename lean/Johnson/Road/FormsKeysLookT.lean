-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysLookT.lean: for a layout whose eight calls are the library's, one point of the
library serves all calls of the lookup.

The theorems that compare the verifier's weights of layers, columns and calls with the library's ask
that the point of a call reads as the library's point of that call (zc in
Inst/Model/FF/Objects.lean) at a point z of the whole lookup. In the library one z serves all eight
calls. Johnson/Road/FormsKeysLook.lean shows, from the numbers of the trees (TreesFit), that the
point zOf, made from the lookup's two points, is such a z. This file concludes TreesFit from the
verifier's layout, and the ties of all families at that one point.

What is compared with what: the verifier's Lean text (layout, Forest.shape, and the line of
Forest.pad that makes the calls' points) against the library's aC, eC, Dk, sg, NT, firstTree, zc.
Of these, and of wc and zpos: eC, zc, wc and zpos are definitions of Inst/Model/FF/Objects.lean that
no theorem of the library reads; Dk, sg, NT and firstTree have readers there
(Inst/Model/FF/IndexFacts.lean, Inst/Model/FF/Trace.lean).

Main theorems.
 - treesFit_of_layout: the numbers of the layout's trees are the library's.
 - callTieV_of_look: the tie CallTieV (Johnson/Road/FormsKeysPortFits.lean), which is CallTie of
   Johnson/Road/FormsKeysAim.lean, holds for EVERY family at the one point zOf.
 - look_fits: the points, the weights and the token point together.

The hypotheses, and where they are met together. hy, S, Z, hc, h8 and H are those of Dk_of_layout
(Johnson/Road/FormsKeysShape.lean): the layout returns; the switches; the sizes agree, with the
verifier's cap on a tree's depth; there are eight calls; call number cc has the line of the
library's call cc, and the verifier's least number of columns does not make it longer (for ALL
eight). At the made-up shape hR8 a guard there holds hy, h8 and H; S, Z and hc are theorems
(switchesR8 in Johnson/Road/FormsKeysRun8.lean, sized_dimC in Johnson/Road/FormsKeysCap.lean). At
the full-size example Johnson/Road/FormsKeysRunK.lean has the switches and the sizes as theorems
(switchesK, sizedKF) and the lines' names and the eight bounds in a guard (scanK); its like guard at
the small example has the bound false for the calls 0, 5, 6 and 7. hsx, hsy, hzk: the two points
have dT and rK coordinates, and the calls' points are made from them in the letters
of Forest.pad (OnBytes/Model/Look.lean). They stand inside a routine that reads messages, so they
are asked here, on the layout's own numbers; hearLook (OnBytes/Model/Layer.lean) refuses unless the
numbers that the run computes are the layout's. A guard of
Johnson/Road/FormsKeysRunZ.lean (padZ) holds them, with that routine's two
tests, at a made-up lookup, at both made-up shapes and both examples; the same file runs all
conclusions with the library's own definitions.

Which value is which: all are public: numbers of the layout, and challenges that the verifier has
kept. No hidden value and no sent value occurs.

What is not claimed. Nothing where the least number of columns makes a call longer: at the two
shapes of that kind that are run (Johnson/Road/FormsKeysRunZ.lean) the two
forests differ as a whole. That no call is made longer is enough for these theorems; it is not shown
to be needed. That v.zk is the array that Forest.pad makes is asked, not shown; that its two points
have these lengths is asked too (Johnson/Road/FormsKeysLookP.lean has them from that routine's own
lines and one of its tests). The numbers of padding keys, the trees' products, the tables and the
end of the lookup are not looked at. The program does not import this file.
-/
import Johnson.Road.FormsKeysLook
import Johnson.Road.FormsKeysForest
import Johnson.Road.FormsKeysPortFits

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading Call CallD Seg lastOf)
open OnBytes.Model.Layer (Env Lay layout)
open Inst.Model.FFSeg (Dim Fam aC eC Dk sg zc wc zpos call fams used lJ)

variable {K : Type} [Field K]

section Layout

variable {h : Model.Layer.Shape} {pc : List (List String)} {v : Env} {D : Dim}

/-- The numbers of the trees of a layout whose eight calls are the library's are the library's. The
hypotheses are those of Dk_of_layout. -/
theorem treesFit_of_layout (hy : layout h pc = .ok v.y) (S : Switches h) (Z : Sized h D)
    (hc : D.cap = h.lidb) (h8 : v.y.calls.size = 8)
    (H : ∀ cc : Fin 8, ∃ cd, v.y.calls[cc.val]? = some cd ∧
      cd.segs.map (·.name) = (fams cc).map segName ∧
      h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc)) :
    TreesFit v.y.fo D := by
  obtain ⟨s0, pub, hs0, e⟩ := shape_of_layout hy
  obtain ⟨-, hN, hr, hf⟩ := shape_numbers hs0
  have hsz : v.y.cl.size = 8 := by rw [(fo_of_layout hy).2.2, h8]
  have hd : v.y.fo.dT = Dk D := (Dk_of_layout hy S Z hc h8 H).symm
  rw [hsz] at hN hf
  rw [e] at hd ⊢
  refine treesFit_of_numbers (n := fun c => (v.y.cl.getD c default).n) (fun cc => ?_) hd
    (fun c hc8 => shape_iota_at hs0 (by rw [hsz]; exact hc8)) hN hr hf
  obtain ⟨cd, hcq, hn, hfl⟩ := H cc
  have h1 := n_of_layout hy S Z hcq hn hfl
  show (v.y.cl.getD cc.val default).n = aC D cc
  rw [Array.getD_eq_getD_getElem?]
  cases hx : v.y.cl[cc.val]? with
  | none => rw [hx] at h1; cases h1
  | some r =>
    rw [hx] at h1
    exact Option.some.inj h1

variable {ρ : Reading K} {zx zy : Array E}

/-- (T) THE TIES OF ALL FAMILIES AT ONE POINT. For a layout whose eight calls are the library's,
with the calls' points made from the lookup's two points in the letters of Forest.pad: for every
family the call that holds its segment is the library's call of the family, and its point reads as
the library's at the one point zOf. -/
theorem callTieV_of_look (hy : layout h pc = .ok v.y) (S : Switches h) (Z : Sized h D)
    (hc : D.cap = h.lidb) (h8 : v.y.calls.size = 8)
    (H : ∀ cc : Fin 8, ∃ cd, v.y.calls[cc.val]? = some cd ∧
      cd.segs.map (·.name) = (fams cc).map segName ∧
      h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc))
    (hsx : zx.size = v.y.fo.dT) (hsy : zy.size = v.y.fo.rK)
    (hzk : v.zk = (Array.range v.y.fo.NC).map fun c =>
      zy.extract (v.y.fo.rK - v.y.fo.iota.getD c 0) zy.size ++ zx) (s0 : Fam) :
    CallTieV ρ v h D (zOf ρ zx zy) s0 := by
  intro q cd s hcall
  have T := treesFit_of_layout hy S Z hc h8 H
  have hNC : v.y.fo.NC = 8 := by rw [(fo_of_layout hy).2.1, (fo_of_layout hy).2.2, h8]
  obtain ⟨hq, hs, hname⟩ := callOf_spec hcall
  have hq8 : q < 8 := by
    rw [← h8]
    exact (Array.getElem?_eq_some_iff.mp hq).1
  obtain ⟨cd', hcq, hn, hfl⟩ := H ⟨q, hq8⟩
  have ecd : cd' = cd := Option.some.inj (hcq.symm.trans hq)
  subst ecd
  have hm : segName s0 ∈ (fams ⟨q, hq8⟩).map segName := by
    rw [← hn, ← hname]
    exact List.mem_map.mpr ⟨s, hs, rfl⟩
  obtain ⟨s', hs', e⟩ := List.mem_map.mp hm
  have es : s' = s0 := segName_inj e
  subst es
  have hcc : call s' = ⟨q, hq8⟩ := Inst.Model.FFSeg.IndexFacts.call_of_mem _ _ hs'
  rw [hcc]
  refine ⟨hn, hfl, ?_, zc_of_look T hNC hsx hsy hzk ⟨q, hq8⟩⟩
  have hsize := size_of_look T hNC hsx hsy hzk ⟨q, hq8⟩
  have hsh := (admitted_of_layout hy S.p3).shape
  have hfl' : h.nmin - h.ll - h.lt ≤ lJ D ⟨q, hq8⟩ := hfl
  have hlJ : cd'.lJ = lJ D ⟨q, hq8⟩ := by
    rw [lJ_of_call hy S Z (Array.mem_of_getElem? hcq) hn, Nat.max_eq_left hfl']
  show v.y.h.ll + cd'.lJ ≤ (v.zk.getD q #[]).size
  rw [hsize, hlJ, hsh, ← Z.lL]
  show D.lL + lJ D ⟨q, hq8⟩ ≤ D.lL + lJ D ⟨q, hq8⟩ + D.lT
  exact Nat.le_add_right _ _

/-- The points, the weights and the token point together, at the one point zOf: each call's point on
all its coordinates; each call's weight as the lookup computes it; the last lT coordinates of the
point inside a tree. -/
theorem look_fits (hy : layout h pc = .ok v.y) (S : Switches h) (Z : Sized h D)
    (hc : D.cap = h.lidb) (h8 : v.y.calls.size = 8)
    (H : ∀ cc : Fin 8, ∃ cd, v.y.calls[cc.val]? = some cd ∧
      cd.segs.map (·.name) = (fams cc).map segName ∧
      h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc))
    (hsx : zx.size = v.y.fo.dT) (hsy : zy.size = v.y.fo.rK)
    (hzk : v.zk = (Array.range v.y.fo.NC).map fun c =>
      zy.extract (v.y.fo.rK - v.y.fo.iota.getD c 0) zy.size ++ zx) :
    (∀ c : Fin 8, ∀ j, j < aC D c → pt ρ (v.zk.getD c.val #[]) j = zc D (zOf ρ zx zy) c j) ∧
      (∀ c : Fin 8, ρ.val (Model.Forest.callWeight v.y.fo zy c.val) = wc D (zOf ρ zx zy) c) ∧
      ∀ zt, lastOf zx D.lT = .ok zt → ∀ j, j < D.lT → zpos D (zOf ρ zx zy) j = pt ρ zt j := by
  have T := treesFit_of_layout hy S Z hc h8 H
  have hNC : v.y.fo.NC = 8 := by rw [(fo_of_layout hy).2.1, (fo_of_layout hy).2.2, h8]
  exact ⟨fun c => zc_of_look T hNC hsx hsy hzk c, fun c => wc_of_look T hsx c,
    fun zt hzt => zpos_of_look T hsx hzt⟩

end Layout

#print axioms treesFit_of_layout
#print axioms callTieV_of_look
#print axioms look_fits

end OnBytes.Road
