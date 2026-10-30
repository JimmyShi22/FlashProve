-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoDig5.lean.
The two layouts of the lookup on the digits, held side by side.

digL (OnBytes/Tie/Pv/Lookup/Digits/PortKnow.lean) takes the cells of the counts' bits from the
matrix BZ at every row number t. digL5 (OnBytes/Tie/Pv/Lookup/Digits/PortEnds.lean) takes them
through a virtual matrix with one row for each plane, so that its cells are a function of
FoNums.cellRC at lm = 5 at every t; below 2^kT they are BZ's (digL5_bc).

* digL5_K, digL5_mkS, digL5_forK: the key vectors and the mask places of the two are the same.
* KFd_digKF: the two names for the digits' key forms are one.
* dig5_KFok_ends: under TailOK tl and FoNums.ok tl.f9 = true, the digits' key forms read the calls'
  key vectors at the points of the record of end values, at digL5 (KFok).
* holeD_port5: under FoNums.ok tl.f9 = true, knowledge soundness (TWhole.KnowAt) of the lookup forB
  at digL5, from forIn to forOut, over the field Cb.Gl.E (by holeCgl).

Limits: those of OnBytes/Tie/Pv/Lookup/Digits/PortEnds.lean. Among them: holeD_port5 is on the typed
verifier forB at V₀, V₀C: nothing here compares it with the routine Forest.pad
(OnBytes/Model/Look.lean). The smallness test writes its three claims on BZ by hand (linBits9,
OnBytes/Model/Tail.lean): that these are the same forms on BZ's entries is not shown here. It writes
linJoin9: that this and the plain twin of Forest.join at KFd are one form on ZZ's entries is held by
a run at one small made-up shape alone. Beyond 2^kT nothing is stated of digL5's cells.

Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Digits.PortEnds
import OnBytes.Tie.Pv.Lookup.Forest.FoKfDig

set_option autoImplicit false

namespace Fo
open TwV FoNums OnBytes OnBytes.Model OnBytes.DgP Cb Cb.LdLkp Cb.Fo Iop IOR TWhole

section
variable {J₀ : Type} (E : Type) [Field E] (tl : HTailF2) (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ)
  (St₀ : Type)

theorem digL5_K : (digL5 E tl en mk jLK St₀).K = (digL E tl en mk jLK St₀).K := rfl
theorem digL5_mkS : (digL5 E tl en mk jLK St₀).mkS = (digL E tl en mk jLK St₀).mkS := rfl
theorem digL5_forK : forK E (digL5 E tl en mk jLK St₀) = forK E (digL E tl en mk jLK St₀) := rfl

variable {E}

theorem KFd_digKF (zk : ℕ → List E) : KFd tl en zk = digKF tl en zk := by
  funext c
  unfold KFd digKF someK KFlJ
  simp only [List.map_map]
  rfl

theorem dig5_KFok_ends {tl : HTailF2} (hT : TailOK tl) (H : FoNums.ok tl.f9 = true)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) {St₀ : Type} (st : St₀) (lm j0 : ℕ) (rs : Rounds E) :
    KFok tl.f9 (forK E (digL5 E tl en mk jLK St₀) st)
      (fun c => (endsOf tl.f9 lm j0 rs).zk.getD c [])
      (digKF tl en fun c => (endsOf tl.f9 lm j0 rs).zk.getD c []) :=
  dig_KFok_ends hT H en mk jLK st lm j0 rs

end

theorem holeD_port5 {J₀ : Type} (St₀ : Type) [Fintype J₀] [DecidableEq J₀] (tl : HTailF2)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) (Ex : ExtSpec) (Kc M Wp : Type)
    (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → Cb.Gl.E) (H : FoNums.ok tl.f9 = true) :
    KnowAt (forB Cb.Gl.E tl.f9 (digL5 Cb.Gl.E tl en mk jLK St₀) V₀ V₀C (Ex := Ex)).R
      (forIn Cb.Gl.E tl.f9 (digL5 Cb.Gl.E tl en mk jLK St₀) R0 msg₀)
      (forOut Cb.Gl.E tl.f9 (digL5 Cb.Gl.E tl en mk jLK St₀) R0 msg₀) (fun _ _ _ wp => wp)
      (forB Cb.Gl.E tl.f9 (digL5 Cb.Gl.E tl en mk jLK St₀) V₀ V₀C (Ex := Ex)).e :=
  holeCgl St₀ J₀ tl.f9 (digL5 Cb.Gl.E tl en mk jLK St₀) Ex Kc M Wp R0 msg₀ H

end Fo
