-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Digits/PortJ.lean: the terms of PortDat.lean and PortKeys.lean at a caller's
own type of entries.

The record of one lookup asks that the type J of entries is finite; `Ent3` = ℕ × ℕ × ℕ is not. Here
every term takes an argument en : Ent3 → J: how the caller's type names the entry (array, row,
column). Nothing is asked of J or of en. Each law of PortKeys.lean holds for every tuple of entries
mu : Ent3 → E; here it is taken at mu := nu ∘ en.

Main names:
  `CbQ.DatQ.mapJ`, `mapJ_ok`, `mapJ_key`: a record of the digits with its places carried along a
    map.
  `portQJ tl en`, `dgP_port_okJ`: the value at the caller's J, and its laws from the test on the
    shape.
  `KpJ`, `KFlJ`, `bcJ`, `bitJ`; `dgP_key_portJ`, `dgP_KFokJ`, `dgP_bcJ`: keys, form, places, with
    laws.
  `dgP_formJ`: where J is finite: the form of the claim on the joint keys, on J.
  `EntF tl`, `enF`, `enF_inj`: one finite J: the entries of ZZ, those of BZ, and one more.
Limits: `EntF` has no entries for a lookup's masks: it shows that a finite J exists, no more.

-/
import OnBytes.Tie.Pv.Lookup.Digits.PortKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.DgP
open OnBytes OnBytes.Model CbQ Cb.LdLkp Cb.Lkp Blocks

/-- A DatQ with its places carried along a map of entries. -/
def _root_.CbQ.DatQ.mapJ {I J J' : Type} (Q : DatQ I J) (en : J → J') : DatQ I J' :=
  { lo := fun i => en (Q.lo i), hi := fun i => en (Q.hi i), v := Q.v, d := Q.d, nc := Q.nc, call :=
      Q.call, pos := Q.pos,
    digAt := Q.digAt, fK := Q.fK, fT := Q.fT, rowV := Q.rowV, tag := Q.tag, rowOf := Q.rowOf, zRow
        := Q.zRow,
    bAt := fun Y j => en (Q.bAt Y j), pads := Q.pads }

/-- DatOK reads no place. -/
theorem mapJ_ok {I J J' : Type} (Q : DatQ I J) (en : J → J') {q H pp : ℕ} (h : Q.DatOK q H pp) :
    (Q.mapJ en).DatOK q H pp :=
  { posLt := h.posLt, inv := h.inv, inv' := h.inv', callK := h.callK, kLt := h.kLt, tLt := h.tLt,
      rowLo := h.rowLo, rowHi := h.rowHi,
    ofLo := h.ofLo, ofHi := h.ofHi, zero := h.zero, tagLt := h.tagLt, tagInj := h.tagInj, pads :=
        h.pads, laid := h.laid }

/-- The joint keys at the carried places are the joint keys at the composed tuple of entries. -/
theorem mapJ_key {I J J' E : Type} [Field E] (Q : DatQ I J) (en : J → J') (ν : J' → E) (X : ℕ) :
    (Q.mapJ en).key ν X = Q.key (fun n => ν (en n)) X := by
  unfold DatQ.key
  show (match Q.digAt X with | some p => ν ((Q.mapJ en).plc p) | none => 0) = _
  cases Q.digAt X with
  | none => rfl
  | some p =>
    obtain ⟨b, i⟩ := p
    cases b <;> rfl

variable {tl : HTailF2} {J : Type} (en : Ent3 → J)

/-- The record of the digits at the caller's type of entries. -/
def portQJ (tl : HTailF2) (en : Ent3 → J) : DatQ (Pl tl) J := (portQ tl).mapJ en

/-- DatOK at it, for a variable tail, from the test on the shape. -/
theorem dgP_port_okJ {pp : ℕ} (h : shapeTest tl pp = true) : (portQJ tl en).DatOK (2 ^ t2D0) (2 ^
    t2D1) pp :=
  mapJ_ok (portQ tl) en (dgP_port_ok h)

section
variable {E : Type} [Field E]

/-- K, KF, bc, bit at the caller's J. -/
def KpJ (tl : HTailF2) (en : Ent3 → J) (ν : J → E) (q kn : ℕ) : E := Kp tl (fun n => ν (en n)) q kn
def KFlJ (tl : HTailF2) (en : Ent3 → J) (q : ℕ) (z : List E) : AffK J E :=
  ((KFl tl q z).1.map fun x => (en x.1, x.2), (KFl tl q z).2)
def bcJ (tl : HTailF2) (en : Ent3 → J) (t c j : ℕ) : J := en (bcP tl t c j)
def bitJ (tl : HTailF2) (en : Ent3 → J) (ν : J → E) (Y j : ℕ) : E := ν ((portQJ tl en).bAt Y j)

theorem dgP_key_portJ (hT : TailOK tl) (ht0 : Port.t0Of tl.f9 0 = 0) (ν : J → E) (X : ℕ) :
    (portQJ tl en).key ν X = Port.key tl.f9 (Tp (E := E)) (KpJ tl en ν) X := by
  unfold portQJ
  rw [mapJ_key]
  exact dgP_key_port hT ht0 _ X

theorem valJ (f : AffK Ent3 E) (ν : J → E) :
    AffK.val ((f.1.map fun x => (en x.1, x.2), f.2) : AffK J E) ν = AffK.val f fun n => ν (en n) :=
        by
  unfold AffK.val
  rw [List.map_map]
  rfl

theorem dgP_KFokJ (hT : TailOK tl) (ν : J → E) {q : ℕ} (hq : q < 2) (z : List E) (hz : z.length =
    Port.nOf tl.f9 q) :
    (KFlJ tl en q z).val ν = ext z.length (KpJ tl en ν q) (ofList z) := by
  unfold KFlJ KpJ
  rw [valJ]
  exact dgP_KFok hT _ hq z hz

theorem dgP_bcJ (u j : ℕ) : bcJ tl en (u / 2 ^ tl.f9.cK) (u % 2 ^ tl.f9.cK) j = (portQJ tl en).bAt u
    j := by
  unfold bcJ
  rw [dgP_bc]
  rfl

/-- Where J is finite: the masked claim's form on J, at the port's value. -/
theorem dgP_formJ [Fintype J] [DecidableEq J] {pp : ℕ} (h : shapeTest tl pp = true) (ν : J → E) (θ :
    E) (pt : ℕ → E) :
    ext (portQJ tl en).v (shKeyQ (portQJ tl en).fK ((portQJ tl en).key ν) (portQJ tl en).tagE θ) pt
        =
      ∑ n, (portQJ tl en).formK pt n * ν n + θ * (portQJ tl en).constK pt :=
  dgQ_form (portQJ tl en) (dgP_port_okJ en h) ν θ pt

end

/-! ## one finite J -/

/-- The entries of ZZ, the entries of BZ, and one more (for whatever is neither). -/
abbrev EntF (tl : HTailF2) : Type := Option ((Fin tl.tau × Fin (2 * tl.mz)) ⊕ (Fin 32 × Fin
    tl.bzColumns))

def enF (tl : HTailF2) (n : Ent3) : EntF tl :=
  if n.1 = tl.ix.ZZ then
    if h : n.2.1 < tl.tau ∧ n.2.2 < 2 * tl.mz then some (.inl (⟨n.2.1, h.1⟩, ⟨n.2.2, h.2⟩)) else
        none
  else if n.1 = tl.ix.BZ then
    if h : n.2.1 < 32 ∧ n.2.2 < tl.bzColumns then some (.inr (⟨n.2.1, h.1⟩, ⟨n.2.2, h.2⟩)) else none
  else none

/-- enF tells the entries of ZZ and BZ in range apart. -/
theorem enF_inj {n n' : Ent3} (h : enF tl n = enF tl n') (hn : enF tl n ≠ none) : n = n' := by
  obtain ⟨a, r, c⟩ := n
  obtain ⟨a', r', c'⟩ := n'
  unfold enF at h hn
  simp only at h hn
  split_ifs at h hn <;> simp_all [Prod.ext_iff, Fin.ext_iff]

example (tl : HTailF2) : Fintype (EntF tl) := inferInstance
example (tl : HTailF2) : DecidableEq (EntF tl) := inferInstance

#print axioms mapJ_ok
#print axioms mapJ_key
#print axioms dgP_port_okJ
#print axioms dgP_key_portJ
#print axioms dgP_KFokJ
#print axioms dgP_bcJ
#print axioms dgP_formJ
#print axioms enF_inj

end OnBytes.DgP
