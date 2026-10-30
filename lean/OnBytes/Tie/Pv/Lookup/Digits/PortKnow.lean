-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Digits/PortKnow.lean: knowledge soundness of the lookup on the digits of a
sub-proof's smallness test, at the verifier's own record tl : OnBytes.Model.HTailF2, with h :=
tl.f9.

Main names:
  `digL E tl en mk jLK St₀`: the caller's layout (`Cb.Fo.Lay`): K := KpJ tl en (call q's own key
    vector in ZZ's entries), bc := bcJ tl en (the places in BZ), mkS s := mk (jLK + s). en: how the
    caller's type J₀ names the entry (array, row, column). mk: how it names the mask row's entry
    under a slot. jLK: the sub-proof's next free slot when the lookup begins.
  `holeD_port`: `TWhole.KnowAt` of `forB` over the field Cb.Gl.E at h := tl.f9, L := digL, from
    `forIn` to `forOut`, under FoNums.ok tl.f9 = true alone (by `holeCgl`). Nothing is asked of en,
    mk or jLK.
  `DigIn`, `forIn_dig`: `forIn` at `digL` is "R0, and every low digit lies in [0, 2^t2D0), every
    high digit in [0, 2^t2D1)", under `shapeTest2` (OnBytes/Tie/Pv/Lookup/Digits/PortSeam.lean).
  `forA_bAt`, `forA_pads`: the planes' places and the padding of `forA` at `digL` are those of
    `portQJ tl en`. The first stands under `PortOK tl` (PortSeam.lean, as above).
  `holeD_dig`: `KnowAt` of the block `digB` (OnBytes/Tie/Pv/Lookup/Holes/HoleD.lean) over Cb.Gl.E at
    Q := portQJ tl en and every P : PlD, from `digIn` to `digOut` (by `hDdig`). Premises:
    shapeTest2 tl Cb.Gl.p = true, which gives `DatOK`, and `NumOK`, a premise on public numbers.
Limits: FoNums.ok tl.f9 and shapeTest2 tl p are Bools on public numbers: that they are true at a
given sub-proof is a run, no proof term. That jLK is the field slotA of the record behind a run of
`transcriptF` is known by reading alone: no statement says it. No statement says that `digB` at
portQJ tl en is `forB` at `digL`: their types of entries differ (J, Option J₀), and P is a variable.
No statement here compares `forB` with the verifier's routine, or `KpJ`, `bcJ` and `portQJ` with
what that routine reads (see the heads of OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean and of
PortSeam.lean). Nothing on the claims behind the lookup in the verifier's own forms.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoAt
import OnBytes.Tie.Pv.Lookup.Holes.HoleD
import OnBytes.Tie.Pv.Lookup.Digits.PortSeam

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.DgP
open OnBytes OnBytes.Model CbQ Cb.LdLkp Cb.Lkp Cb.Fo Iop IOR TWhole

variable {J₀ : Type}

/-- The caller's layout of the lookup on the digits, at the verifier's own record. -/
def digL (E : Type) [Field E] (tl : HTailF2) (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) (St₀ : Type) :
    Lay E St₀ J₀ where
  K := fun _ ν => KpJ tl en ν
  bc := bcJ tl en
  mkS := fun s => mk (jLK + s)

/-- Knowledge soundness of the lookup on the digits, at the verifier's own record. -/
theorem holeD_port (St₀ : Type) [Fintype J₀] [DecidableEq J₀] (tl : HTailF2) (en : Ent3 → J₀) (mk :
    ℕ → J₀) (jLK : ℕ)
    (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → Cb.Gl.E) (H :
        FoNums.ok tl.f9 = true) :
    KnowAt (forB Cb.Gl.E tl.f9 (digL Cb.Gl.E tl en mk jLK St₀) V₀ V₀C (Ex := Ex)).R
      (forIn Cb.Gl.E tl.f9 (digL Cb.Gl.E tl en mk jLK St₀) R0 msg₀) (forOut Cb.Gl.E tl.f9 (digL
          Cb.Gl.E tl en mk jLK St₀) R0 msg₀)
      (fun _ _ _ wp => wp) (forB Cb.Gl.E tl.f9 (digL Cb.Gl.E tl en mk jLK St₀) V₀ V₀C (Ex := Ex)).e
          :=
  holeCgl St₀ J₀ tl.f9 (digL Cb.Gl.E tl en mk jLK St₀) Ex Kc M Wp R0 msg₀ H

section
variable {E : Type} [Field E] {tl : HTailF2}

/-- All digits are in range, in ZZ's entries. -/
def DigIn (tl : HTailF2) (en : Ent3 → J₀) (ν : J₀ → E) : Prop :=
  (∀ i : Pl tl, Cb.Rng.InTab (2 ^ t2D0) (ν (en (tl.ix.ZZ, i.2.val, i.1.val)))) ∧
  ∀ i : Pl tl, Cb.Rng.InTab (2 ^ t2D1) (ν (en (tl.ix.ZZ, i.2.val, tl.mz + i.1.val)))

/-- The block's own joint before, at `digL`, in the digits' words. -/
theorem forIn_dig {pp : ℕ} (h : shapeTest2 tl pp = true) (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ)
    {St₀ Kc M Wp : Type} {Ex : ExtSpec}
    (R0 : Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → E) :
    forIn E tl.f9 (digL E tl en mk jLK St₀) R0 msg₀ =
      ⟨fun x y w => R0.rel x y w ∧ DigIn tl en (msg₀ w.1), fun a w => R0.relR a w ∧ DigIn tl en
          (msg₀ w.1), R0.on, R0.core⟩ := by
  have e : ∀ (x : St₀) (m : M),
      (∀ c < tl.f9.NC, InTable (Port.nOf tl.f9 c) (Port.kOf tl.f9 c)
        (forK E (digL E tl en mk jLK St₀) x (zext (msg₀ m)) c) (forT E tl.f9 x c)) = DigIn tl en
            (msg₀ m) := fun x m =>
    propext (dgP_in_iff en h (msg₀ m) (forT E tl.f9 x) fun c hc t ht => by
      show ((FoNums.tauN tl.f9 c t : ℕ) : E) = _
      rw [show FoNums.tauN tl.f9 c t = t from (shape2_parts h).2.2.rows c hc t ht])
  unfold Cb.Fo.forIn Port.jIn
  simp only [e]

variable [Fintype E] [Fintype J₀] [DecidableEq J₀]

/-- The places of the planes in `forA` at `digL` are those of the record of the digits. -/
theorem forA_bAt (hP : PortOK tl) (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) (St₀ : Type) (u j : ℕ) :
    (forA E tl.f9 (digL E tl en mk jLK St₀)).bAt u j = some ((portQJ tl en).bAt u j) := by
  have hlt : u % 2 ^ tl.f9.cK < tl.f9.NC := by
    rw [← hP.full]
    exact Nat.mod_lt _ (by positivity)
  show (FoNums.cellOf tl.f9 u j).map (fun x => bcJ tl en x.1 x.2.1 x.2.2) = _
  unfold FoNums.cellOf
  rw [if_pos hlt]
  show some (bcJ tl en (u / 2 ^ tl.f9.cK) (u % 2 ^ tl.f9.cK) j) = _
  rw [dgP_bcJ]

/-- The padding in `forA` at `digL` is that of the record of the digits. -/
theorem forA_pads (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) (St₀ : Type) :
    (forA E tl.f9 (digL E tl en mk jLK St₀)).pads = (portQJ tl en).pads := rfl

end

/-- The block `digB` of the record of the digits, at the value `portQJ tl en` of that record. -/
theorem holeD_dig (St : Type) {J : Type} [Fintype J] [DecidableEq J] (tl : HTailF2) (en : Ent3 → J)
    (P : PlD Cb.Gl.E J (portQJ tl en).d) (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc St Ex (M ×
        Wp)) (msg : M → J → Cb.Gl.E)
    (h : shapeTest2 tl Cb.Gl.p = true) (hN : NumOK (portQJ tl en) P Cb.Gl.p) :
    KnowAt (digB St (portQJ tl en) P (Ex := Ex)).R (digIn (portQJ tl en) (2 ^ t2D0) (2 ^ t2D1) R0
        msg)
      (digOut (portQJ tl en) P R0 msg) (fun _ _ _ wp => wp) (digB St (portQJ tl en) P (Ex := Ex)).e
          :=
  hDdig Cb.Gl.E Cb.Gl.p St (Pl tl) J (portQJ tl en) P (2 ^ t2D0) (2 ^ t2D1) Ex Kc M Wp R0 msg
    (dgP_port_okJ en (shape2_parts h).1) hN

#print axioms holeD_port
#print axioms forIn_dig
#print axioms forA_bAt
#print axioms forA_pads
#print axioms holeD_dig

end OnBytes.DgP
