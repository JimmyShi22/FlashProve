-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/EmbPort.lean: the port from the one claim that the layers' own rounds make in the
first group alone, on the stream that comes in (group 12 of K4's run "front": embeddingForm,
OnBytes/Desc/First/K4/Claims.lean), to the library-side claim cEmb | embClaim
(Cb/Pv/Lay/End/EmbCl.lean, EmbShare.lean): where K4's form is worth 0, so is the library's.

The two have one shape: a hidden scalar against the blocks' reads of the stream under equality
weights. K4's form is the library's with the other sign. The library's offset of the array x0 is 0,
and K4's reading of a block (Env.xbA) has none.

Main names:
  `EmbDict`: the port's premises, at an environment v, what was heard H, a slot sVE and at
    library-side letters sh, mE, uX, nb, gB, pb and entries y: how numerals are read; two sizes; the
    hidden value under the slot; the verifier's table of weights against the library's equality
    weights; the entries of the reads against the library-side entries.
  `xbA_read`: a block of the stream, read from a long table: its limbs under the powers of 256.
  `emb_val`: K4's form is worth the negative of the library's.
  `emb_port`: K4's form worth 0 gives cEmb worth 0. `emb_port_claim`: the same at embClaim.
  `emb_mem`: in the first group the form is a member of the list that K4's run "front" returns.
  `emb_of_front`: where that list is worth 0 form by form, embClaim is worth 0.
Limits. EmbDict is a premise: no run, world and entries are shown at which it holds. The point at
which the table "xbI@Z_E" is read does not occur: it stands in what the entries y are, of which
nothing is said here. Implications in one world: no draw, nothing on soundness or on hiding.


-/
import Johnson.Road.Rows.LayerGatedPort
import OnBytes.Desc.First.K4.ClaimsLaws
import Cb.Pv.Lay.End.EmbShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (Reading World Aff Fork tenCell eqTab)
open OnBytes.Model.Layer (Env Heard Pub Own)
open OnBytes.Road.Rows (readAtW U3at_read sumForms_value_lt)
open OnBytes.Desc.First.K4 (embeddingForm)
open Inst.Model.FFSeg (Arr)
open Cb.Pv.Lay.End (LateLay)
open Cb.Pv.Lay.End.Gated (cEmb embClaim EmbNm)
open Blocks (Form eqN)

variable {K : Type} [Field K] {J : Type} [Fintype J] [DecidableEq J]

/-- The premises of the port. sh: the scalar that was sent; mE: its mask entry; uX l kh: the read of
limb l of block kh; nb: the blocks of the stream's width; gB, pb: the bits and the point of the
blocks' weights. -/
structure EmbDict (ρ : Reading K) (W : World K) (v : Env) (H : Heard) (sVE : ℕ) (sh : K) (mE : J)
    (uX : ℕ → ℕ → J) (nb gB : ℕ) (pb : ℕ → K) (y : J → K) : Prop where
  /-- how numerals are read -/
  num : Numerals ρ
  /-- sizes: the limbs of the stream; its blocks -/
  nl5 : v.y.xb.nl = 5
  hB : v.y.h.d / v.y.S2 = nb
  /-- the hidden value under the slot -/
  slot : W.slot sVE = sh - y mE
  /-- the weights of the blocks -/
  wts : ∀ kh, kh < nb → ρ.val ((eqTab H.tkh).getD kh zeroE) = eqN gB 0 pb kh
  /-- the reads of the stream's limbs at the embedding's point -/
  reads : ∀ t, v.tabAt "xbI@Z_E" = some t → ∀ l kh, l < 5 → kh < nb →
    readAtW W v t (tenCell v.y.xb l 0 0 / v.y.S2 + kh) = y (uX l kh)

variable {ρ : Reading K} {W : World K} {v : Env} {H : Heard} {sVE : ℕ} {sh : K} {mE : J}
  {uX : ℕ → ℕ → J} {nb gB : ℕ} {pb : ℕ → K} {y : J → K}

/-- A block of a residual stream, read from a long table. -/
theorem xbA_read (hρ : Numerals ρ) {t kh : ℕ} {a : Aff} (h : v.xbA t kh = some a) :
    a.value ρ W =
      ∑ l ∈ range v.y.xb.nl, (256 : K) ^ l * readAtW W v t (tenCell v.y.xb l 0 0 / v.y.S2 + kh) :=
  limbs_value hρ (readAtW W v t) (fun _ _ hb => U3at_read hb) h

/-- The library-side claim, written out. -/
theorem val_cEmb : Form.val y (cEmb sh mE uX nb gB pb) =
    sh - y mE - ∑ kh ∈ range nb, eqN gB 0 pb kh * ∑ l ∈ range 5, (256 : K) ^ l * y (uX l kh) := by
  unfold cEmb
  rw [map_sub, Form.val_masked, map_sum]
  congr 1
  refine sum_congr rfl fun kh _ => ?_
  have e0 : ((Arr.x0.off : ℤ) : K) = 0 := by
    show ((0 : ℤ) : K) = 0
    exact Int.cast_zero
  have e5 : Arr.x0.nCell = 5 := rfl
  rw [map_smul, smul_eq_mul, map_add, Form.val_const, e0, add_zero, map_sum, e5]
  refine congrArg (eqN gB 0 pb kh * ·) ?_
  exact sum_congr rfl fun l _ => by rw [map_smul, Form.val_ent, smul_eq_mul]

/-- **K4's form is worth the negative of the library's.** -/
theorem emb_val (Dc : EmbDict ρ W v H sVE sh mE uX nb gB pb y) {a : Aff}
    (h : embeddingForm v H sVE = some a) :
    a.value ρ W = -Form.val y (cEmb sh mE uX nb gB pb) := by
  unfold embeddingForm at h
  obtain ⟨t, ht, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨s, hs, h2⟩ := Option.bind_eq_some_iff.mp h1
  have ea : (Aff.slot sVE).scale (negE oneE) + s = a := Option.some.inj h2
  have hv : s.value ρ W =
      ∑ kh ∈ range nb, eqN gB 0 pb kh * ∑ l ∈ range 5, (256 : K) ^ l * y (uX l kh) := by
    have hs' : Model.Layer.sumForms nb
        (fun kh => (v.xbA t kh).map fun a => (a, (eqTab H.tkh).getD kh zeroE)) = some s := by
      rw [← Dc.hB]
      exact hs
    refine sumForms_value_lt _ _ _ (fun kh hk c k hc => ?_) hs'
    obtain ⟨hx, rfl⟩ := map_pair_some hc
    rw [Dc.wts kh hk, xbA_read Dc.num hx, Dc.nl5]
    refine congrArg (eqN gB 0 pb kh * ·) ?_
    exact sum_congr rfl fun l hl => by rw [Dc.reads t ht l kh (mem_range.mp hl) hk]
  rw [← ea, Aff.value_add, Aff.value_scale, Aff.value_slot, Dc.num.neg, ρ.one, Dc.slot, hv,
    val_cEmb]
  ring

/-- **The port.** -/
theorem emb_port (Dc : EmbDict ρ W v H sVE sh mE uX nb gB pb y) {a : Aff}
    (h : embeddingForm v H sVE = some a) (hz : a.value ρ W = 0) :
    Form.val y (cEmb sh mE uX nb gB pb) = 0 := by
  rw [emb_val Dc h] at hz
  exact neg_eq_zero.mp hz

/-- In the first group the form is there, and is a member of the list that "front" returns. -/
theorem emb_mem {rows : Bool} {P : Pub} {o : Own} {F G : Fork} {fs : Array Aff}
    (h : Desc.First.K4.formsFrontWith rows P 0 o F = some (fs, G)) :
    ∃ a, embeddingForm o.v o.H o.sVE = some a ∧ a ∈ fs.toList := by
  obtain ⟨sw, pp, l, -, -, -, -, k3, k4, -, -, -⟩ := Desc.First.K4.formsFrontWith_some h
  obtain ⟨l2, g46, l7, l89, l10, g11, g12, -, -, -, -, -, -, c7, e⟩ :=
    Desc.First.K4.front_some k3
  have c8 : (embeddingForm o.v o.H o.sVE).map ([·]) = some g12 := c7
  obtain ⟨a, ha, rfl⟩ := map_some c8
  refine ⟨a, ha, ?_⟩
  rw [k4, e]
  simp

section Claim

variable {J₁ Nm J₂ : Type} [Fintype J₁] [DecidableEq J₁] [Fintype J₂] [DecidableEq J₂]
  {Y : LateLay Nm J₂} {ι : EmbNm → Nm} {m₁ : J₁} {y₂ : J₁ ⊕ J₂ → K}

/-- The port at the names of early and late entries. -/
theorem emb_port_claim
    (Dc : EmbDict ρ W v H sVE sh (Sum.inl m₁ : J₁ ⊕ J₂)
      (fun l kh => Sum.inr (Y.at' (ι (.x0 l kh)))) nb gB pb y₂) {a : Aff}
    (h : embeddingForm v H sVE = some a) (hz : a.value ρ W = 0) :
    Form.val y₂ (embClaim Y ι sh m₁ nb gB pb) = 0 :=
  emb_port Dc h hz

/-- **From the list of K4's run "front" in the first group.** -/
theorem emb_of_front {rows : Bool} {P : Pub} {o : Own} {F G : Fork} {fs : Array Aff}
    (Dc : EmbDict ρ W o.v o.H o.sVE sh (Sum.inl m₁ : J₁ ⊕ J₂)
      (fun l kh => Sum.inr (Y.at' (ι (.x0 l kh)))) nb gB pb y₂)
    (h : Desc.First.K4.formsFrontWith rows P 0 o F = some (fs, G))
    (hz : ∀ f ∈ fs.toList, f.value ρ W = 0) :
    Form.val y₂ (embClaim Y ι sh m₁ nb gB pb) = 0 := by
  obtain ⟨a, ha, hm⟩ := emb_mem h
  exact emb_port_claim Dc ha (hz a hm)

end Claim

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.emb_val
#print axioms OnBytes.Road.K4.emb_port
#print axioms OnBytes.Road.K4.emb_mem
#print axioms OnBytes.Road.K4.emb_of_front
