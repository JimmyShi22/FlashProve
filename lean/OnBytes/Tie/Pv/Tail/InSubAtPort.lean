-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/InSubAtPort.lean: the seam in front of the lookup on the digits, at one tuple of
messages (Cb/Pv/Tail/InSubSeam.lean), at the verifier's own record tl : OnBytes.Model.HTailF2.

Main names:
  `digsU h entU en u`: the digits read off a late tuple u: the entries, under `entU` and `en`, at
    the places of `portQJ tl en` that `ixAt` names.
  `digsU_zl`, `digsU_zh`: they are the entries of ZZ in row c and in the columns that the verifier's
    `zzCol` gives for (mu, plane 0 or 1, i).
  `lateU`: the letters `LateU` at the record: I := Pl tl, Q := portQJ tl en, ix := ixAt h.
    `lateU_ok`: the laws of its numbering at the two tables' sizes, under `shapeTest2`.
  `seam₁_port`: the seam at one tuple of messages, under `shapeTest2` and `colsTest`, for every
    letter `bk` whose witness holds the digits of the late tuple.
Limits: `shapeTest2` and `colsTest` are Bools on public numbers: that they are true at a given
sub-proof is a run, no proof term. `entU` and `en` are letters: that the entries which `entU` reads
under `en` are what the prover commits to in ZZ is not said. The letters Λ are free at the record's
sizes: nothing ties their weights, symbols and reads to the record's tables or to committed entries.
No link and no lookup occur here. Nothing on an honest prover.

-/
import Cb.Pv.Tail.InSubSeam
import OnBytes.Tie.Pv.Tail.SeamAtPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.DgP Cb.Pv.Tail Iop CbQ

section
variable {K : Type} {tl : HTailF2} {U W₀ J : Type}

/-- The digits, read off a late tuple at their places in ZZ. -/
def digsU (h : colsTest tl = true) (entU : U → J → K) (en : Ent3 → J) (u : U) :
    Dig K (sizeOf tl).size :=
  ⟨fun μ c i => entU u ((portQJ tl en).lo (ixAt h ⟨μ, c, i⟩)),
    fun μ c i => entU u ((portQJ tl en).hi (ixAt h ⟨μ, c, i⟩))⟩

/-- The low digits that are read are the entries of ZZ in the verifier's own columns. -/
theorem digsU_zl (h : colsTest tl = true) (entU : U → J → K) (en : Ent3 → J) (u : U)
    (μ : Fin (sizeOf tl).size.NM) (c : Fin (sizeOf tl).size.tau)
    (i : Fin ((sizeOf tl).size.m μ)) :
    ∃ col, tl.zzCol μ.val 0 i.val = some col ∧
      (digsU h entU en u).zl μ c i = entU u (en (tl.ix.ZZ, c.val, col)) :=
  ⟨_, (dgP_ix_lo h μ.isLt i.isLt c.isLt).1, rfl⟩

/-- The same for the high digits. -/
theorem digsU_zh (h : colsTest tl = true) (entU : U → J → K) (en : Ent3 → J) (u : U)
    (μ : Fin (sizeOf tl).size.NM) (c : Fin (sizeOf tl).size.tau)
    (i : Fin ((sizeOf tl).size.m μ)) :
    ∃ col, tl.zzCol μ.val 1 i.val = some col ∧
      (digsU h entU en u).zh μ c i = entU u (en (tl.ix.ZZ, c.val, col)) :=
  ⟨_, (dgP_ix_hi h μ.isLt i.isLt c.isLt).1, rfl⟩

/-- The letters of the seam at the verifier's record. -/
def lateU (Λ : Letters K (sizeOf tl).size) (h : colsTest tl = true) (entU : U → J → K)
    (en : Ent3 → J) (bk : U → W₀ → Λ.W) : LateU Λ U W₀ where
  I := Pl tl
  J := J
  bk := bk
  ent := entU
  ix := ixAt h
  Q := portQJ tl en

/-- The laws of the numbering, at the sizes of the two tables. -/
theorem lateU_ok (Λ : Letters K (sizeOf tl).size) (h : colsTest tl = true) (entU : U → J → K)
    (en : Ent3 → J) (bk : U → W₀ → Λ.W) {pp : ℕ} (hs : shapeTest2 tl pp = true) :
    (lateU Λ h entU en bk).Q.DatOK (sizeOf tl).size.lo (sizeOf tl).size.hi pp :=
  dgP_port_okJ en (shape2_parts hs).1

/-- The seam at one tuple of messages, at the verifier's record. -/
theorem seam₁_port [Field K] (Λ : Letters K (sizeOf tl).size) (h : colsTest tl = true)
    (entU : U → J → K) (en : Ent3 → J) (bk : U → W₀ → Λ.W) {pp : ℕ}
    (hs : shapeTest2 tl pp = true) (hr : ∀ u w, Λ.dig (bk u w) = digsU h entU en u)
    {MM Kc : Type} (left : MM → Λ.M) (right : MM → U) (k : MM × W₀ → Kc) :
    ∀ b m w', ((lateU Λ h entU en bk).inD₁ left right k).relR b (m, w') →
      (B Λ).relR b (left m, bk (right m) w') :=
  seam₁ (lateU Λ h entU en bk) left right k (lateU_ok Λ h entU en bk hs) hr

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.digsU_zl
#print axioms OnBytes.Tie.Pv.Tail.digsU_zh
#print axioms OnBytes.Tie.Pv.Tail.lateU_ok
#print axioms OnBytes.Tie.Pv.Tail.seam₁_port
