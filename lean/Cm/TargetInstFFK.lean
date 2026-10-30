-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetInstFFK.lean: a feed-forward segment for every lawful table of scales: from the field
relation to the program, at a variable prime.

Three statements with their proofs, for a prime p with 2^61 - 1 ≤ p (the class `Big p`:
Inst/Model/Bound/Base.lean; `Fact p.Prime`).

Main names:
  `noWrap1K`, `noWrap2K`, `noWrap3K`: if every layer's words are lawful (`hκ`), the setting holds
    (`hS`) and integer cells t meet the segment's field relation over `ZMod p` (`hRF`), then, under
    the other hypotheses of each statement, `Part1`, `Part2`, `Part3` (Inst/Model/FF/Trace.lean)
    hold, at the reference sizes (`Dim.ref`), of every layer of the segment; `noWrap3K` has the
    embedding in the first segment too.

Why: the assembly at a variable prime is Cm/TargetInstFFAll.lean (`part1`, `part2`, `part3`); the
three records of size conditions hold at 2^61 - 1 (`admN_K`, `admP_K`, `admS_K` of
Inst/Model/FF/Scales.lean) and go up with p (Inst/Model/Bound/Base.lean) (three: those that name the
prime, under `hκ`, the last two under `hS` too; a fourth, `NWR.SzR`, names none: `szR_K`, in
`noWrap1K`, `noWrap3K`).

Limits: `hS` is the setting: `Spec.Setting` (Inst/Model/FF/Trace.lean), here as `SettingK`
(Inst/Model/FF/Scales.lean). What the head of that file lists as not said is not said here either.
Terms: lean/GLOSSARY.md.
-/
import Inst.Model.FF.Scales
import Cm.TargetInstFFAll

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.TI.FFSeg

open Inst.Model Inst.Model.FFSeg

variable {p : ℕ} [Big p] [Fact p.Prime] {κ : ℕ → LayerScale}
  {nf : NormPar} (hκ : ∀ l, LawfulW (κ l))
include hκ

/-- From the field relation to the program, 1. -/
theorem noWrap1K {tb : Tables} {W : Mat} {L0 : ℕ} {tok : ℕ → ℕ} {first : Bool}
    {t : {c : Cell // c.Valid Dim.ref} → ℤ} (hS : SettingK κ nf tb W L0 tok)
    (hRF : (trace (scl := ⟨κ, nf⟩) Dim.ref tb Layout.kRef L0 first (ZMod p)).RF
      tok (fun y c => ((W y c : ℤ) : ZMod p)) t) :
    ∀ l < Dim.ref.nl, Part1 (scl := ⟨κ, nf⟩) Dim.ref tb
      (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 (rd Dim.ref t) l := by
  letI : Scl := ⟨κ, nf⟩
  intro l hl
  exact NWA.part1 ((rf_iff Dim.ref tb L0 first Layout.kRef _ tok W t).1 hRF)
    (AdmN.mono (admN_K hκ) (big_pow p)) (AdmP.mono (admP_K hκ hS) (big_pow p)) (szR_K hκ) hl

/-- From the field relation to the program, 2. -/
theorem noWrap2K {tb : Tables} {W : Mat} {L0 : ℕ} {tok : ℕ → ℕ} {first : Bool}
    {t : {c : Cell // c.Valid Dim.ref} → ℤ} (hS : SettingK κ nf tb W L0 tok)
    (hRF : (trace (scl := ⟨κ, nf⟩) Dim.ref tb Layout.kRef L0 first (ZMod p)).RF
      tok (fun y c => ((W y c : ℤ) : ZMod p)) t)
    (ho : OBound Dim.ref (rd Dim.ref t)) :
    ∀ l < Dim.ref.nl, Part2 (scl := ⟨κ, nf⟩) Dim.ref
      (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) (rd Dim.ref t) l := by
  letI : Scl := ⟨κ, nf⟩
  intro l hl
  exact NWA.part2 ((rf_iff Dim.ref tb L0 first Layout.kRef _ tok W t).1 hRF)
    (AdmN.mono (admN_K hκ) (big_pow p)) (AdmS.mono (admS_K hκ hS) (big_pow p)) ho hl

/-- From the field relation to the program, 3. -/
theorem noWrap3K {tb : Tables} {W : Mat} {L0 : ℕ} {tok : ℕ → ℕ} {first : Bool}
    {t : {c : Cell // c.Valid Dim.ref} → ℤ} (hS : SettingK κ nf tb W L0 tok)
    (hRF : (trace (scl := ⟨κ, nf⟩) Dim.ref tb Layout.kRef L0 first (ZMod p)).RF
      tok (fun y c => ((W y c : ℤ) : ZMod p)) t)
    (hlast : LastBound Dim.ref (rd Dim.ref t)) :
    (∀ l < Dim.ref.nl, Part3 (scl := ⟨κ, nf⟩) Dim.ref tb
      (fun l => Layout.layerOf ppref Layout.kRef W (L0 + l)) L0 (rd Dim.ref t) l) ∧
    (first = true →
      ∀ i < Dim.ref.T, ∀ j < Dim.ref.d, xS Dim.ref (rd Dim.ref t) 0 j i =
        (Layout.weightsOf ppref Layout.kRef W).Emb (tok i) j) := by
  letI : Scl := ⟨κ, nf⟩
  have hR := (rf_iff Dim.ref tb L0 first Layout.kRef _ tok W t).1 hRF
  refine ⟨fun l hl =>
      NWA.part3 hR (AdmN.mono (admN_K hκ) (big_pow p)) (AdmP.mono (admP_K hκ hS) (big_pow p))
        (szR_K hκ) (AdmS.mono (admS_K hκ hS) (big_pow p)) hlast hl,
    ?_⟩
  rintro rfl i hi j hj
  exact NWR.emb_facts hR (Inst.Model.FFSeg.NWA.emb_abs hS.wf) hi hj

end Cm.TI.FFSeg
