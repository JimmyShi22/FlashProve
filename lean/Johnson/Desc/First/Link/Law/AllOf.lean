-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/AllOf.lean: THE CLAUSE `all` OF `FrontFitsAt` (CarryAtFull.lean: the
code switch's front's reading answers at every position) FROM THE BUNDLE's OTHER CLAUSES, `Opens`
(FrontAnswers.lean) AND TWO COUNTS; AND THE CLAUSE `firstZ` AT THE PROGRAM's OWN LAYOUT. Theorems.
It changes no other file.

  `colFits_of`: R.Good · LaysFit R L ix · the first mask rows are R.oZ ⊢ each member a, with R.nM a
    main and R.nZ a mask symbols, fits tables of 2 ^ (h + g) and 2 ^ h rows (`ColFits`).
  `all_of`: **R.Good · LaysFit · firstZ · two masks · the layout's exponents · the layout's member
    number ix a is the message no a · the front's statement has the written shape at no a · Opens ·
    the kept members' main rows add up to rows.keptRows · the fresh mask's shape has 2 ^ h mask rows
    ⊢ ∀ q, ∃ seg, K2.longFront p t fx orc q = some seg.**
  `firstZ_at`: AgreesWith lo kb L (Johnson/Desc/First/Close/Law/Drawn/Def.lean) ⊢ the clause firstZ
    at groupLayK cs lo s e kb hM hZ and ix a := posOf lo a.1: its fourth clause as it stands.
Limits. `Opens` and the two counts are premises. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.FrontAnswers
import Johnson.Desc.First.Link.Law.MainTable
import Johnson.Desc.First.Close.Law.CubeOfShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params Cb Johnson.Top.H Johnson.Pack Johnson.G
open VerifiableInference.Desc.First.Close (groupLayK layAt sizesM sizesZ AgreesWith posOf)

/-- Each member fits the layout's tables. -/
theorem colFits_of {S : Sig GE} (R : RowsK S) (hg : R.Good) {L : GroupLayout} {ix : R.G.A → ℕ}
    (Ft : LaysFit R L ix)
    (hf : ∀ a, R.nZ a ≠ 0 → L.maskFirst.getD (ix a) none = some (R.oZ a)) (a : R.G.A) :
    ColFits L (ix a) (R.nM a) (R.nZ a) (2 ^ (R.s.h + R.s.g)) (2 ^ R.s.h) := by
  refine ⟨?_, ?_⟩
  · by_cases h0 : R.nZ a = 0
    · exact Or.inl h0
    · refine Or.inr ⟨R.oZ a, hf a h0, ?_⟩
      have h1 := hg.fitZ ⟨a, ⟨R.nZ a - 1, by omega⟩⟩
      have h2 : R.oZ a + (R.nZ a - 1) < 2 ^ R.s.h := h1
      omega
  · by_cases hk : L.kept.getD (ix a) false = true
    · exact Or.inl hk
    · have hk' : L.kept.getD (ix a) false = false := by simpa using hk
      by_cases h0 : R.nM a = 0
      · exact Or.inr (Or.inl h0)
      · refine Or.inr (Or.inr ⟨R.oM a, Ft.first a hk', ?_⟩)
        have h1 := hg.fitM ⟨a, ⟨R.nM a - 1, by omega⟩⟩ (Ft.free a hk' _)
        have h2 : R.oM a + (R.nM a - 1) < 2 ^ (R.s.h + R.s.g) := h1
        omega

/-- **THE CLAUSE all.** -/
theorem all_of {S : Sig GE} (R : RowsK S) (hg : R.Good) {p : First.K2.P2} {t : First.S}
    {fx : _root_.Tw.K2.Front} {B : TreeBook} {ix no : R.G.A → ℕ}
    (Ft : LaysFit R fx.f.rows.layout ix)
    (hf : ∀ a, R.nZ a ≠ 0 → fx.f.rows.layout.maskFirst.getD (ix a) none = some (R.oZ a))
    (hm : fx.f.rows.masks = 2) (hk : fx.f.rows.layout.k = R.s.h + R.s.g)
    (hh : fx.f.rows.layout.h = R.s.h)
    (hno : ∀ a, fx.f.rows.layout.members[ix a]? = some (no a))
    (hsh : ∀ a, ∃ xo, (First.K2.skelOf fx).oracles[no a]? = some xo ∧
      xo.shape.mainRows = R.nM a ∧ xo.shape.maskRows = R.nZ a)
    (O : Opens p t fx B) (orc : ℕ → ℕ → List UInt64)
    (hkc : keptCount fx.f.rows.layout
      (fun w => ((First.K2.skelOf fx).oracles.getD (fx.f.rows.layout.members.getD w 0)
        default).shape.mainRows) (List.range fx.f.rows.layout.members.size) = fx.f.rows.keptRows)
    (hfr : ((First.K2.skelOf fx).oracles.getD fx.f.rows.fresh default).shape.maskRows =
      2 ^ R.s.h) (q : ℕ) :
    ∃ seg, First.K2.longFront p t fx orc q = some seg := by
  refine front_answers O orc hm (fun w hw => ?_) hkc (by rw [hh]; exact hfr) q
  obtain ⟨a, rfl⟩ := Ft.onto w hw
  obtain ⟨xo, h1, h2, h3⟩ := hsh a
  have e0 := hno a
  rw [Array.getElem?_eq_getElem hw] at e0
  have eg : (First.K2.skelOf fx).oracles.getD fx.f.rows.layout.members[ix a] default = xo := by
    rw [Option.some.inj e0, Array.getD_eq_getD_getElem?, h1]
    rfl
  rw [eg, h2, h3, hk, hh]
  exact colFits_of R hg Ft hf a

/-- **THE CLAUSE firstZ AT THE PROGRAM's OWN LAYOUT.** -/
theorem firstZ_at (cs : Codes) (lo : List (OracleShape × ℕ)) (s : Sg) (e : ℕ)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
    {L : GroupLayout} (hA : AgreesWith lo kb L) (a : (groupLayK cs lo s e kb hM hZ).G.A)
    (h : (groupLayK cs lo s e kb hM hZ).nZ a ≠ 0) :
    L.maskFirst.getD (posOf lo a.1) none = some ((groupLayK cs lo s e kb hM hZ).oZ a) :=
  hA.2.2.2 a.1 a.2 h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.colFits_of
#print axioms VerifiableInference.Desc.LinkJoin.all_of
#print axioms VerifiableInference.Desc.LinkJoin.firstZ_at
