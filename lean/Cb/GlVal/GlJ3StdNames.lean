-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3StdNames.lean: small test instances of oracle messages over a
Reed-Solomon code of length 8, read at the radius 3, with the facts on them that other test files
cite.




Definitions and restatements. A guard against empty theorems; no parameter of a protocol.
The analogue, in namespace `Cb.GlJ3`, of the part of Cb/GlVal/GlToyStdNames.lean that depends on the
radius: `toyStd74`, `ld_toy74`, `toyStd74_ok`; and of `mW`, `mU`, `mO`, `n84` of
Cb/GlVal/GlToyReqEnd.lean. UNCHANGED, and taken from Cb.Gl: P5, P74, toyLd74, toyPlace, toyPlace74,
finNS_toy74(x). The digits in the names are those of the toys over the field with 101 elements; they
say nothing about this code (eight points, dimension 4, distance 5, hides 3).

Main names: `ld_toy74 R`: laws; distance 5 (Cb/GlVal/GlToyStdNames.lean keeps the bound 4); [the
  radius is not within half the distance]; lists of at most `LJ3`; at most `bJ3` exceptional values
  (the count of the statement on codes, a true count here with nothing assumed: head of
  Cb/GlVal/GlJ3Base.lean); zero knowledge at 3 positions; transparent.
  `toyStd74 Dt μ plc`: the standard oracle message (`StdM E P74`, Cb/Obj/LdObjectToyKit.lean) at the
    radius 3.
  `toyStd74_ok`, if `plc` is injective: `M.OK LJ3 3` (M = `toyStd74 Dt μ plc`), distance 5,
    transparent. `toyStd74_john`, if `plc` is injective: `M.John 5 eJ3 3`
    (Cb/Ld/LdGroupJohnPack.lean). `toyStd74_smp`, if `plc` is injective: its sample is a zero-evader
    (`M.om.Z.OK`).

Limits: this file says nothing on real parameters, nor on the size of errors.
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyStdNames
import Cb.GlVal.GlToyReqEnd
import Cb.Ld.LdGroupJohnPack
import Cb.GlVal.GlJ3Send
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Code Prob Blocks Iop Hiop Cb.Ood Cb.Gl Cb.Gl.Wf8J

/-- The pad's coefficient. -/
abbrev bnVal : Bn → E := Bq.val
theorem bnVal_inj : Function.Injective bnVal := Bq.val_inj
theorem bnVal_ne (β : Bn) : bnVal β ≠ 0 := Bq.val_ne β

/-- The standard oracle message, radius 3. -/
@[reducible] def toyStd74
    (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ] [DecidableEq μ] (plc : Dt → μ → Bool) :
    StdM E P74 where
  Cm := toyLd84 (Dt ⊕ Unit)
  Dt := Dt
  place := toyPlace84 (Dt ⊕ Unit)
  μ := μ
  plc := plc
  B := Bn
  b := bnVal
  e := eJ3

/-- In the shape of `ld_toy74` of Cb/GlVal/GlToyStdNames.lean. -/
theorem ld_toy74 (R : Type) [Fintype R] [DecidableEq R] :
    (toyLd74 R).Laws ∧ (toyLd74 R).Dist 5 ∧ ¬ 2 * eJ3 < 5 ∧ (toyLd74 R).ListAt eJ3 LJ3 ∧
    (toyLd74 R).MCAat eJ3 bJ3 ∧ True ∧ (toyLd74 R).Zk 3 ∧ (toyLd74 R).Transparent ∧ True := by
  obtain ⟨-, hL, hD, hT, -, hZ, -, -, -⟩ := gl_toy84 R
  exact ⟨hL, hD, by decide, listJ3 _ hL hD, mcaJ3 _ hL, trivial, hZ, hT, trivial⟩

theorem toyStd74_ok (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ] [DecidableEq μ]
    (plc : Dt → μ → Bool) (hp : Function.Injective plc) :
    (toyStd74 Dt μ plc).OK LJ3 3 ∧
    (toyStd74 Dt μ plc).Cm.Dist 5 ∧
    (toyStd74 Dt μ plc).Cm.Transparent := by
  obtain ⟨hL, hD, -, hl, -, -, hz, ht, -⟩ := ld_toy74 (Dt ⊕ Unit)
  exact ⟨⟨hL, hl, hz, hp, bnVal_inj, bnVal_ne⟩, hD, ht⟩

/-- What is asked of a new message below the Johnson radius, if `plc` is injective (`hp`): nothing
assumed. -/
theorem toyStd74_john (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ] [DecidableEq μ]
    (plc : Dt → μ → Bool) (hp : Function.Injective plc) :
    (toyStd74 Dt μ plc).John 5 eJ3 3 :=
  have h := toyStd74_ok Dt μ plc hp
  ⟨rfl, h.1.laws, h.2.1, h.1.zk, h.1.plc, h.1.inj, h.1.ne0⟩

/-- The sample of a standard oracle message in order (`h`) is a zero-evader on all vectors: the pad
lies in the field of the message. -/
theorem stdM_smpJ3 {K P : Type} [Fintype P] [Field K] [Fintype K] (M : StdM K P)
    {L t : ℕ} (h : M.OK L t) : M.om.Z.OK := fun v hv =>
  ood_okOn_comap K (M.Dt ⊕ Unit) M.Cm.J M.Z₀ M.place.symm (PadInF K)
    (ood_okOn_pad K K M.μ M.Dt Unit M.B _ _ _ h.plc h.inj std_padBasis.1) v (fun _ => ⟨_, rfl⟩) hv

theorem toyStd74_smp (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ] [DecidableEq μ]
    (plc : Dt → μ → Bool) (hp : Function.Injective plc) : (toyStd74 Dt μ plc).om.Z.OK :=
  stdM_smpJ3 _ (toyStd74_ok Dt μ plc hp).1

/-- The three standard oracle messages of the test that follows. -/
@[reducible] def mW (Mo : ToyMo8) : StdM E P84 :=
  toyStd74 ((Fin (toyCf8 Mo).X.v ⊕ Fin 0) → Bool) (Fin (toyCf8 Mo).X.v ⊕ Fin 0) id
@[reducible] def mU : StdM E P84 := toyStd74 (Fin C8.k) (Fin 2) plcK8
@[reducible] def mO : StdM E P84 := toyStd74 Unit Empty fun _ e => e.elim

/-- The test's families, at the radius 3. -/
@[reducible] def n84 (Mo : ToyMo8) : ReToy.Ln Mo where
  l := 0
  py := fun _ i => i.elim0
  e' := eJ3
  t := 1
  NW := Sig.one (mW Mo).om
  SdW := Sig.Seeds.indep _
  iW := ()
  lW := fun c => (mW Mo).place (Sum.inl c)
  NU := Sig.one mU.om
  SdU := Sig.Seeds.indep _
  iU := ()
  lU := fun k => mU.place (Sum.inl k)
  NO := Sig.one mO.om
  SdO := Sig.Seeds.indep _
  iO := ()
  lO := fun y => mO.place (Sum.inl y)

end Cb.GlJ3
