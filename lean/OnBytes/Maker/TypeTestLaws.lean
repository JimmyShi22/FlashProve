-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypeTestLaws.lean: the typing of a whole file returns exactly where the test
`typeReturns` (OnBytes/Maker/TypeTest.lean) says yes.

Main theorem. `typeFile_isSome`: `(typeFile ..).isSome = typeReturns ..`, whatever the silent
rounds' plain parts, the binding leaf's salt and siblings, the test on the silent rounds and the
decision are.


-/
import OnBytes.Maker.TypeFile
import OnBytes.Maker.TypeTest

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ

theorem typeFile_isSome {TF TJ T3 Xi : Type} (C : CK) (a : ℕ) (W : Three.Whole) (tF : TF) (tJ : TJ)
    (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
    (saltBytes : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead) :
    (typeFile C a W tF tJ t3 silent run saltBytes cfg pF pJ p3 salt path r).isSome =
      typeReturns C a W saltBytes cfg r := by
  unfold typeFile typeReturns toBPrfW
  cases tabsWFull W saltBytes r <;> cases extWFull a cfg W r <;> cases r.first.out.run <;>
    cases plainsT C (WholeD.of a W).ds₁ r.first.out.rounds.toList.dropLast <;>
    cases plainsT C (WholeD.of a W).ds₂ r.shared.out.rounds.toList <;>
    cases plainsT C (WholeD.of a W).ds₃ r.second.out.rounds.toList <;> rfl

end OnBytes.Maker
