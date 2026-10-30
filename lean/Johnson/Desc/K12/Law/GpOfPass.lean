-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/GpOfPass.lean: the plain data of the group under test hang on no round of the
proximity test.

`gpOf` (Johnson/Desc/K12/Law/FirstOk.lean) reads of the record behind the batching the statement,
the book, the roots and the mask, not what passes; and the statement behind the batching and the
layout hang on the record in front alone (`bat_front`, Johnson/Desc/K12/Law/TopF.lean). So the plain
data D, and with them the typed group, its public data and the word `yOf`, are one at every element
that the round "BAT" draws. Statements and proofs.
Main names:
  `gpOf_pass`: `gpOf` at a record does not hang on what passes.
  `front_one`: two returns of the batching at one record in front, on any two rounds and entries,
    give one layout, one statement behind and one D.
  `yOf_row`: the word `yOf` does not hang on the row; the row stands in a proof alone.
Limits: No soundness is claimed. Nothing here is about hiding.
-/
import Johnson.Desc.K12.Law.K12Lemma

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First (gpOf gpL Plain)

theorem gpOf_pass (p : P12) (t : T12) (π : Passing) (a : Fmt.M1.Stage) (L : GroupLayout) :
    gpOf p { t with pass := π } a L = gpOf p t a L := rfl

theorem front_one (p : P12) (t0 : T12) (a : Fmt.M1.Stage) (r0 r1 : Fmt.RoundView) (e e' : Fmt.Entry)
    (row row' : GroupRow) (Ly Ly' : GroupLayout) (S' S'' : Statement) (D D' : Plain)
    (h : FrontK p t0 a r0 e row Ly S' D) (h' : FrontK p t0 a r1 e' row' Ly' S'' D') :
    Ly = Ly' ∧ S' = S'' ∧ D = D' := by
  obtain ⟨G0, g1, g2, g3⟩ := bat_front _ _ _ _ _ _ _ h.bat
  obtain ⟨G1, k1, k2, k3⟩ := bat_front _ _ _ _ _ _ _ h'.bat
  obtain rfl := Option.some.inj (g1.symm.trans k1)
  obtain rfl := Option.some.inj (g2.symm.trans k2)
  subst g3
  subst k3
  refine ⟨rfl, rfl, ?_⟩
  have m1 := h.made
  have m2 : gpOf p { t0 with st := begun t0.st t0.g G0, pass := .claim row Ly } a Ly = some D' :=
    (gpOf_pass p { t0 with st := begun t0.st t0.g G0, pass := .claim row' Ly } (.claim row Ly) a
      Ly).trans h'.made
  exact Option.some.inj (m1.symm.trans m2)

theorem yOf_row (p : P12) (a : Fmt.M1.Stage) (row row' : GroupRow) (D : Plain)
    (hok : H2K.First.ok (gpL p a row D) = true) (hok' : H2K.First.ok (gpL p a row' D) = true)
    (rd : ℕ → ℕ) (W0 : ℕ → WO) : yOf p a row D hok rd W0 = yOf p a row' D hok' rd W0 := rfl

end H2K.JointK
