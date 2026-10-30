-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectWfRows.lean: assembly of the holographic IOP from its sub-protocols: under `EntAt`,
what weights-formedness leaves beside the tensor row is a finite family of rows on named places; so
"the rest" of the offline plan reduces to conditions on places, the test's own hypotheses and
inequalities.

Definitions and statements; the proofs are in Cb/Obj/LdObjectWfRowsProofs.lean. By instantiation
only.
A form (`Slf E St J`, Cb/Ld/LdRel.lean) is a linear form on vectors with coordinates J whose
coefficients depend on a state; a row is a form with a target, and holds of a vector if the form's
value there is the target.
`W : LdOWf F E` is the data of preamble and test; `W.O` is the data of the test for linear
constraints, read off the preamble's last claims (Cb/Obj/LdObjectWf.lean), and `W.O.toC` the same
test over a signature (Cb/Obj/LdObjectLinFull.lean). The rows are those that the lookups filed
(Cb/Ld/LdWf.lean), with their public supports `gR`; every use reads a filed row cut to its support.
`nAt n` is the place of the named entry n among the entries of the messages. `W.P.EntAt nAt`
(Cb/Ld/LdWfMasksBatt.lean): the named entries are entries of the messages, at different places.
Filed rows on named places: Cb/Ld/LdLinClosePlanRowsAt.lean. The rest of the plan, with one group:
Cb/Ld/LdLinClosePlanOne.lean.

Main names:
  `W.RN r`: the names of the places of the row r: the named entries in its public support `gR`: a
    type that does not depend on the state.
  `W.rowsA nAt`, `W.tgA`: the filed rows as forms with the state "claim" on all entries of the
    preamble's messages; their targets.
  `Spec.ldOWfRows_more`: under `EntAt`, `W.O.more cl m`, "the rows that ride along hold", is "all
    rows `W.rowsA` hold".
  `Spec.ldOWfRows_ab`: so, under `EntAt`, the base joint of what the preamble left (`W.O.toC.Ab`)
    says, in the exact and in the relaxed form, exactly that.
  `Spec.ldOWfRows_read`: a filed row has a non-zero coefficient only at the place of a named entry
    of its support: at every state.
  `Spec.ldOWfRows_three`: the three clauses of "the rest" at the object, with one group: for a plan
    p without a splitting (`LdLinPl`, Cb/Ld/LdLinClosePlan.lean) and one test X that takes all rows
    and keeps nothing, and a fixed value w₀: of the closing `X.one W.tgA w₀` (the test X, then
    nothing): `p.SaysA`; the closing is a closing (`LdTc.OK`); at most `X.t` long positions of each
    oracle message left. Asked: `EntAt`; a condition on places: the oracle message of every
    named entry in some row's support is kept at the plan's two bridges (`p.kp₁`, `p.kp₂`); the
    test's own hypotheses (`X.run.OK`).

Limits: the state of a row is its vector of coefficients on its support, free data of the claim; the
form lays it on the places. That is a wider family of statements than this protocol's technical
report (lean/CREDITS.md) has, under the same notion (a form of the configuration at a state): a
theorem for all coefficients inside the support covers its rows. That the report's forms are
succinct (the verifier evaluates them from points and challenges) is not rendered: it is a matter of
running time.
This file says nothing on several groups for the filed rows, on "restG is rest" for the tensor row's
mask part, or on the online side. It does not say that the conditions can be met together at a
concrete preamble.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectWf
import Cb.Ld.LdWfMasksBatt
import Cb.Obj.LdObjectLinFull
import Cb.Ld.LdLinClosePlanRowsAt
import Cb.Ld.LdLinClosePlanOneProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp

namespace LdOWf
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (W : LdOWf F E)

/-- the names of the filed rows -/
abbrev RB : Type := Σ f : Fin (W.P.n + 1), Fin (W.P.nR f.1)

/-- the names of the places of a row: the named entries in its public support -/
abbrev RN (r : W.RB) : Type := {n : W.P.N // W.P.gR r.1.1 r.2 n}

open Classical in
instance (r : W.RB) : Fintype (W.RN r) := Subtype.fintype _

/-- the places -/
def rPl (nAt : W.P.N → W.P.S.Ent) : ∀ r, W.RN r → W.P.S.Ent := fun _ n => nAt n.1

/-- the row filed in the claim, pulled to its places -/
def rRow : W.P.Cl → ∀ r, Row E (W.RN r) := fun cl r =>
  ⟨fun n => ((W.P.stOf cl).2.2 r.1.1 r.2).cf n.1, ((W.P.stOf cl).2.2 r.1.1 r.2).tg⟩

/-- The filed rows as forms on all entries; their targets. -/
def rowsA (nAt : W.P.N → W.P.S.Ent) : W.RB → Slf E W.P.Cl W.P.S.Ent :=
  rowsAt (W.rPl nAt) W.rRow
def tgA : W.P.Cl → W.RB → E := tgAt W.rRow

end LdOWf

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- States: under `EntAt`, "the rows that ride along hold" is "all rows hold". -/
def ldOWfRows_more : Prop :=
  ∀ (W : LdOWf F E) (nAt : W.P.N → W.P.S.Ent), W.P.EntAt nAt →
    ∀ (cl : W.P.Cl) (m : W.P.S.Msg), W.O.more cl m ↔ rowsHold (W.rowsA nAt) W.tgA cl (W.P.S.ents m)

def ldOWfRows_ab : Prop :=
  ∀ (W : LdOWf F E) (nAt : W.P.N → W.P.S.Ent), W.P.EntAt nAt →
    (∀ sa y m wp,
      W.O.toC.Ab.rel sa y (m, wp) ↔ rowsHold (W.rowsA nAt) W.tgA sa (W.O.toC.Sa.ents m)) ∧
    ∀ sa y m wp,
      W.O.toC.Ab.relR (sa, y) (m, wp) ↔ rowsHold (W.rowsA nAt) W.tgA sa (W.O.toC.Sa.ents m)

/-- A filed row is non-zero only at the place of a named entry of its support. -/
def ldOWfRows_read : Prop :=
  ∀ (W : LdOWf F E) (nAt : W.P.N → W.P.S.Ent) (r : W.RB) (cl : W.P.Cl) (e : W.P.S.Ent),
    W.rowsA nAt r cl e ≠ 0 → ∃ n, W.P.gR r.1.1 r.2 n ∧ nAt n = e

/-- The three clauses of "the rest" at the object, with one group. -/
def ldOWfRows_three : Prop :=
  ∀ (W : LdOWf F E) (nAt : W.P.N → W.P.S.Ent) (p : LdLinPl W.O.toC)
      (X : LdRowsD p.S₂ W.O.toC.E₀ W.O.toC.Wpa (p.rowsL (W.rowsA nAt)))
      (w₀ : (p.S₂.sub X.kp).Wit × W.O.toC.Wpa),
    W.P.EntAt nAt → (∀ b, X.now b) → (∀ o, ¬ X.kp o) →
    (∀ (r : W.RB) n,
      W.P.gR r.1.1 r.2 n → ∃ h : p.kp₁ (.inl (.inl (.inl (nAt n).1))), p.kp₂ ⟨_, h⟩) →
    X.run.OK →
    p.SaysA (X.one W.tgA w₀).Q.base (X.one W.tgA w₀).fx ∧
    (X.one W.tgA w₀).Q.OK ∧
    ∀ V,
      (X.one W.tgA w₀).Q.q V → p.S₂.qFam (fun U : Finset W.O.toC.E₀.Pos => U = ∅) (fun _ => X.t) V

end
end Spec
end Cb
