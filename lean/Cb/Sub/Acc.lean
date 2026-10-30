-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Sub/Acc.lean: a block beside any carried value that the block's output statement updates: the
rule of Cb/Sub/Joint.lean for a ledger, for every kind of ledger.

Definitions, statements and their proofs.
Cb/Sub/Joint.lean seats a block beside a list of claims, to which claims are appended. A sub-proof
may keep more beside a claim (the exponent under which it is batched; an owner's mark), or keep
several lists. This file has the same rule for any type Z of carried values, any update
`upd x' z` read off the block's output statement, any meaning Q and any condition P of a carried
value.

Main names:
  `R.acc upd`: R beside a carried value, updated behind R. Its rounds are R's.
  `acc_knowAt`: from `KnowAt R A B idW ε`; "B's condition gives B₀'s"; "the condition P of the old
    value gives P' of the new"; "B₀ and the meaning Q' of the new value give B and the meaning Q of
    the old": `KnowAt (R.acc upd) (withZ A Q P) (withZ B₀ Q' P') idW ε`, with the same errors.
  `led_eq_acc`: `R.led cl` is `R.acc` at "append `cl x'`".

Limits: nothing on an honest prover. Meaning and condition read the carried value and the witness,
not the statement's other part.
Terms: lean/GLOSSARY.md.
-/
import Cb.Sub.Joint

set_option autoImplicit false

namespace Cb.Sub
open Iop Prob Hiop TWhole IOR

/-- R beside a carried value that is updated behind R. -/
noncomputable def _root_.Iop.IOR.acc {X X' Z : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo)
    (upd : X' → Z → Z) : IOR (X × Z) Ei (X' × Z) Eo :=
  (R.keepX Z).post (fun b => some (b.1, upd b.1 b.2)) (ExtMap.id Eo)

/-- A block beside a carried value. -/
theorem acc_knowAt {K M X X' Z Wp : Type} {Ei Eo : ExtSpec} {R : IOR X Ei X' Eo}
    {A : Rels K X Ei (M × Wp)} {B B₀ : Rels K X' Eo (M × Wp)} {ε : Err R.shape}
    (upd : X' → Z → Z) (Q Q' : Z → M × Wp → Prop) (P P' : Z → Prop) (h : KnowAt R A B idW ε)
    (ho : ∀ b, B.on b → B₀.on b) (hP : ∀ x' z, P z → P' (upd x' z))
    (hB : ∀ x' y z w, B.on (x', y) → P z → B₀.relR (x', y) w → Q' (upd x' z) w →
      B.relR (x', y) w ∧ Q z w) :
    KnowAt (R.acc upd) (withZ A Q P) (withZ B₀ Q' P') idW ε :=
  knowAt_postMap (B := withZ B Q P) (B' := withZ B₀ Q' P') (fun b : X' × Z => (b.1, upd b.1 b.2))
    (keepX_knowAt Q P h)
    (fun x y (hx : B.on (x.1, y) ∧ P x.2) =>
      (⟨ho _ hx.1, hP x.1 x.2 hx.2⟩ : B₀.on (x.1, y) ∧ P' (upd x.1 x.2)))
    fun x y w (hx : B.on (x.1, y) ∧ P x.2) (hw : B₀.relR (x.1, y) w ∧ Q' (upd x.1 x.2) w) =>
      hB x.1 y x.2 w hx.1 hx.2 hw.1 hw.2

/-- The ledger's block is the case "append". -/
theorem led_eq_acc {E J X X' : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo)
    (cl : X' → Ledger E J) : R.led cl = R.acc fun x' L => L ++ cl x' := rfl

end Cb.Sub
