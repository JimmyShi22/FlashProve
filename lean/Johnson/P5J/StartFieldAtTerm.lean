-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/StartFieldAtTerm.lean: The field start of `P5J.TablesFitR` (Johnson/P5J/TopTablesR.lean), at
the seated description's own term `P5J.F0T o Zp Np cF`. One theorem and one example that checks its type.

What the field says: wherever the last chain's start accepts, the first chain's last state bears no
failure mark. (By its name one might expect a statement on a table's first border: it is not one.)

  `start_field_at_term`: the field, in its own letters, at start₃ := the term's start₃ read through
    `Except.toOption` and get := the pair as it stands; for every first meaning Mg₁ and every shared
    meaning Mg: `tiedMeaning` lays `unmarked1` over, so neither is read.
  The example at the foot: the theorem is laid into the field start of a `TablesFitR` at these two
    letters, all other letters free: so that it has the field's type is checked by Lean, not by a
    comparison of texts.

The proof is one call of `P5J.start3_no_mark_at_term` (Johnson/P5J/AtTerm.lean).

Limits. It pays this one field of twelve. It has no premise of its own, so it cannot be empty; but it
does not say that the last chain's start ever accepts: where it never does, the field holds idly.
It speaks of `F0T` alone (Johnson/P5J/AtTerm.lean, with that file's own limits). No soundness follows
from it alone. Nothing on hiding.

-/
import Johnson.P5J.AtTerm
import Johnson.P5J.TopTablesR

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)

/-- **`TablesFitR`'s field START at the seated term**, for every first meaning and every shared
meaning. -/
theorem start_field_at_term (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) {W : Type}
    (Mg₁ : VerifiableInference.Desc.First.Meaning (F0T o Zp Np cF).XiPub W)
    (Mg : VerifiableInference.Desc.Shared.MeaningS (F0T o Zp Np cF).S₂
      ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) W) :
    ∀ (p : (F0T o Zp Np cF).XiPub) (s₁ : (F0T o Zp Np cF).S₁) (s₂ : (F0T o Zp Np cF).S₂)
      (s : (F0T o Zp Np cF).S₃),
      (fun p a b => ((F0T o Zp Np cF).start₃ p a b).toOption) p s₁ s₂ = some s →
      (VerifiableInference.Desc.Sound.tiedMeaning
        (fun a : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ =>
          ((a.1, (fun s => s) a.2) : (F0T o Zp Np cF).XiPub × TS)) Mg₁ Mg).unmarked1 (p, s₁) :=
  start3_no_mark_at_term o Zp Np cF

/-- An example that checks the type; it says nothing by itself (its end is its premise): the theorem
is accepted as the field START of `TablesFitR` at the term's start₃ and the plain pair, whatever the other letters. -/
example (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    {C : CK} {D : WholeD} {all : List LeftT} {Y X₁ X₂ Cl W : Type}
    (start₂ : (F0T o Zp Np cF).XiPub → (F0T o Zp Np cF).S₂)
    (T : Three C D all Y ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁)
      (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂)
      (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ × (F0T o Zp Np cF).S₂) × (F0T o Zp Np cF).S₃)
      X₁ X₂ Cl W)
    (Q : Places D all ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁)
      (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂)
      (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ × (F0T o Zp Np cF).S₂) × (F0T o Zp Np cF).S₃) W)
    (N₁ : Numbers) (Mg₁ : VerifiableInference.Desc.First.Meaning (F0T o Zp Np cF).XiPub W)
    (links : List ModelPart) (ps : List Place)
    (R₀ : ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (EAll D all).Str → W → Prop)
    (Ns : NumbersS)
    (Mg : MeaningS (F0T o Zp Np cF).S₂ ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) W)
    (Pm : PromMeaning (F0T o Zp Np cF).S₂)
    (PLm : PromMeaningL (F0T o Zp Np cF).S₂ (F0T o Zp Np cF).S₃
      ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁))
    (split : Bool)
    (Q₂ : ℕ → (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) ×
        (EAll D all).Str →
      (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) × (EAll D all).Str →
      Prop)
    (Rc : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ → Prop)
    (t : TablesFitR start₂ (fun p a b => ((F0T o Zp Np cF).start₃ p a b).toOption) T Q
      (fun a : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ =>
        ((a.1, (fun s => s) a.2) : (F0T o Zp Np cF).XiPub × TS))
      N₁ Mg₁ links ps R₀ Ns Mg Pm PLm split Q₂ Rc) :
    TablesFitR start₂ (fun p a b => ((F0T o Zp Np cF).start₃ p a b).toOption) T Q
      (fun a : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ =>
        ((a.1, (fun s => s) a.2) : (F0T o Zp Np cF).XiPub × TS))
      N₁ Mg₁ links ps R₀ Ns Mg Pm PLm split Q₂ Rc :=
  { t with START := start_field_at_term o Zp Np cF Mg₁ Mg }

end P5J

#print axioms P5J.start_field_at_term
