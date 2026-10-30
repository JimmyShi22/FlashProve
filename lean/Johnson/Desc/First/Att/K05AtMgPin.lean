-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05AtMgPin.lean: KIND K5: K5AtMg's field pinOk (Johnson/Desc/First/Att/K05AtMg.lean) AT THE FILLED PIN I := k5Pin … (Johnson/Desc/First/Att/K05LawPin.lean): it holds outright: that
pin's side condition is True. So whoever proves K5AtMg at the filled pin owes eight fields. One theorem: `pinOk_at_pin`. What falls moves: the pin's weight lies in the field behind (its item "pinned").
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05AtMg
import Johnson.Desc.First.Att.K05LawPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent sigListCalls)

theorem pinOk_at_pin {Xi Cells Tok Pp : Type} (Gd : FileDescription Xi) (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
    (rad : OracleShape → Nat) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
    (smp : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((Johnson.Pack.sigOf D.codes (sigListCalls D rad x.link)).om i).Smp)
    (arr : ℕ → ℕ → ℕ) (Fr : Frame) (base : ℕ) (hlow : ∀ i, (seat i).1 < base) (N : Numbers)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (links : List ModelPart) (pl : Place) (O : List Item) (Q : List Pub) :
    ∀ π : Pp, ∀ a', onT N Mg links π Fr pl O Q a' →
      (k5Pin (Cells := Cells) (Tok := Tok) Gd x D rad seat smp arr Fr base hlow).ok
        ((k5Pin (Cells := Cells) (Tok := Tok) Gd x D rad seat smp arr Fr base hlow).rc a'.1) a'.2 :=
  fun _ _ _ => trivial

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.pinOk_at_pin
