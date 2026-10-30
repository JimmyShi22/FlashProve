-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/FinReply.lean: THE PLAIN
ROAD'S PREMISE finReply, AT A DESCRIPTION WHOSE LAST TEST CALLS `S.finAsked`. One definition, one
theorem. A rule: no description of the protocol is laid in.

What is said. `repHeard getS`: the reader of the reply that was heard, off the first chain's record:
THROUGH THE ONE READING `S.heard` (`S.heardTok?`, Johnson/Desc/First/HeardAsked.lean), as a token of
the model where it is below the vocabulary's size.


`finReply_of_finAsked`: at a description F over any type of instances, laid on the requests along
instP (`FileDescription.pull`): IF the last test's yes gives `finAsked`'s at what the instance asks (hfin:
by the last test's own text) AND what instP's instance asks is the request's own reply, laid as an
element (hask: an equation on the map of instances), THEN the last test's yes gives: the reply heard
is the request's own: TopPlain.lean's finReply at repS := repHeard getS (TieAt.lean calls it so).

Silly members. A last test that never says yes meets hfin for nothing, and the conclusion is idle. A
last test that says yes to all fails hfin at a record that holds no reply.

Limits: hfin and hask are premises. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block
import Johnson.Desc.First.HeardAsked
import Johnson.Flat.TiesAtReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J

open Inst.Model
open OnBytes OnBytes.Flat
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.OnPublicFiles.Flat (Req)

/-- **The reader of the reply that was heard**, as a token of the model. -/
def repHeard {P S₁ : Type} (getS : S₁ → VerifiableInference.Desc.First.S) (a : P × S₁) :
    Option (Fin ppref.V) :=
  (getS a.2).heardTok?.bind fun n => if h : n < ppref.V then some ⟨n, h⟩ else none

/-- **The last test's yes: the reply heard is the request's own.** -/
theorem finReply_of_finAsked {Xi Rec : Type} (F : FileDescription Xi)
    (getS : F.S₁ → VerifiableInference.Desc.First.S) (asked : Xi → E) (instP : Req × Rec → Xi)
    (hfin : ∀ ξ s₁ s₂ s₃, F.fin ξ s₁ s₂ s₃ = true → (getS s₁).finAsked (asked ξ) = true)
    (hask : ∀ x rec, asked (instP (x, rec)) = OnBytes.Model.ofNat (dropReq x).val)
    (x : Req) (rec : Rec) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
    (h : (F.pull instP).fin (x, rec) s₁ s₂ s₃ = true) :
    repHeard getS ((F.pull instP).pub (x, rec), s₁) = some (dropReq x) := by
  have h1 : (getS s₁).finAsked (OnBytes.Model.ofNat (dropReq x).val) = true := by
    rw [← hask x rec]
    exact hfin _ s₁ s₂ s₃ h
  have hV : (dropReq x).val < pW.toNat :=
    Nat.lt_of_lt_of_le (dropReq x).isLt (by decide)
  have h2 := VerifiableInference.Desc.First.S.finAsked_heardTok _ hV _ h1
  show ((getS s₁).heardTok?.bind fun n =>
    if h : n < ppref.V then some (⟨n, h⟩ : Fin ppref.V) else none) = some (dropReq x)
  rw [h2]
  show (if h : (dropReq x).val < ppref.V then some (⟨(dropReq x).val, h⟩ : Fin ppref.V) else none) =
    some (dropReq x)
  rw [dif_pos (dropReq x).isLt]

#print axioms finReply_of_finAsked

end P5J
