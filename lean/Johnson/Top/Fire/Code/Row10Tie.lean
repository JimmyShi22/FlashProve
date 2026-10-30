-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row10Tie.lean: THE TRACER ON ROW 1.0: Left10's FIELD tieS FROM SealReads (Johnson/Desc/Key/KeySealTie.lean), BY ITS ADAPTOR sealed_gives_lift: HERE THAT ADAPTOR's PREMISE MEETS THE SENDING KIND's FILES' OWN «Sealed» (Johnson/Desc/K1/Law/GoodSend3.lean:115) AT LEAN.
OBJECT: hasSmp ∧ NoColl at a seat (j, t) of a table's reading G · USER: Left10.tieS · LETTERS: all: general in F G Fr; cs s e; the reader fOf of the word; stOf | oOf: the statement and the message's number off the record.
  tie_of_sealReads   PROVED: SealReads at Lst y := (portOmZ cs s e).InList (fOf y) · ev := (portOmZ cs s e).Z.val · seedIs a ρ v := ∃ y₀, SeedIs cs s (stOf a) (oOf a) ρ y₀ ∧ v = fun _ => y₀ ⟹ (Sealed cs s e (fOf y) (stOf a) (oOf a) → hasSmp ∧ NoColl)
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.GoodSend3
import Johnson.Desc.Key.KeySealTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.K1 (Sealed SeedIs)
open Johnson.Pack (portOmZ)

theorem tie_of_sealReads {XI A Cells M Smp Rec Y' : Type} (F : FileDescription XI) (G : Reading A Cells M Smp Rec) (str : Y' → Strs)
    (cs : Codes) (s : OracleShape) (e : ℕ) (fOf : Y' → (portOmZ cs s e).Str) (stOf : A → Statement) (oOf : A → ℕ) (j t : ℕ)
    (H : SealReads F G str (fun y => (portOmZ cs s e).InList (fOf y)) (portOmZ cs s e).Z.val
      (fun a ρ v => ∃ y₀, SeedIs cs s (stOf a) (oOf a) ρ y₀ ∧ v = fun _ => y₀) j t)
    (a : A) (y : Y') (h : Sealed cs s e (fOf y) (stOf a) (oOf a)) :
    hasSmp G j t a = true ∧ NoColl F G j t a (str y) :=
  sealed_gives_lift F G str (fun y => (portOmZ cs s e).InList (fOf y)) (portOmZ cs s e).Z.val (fun y₀ _ => y₀)
    (fun a ρ y₀ => SeedIs cs s (stOf a) (oOf a) ρ y₀) j t H a y h

end LPFD

#print axioms LPFD.tie_of_sealReads
