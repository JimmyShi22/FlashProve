-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/BatOf/Size.lean: the public data of the round before a test (`Cb.Pv.Bat.Size`, Cb/Pv/Bat.lean)
made over a given signature, and the group's data made member by member, so that they can be given
for signatures that are sums.

Definitions, statements and proofs. `Bat.Size` holds its own signature S with a group over S (`Grp
S`, Cb/Ld/LdBatSig.lean). Where a protocol's signature grows by sendings (`Sig.sum`,
Cb/Ld/LdSigSum.lean), whoever lays a round before a test behind a sending needs a size whose
signature is that sum by definition.

Main names:
  `GrpD P S`: a group's data over S at the common long positions P: which messages are members, and
    where a member is read.
  `GrpD.none`: no member. `GrpD.sum G H`: over `S.sum N`: the members of G and those of H.
  `GrpD.toGrp G e`: the group, at the joint radius e.
  `fits_none`, `fits_sum`: the law that the joint radius implies each member's own (`Grp.Fits`) goes
    member by member.
  `batSizeOf S G e keep B Sb sl Z L`: the size. `batSizeOf_S`: its signature is S, by definition.
    `batSizeOf_kp`: a message is kept if and only if it is no member or is marked.

Limits: data and one law. The rows sl and the coefficients Z are typed over the group of the whole
signature and are arguments. The bound on the lists of the group's code is not treated: it is a law
of all members together.
-/
import Cb.Pv.Bat
import Cb.Ld.LdSigSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.BatOf
open Cb

variable {E : Type}

/-- A group's data over S, at the common long positions P. -/
structure GrpD (P : Type) (S : Sig E) where
  /-- the members -/
  mem : S.O → Bool
  /-- where a member is read for a common long position -/
  pos : ∀ a : {o // mem o = true}, P → (S.om a.1).P

namespace GrpD
variable {P : Type} {S N : Sig E}

/-- No member. -/
def none : GrpD P S := ⟨fun _ => false, fun a => absurd a.2 Bool.false_ne_true⟩

/-- The members of G and those of H. -/
def sum (G : GrpD P S) (H : GrpD P N) : GrpD P (S.sum N) where
  mem := Sum.elim G.mem H.mem
  pos := fun a => match a with
    | ⟨.inl o, h⟩ => G.pos ⟨o, h⟩
    | ⟨.inr o, h⟩ => H.pos ⟨o, h⟩

/-- The group. -/
@[reducible] def toGrp [Fintype P] (G : GrpD P S) (e : ℕ) : Grp S where
  P := P
  mem := fun o => G.mem o = true
  pos := G.pos
  e := e

variable [Field E] [Fintype P]

theorem fits_none (e : ℕ) : ((none : GrpD P S).toGrp e).Fits :=
  fun a => absurd a.2 Bool.false_ne_true

/-- The law goes member by member. -/
theorem fits_sum (G : GrpD P S) (H : GrpD P N) (e : ℕ) (hG : (G.toGrp e).Fits)
    (hH : (H.toGrp e).Fits) : ((G.sum H).toGrp e).Fits := fun a =>
  match a with
  | ⟨.inl o, h⟩ => hG ⟨o, h⟩
  | ⟨.inr o, h⟩ => hH ⟨o, h⟩

end GrpD

variable [Field E] [Fintype E]

/-- The size over a given signature. -/
@[reducible] def batSizeOf (S : Sig E) {P : Type} [Fintype P] (G : GrpD P S) (e : ℕ)
    (keep : S.O → Bool) (B : Type) [Fintype B] (Sb : B → Type)
    (sl : ∀ b, Slf E (Sb b) (G.toGrp e).C.J) (Z : Evader E ((G.toGrp e).Row B)) (L : ℕ) :
    Cb.Pv.Bat.Size E where
  S := S
  G := G.toGrp e
  keep := fun o => keep o = true
  B := B
  Sb := Sb
  sl := sl
  Z := Z
  L := L

section
variable (S : Sig E) {P : Type} [Fintype P] (G : GrpD P S) (e : ℕ) (keep : S.O → Bool) (B : Type)
  [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) (G.toGrp e).C.J)
  (Z : Evader E ((G.toGrp e).Row B)) (L : ℕ)

theorem batSizeOf_S : (batSizeOf S G e keep B Sb sl Z L).S = S := rfl

theorem batSizeOf_kp (o : S.O) :
    (batSizeOf S G e keep B Sb sl Z L).kp o ↔ (¬ G.mem o = true ∨ keep o = true) := Iff.rfl

end

end Cb.Pv.BatOf

#print axioms Cb.Pv.BatOf.GrpD.fits_sum
#print axioms Cb.Pv.BatOf.batSizeOf_S
#print axioms Cb.Pv.BatOf.batSizeOf_kp
