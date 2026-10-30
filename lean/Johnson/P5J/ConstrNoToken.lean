-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ConstrNoToken.lean: AT A SEGMENT THAT IS NOT THE OUTPUT HEAD's, THE MEANT SENTENCE "this
part of the segment's relaxed relation holds of the witness" DOES NOT TURN WITH THE WITNESS's TOKEN.
Three theorems.

Why. The sentence (`constrQAt`, Johnson/P5J/MeansQ.lean) is spelt, at a layers' segment, at the
request WITH THE WITNESS's TOKEN PUT IN (`put (H.req a) (H.hid w).tok`), and the table of joints
books the token among what the layers' identities and rider read (`Item.reads`,
Johnson/Desc/First/Borders.lean). A reader asked which token these sentences hold: they stand long
before the place at which the reply's token is named. They hold none: of the request they read the
prompt's tokens alone (`Cm.Seg.tokX`), which `putReq` leaves (`tokX_putReq`,
Johnson/Goal/Meaning/RowLocal.lean). The booking tells more than the sentence reads, which is safe.

What is said. `partG_tokens`: a group of layers' part reads of the request its prompt's tokens
alone. `partG_putReq`: so it is the same at the request with any token put in and at the request
itself. `constrQAt_noToken`: at put := `putReq`, a segment k that is not the head's and a part that
is not the digits': of two witnesses whose hidden data part in the token alone (the same lists `MG`,
`MA`; the same `base`), the sentence holds of the one if it holds of the other.

Limits. At the head's segment and at the digits' part the sentence is another author's letter:
nothing is said of it here. Nothing on soundness, nothing on when a challenge is drawn.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.MeansQ
import Johnson.Goal.Meaning.RowLocal

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Flat (putReq)
open VerifiableInference.OnPublicFiles.Flat (Holds GE Req)
open VerifiableInference.Desc (Strs)
open Meaning

variable {X : Model.Verify.Public} {P W : Type} {rows cols : ℕ}

/-- A group of layers' part reads of the request its prompt's tokens alone. -/
theorem partG_tokens {i : Cm.Idx} {x x' : Instance ppref} (h : Cm.Seg.tokX x = Cm.Seg.tokX x')
    (MG : ℕ → Mats ℤ) (g : ℕ) (p : TPart) (k : partG X i x MG g p) : partG X i x' MG g p := by
  cases p with
  | idn =>
    unfold partG NormField EmbField at k ⊢
    rw [← h]
    exact k
  | rider =>
    unfold partG HotField at k ⊢
    rw [← h]
    exact k
  | _ => exact k

/-- It is the same at the request with any token put in and at the request itself. -/
theorem partG_putReq {i : Cm.Idx} (q : Req) (t : Fin ppref.V) (MG : ℕ → Mats ℤ) (g : ℕ)
    (p : TPart) : partG X i (putReq q t).val MG g p ↔ partG X i q.val MG g p :=
  ⟨partG_tokens (tokX_putReq q t) MG g p, partG_tokens (tokX_putReq q t).symm MG g p⟩

/-- **Off the head's segment the meant sentence does not turn with the witness's token.** -/
theorem constrQAt_noToken (hd : ℕ) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (k : ℕ) (p : TPart) (hp : p ≠ .lookDigits)
    (hk : k ≠ hd) (a : P × TS) (y : Strs) (w w' : W) (hG : (H.hid w').MG = (H.hid w).MG)
    (hA : (H.hid w').MA = (H.hid w).MA) (hB : H.base k w → H.base k w')
    (h : constrQAt hd putReq H headPart digitsPart k p a y w) :
    constrQAt hd putReq H headPart digitsPart k p a y w' := by
  unfold constrQAt at h ⊢
  rw [if_neg hp] at h ⊢
  refine ⟨fun e => hB (h.1 e), fun M i hM hi => ?_⟩
  have h2 := h.2 M i hM hi
  rw [if_neg hk] at h2 ⊢
  by_cases h0 : k % 2 = 0
  · rw [if_pos h0] at h2 ⊢
    rw [hG]
    exact (partG_putReq _ _ _ _ _).2 ((partG_putReq _ _ _ _ _).1 h2)
  · rw [if_neg h0] at h2 ⊢
    rw [hA]
    exact h2

end P5J

#print axioms P5J.partG_tokens
#print axioms P5J.partG_putReq
#print axioms P5J.constrQAt_noToken
