-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/Constr.lean: THE PARTS OF THE SEGMENTS' RELATIONS BEAR A TURN OF PADS, at the
sentence that the composed meaning gives (`constrQAt`, Johnson/P5J/MeansQ.lean). Two definitions,
three theorems. A law file: no sub-protocol imports it.

Why. At a code switch in front of segment m the parts of the relations of the segments from m on
stay
open. The tie asks each at the extractor's value, which turns the pads of the tenants that the group
in front has kept (PadsTurn.lean). The sentence reads the witness through the parameter H (how a
witness is read as what the prover hides) and, at the output head's segment, through the parameter
headPart. (The statement's side stands in another file: `constr_all`,
Johnson/Desc/Sound/ConstrRidesHead.lean.)

What is said.
  `HidBears H T m`: what `constrQAt` reads of the witness at a segment j, m ≤ j, other than the
    output head's, is the same at two witnesses that part in the pads of T alone: the token; "the
    committed symbols are a packing of small integers" at j; the group of layers' arrays (j even);
    the attention's (j odd).
  `hidBears_of_eq`: whoever shows that the whole of what is hidden, and that sentence at every j,
    bear the turn, has it.
  `HeadBears headPart T`: the like for the output head's parts.
  `partG_congr`: a group of layers' part reads that group's arrays alone.
  `constr_bears`: THE WITNESS's SIDE, from the two.

Limits. `HidBears` AND `HeadBears` ARE PREMISES ON PARAMETERS: each is owed by whoever closes the
parameter. ON PURPOSE WEAKER THAN "what is hidden is the same": it can be met though an entry of a
segment in front of m should lie on a pad. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.MeansQ
import Johnson.Top.H0.K2Ties.PadsTurn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open Inst.Model Inst.Model.All
open VerifiableInference.Desc (Wit Strs)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (HidAt TPart TReq TS constrQAt partG partA)

variable {X : OnBytes.Model.Verify.Public} {P Cells Tok : Type} {rows cols : ℕ}

/-- **What the parts of the segments from m on read of the witness bears a turn of the pads of T.**
-/
def HidBears (H : HidAt X P (Wit Cells Tok MsgT) rows cols) (T : List (ℕ × ℕ)) (m : ℕ) : Prop :=
  ∀ w w', PadsTurn T w w' → (H.hid w').tok = (H.hid w).tok ∧ ∀ j, m ≤ j →
    (H.base j w' ↔ H.base j w) ∧
      (j % 2 = 0 → (H.hid w').MG (j / 2) = (H.hid w).MG (j / 2)) ∧
      (j % 2 = 1 → (H.hid w').MA (j / 2) = (H.hid w).MA (j / 2))

/-- From the whole equation. -/
theorem hidBears_of_eq (H : HidAt X P (Wit Cells Tok MsgT) rows cols) (T : List (ℕ × ℕ)) (m : ℕ)
    (h : ∀ w w', PadsTurn T w w' → H.hid w' = H.hid w ∧ ∀ j, (H.base j w' ↔ H.base j w)) :
    HidBears H T m := fun w w' hw => by
  obtain ⟨e, hb⟩ := h w w' hw
  exact ⟨by rw [e], fun j _ => ⟨hb j, fun _ => by rw [e], fun _ => by rw [e]⟩⟩

/-- The like for the output head's parts. -/
def HeadBears (headPart : TPart → Cm.Idx → P × TS → Strs → Wit Cells Tok MsgT → Prop)
    (T : List (ℕ × ℕ)) : Prop :=
  ∀ p i a y w w', PadsTurn T w w' → headPart p i a y w → headPart p i a y w'

/-- A group of layers' part reads that group's arrays alone. -/
theorem partG_congr (i : Cm.Idx) (x : Instance ppref) (MG MG' : ℕ → _) (g : ℕ)
    (p : TPart) (h : MG' g = MG g) : partG X i x MG' g p = partG X i x MG g p := by
  cases p <;> simp only [partG, h]

/-- **The witness's side**: a part of the relation of a segment from m on bears the turn. -/
theorem constr_bears (hd : ℕ) (put : TReq → Fin ppref.V → TReq)
    (H : HidAt X P (Wit Cells Tok MsgT) rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → Wit Cells Tok MsgT → Prop)
    (digitsPart : ℕ → P × TS → Strs → Wit Cells Tok MsgT → Prop) (T : List (ℕ × ℕ)) (m : ℕ)
    (hH : HidBears H T m) (hK : HeadBears headPart T) (j : ℕ) (hj : m ≤ j) (p : TPart)
    (hp : p ≠ .lookDigits) (a : P × TS) (y : Strs) (w w' : Wit Cells Tok MsgT)
    (hw : PadsTurn T w w') (h : constrQAt hd put H headPart digitsPart j p a y w) :
    constrQAt hd put H headPart digitsPart j p a y w' := by
  unfold constrQAt at h ⊢
  rw [if_neg hp] at h ⊢
  obtain ⟨ht, hall⟩ := hH w w' hw
  obtain ⟨hb, hG, hA⟩ := hall j hj
  refine ⟨fun e => hb.2 (h.1 e), fun M i hM hi => ?_⟩
  have h2 := h.2 M i hM hi
  by_cases e1 : j = hd
  · rw [if_pos e1] at h2 ⊢
    exact hK p i a y w w' hw h2
  · rw [if_neg e1] at h2 ⊢
    by_cases e2 : j % 2 = 0
    · rw [if_pos e2] at h2 ⊢
      rw [ht, partG_congr i _ _ _ (j / 2) p (hG e2)]
      exact h2
    · rw [if_neg e2] at h2 ⊢
      rw [hA (by omega)]
      exact h2

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.hidBears_of_eq
#print axioms VerifiableInference.Desc.First.K2Ties.partG_congr
#print axioms VerifiableInference.Desc.First.K2Ties.constr_bears
