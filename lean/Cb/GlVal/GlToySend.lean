-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToySend.lean: a small test instance of a sending: the prover sends one word of two
interleaved Reed-Solomon rows as an oracle, the verifier draws a seed, and the prover answers with a
linear sample of the encoded message. Every hypothesis of the theorem on that step
(`Spec.ldSend_goodT`, Cb/Ld/LdSend.lean) is proved for it, nothing assumed.

Definitions, statement (`Cb.Gl.Spec.gl_ldSend_toy`) and proof. A guard against empty theorems; no
parameter of a protocol.
The analogue of the guard of Cb/Ld/LdSendToy.lean, under that file's names (and `toyLd`, `ld_toy` of
Cb/Ld/LdRelToy.lean), so that a toy file that cites these names can be stated over `F` and `E`
(Cb/Gl/GlField.lean) under the same names.

The oracle message. The code of Cb/GlVal/GlToyBase4.lean (`C84` over F: the subgroup of order 8,
dimension 4: one message symbol and three symbols of randomness a row; distance 5; read over E), two
rows: the first holds one datum, the second the pad. Plain format.
The sample. The row with a pad of Cb/Gen/OodDecPad.lean, with a point of no coordinates. The sender.
The witness is the datum; the coin that goes into the message is the pad; the extractor reads the
datum off the message.
Radius 1, within a third of the distance 5: lists of at most one member. The encoding hides
3 long positions. The pad's
coefficient is the one value 1: `Bn := Unit`: nothing enumerates the
field; the answer is datum + pad. Of the guard of Cb/Ld/LdSendToy.lean the two clauses that write
numbers of seeds in numerals are dropped.

Main names:
  `Spec.gl_ldSend_toy`: 3 · radius < 5; distance; the laws of the code; lists of at most one member;
    two messages of one list agree at no more seeds than the sample's number; the sender's laws; the
    answers are uniform at every seed; the encoding hides 3 long positions; and so, for every joint
    A with these witnesses, the sending is `GoodT` from A into "one more oracle message",
    collision-free.

Of the clauses of `Spec.gl_ldSend_toy` none needs F = E.

Limits: this file says nothing on real parameters.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendProofs
import Cb.GlVal.GlToyBase4
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.Gl
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- A local instance, so that Lean's search finds `Nonempty E` at once, whatever is imported. -/
local instance neESend : Nonempty E := ⟨0⟩

/-- The toys' code, under the name that it has in Cb/Ld/LdRelToy.lean. -/
abbrev toyLd (R : Type) [Fintype R] [DecidableEq R] : LdCode E P84 := toyLd84 R

/-- What the toys cite of their code, in the shape of `ld_toy` of Cb/Ld/LdRelToy.lean, so that
projections carry over: laws; distance; [there: the radius is not below half the distance; here:
within a third]; lists, at the bound 2 that the toys write (here the lists have at most one member);
exceptional values; [there: fewer than the field has elements; here nothing]; zero knowledge at the
one position that the toys write (the code hides 3); transparent; [there: locality; here nothing].
-/
theorem ld_toy (R : Type) [Fintype R] [DecidableEq R] :
    (toyLd R).Laws ∧ (toyLd R).Dist 5 ∧ 3 * 1 < 5 ∧ (toyLd R).ListAt 1 2 ∧ (toyLd R).MCAat 1 2 ∧
    True ∧ (toyLd R).Zk 1 ∧ (toyLd R).Transparent ∧ True := by
  obtain ⟨hG, hL, hD, hT, -, -, h3, hLi, hM⟩ := gl_toy84 R
  exact ⟨hL, hD, h3, fun f => le_trans (hLi f) (by norm_num), hM, trivial,
    (glC_code P84 _ 5 1 (glC_mono P84 _ 5 3 5 1 hG le_rfl (by norm_num))).2.2.2.2, hT, trivial⟩

/-- The two entries of a message: the datum (first row), the pad (second row). -/
def nu : (toyLd84 Bool).J ≃ Unit ⊕ Unit where
  toFun j := if j.2.1 then Sum.inr () else Sum.inl ()
  invFun n := match n with
    | .inl _ => ⟨(), (false, (0 : Fin 1))⟩
    | .inr _ => ⟨(), (true, (0 : Fin 1))⟩
  left_inv := by
    rintro ⟨⟨⟩, b, i⟩
    have h : i.val < 1 := i.isLt
    have hi : i = (0 : Fin 1) := Fin.ext (show i.val = 0 from Nat.lt_one_iff.1 h)
    subst hi
    cases b <;> rfl
  right_inv := by rintro (⟨⟩ | ⟨⟩) <;> rfl

/-- The seeds: one. -/
abbrev Bn : Type := Unit

/-- The row with a pad: datum + pad. -/
@[reducible] def padZ : Sample E (Unit ⊕ Unit) :=
  Sample.pad E Empty Unit Unit Bn (fun _ e => e.elim) (fun _ => 1) fun _ => 1

/-- The oracle message. -/
@[reducible] def toyS : OMsg E :=
  OMsg.plain (toyLd84 Bool) (padZ.comap nu) 1 fun _ => 0

/-- The extractor: the datum. -/
def toyBack : toyS.Msg → Unit → E := fun m _ => m (nu.symm (Sum.inl ()))

/-- The sender. -/
@[reducible] def toyD : toyS.Sender E Unit where
  N := (toyLd84 Bool).Nn
  upM := fun m => m
  upR := fun r => r
  Mk := E
  put := fun w k j => Sum.elim (fun _ => w) (fun _ => k) (nu j)
  rest := fun _ => ()
  w0 := 0

def Spec.gl_ldSend_toy : Prop :=
  3 * toyS.e < 5 ∧ toyS.C.Dist 5 ∧ toyS.C.Laws ∧ toyS.ListLE 1 ∧ toyS.Evades ∧ toyD.Laws toyBack ∧
  toyD.Uniform ∧ toyD.N.Hides (toyS.C.budT 3) ∧
  ∀ (Kc X : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ E),
    GoodT (ldSend toyS X E₀) (ldSendHon X E₀ toyD) A (toyS.sent A toyBack).cf
      (fun _ _ w => toyBack w.1.1 w.2) (ldSendNums toyS X E₀ Kc 1 3)

theorem padBasis : PadBasis E (fun _ : Unit => (1 : E)) := by
  have h : ∀ c : Unit → E, padVal (F := E) (fun _ : Unit => (1 : E)) c = c () :=
    fun c => by simp [padVal]
  exact ⟨fun c c' hc => funext fun _ => by rw [← h c, ← h c', hc], fun y => ⟨fun _ => y, h _⟩⟩

theorem padZ_okOn : padZ.OKOn (PadInF E) :=
  ood_okOn_pad E E Empty Unit Unit Bn _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) padBasis.1

theorem toyS_evades : toyS.Evades :=
  sig_evades_of_okOn E toyS _
    (ood_okOn_comap E (Unit ⊕ Unit) (toyLd84 Bool).J padZ nu (PadInF E) padZ_okOn)
    fun _ _ _ _ _ _ => ⟨_, rfl⟩

theorem comap_comap : (padZ.comap nu).comap nu.symm = padZ := by
  show ({ D := padZ.D, S := padZ.S, mat := fun ρ s n => padZ.mat ρ s (nu (nu.symm n)),
          err := padZ.err } : Sample E (Unit ⊕ Unit)) = padZ
  simp only [Equiv.apply_symm_apply]

theorem toyD_uniform : toyD.Uniform := by
  refine ldSend_uniform_of_private E E toyS E Unit toyD Unit Unit Unit nu
    ⟨fun k => ((), fun _ => k), fun x => x.2 (), fun _ => rfl, fun _ => rfl⟩ (fun w _ _ => w) ?_ ?_
  · intro w k n
    show Sum.elim (fun _ => w) (fun _ => k) (nu (nu.symm n)) = _
    rw [Equiv.apply_symm_apply]
    rcases n with _ | _ <;> rfl
  · show ((padZ.comap nu).comap nu.symm).Private E fun _ => True
    rw [comap_comap]
    exact fun ρ _ a => ood_private_pad E E Empty Unit Unit Bn _ _ _ padBasis ρ one_ne_zero a

theorem gl_ldSend_toy : Spec.gl_ldSend_toy := by
  obtain ⟨-, hL, hD, -, -, hZ, -, hLi, -⟩ := gl_toy84 Bool
  have hLs : toyS.ListLE 1 := sig_list_of_code E toyS 1 hLi
  have hLaws : toyD.Laws toyBack := ⟨fun _ _ => rfl, fun w k => by
    show Sum.elim (fun _ => w) (fun _ => k) (nu (nu.symm (Sum.inl ()))) = w
    rw [Equiv.apply_symm_apply]
    rfl⟩
  exact ⟨by norm_num, hD, hL, hLs, toyS_evades, hLaws, toyD_uniform, hZ,
    fun Kc X E₀ A =>
      ldSend_goodT E toyS Kc X E Unit E₀ A toyBack toyD 1 3 hL hLs toyS_evades hLaws
        (ldSend_blind_of_uniform E toyS E Unit toyD toyD_uniform) hZ⟩

end Cb.Gl
