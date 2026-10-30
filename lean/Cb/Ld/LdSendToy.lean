-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendToy.lean: the sending at a small code, at a radius not below half the distance: all
hypotheses of `Spec.ldSend_goodT` (Cb/Ld/LdSend.lean) met together, nothing assumed beyond the
hypotheses of `Spec.ldSend_toy`.

Statement (`Cb.Spec.ldSend_toy`) and proof. A guard against empty theorems; no parameter of a
protocol.
In the sending (`ldSend`, Cb/Ld/LdSend.lean) the prover sends a word as an oracle, the verifier a
seed, and the prover the answers at that seed.
A statement is collision-free if at its seed no two different messages with an encoding within the
radius of the word sent have the same answers (`OMsg.Clash`, Cb/Ld/LdSig.lean).
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

The oracle message. The code of Cb/Ld/LdRelToy.lean (Reed-Solomon over the field with 101 elements,
five points, one message symbol and one symbol of randomness a row, distance 4), two rows: the first
holds one datum, the second the pad. Plain format. Radius 2: not below half the distance; lists have
at most 2 members.
The sample. The row with a pad of Cb/Gen/OodDecPad.lean (`Sample.pad`), with a point of no
coordinates: a seed is β other than 0, the answer is datum + β · pad. Its number (`Sample.err`) is
1, of 100 seeds.
The sender. The witness is the datum; the coin that goes into the message is the pad; the extractor
reads the datum off the message.

Main names:
  `Spec.ldSend_toy`:
    the radius is not below half the distance and is below the distance (`Dist 4`, a lower bound;
      `¬ 2 * toyS.e < 4`; `toyS.e < 4`; `toyS.e` is 2);
    the laws of the code;
    lists of at most 2;
    two messages of one list agree at no more than 1 seed;
    the sender's laws;
    the answers are uniform at every seed;
    the encoding hides 1 long position;
    the error of round 1 is 1 (a count of seeds), and there are 100 seeds;
    and so, for every joint A with these witnesses, the sending is `GoodT` (Ior/KnowCollGood.lean)
      from A into "one more oracle message", collision-free.

What `Laws`, `ListLE`, `Evades` and `Hides` ask: the head of Cb/Ld/LdRng.lean ("What the sending's
hypotheses ask").

Limits: this file says nothing on real parameters: 1 of 100 is no security.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendProofs
import Cb.Ld.LdSigTest
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
namespace LdToy
open Iop Prob Hiop Blocks Cb.Ood

/-- the two entries of a message: the datum (first row), the pad (second row) -/
def nu : (toyLd Bool).J ≃ Unit ⊕ Unit where
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

/-- the seeds: β other than 0 -/
abbrev Bn : Type := {β : K // β ≠ 0}
instance : Nonempty Bn := ⟨⟨1, one_ne_zero⟩⟩

/-- the row with a pad: datum + β · pad -/
@[reducible] def padZ : Sample K (Unit ⊕ Unit) :=
  Sample.pad K Empty Unit Unit Bn (fun _ e => e.elim) (fun _ => 1) fun β => β.1

/-- the oracle message -/
@[reducible] def toyS : OMsg K := OMsg.plain (toyLd Bool) (padZ.comap nu) 2 fun _ => 0

/-- the extractor: the datum -/
def toyBack : toyS.Msg → Unit → K := fun m _ => m (nu.symm (Sum.inl ()))

/-- the sender -/
@[reducible] def toyD : toyS.Sender K Unit where
  N := (toyLd Bool).Nn
  upM := fun m => m
  upR := fun r => r
  Mk := K
  put := fun w k j => Sum.elim (fun _ => w) (fun _ => k) (nu j)
  rest := fun _ => ()
  w0 := 0

end LdToy

namespace Spec
open Iop LdToy IOR

def ldSend_toy : Prop :=
  ¬ 2 * toyS.e < 4 ∧ toyS.e < 4 ∧ toyS.C.Dist 4 ∧ toyS.C.Laws ∧ toyS.ListLE 2 ∧ toyS.Evades ∧
    toyD.Laws toyBack ∧ toyD.Uniform ∧ toyD.N.Hides (toyS.C.budT 1) ∧
  Nat.choose 2 2 * toyS.Z.err = 1 ∧ Fintype.card toyS.Z.D = 100 ∧
  ∀ (Kc X : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ K),
    GoodT (ldSend toyS X E₀) (ldSendHon X E₀ toyD) A (toyS.sent A toyBack).cf
      (fun _ _ w => toyBack w.1.1 w.2) (ldSendNums toyS X E₀ Kc 2 1)

end Spec

namespace LdToy
open Iop Prob Hiop Blocks Cb.Ood

theorem padBasis : PadBasis K (fun _ : Unit => (1 : K)) := by
  have h : ∀ c : Unit → K, padVal (F := K) (fun _ : Unit => (1 : K)) c = c () :=
    fun c => by simp [padVal]
  exact ⟨fun c c' hc => funext fun _ => by rw [← h c, ← h c', hc], fun y => ⟨fun _ => y, h _⟩⟩

theorem padZ_okOn : padZ.OKOn (PadInF K) :=
  ood_okOn_pad K K Empty Unit Unit Bn _ _ _ (fun _ _ _ => rfl)
    (fun _ _ h => Subtype.ext h) padBasis.1

theorem toyS_evades : toyS.Evades :=
  sig_evades_of_okOn K toyS _
    (ood_okOn_comap K (Unit ⊕ Unit) (toyLd Bool).J padZ nu (PadInF K) padZ_okOn)
    fun _ _ _ _ _ _ => ⟨_, rfl⟩

theorem comap_comap : (padZ.comap nu).comap nu.symm = padZ := by
  show ({ D := padZ.D, S := padZ.S, mat := fun ρ s n => padZ.mat ρ s (nu (nu.symm n)),
          err := padZ.err } : Sample K (Unit ⊕ Unit)) = padZ
  simp only [Equiv.apply_symm_apply]

theorem toyD_uniform : toyD.Uniform := by
  refine ldSend_uniform_of_private K K toyS K Unit toyD Unit Unit Unit nu
    ⟨fun k => ((), fun _ => k), fun x => x.2 (), fun _ => rfl, fun _ => rfl⟩ (fun w _ _ => w) ?_ ?_
  · intro w k n
    show Sum.elim (fun _ => w) (fun _ => k) (nu (nu.symm n)) = _
    rw [Equiv.apply_symm_apply]
    rcases n with _ | _ <;> rfl
  · show ((padZ.comap nu).comap nu.symm).Private K fun _ => True
    rw [comap_comap]
    exact fun ρ _ a => ood_private_pad K K Empty Unit Unit Bn _ _ _ padBasis ρ ρ.2.2 a

theorem card_seeds : Fintype.card toyS.Z.D = 100 := by
  show Fintype.card ((Empty → K) × Bn) = 100
  rw [Fintype.card_prod, Fintype.card_subtype_compl, Fintype.card_subtype_eq, ZMod.card]
  simp

end LdToy

open LdToy in
theorem ldSend_toy : Spec.ldSend_toy := by
  have hT := ld_toy Bool
  have hLs : toyS.ListLE 2 := sig_list_of_code K toyS 2 hT.2.2.2.1
  have hLaws : toyD.Laws toyBack := ⟨fun _ _ => rfl, fun w k => by
    show Sum.elim (fun _ => w) (fun _ => k) (nu (nu.symm (Sum.inl ()))) = w
    rw [Equiv.apply_symm_apply]
    rfl⟩
  have hH : toyD.N.Hides (toyS.C.budT 1) := hT.2.2.2.2.2.2.1
  refine ⟨by norm_num, by norm_num, hT.2.1, hT.1, hLs, toyS_evades, hLaws, toyD_uniform, hH, ?_,
    card_seeds, fun Kc X E₀ A => ?_⟩
  · show Nat.choose 2 2 *
        max (Fintype.card Empty * Fintype.card K ^ (Fintype.card Empty - 1) * Fintype.card Bn)
          (Fintype.card K ^ Fintype.card Empty) = 1
    simp
  · exact ldSend_goodT K toyS Kc X K Unit E₀ A toyBack toyD 2 1 hT.1 hLs toyS_evades hLaws
      (ldSend_blind_of_uniform K toyS K Unit toyD toyD_uniform) hH

end Cb
