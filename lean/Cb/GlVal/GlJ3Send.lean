-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3Send.lean: a small test instance of a sending: the prover
sends one word of two Reed-Solomon rows (a datum, a pad) as an oracle, the verifier draws a seed,
and the prover answers with a linear sample of the encoded message. Every hypothesis of the theorem
on that step is proved for it.


The toys' oracle message with one datum and one pad, and its
sending, at the radius 3 of the distance 5 (not within half the distance, below the Johnson radius):
all hypotheses of Cb/Ld/LdSend.lean met together, nothing assumed.

Definitions, statement (`Cb.GlJ3.Spec.gl_j3_send`) and proof. A guard against empty theorems; no
parameter of a protocol.
The analogue of the guard of Cb/GlVal/GlToySend.lean, under that file's names, in namespace
`Cb.GlJ3`, so that toy files which name them can follow by a change of names. UNCHANGED, and taken
from there: the code (toyLd), the two entries of a message (nu).
Against Cb/GlVal/GlToySend.lean. (1) The radius is 3 (there 1, within a third): lists by the Johnson
bound, at most `LJ3` members (Cb/GlVal/GlJ3Base.lean). (2) The pad's coefficient is drawn among all
values other than 0 (`Bq`, Cb/GlVal/GlToyWfJ.lean; there: the one value 1, with which a sample's
number is the number of all its seeds: harmless only where lists have one member).
A sample map (`Sample`, Cb/Gen/OodDec.lean) is a zero-evader (`Sample.OK`) if each vector other than
0 has all answers 0 at no more than `err` seeds.

Main names:
  `ld_toy R`: what the toys cite of their code, in the shape of `ld_toy` of Cb/GlVal/GlToySend.lean:
    laws; distance 5; [the radius is not within half the distance]; lists of at most `LJ3`; at most
    `bJ3` exceptional values (the count of the statement on codes, a true count here with nothing
    assumed: head of Cb/GlVal/GlJ3Base.lean); [nothing]; zero knowledge at one position;
    transparent; [nothing].
  `Spec.gl_j3_send`: the radius is not within half the distance; it is below the distance; distance;
    laws; lists of at most `LJ3` members; the sample is a zero-evader (`toyS.Z.OK`: pads in E); two
    messages of one list agree at no more seeds than the sample's number; the sender's laws; the
    answers are uniform at every seed; the encoding hides 3 long positions; and so the sending is
    `GoodT`, for every joint A with these witnesses (`A : Rels Kc X E₀ E`).

Limits: this file says nothing on real parameters, nor on the size of errors.
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToySend
import Cb.GlVal.GlToyWfJ
import Cb.GlVal.GlJ3Base
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.Gl Cb.Gl.Wf8J

/-- Found at once, whatever is imported. -/
local instance neEJ3Send : Nonempty E := ⟨0⟩

/-- What the toys cite of their code, at the radius 3. -/
theorem ld_toy (R : Type) [Fintype R] [DecidableEq R] :
    (toyLd R).Laws ∧ (toyLd R).Dist 5 ∧ ¬ 2 * eJ3 < 5 ∧ (toyLd R).ListAt eJ3 LJ3 ∧
    (toyLd R).MCAat eJ3 bJ3 ∧ True ∧ (toyLd R).Zk 1 ∧ (toyLd R).Transparent ∧ True := by
  obtain ⟨hG, hL, hD, hT, -, -, -, -, -⟩ := gl_toy84 R
  exact ⟨hL, hD, by decide, listJ3 _ hL hD, mcaJ3 _ hL, trivial,
    (glC_code P84 _ 5 1 (glC_mono P84 _ 5 3 5 1 hG le_rfl (by norm_num))).2.2.2.2, hT, trivial⟩

/-- The seeds: the values other than 0. -/
abbrev Bn : Type := Bq

/-- The row with a pad: datum + β · pad. -/
@[reducible] def padZ : Sample E (Unit ⊕ Unit) :=
  Sample.pad E Empty Unit Unit Bn (fun _ e => e.elim) (fun _ => 1) Bq.val

/-- The oracle message. -/
@[reducible] def toyS : OMsg E :=
  OMsg.plain (toyLd84 Bool) (padZ.comap nu) eJ3 fun _ => 0

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

def Spec.gl_j3_send : Prop :=
  ¬
  2 * toyS.e < 5 ∧ toyS.e < 5 ∧ toyS.C.Dist 5 ∧ toyS.C.Laws ∧ toyS.ListLE LJ3 ∧ toyS.Z.OK ∧
  toyS.Evades ∧ toyD.Laws toyBack ∧ toyD.Uniform ∧ toyD.N.Hides (toyS.C.budT 3) ∧
  ∀ (Kc X : Type) (E₀ : ExtSpec) (A : Rels Kc X E₀ E),
    GoodT (ldSend toyS X E₀) (ldSendHon X E₀ toyD) A (toyS.sent A toyBack).cf
      (fun _ _ w => toyBack w.1.1 w.2) (ldSendNums toyS X E₀ Kc LJ3 3)

theorem padBasis : PadBasis E (fun _ : Unit => (1 : E)) := Cb.Gl.padBasis

theorem padZ_okOn : padZ.OKOn (PadInF E) :=
  ood_okOn_pad E E Empty Unit Unit Bn _ _ _ (fun _ _ _ => rfl) Bq.val_inj padBasis.1

/-- The sample is a zero-evader on all vectors: the pad lies in E. -/
theorem toyS_ok : toyS.Z.OK := fun v hv =>
  ood_okOn_comap E (Unit ⊕ Unit) (toyLd84 Bool).J padZ nu (PadInF E)
    padZ_okOn v (fun _ => ⟨_, rfl⟩) hv

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
    exact fun ρ _ a => ood_private_pad E E Empty Unit Unit Bn _ _ _ padBasis ρ (Bq.val_ne ρ.2) a

theorem gl_j3_send : Spec.gl_j3_send := by
  obtain ⟨-, hL, hD, -, -, hZ, -, -, -⟩ := gl_toy84 Bool
  have hLs : toyS.ListLE LJ3 := sig_list_of_code E toyS LJ3 (listJ3 _ hL hD)
  have hLaws : toyD.Laws toyBack := ⟨fun _ _ => rfl, fun w k => by
    show Sum.elim (fun _ => w) (fun _ => k) (nu (nu.symm (Sum.inl ()))) = w
    rw [Equiv.apply_symm_apply]
    rfl⟩
  exact ⟨by decide, by decide, hD, hL, hLs, toyS_ok, toyS_evades, hLaws, toyD_uniform, hZ,
    fun Kc X E₀ A =>
      ldSend_goodT E toyS Kc X E Unit E₀ A toyBack toyD LJ3 3 hL hLs toyS_evades hLaws
        (ldSend_blind_of_uniform E toyS E Unit toyD toyD_uniform) hZ⟩

end Cb.GlJ3
