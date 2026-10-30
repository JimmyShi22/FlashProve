-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/GrindK.lean: the interface with tests (proof of work, "grinding") in the knowledge form.

In standard terms: proof of work in the rounds of an interactive oracle proof, and what it does to
round-by-round knowledge soundness. A round whose error without the test is ε, as a probability,
has error ε 2^-b with a test of b bits. Knowledge form: for relations with witnesses and a named
witness map `wit`, in place of languages.

Definitions, statements and proofs.

The step on interfaces is Iop/BatchGrind.lean's: `L.grind W gT gL gB` puts tests into the rounds of
the offline IOP, of the link IOP and of a session, along three lists of numbers of test bits (W:
the type of nonces, inhabited). An interface with tests has no `BatchProtocol.Props`, hence no `BatchProtocol.PropsK`:
its interactive protocols are not complete, since nothing of the honest side looks at the test bits
and a failed test is not withheld (header of Iop/BatchGrind.lean: `Props` is false as soon as, in
one of the three protocols, a round has a test and some verifier randomness of some valid input is
not withheld). What the compiler's theorem for rounds with a test takes in the place of Props is
`BatchProtocol.PropsNoAcc` (all clauses but acceptance) together with a condition on the wire
(Compile/Batch/SpecFit.lean: `GrFitB`: among its clauses, acceptance where all tests are passed).
This file gives the knowledge form of the first. Below, for round i of a list of errors: e_i is the
list's entry, a count; b_i the round's number of test bits; |C_i| the number of values of its
verifier message; ε_i = e_i / |C_i|.

Main names:
  `BatchProtocol.SoundAtK L Rno wit εT εL εB`: index-binding round-by-round knowledge soundness for three
    explicit lists of errors. `BatchProtocol.SoundK` hides the lists behind one number, a bound on all of
    them, and from that number no factor 2^-b can come out.
  `BatchProtocol.PropsNoAccK L Ryes Rno wit M`: the record that the compiler with tests takes,
    in the knowledge form: `PropsNoAcc` for the languages of the two
    relations, and `SoundK`.
  `BatchProtocol.SoundKG L Rno wit gT gL gB c`: some three lists satisfy `SoundAtK`, and for each round i,
    with b_i its bits of work, e_i ≤ c (2^b_i |C_i|): so the error of round i without its work can
    reach c 2^b_i. A property of L itself, the interface without tests, and of
    the lists of test bits. It is the soundness hypothesis of the compiler's statements with proof
    of work (CompileK/GrindMain.lean), which also take `BatchProtocol.PropsK`, and with it soundness at M.εs.
  `Spec.soundKG_of_soundK`, `Spec.soundKG_zero`, `Spec.soundKG_mono`: `SoundK` at εs gives
    `SoundKG` at εs for all lists of test bits; at lists of zeros the two are the same; more test
    bits never hurt.
  `Spec.grindSoundKG`, `Spec.grindPropsKG`: `Spec.grindSoundK` and `Spec.grindPropsK` below, from
    `SoundKG`.
  `Spec.soundK_iff_at`: `SoundK` at εs says: there are three lists, every error of which, as a
    probability, is at most εs, with `SoundAtK`.
  `Spec.soundAt_of_soundAtK`: the explicit lists serve the languages too (`BatchProtocol.SoundAt`).
  `Spec.grindSoundAtK`: the step keeps knowledge soundness: same relation, witness map wit ∘
    Orcs.strip (the same symbols), the same counts, now out of |C| 2^b values. No hypothesis on the
    lists of test bits.
  `Spec.grindSoundK`: from `SoundAtK` of L, `SoundK` of the interface with tests at one number c,
    if in every round e_i ≤ c (2^b_i |C_i|), that is ε_i 2^-b_i ≤ c (`Err.BelowG`). c is a maximum
    over all rounds: a round without a test must lie below c by itself.
  `Spec.grindPropsK`: from `PropsK` of L and explicit lists as in `Spec.grindSoundK`: `PropsNoAccK`
    of the interface with tests, with the numbers of L and c in the place of εs.
  `Spec.grindPropsK_same`: without explicit lists: `PropsNoAccK` with the numbers of L unchanged,
    for all lists of test bits (the step never raises a bound).

Which clauses of `PropsK` survive: all but the three on acceptance (accT, accL, accB). Knowledge
soundness: with errors ε_i 2^-b_i and the same witness map. Honest-verifier zero knowledge of each
run: with the same numbers, for honest provers that send a nonce given in advance; the sets that
the numbers measure do not look at the test bits. The probabilities of the withheld sets, the
numbers of positions read, what an encoded index hides, locality, coherence: unchanged. Acceptance
survives in the form "outside the withheld set and where all tests are passed, with any nonces"
(Compile/Batch/FitGrind.lean: `fitGrind` gives `GrFitB` for the wire with tests from `BatchProtocol.Props` of
L, under the further hypotheses of its statement); the tries and the chance of a failed search are
the compiler's (`alphaBG`).

Limits: an idle part of the hypothesis of `grindPropsK`: `PropsK` brings L's own soundness at M.εs,
the errors without tests; the conclusion does not read it. This file says nothing on a compiled
scheme, on tries or queries. It says nothing on whether any interface has the properties, nor on
the size of an error: at c ≥ 1 the bound says nothing. That L.grind at lists of zeros is L is not
stated (the shapes agree by a proved equation only: `Iop.Shape.grind_zero`).
That work should count round by round was asked for (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Hiop.InterfaceProofs
import Ior.GrindK

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

variable {I X Wn : Type}

/-- Index-binding round-by-round knowledge soundness for three explicit lists of errors. -/
structure BatchProtocol.SoundAtK (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) : Prop where
  sndT : L.offline.Sound (fun _ y => L.decodeIndex y ≠ none) εT
  sndL : L.link.Sound (fun _ y => L.decodeIndex y.1 = none ∨ L.decodeIndex y.2 = L.decodeIndex y.1) εL
  sndB : L.onlineBatch.SndBK L.maxBatchSize L.early L.late
    (fun x y w => L.decodeIndex y = none ∨ ∃ i, L.decodeIndex y = some i ∧ Rno i x w) wit εB

/-- Some three lists of errors give `SoundAtK`, each meeting `Err.BelowG` at c with its bits: so
in round i the error without work, read as a probability, stays ≤ c * 2^b_i. -/
def BatchProtocol.SoundKG (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
    (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞) :
    Prop :=
  ∃ εT εL εB,
    L.SoundAtK Rno wit εT εL εB ∧ Err.BelowG gT εT c ∧ Err.BelowG gL εL c ∧ Err.BelowG gB εB c

/-- All properties but acceptance, with a witness: what the compiler's theorem for rounds with a
test takes of the interface. -/
structure BatchProtocol.PropsNoAccK (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
    (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (M : LH.Nums) : Prop where
  props  : L.PropsNoAcc (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) M
  soundK : L.SoundK Rno wit M.εs

namespace Spec

/-- `SoundK` at εs: three lists, as probabilities at most εs, with `SoundAtK`. -/
def soundK_iff_at : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞),
    L.SoundK Rno wit εs ↔
    ∃ εT εL εB, L.SoundAtK Rno wit εT εL εB ∧ Err.Below εT εs ∧ Err.Below εL εs ∧ Err.Below εB εs

/-- The explicit lists serve the languages. -/
def soundAt_of_soundAtK : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape),
    L.SoundAtK Rno wit εT εL εB → L.SoundAt (fun i x => ∃ w, Rno i x w) εT εL εB

/-- Knowledge soundness for explicit lists is kept by the step that adds tests: the same counts,
the same witness map on the same symbols. -/
def grindSoundAtK : Prop :=
  ∀ (W : Type) [Inhabited W] (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (gT : GBits L.offline.shape)
      (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (εT : Err L.offline.shape)
      (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape),
    L.SoundAtK Rno wit εT εL εB →
    (L.grind W gT gL gB).SoundAtK
      Rno (fun x o => wit x (Orcs.strip gB o)) (Err.grind gT εT) (Err.grind gL εL) (Err.grind gB εB)

/-- From `SoundAtK` of L for three lists: knowledge soundness of the interface with tests at the
bound c, if in every round their entries e_i ≤ c * (2^b_i * card C_i). -/
def grindSoundK : Prop :=
  ∀ (W : Type) [Inhabited W] (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
      (gB : GBits L.onlineBatch.loc.shape) (εT : Err L.offline.shape) (εL : Err L.link.shape)
      (εB : Err L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    L.SoundAtK Rno wit εT εL εB → Err.BelowG gT εT c → Err.BelowG gL εL c → Err.BelowG gB εB c →
    (L.grind W gT gL gB).SoundK Rno (fun x o => wit x (Orcs.strip gB o)) c

/-- All clauses but acceptance, with a witness, for the interface with tests: the numbers of L, and
c in the place of εs. (From `PropsK` of L and explicit lists as in `Spec.grindSoundK`.) -/
def grindPropsK : Prop :=
  ∀ (W : Type) [Inhabited W] (I X Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (M : LH.Nums) (gT : GBits L.offline.shape)
      (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (εT : Err L.offline.shape)
      (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    L.PropsK Ryes Rno wit M → L.SoundAtK Rno wit εT εL εB → Err.BelowG gT εT c →
    Err.BelowG gL εL c → Err.BelowG gB εB c →
    (L.grind W gT gL gB).PropsNoAccK
      Ryes Rno (fun x o => wit x (Orcs.strip gB o)) { M with εs := c }

/-- A bound on the bare errors is a bound counting work, whatever the numbers of test bits. -/
def soundKG_of_soundK : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞),
    L.SoundK Rno wit εs →
    ∀ (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape),
      L.SoundKG Rno wit gT gL gB εs

/-- Without work the notion is `SoundK`. -/
def soundKG_zero : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (c : ℝ≥0∞),
    L.SoundKG Rno wit (GBits.zero _) (GBits.zero _) (GBits.zero _) c ↔ L.SoundK Rno wit c

/-- More test bits never hurt, nor does a larger bound. -/
def soundKG_mono : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (gT gT' : GBits L.offline.shape) (gL gL' : GBits L.link.shape)
      (gB gB' : GBits L.onlineBatch.loc.shape) (c c' : ℝ≥0∞),
    GBits.Le gT gT' → GBits.Le gL gL' → GBits.Le gB gB' → c ≤ c' →
    L.SoundKG Rno wit gT gL gB c → L.SoundKG Rno wit gT' gL' gB' c'

/-- Given `L.SoundKG` at c, with each round's bits of work credited, putting these tests into the
interface yields knowledge soundness at c. -/
def grindSoundKG : Prop :=
  ∀ (W : Type) [Inhabited W] (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (gT : GBits L.offline.shape) (gL : GBits L.link.shape)
      (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    L.SoundKG Rno wit gT gL gB c →
    (L.grind W gT gL gB).SoundK Rno (fun x o => wit x (Orcs.strip gB o)) c

/-- .. and all clauses but acceptance, with a witness. (not all hypotheses are named here: see the
statement below) -/
def grindPropsKG : Prop :=
  ∀ (W : Type) [Inhabited W] (I X Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (M : LH.Nums) (gT : GBits L.offline.shape)
      (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    L.PropsK Ryes Rno wit M → L.SoundKG Rno wit gT gL gB c →
    (L.grind W gT gL gB).PropsNoAccK
      Ryes Rno (fun x o => wit x (Orcs.strip gB o)) { M with εs := c }

/-- The step never raises a bound: from `PropsK` of L: `PropsNoAccK` of the interface with tests,
with the numbers of L, for all lists of test bits. -/
def grindPropsK_same : Prop :=
  ∀ (W : Type) [Inhabited W] (I X Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (M : LH.Nums) (gT : GBits L.offline.shape)
      (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape),
    L.PropsK Ryes Rno wit M →
    (L.grind W gT gL gB).PropsNoAccK Ryes Rno (fun x o => wit x (Orcs.strip gB o)) M

end Spec

section
variable {L : BatchProtocol I X} {Rno : I → X → Wn → Prop} {wit : X → Orcs L.onlineBatch.loc.shape → Wn}
  {εT : Err L.offline.shape} {εL : Err L.link.shape} {εB : Err L.onlineBatch.loc.shape}

theorem BatchProtocol.SoundAtK.soundK (h : L.SoundAtK Rno wit εT εL εB) {εs : ℝ≥0∞} (bT : Err.Below εT εs)
    (bL : Err.Below εL εs) (bB : Err.Below εB εs) : L.SoundK Rno wit εs :=
  ⟨⟨εT, bT, h.sndT⟩, ⟨εL, bL, h.sndL⟩, ⟨εB, bB, h.sndB⟩⟩

end

theorem soundK_iff_at : Spec.soundK_iff_at := by
  intro I X Wn L Rno wit εs
  constructor
  · rintro ⟨⟨εT, bT, hT⟩, ⟨εL, bL, hL⟩, ⟨εB, bB, hB⟩⟩
    exact ⟨εT, εL, εB, ⟨hT, hL, hB⟩, bT, bL, bB⟩
  · rintro ⟨εT, εL, εB, h, bT, bL, bB⟩
    exact h.soundK bT bL bB

theorem soundAt_of_soundAtK : Spec.soundAt_of_soundAtK := by
  intro I X Wn L Rno wit εT εL εB h
  refine ⟨h.sndT, h.sndL, (sndB_of_sndBK X Wn _ L.onlineBatch L.maxBatchSize L.early L.late _ wit εB h.sndB).larger ?_⟩
  rintro x y ⟨w, hw | ⟨i, hi, hw⟩⟩
  · exact Or.inl hw
  · exact Or.inr ⟨i, hi, w, hw⟩

theorem grindSoundAtK : Spec.grindSoundAtK := fun W _ _ X Wn L _ wit gT gL gB _ _ εB h =>
  ⟨h.sndT.grind gT, h.sndL.grind gL,
    sndBK_grind W X Wn _ L.onlineBatch gB L.maxBatchSize L.early L.late _ wit εB h.sndB⟩

theorem grindSoundK : Spec.grindSoundK := fun W _ I X Wn L Rno wit gT gL gB εT εL εB c h bT bL bB =>
  (grindSoundAtK W I X Wn L Rno wit gT gL gB εT εL εB h).soundK ((Err.below_grind_iff gT εT c).2 bT)
    ((Err.below_grind_iff gL εL c).2 bL) ((Err.below_grind_iff gB εB c).2 bB)

theorem grindPropsK : Spec.grindPropsK := by
  intro W _ I X Wn L Ryes Rno wit M gT gL gB εT εL εB c h hA bT bL bB
  have hK := grindSoundK W I X Wn L Rno wit gT gL gB εT εL εB c hA bT bL bB
  exact ⟨grindPropsB W I X L _ _ M gT gL gB c h.props (sound_of_soundK I X Wn _ Rno _ c hK), hK⟩

theorem grindPropsK_same : Spec.grindPropsK_same := by
  intro W _ I X Wn L Ryes Rno wit M gT gL gB h
  obtain ⟨εT, εL, εB, hA, bT, bL, bB⟩ := (soundK_iff_at I X Wn L Rno wit M.εs).1 h.soundK
  exact grindPropsK W I X Wn L Ryes Rno wit M gT gL gB εT εL εB M.εs h hA
    (Err.BelowG.of_below gT bT) (Err.BelowG.of_below gL bL) (Err.BelowG.of_below gB bB)

/-- at lists of zeros the bound counting work is the bound -/
theorem Err.belowG_zero :
    ∀ {s : Shape} (ε : Err s) (c : ℝ≥0∞), Err.BelowG (GBits.zero s) ε c ↔ Err.Below ε c
  | [], _, _ => Iff.rfl
  | r :: _, (e, ε), c => by
      show ((e : ℝ≥0∞) ≤ c * ((2 : ℝ≥0∞) ^ 0 * (Fintype.card r.Chal : ℝ≥0∞)) ∧
          Err.BelowG (GBits.zero _) ε c) ↔
        ((e : ℝ≥0∞) ≤ c * (Fintype.card r.Chal : ℝ≥0∞) ∧ Err.Below ε c)
      rw [pow_zero, one_mul, Err.belowG_zero ε c]

/-- more test bits, a larger bound -/
theorem Err.BelowG.mono :
    ∀ {s : Shape} {g g' : GBits s} {ε : Err s} {c c' : ℝ≥0∞},
      GBits.Le g g' → c ≤ c' → Err.BelowG g ε c → Err.BelowG g' ε c'
  | [], _, _, _, _, _, _, _, _ => trivial
  | _ :: _, (_, _), (_, _), (_, _), _, _, hg, hc, h =>
      ⟨_root_.le_trans h.1
          (mul_le_mul' hc (mul_le_mul' (pow_le_pow_right₀ (by norm_num) hg.1) le_rfl)),
        Err.BelowG.mono hg.2 hc h.2⟩

theorem soundKG_of_soundK : Spec.soundKG_of_soundK := by
  intro I X Wn L Rno wit εs h gT gL gB
  obtain ⟨εT, εL, εB, hA, bT, bL, bB⟩ := (soundK_iff_at I X Wn L Rno wit εs).1 h
  exact ⟨εT, εL, εB, hA, Err.BelowG.of_below gT bT,
    Err.BelowG.of_below gL bL, Err.BelowG.of_below gB bB⟩

theorem soundKG_zero : Spec.soundKG_zero := by
  intro I X Wn L Rno wit c
  rw [soundK_iff_at I X Wn L Rno wit c]
  constructor
  · rintro ⟨εT, εL, εB, hA, bT, bL, bB⟩
    exact ⟨εT, εL, εB, hA, (Err.belowG_zero εT c).1 bT,
      (Err.belowG_zero εL c).1 bL, (Err.belowG_zero εB c).1 bB⟩
  · rintro ⟨εT, εL, εB, hA, bT, bL, bB⟩
    exact ⟨εT, εL, εB, hA, (Err.belowG_zero εT c).2 bT,
      (Err.belowG_zero εL c).2 bL, (Err.belowG_zero εB c).2 bB⟩

theorem soundKG_mono : Spec.soundKG_mono := by
  rintro I X Wn L Rno wit gT gT' gL gL' gB gB' c c' hT hL hB hc ⟨εT, εL, εB, hA, bT, bL, bB⟩
  exact ⟨εT, εL, εB, hA, bT.mono hT hc, bL.mono hL hc, bB.mono hB hc⟩

theorem grindSoundKG : Spec.grindSoundKG := by
  rintro W _ I X Wn L Rno wit gT gL gB c ⟨εT, εL, εB, hA, bT, bL, bB⟩
  exact grindSoundK W I X Wn L Rno wit gT gL gB εT εL εB c hA bT bL bB

theorem grindPropsKG : Spec.grindPropsKG := by
  rintro W _ I X Wn L Ryes Rno wit M gT gL gB c h ⟨εT, εL, εB, hA, bT, bL, bB⟩
  exact grindPropsK W I X Wn L Ryes Rno wit M gT gL gB εT εL εB c h hA bT bL bB

end Iop
