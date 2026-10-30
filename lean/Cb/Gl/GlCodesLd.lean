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
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlCodesLd.lean: several interleaved Reed-Solomon codes over p = 2^64
- 2^32 + 1, of different lengths, queried at common positions: their joint distance, list sizes and
mutual correlated agreement.

Exactly: a family of plain Reed-Solomon codes over p, read at common positions, is taken as one code
read under a transformation (`T.ld E R`, Cb/Ld/LdRelRep.lean); `Laws`, `Transparent`, `Zk t`, `Dist
D`, `ListAt` and `MCAat` (Cb/Ld/LdRel.lean) are concluded of it, under the hypotheses of the
statements below; of its interleavings (`LdCode.il`) and of a fold's stages: Cb/Ld/LdRelRows.lean,
Cb/Gl/GlLdJ.lean.

Definitions, statements (in `Cb.Gl.Spec`) and proofs. No length, no rate, no radius is fixed. The
single code `rs a k msg r e mca` and its properties: Cb/Gl/GlCodes.lean; words and tables are over
the cubic extension E (Cb/Gl/GlField.lean).
A reading (`Reading`, Cb/Gen/CodeRep.lean) says where each common long position is read in each
component; it is even (`Reading.Even`) if each position of component i is read `T.mult i` > 0 times.

Main names (each statement under the hypotheses of its statement):
  `Spec.gl_group_third`: for a i ≤ 32, k i < 2^(a i): list and agreement of a family under an even
    reading: nothing assumed: at long radii whose share (e / T.mult i) is below a third of each
    component's distance.
  The next is for a i ≤ 32, 0 < k i < 2^(a i), D ≤ mult i · (2^(a i) - k i), mult i ≤ e:
  **Spec.gl_group_prox** the same below the Johnson radius of the group, UNDER BCHKS46 BY NAME
  (Cb/Gen/CodeListRS.lean: stated in its source with an outline of a proof; taken as a named
  hypothesis, not an axiom)
    (The source of the statement on codes: the head of Cb/Gen/CodeListRS.lean.)
  `Spec.gl_ld`: for a i ≤ 32, k i < 2^(a i), msg i + r i ≤ k i + 1 (and, for the distance, every
    D ≤ mult i · (2^(a i) - k i)): as a code read under a transformation (Cb/Ld/LdRel.lean, through
    Cb/Ld/LdRelRep.lean): the laws, transparency, the distance under an even reading, zero knowledge
    of the encoding at t ≤ r i long positions.
    The laws of a code read under a transformation (`C.Laws`, that is `LdCode.Laws`) ask: the
    encoder `C.enc`, as a map of the pair (message, randomness), and the transformation `C.T`, from
    native words to long words, are linear over E; the encoder sends only the zero message with zero
    randomness to zero; and, for every long position x, any two native words that agree at the
    native positions `C.src x` have the same long symbol at x. Here they are a conclusion.
  `Spec.gl_ld_third`, `Spec.gl_ld_prox`: for a i ≤ 32, k i < 2^(a i), under an even reading: where
    message and randomness fill the dimension (msg + r = k + 1), its list and its agreement: proved
    up to a third; under BCHKS46 below the Johnson radius of the group (there also 0 < k i,
    D ≤ mult i · (2^(a i) - k i), mult i ≤ e).

Notation: `T`: a reading; `D`: a number, at most every mult i · (2^(a i) - k i) (a premise of the
statements).

Limits: this file says nothing on lengths above 2^32, but for `Spec.gl_rep_even`, which asks
a i ≤ b and not a i ≤ 32. It says nothing on which lengths, rates, radii an instance takes. Nothing
is said between the Johnson radius and capacity.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlCodes
import Cb.Gen.CodeRepRS
import Cb.Ld.LdRelRepProofs

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks

/-- A family of codes `rs`. -/
@[reducible] def grp {A : Type} (a k msg r : A → ℕ) : A → Code.Enc F := fun i =>
  rs (a i) (k i) (msg i) (r i) 0 0

namespace Spec

/-- Lengths that divide 2^b, read by repetition. -/
def gl_rep_even : Prop :=
  ∀ (A : Type) (a k msg r : A → ℕ) (b : ℕ) (h : ∀ i, a i ≤ b),
    (Reading.rep (grp a k msg r) (2 ^ b) fun i => pow_dvd_pow 2 (h i)).Even

/-- A family under an even reading, up to a third: nothing assumed beyond the hypotheses of the
statement and whatever the arguments hold as proofs. -/
def gl_group_third : Prop :=
  ∀ (A : Type) [Fintype A] (a k msg r : A → ℕ), (∀ i, a i ≤ 32) → (∀ i, k i < 2 ^ a i) →
    ∀ T : Reading (grp a k msg r), T.Even →
      ∀ (R : A → Type) [∀ i, Finite (R i)], T.Prox E R
        (fun e => ∀ i, 3 * (e / T.mult i) < 2 ^ a i - k i)
        (fun _ => 1) (fun e => ∑ i, (e / T.mult i + 1))

/-- A family under an even reading, below the Johnson radius of the group: under the statement
on codes (`Cb.BCHKS46`), by name. (not all hypotheses are named here: see the statement below) -/
def gl_group_prox : Prop :=
  Cb.BCHKS46 →
  ∀ (A : Type) [Fintype A] (a k msg r : A → ℕ), (∀ i, a i ≤ 32) →
    (∀ i, 0 < k i) → (∀ i, k i < 2 ^ a i) →
    ∀ T : Reading (grp a k msg r), T.Even →
      ∀ D : ℕ, (∀ i, D ≤ T.mult i * (2 ^ a i - k i)) →
        ∀ (R : A → Type) [∀ i, Finite (R i)], T.Prox E R
          (fun e => InJohnson (Fintype.card T.P) D e ∧ ∀ i, T.mult i ≤ e)
          (fun e => listMax (Fintype.card T.P) D e)
          (fun e => ∑ i, ⌊Cb.bchksBound (2 ^ a i) (k i) (e / T.mult i)⌋₊)

/-- As a code read under a transformation. -/
def gl_ld : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (a k msg r : A → ℕ), (∀ i, a i ≤ 32) →
    (∀ i, k i < 2 ^ a i) → (∀ i, msg i + r i ≤ k i + 1) →
    ∀ (T : Reading (grp a k msg r)) (R : A → Type) [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)],
      (T.ld E R).Laws ∧
      (T.ld E R).Transparent ∧
      (∀ t, (∀ i, t ≤ r i) → (T.ld E R).Zk t) ∧
      (T.Even → ∀ D, (∀ i, D ≤ T.mult i * (2 ^ a i - k i)) → (T.ld E R).Dist D)

def gl_ld_third : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (a k msg r : A → ℕ), (∀ i, a i ≤ 32) →
    (∀ i, k i < 2 ^ a i) → (∀ i, msg i + r i = k i + 1) →
    ∀ (T : Reading (grp a k msg r)), T.Even →
      ∀ (R : A → Type) [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)] (e : ℕ),
        (∀ i, 3 * (e / T.mult i) < 2 ^ a i - k i) →
        (T.ld E R).ListAt e 1 ∧ (T.ld E R).MCAat e (∑ i, (e / T.mult i + 1))

def gl_ld_prox : Prop :=
  Cb.BCHKS46 →
  ∀ (A : Type) [Fintype A] [DecidableEq A] (a k msg r : A → ℕ), (∀ i, a i ≤ 32) → (∀ i, 0 < k i) →
    (∀ i, k i < 2 ^ a i) → (∀ i, msg i + r i = k i + 1) →
    ∀ (T : Reading (grp a k msg r)), T.Even →
      ∀ D : ℕ, (∀ i, D ≤ T.mult i * (2 ^ a i - k i)) →
        ∀ (R : A → Type) [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)] (e : ℕ),
          InJohnson (Fintype.card T.P) D e → (∀ i, T.mult i ≤ e) →
          (T.ld E R).ListAt e (listMax (Fintype.card T.P) D e) ∧
          (T.ld E R).MCAat e (∑ i, ⌊Cb.bchksBound (2 ^ a i) (k i) (e / T.mult i)⌋₊)

end Spec

theorem gl_rep_even : Spec.gl_rep_even := fun A a k msg r b h =>
  rep_even F A (grp a k msg r) (2 ^ b) _ (pow_pos (by norm_num) b)

theorem gl_group_third : Spec.gl_group_third := by
  intro A _ a k msg r ha hk T hT R _
  have h := prox_of_comps F E A (grp a k msg r) T hT R (fun i e' => 3 * e' < 2 ^ a i - k i)
    (fun _ _ _ => 1) (fun _ e' _ => e' + 1)
    fun i => gl_rs_third (a i) (k i) (msg i) (r i) 0 0 (ha i) (hk i)
  simpa using h

-- Limit: the statement has the premise `Cb.BCHKS46`, a hypothesis; this file does not prove it.
theorem gl_group_prox : Spec.gl_group_prox := fun H A _ a k msg r ha hk0 hk T hT D hD R _ =>
  rs_group_prox H F E A (fun i => 2 ^ a i) k msg r (fun i => pts (a i))
    (fun i => gl_pts_inj (a i) (ha i)) hk0 hk T hT D hD R

theorem gl_ld : Spec.gl_ld := by
  intro A _ _ a k msg r ha hk hp T R _ _
  have hd : ∀ i, HasDist (grp a k msg r i).G (grp a k msg r i).d := fun i =>
    rs_hasDist _ _ _ _ (ha i) (hk i)
  refine ⟨ldr_laws F E A _ T R hp hd fun i => Nat.succ_pos _,
    ldr_transparent F E A _ T R,
    fun t ht => ldr_zk F E A _ T R t (fun i => gl_rs_core _ _ _ _ _ _ (ha i) (hk i) (hp i)) ht,
    fun hT D hD => ?_⟩
  exact ldr_dist F E A _ T R D hT hp hd fun i => by rw [rs_d _ _ _ _ (hk i)]; exact hD i

theorem gl_ld_third : Spec.gl_ld_third := by
  intro A _ _ a k msg r ha hk hp T hT R _ _ e he
  have h := gl_group_third A a k msg r ha hk T hT R
  exact ⟨ldr_list F E A _ T R e 1 (fun i => le_of_eq (hp i)) (h.list e he),
    ldr_mca F E A _ T R e _ hp (h.mca e he)⟩

-- Limit: the statement has the premise `Cb.BCHKS46`, a hypothesis; this file does not prove it.
theorem gl_ld_prox : Spec.gl_ld_prox := by
  intro H A _ _ a k msg r ha hk0 hk hp T hT D hD R _ _ e hJ hm
  have h := gl_group_prox H A a k msg r ha hk0 hk T hT D hD R
  exact ⟨ldr_list F E A _ T R e _ (fun i => le_of_eq (hp i)) (h.list e ⟨hJ, hm⟩),
    ldr_mca F E A _ T R e _ hp (h.mca e ⟨hJ, hm⟩)⟩

end Cb.Gl
