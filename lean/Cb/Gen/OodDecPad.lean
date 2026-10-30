-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecPad.lean: out-of-domain samples, continued: sample maps on a set of vectors, the sample
row with a pad, one sample for each row, and privacy.

Definitions and statements (Cb.Spec.ood_*); proofs in Cb/Gen/OodDecPadProofs.lean. It builds on
Cb/Gen/OodDec.lean.
A sample map (`Sample`, Cb/Gen/OodDec.lean) has for each seed a matrix that takes a vector to its
answers. `Sample.OK` is the property of a zero-evader: a vector other than 0 has all answers 0 for
at most err seeds. The counting lemma is `ood_cnt_clash` there.

Why: an answer of a sample is a linear functional of the message, so it gives something away. The
cure: the message carries fresh random entries (a pad), which nothing else reads, and the sample's
row has coefficients on them that turn the pad into one uniform element of E. The pad entries lie in
the small field F, as many for one answer as E has dimension over F; the coefficients on them are
b(β) w_i, where (w_i) is a basis of E over F, fixed once, and β is part of the seed. Such a row is
not a zero-evader on all vectors over E (a vector over E may be annihilated by the w_i for every
seed): it is one on the vectors whose pad part lies in F (`ood_okOn_pad`, under the hypotheses of
its statement). Differences of messages are of this kind. Hence the first notion, `Sample.OKOn`.

Main names:
  `Sample.OKOn Z V`: the property of a sample map for the vectors in V only.
  `PadInF F`: the pad part of a vector on J₀ ⊕ P (entries proper, pad entries) lies in F.
  `Sample.pad`: the row with a pad. A seed is (z, β): a point z of E^μ and an element β of a finite
    non-empty set B with a map b : B → E. The coefficient of an entry j is eq(z, pl j), that of the
    pad entry i is b(β) w_i. The point's weights put nothing on the pad. B and b are parameters: B =
    the elements other than 0, or B = E with the seeds with β = 0 counted apart (the statements on
    privacy ask for b(β) ≠ 0; the count does not). err = the larger of m |E|^(m-1) |B| and |E|^m, of
    |E|^m |B| seeds (m = |μ|).
  `Sample.rows`: one sample for each row of a table, all with the same seed: the entries are R × J,
    the answers R × S, and the answer (a, s) reads row a only.
  `Sample.Private`: privacy, seed by seed, error 0: at every good seed and for all entries proper,
    the answers, over uniform pad entries in F, are uniform. So their law does not depend on the
    message.
  `Sample.PrivateSim`: privacy with a simulator, error 0: a law made without any input is the law of
    the pair (seed, answers), over a uniform seed and uniform pad entries together, whatever the
    entries proper. The weaker notion (weaker than privacy at every seed: `ood_privateSim`), and the
    one that an honest-verifier zero-knowledge proof uses (in this sense: `Spec.ldSwitch_goodT`,
    Cb/Ld/LdSwitch.lean, takes it as a premise).
  `ood_cnt_clash_on`, `ood_cnt_several_on`: the counting lemma for a sample map with the property on
    V and a list of at most L members whose differences lie in V: the seeds at which two different
    members of the list have the same answers number at most (L choose 2) err.
  `ood_frac_pad`: err as a fraction (b injective): err · |B| ≤ (m + 1) · (number of seeds): the
    fraction is at most (m + 1) / |B|.
  `ood_private_pad`: the row with a pad is private, seed by seed, at the seeds with b(β) ≠ 0, if
    (w_i) is a basis.
  `ood_privateSim`: privacy at every seed gives privacy with a simulator (uniform seed, uniform
    answers); `ood_privateSim_pad`: under `PadBasis F w`, so for the row with a pad if b is never 0.
  `ood_val_rows_same`, `ood_okOn_rows`: one sample for each row: its answers; the property carries
    over (on the tables all of whose rows are in V).

Limits: privacy speaks of the answers alone: not jointly with opened positions of an encoding of the
message, and not of several samples that share pad entries (each pad entry is to mask one shown
scalar only; nothing here enforces it). A fixed β would not do for `ood_okOn_pad` (|B| = 1 makes err
at least the number of seeds). How s > 1 rows for one vector are drawn is left open. `Sample.pow` of
Cb/Gen/OodDec.lean takes a one-row evader on all vectors, which this row is not. One way is
`Sample.padPow` (Cb/Gen/OodDecPadPow.lean; see "Limits" in its head).
The row with a pad, and that privacy is asked of the sample's map, follows advice; the particular
row follows this protocol's technical report, which in part follows the paper that this protocol
builds on, and the factor on the pad follows that paper (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.OodDecMle
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.Ood
open Prob Blocks Alg

/-- The property of a sample map, on a set of vectors. -/
def Sample.OKOn {E J : Type} [Field E] [Fintype J] (Z : Sample E J) (V : (J → E) → Prop) : Prop :=
  ∀ v : J → E, V v → v ≠ 0 → cnt (fun ρ : Z.D => Z.val ρ v = 0) ≤ Z.err

/-- The pad part of a vector lies in F. -/
def PadInF (F : Type) {E J₀ P : Type} [Field F] [Field E] [Algebra F E] (v : J₀ ⊕ P → E) : Prop :=
  ∀ i, v (Sum.inr i) ∈ Set.range (algebraMap F E)

/-- the element of E that pad entries in F stand for -/
def padVal {F E P : Type} [Field F] [Field E] [Algebra F E] [Fintype P] (w : P → E) (c : P → F) :
    E :=
  ∑ i, w i * algebraMap F E (c i)

/-- (w_i) is a basis of E over F. -/
def PadBasis (F : Type) {E P : Type} [Field F] [Field E] [Algebra F E] [Fintype P] (w : P → E) :
    Prop :=
  Function.Bijective (padVal (F := F) w)

/-- The sample row with a pad. -/
@[reducible] def Sample.pad (E μ J₀ P B : Type) [Field E] [Fintype E] [Fintype μ] [DecidableEq μ]
    [Fintype B] [Nonempty B] (pl : J₀ → μ → Bool) (w : P → E) (b : B → E) : Sample E (J₀ ⊕ P) :=
  { D := (μ → E) × B, S := Unit,
    mat := fun ρ _ => Sum.elim (fun j => eqk ρ.1 (pl j)) fun i => b ρ.2 * w i,
    err := max (Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1) * Fintype.card B)
        (Fintype.card E ^ Fintype.card μ) }

open Classical in
/-- One sample for each row, with the same seed. -/
@[reducible] def Sample.rows
    {E J : Type} [Field E] (Z : Sample E J) (R : Type) [Fintype R] : Sample E (R × J) :=
  { D := Z.D, S := R × Z.S,
    mat := fun ρ s n => if n.1 = s.1 then Z.mat ρ s.2 n.2 else 0, err := Z.err }

/-- entries proper and pad entries in F, as one vector over E -/
def withPad {F E J₀ P : Type} [Field F] [Field E] [Algebra F E] (a : J₀ → E) (c : P → F) :
    J₀ ⊕ P → E :=
  Sum.elim a fun i => algebraMap F E (c i)

open Classical in
/-- Privacy, seed by seed: at every good seed and for all entries proper, the answers, over uniform
pad entries, are uniform. -/
def Sample.Private (F : Type) {E J₀ P : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] [Fintype J₀] [Fintype P] (Z : Sample E (J₀ ⊕ P)) (good : Z.D → Prop) : Prop :=
  ∀ ρ, good ρ → ∀ a : J₀ → E, (unif (P → F)).map (fun c => Z.val ρ (withPad a c)) = unif (Z.S → E)

open Classical in
/-- Privacy, with a simulator (error 0): there is a law, made without any input, that is the law of
the pair (seed, answers), over a uniform seed and uniform pad entries, whatever the entries
proper. -/
def Sample.PrivateSim (F : Type) {E J₀ P : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] [Fintype J₀] [Fintype P] (Z : Sample E (J₀ ⊕ P)) : Prop :=
  ∃ sim : PMF (Z.D × (Z.S → E)),
    ∀ a : J₀ → E, (unif (Z.D × (P → F))).map (fun x => (x.1, Z.val x.1 (withPad a x.2))) = sim

end Cb.Ood

namespace Cb.Spec
open Prob Blocks Alg Cb.Ood

def ood_ok_iff_okOn : Prop :=
  ∀ (E J : Type) [Field E] [Fintype J] (Z : Sample E J), Z.OK ↔ Z.OKOn fun _ => True
def ood_okOn_of_ok : Prop :=
  ∀ (E J : Type) [Field E] [Fintype J] (Z : Sample E J) (V : (J → E) → Prop), Z.OK → Z.OKOn V

/-- The counting lemma, on a set of vectors. -/
def ood_cnt_clash_on : Prop :=
  ∀ (E J : Type) [Field E] [Fintype J] (Z : Sample E J) (V : (J → E) → Prop)
      (Lst : (J → E) → Prop) (L : ℕ),
    ListLE Lst L → Z.OKOn V → (∀ u u', Lst u → Lst u' → V (u - u')) →
    cnt (Clash Lst Z.val) ≤ L.choose 2 * Z.err

def ood_cnt_several_on : Prop :=
  ∀ (E J : Type) [Field E] [Fintype J] (Z : Sample E J) (V : (J → E) → Prop)
      (Lst : (J → E) → Prop) (L : ℕ),
    ListLE Lst L → Z.OKOn V → (∀ u u', Lst u → Lst u' → V (u - u')) →
    cnt (fun ρ : Z.D => ∃ y, Coll Lst Z.val ρ y) ≤ L.choose 2 * Z.err ∧
    2 * cnt (fun ρ : Z.D => ∃ y, Coll Lst Z.val ρ y) ≤ L ^ 2 * Z.err

def ood_padInF_sub : Prop :=
  ∀ (F E J₀ P : Type) [Field F] [Field E] [Algebra F E] (u u' : J₀ ⊕ P → E),
    PadInF F u → PadInF F u' → PadInF F (u - u')

/-- The answer of the row with a pad. -/
def ood_val_pad : Prop :=
  ∀ (E μ J₀ P B : Type) [Field E] [Fintype E] [Fintype μ] [DecidableEq μ] [Fintype B]
      [Nonempty B] [Fintype J₀] [Fintype P] (pl : J₀ → μ → Bool) (w : P → E) (b : B → E)
      (z : μ → E) (β : B) (v : J₀ ⊕ P → E),
    (Sample.pad E μ J₀ P B pl w b).val (z, β) v () =
      Alg.mle (placed pl fun j => v (Sum.inl j)) z + b β * ∑ i, w i * v (Sum.inr i)

/-- For non-empty B: if pl, b and `padVal w` on F^P are injective, the row with a pad is a
zero-evader on the vectors whose pad part lies in F. -/
def ood_okOn_pad : Prop :=
  ∀ (F E μ J₀ P B : Type) [Field F] [Field E] [Algebra F E] [Fintype E] [Fintype μ]
      [DecidableEq μ] [Fintype B] [Nonempty B] [Fintype J₀] [Fintype P] (pl : J₀ → μ → Bool)
      (w : P → E) (b : B → E),
    Function.Injective pl → Function.Injective b → Function.Injective (padVal (F := F) w) →
    (Sample.pad E μ J₀ P B pl w b).OKOn (PadInF F)

/-- The number err of the row with a pad against the number of seeds, for non-empty B, if b is
injective: the fraction is at most (m + 1) / |B|, m = |μ|. -/
def ood_frac_pad : Prop :=
  ∀ (E μ J₀ P B : Type) [Field E] [Fintype E] [Fintype μ] [DecidableEq μ] [Fintype B] [Nonempty B]
      (pl : J₀ → μ → Bool) (w : P → E) (b : B → E),
    Function.Injective b →
    (Sample.pad E μ J₀ P B pl w b).err * Fintype.card B ≤
      (Fintype.card μ + 1) * Fintype.card ((μ → E) × B)

/-- For non-empty B: the row with a pad is private, seed by seed, at the seeds with b(β) ≠ 0, if
(w_i) is a basis. -/
def ood_private_pad : Prop :=
  ∀ (F E μ J₀ P B : Type) [Field F] [Fintype F] [Field E] [Algebra F E] [Fintype E] [Fintype μ]
      [DecidableEq μ] [Fintype B] [Nonempty B] [Fintype J₀] [Fintype P] (pl : J₀ → μ → Bool)
      (w : P → E) (b : B → E),
    PadBasis F w → (Sample.pad E μ J₀ P B pl w b).Private F fun ρ => b ρ.2 ≠ 0

/-- Privacy at every seed gives privacy with a simulator: a uniform seed and uniform answers. -/
def ood_privateSim : Prop :=
  ∀ (F E J₀ P : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Fintype J₀]
      [Fintype P] (Z : Sample E (J₀ ⊕ P)),
    (Z.Private F fun _ => True) → Z.PrivateSim F

/-- Under `PadBasis F w`, for non-empty B: the row with a pad, if b is never 0, is private with a
simulator. -/
def ood_privateSim_pad : Prop :=
  ∀ (F E μ J₀ P B : Type) [Field F] [Fintype F] [Field E] [Algebra F E] [Fintype E] [Fintype μ]
      [DecidableEq μ] [Fintype B] [Nonempty B] [Fintype J₀] [Fintype P] (pl : J₀ → μ → Bool)
      (w : P → E) (b : B → E),
    PadBasis F w → (∀ β, b β ≠ 0) → (Sample.pad E μ J₀ P B pl w b).PrivateSim F

/-- One sample for each row: the property. -/
def ood_okOn_rows : Prop :=
  ∀ (E J R : Type) [Field E] [Fintype J] [Fintype R] (Z : Sample E J) (V : (J → E) → Prop),
    Z.OKOn V → (Z.rows R).OKOn fun v => ∀ a, V fun j => v (a, j)

/-- The answers of "one sample for each row". -/
def ood_val_rows_same : Prop :=
  ∀ (E J R : Type) [Field E] [Fintype J] [Fintype R] (Z : Sample E J) (ρ : Z.D)
      (v : R × J → E) (a : R) (s : Z.S),
    (Z.rows R).val ρ v (a, s) = Z.val ρ (fun j => v (a, j)) s

end Cb.Spec
