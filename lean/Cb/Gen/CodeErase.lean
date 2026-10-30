-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeErase.lean: erasure correction for interleaved linear codes: the messages of a table,
recovered from a set of positions on which it agrees with codewords.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Gen/CodeEraseProofs.lean.

Why: beyond half the distance a word need not have one nearest codeword, so an extractor that runs
backwards cannot "decode" its input. It knows more: a set S of positions on which the input agrees
with some codeword. If S has more than n - d positions, that codeword is determined by S alone. No
errors are corrected. The names of the three functions `erase?` end in a question mark, as Lean's
functions with an optional result do.

Main names, for a generator matrix G and tables with any rows R. S is large if it has more than
n - d positions: in standard terms, the positions outside S are at most d - 1 erasures. Where a
statement needs the distance it assumes `HasDist G d`, under a reading `Spec.RdOK`; the rows below
do not repeat this.
  `erase? G d S f`: a table of messages M with `AgreesOn G S f M` (the only one if G has the
    distance d: `Spec.agreesOn_unique`), if S is large and there is one; "none" else. A total
    function.
  `Spec.erase_iff`: what it returns, from the distance alone (`HasDist G d`).
  Linearity and rows, on a common set S: `Spec.erase_combs`, `Spec.erase_line`, `Spec.erase_comp`; a
    smaller large set gives the same: `Spec.erase_anti`.
  Subfields: `Spec.erase_lift`: for a table over F, erasure correction over E is erasure correction
    over F. In particular a codeword over E that agrees with a word over F at more than n - d
    positions is a codeword over F.
  Under a reading T (Cb/Gen/CodeRep.lean), S a set of long positions, D a lower bound for the
    distance of the group under T (`Spec.RdOK`): `Reading.AgreesOn`, `Reading.erase?`,
    `Reading.agr`; `Spec.rd_erase_iff`, `Spec.rd_decodesTo_iff_agr`, `Spec.rd_erase_agr`,
    `Spec.rd_erase_decodesTo`, `Spec.rd_erase_line`.
  `Spec.rd_erase_comps`: for a large S (more than |P| - D long positions), erasure correction under
    T is erasure correction in each component on the image of S. Guard `Spec.rd_erase_one`: for one
    code with its distance, read as it stands, it is `Code.Enc.erase?`.

Limits: what is asked of a code is its distance, nothing else (no systematic form, no bound on S
other than |S| > n - d). The paper that this protocol builds on (lean/CREDITS.md) has the same
threshold and also counts running time (in the version named there).
This file says nothing on running time: `erase?` is a choice among the messages that fit, which is
unique if G has the distance d (`Spec.agreesOn_unique`). Here a reading is even (`Spec.RdOK`), so
the messages are determined, not only what is read of their codewords. This file says nothing on
which part of a full message is message and which randomness (`Blocks.msgPart`, `Cb.rndPart` read
them off). It says nothing on protocols. This file says nothing on the value of any number.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.CodeRep
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Prob Blocks

section
variable {E ι κ R : Type} [Field E] [Fintype κ]

/-- On the set S every row of f is the codeword of its message. -/
def AgreesOn (G : Matrix ι κ E) (S : Finset ι) (f : R → ι → E) (M : R → κ → E) : Prop :=
  ∀ j ∈ S, ∀ a, f a j = G.mulVec (M a) j

variable [Fintype ι]

open Classical in
/-- Erasure correction. Where a statement needs the distance, it assumes `HasDist G d`: G has
distance at least d. -/
def erase? (G : Matrix ι κ E) (d : ℕ) (S : Finset ι) (f : R → ι → E) :
    Option (R → κ → E) :=
  if h : Fintype.card ι < S.card + d ∧ ∃ M, AgreesOn G S f M then some h.2.choose else none

open Classical in
/-- The set of all positions at which f agrees with the codewords of M. -/
def agr (G : Matrix ι κ E) (f : R → ι → E) (M : R → κ → E) : Finset ι :=
  Finset.univ.filter fun j => ¬ Off G f M j

end

/-- Erasure correction for a code with encoder: tables over E, full messages. -/
def _root_.Code.Enc.erase? {F : Type} [Field F] (C : Code.Enc F) (E : Type) [Field E]
    [Algebra F E] {R : Type} (S : Finset (Fin C.n)) (f : R → Fin C.n → E) :
    Option (R → Fin C.k → E) :=
  Cb.erase? (C.GE E) C.d S f

namespace Reading
variable {F A : Type} {C : A → Code.Enc F} [Field F] (T : Reading C) (E : Type) [Field E]
  [Algebra F E] {R : A → Type}

/-- On the set S of long positions every row of every component is the codeword of its message. -/
def AgreesOn (S : Finset T.P) (f : ∀ a, R a → Fin (C a).n → E) (M : ∀ a, R a → Fin (C a).k → E) :
    Prop :=
  ∀ x ∈ S, ∀ a r, f a r (T.pos a x) = ((C a).GE E).mulVec (M a r) (T.pos a x)

open Classical in
/-- Erasure correction under a reading. Where a statement needs the distance, it assumes
`Spec.RdOK`: D is a lower bound for the distance of the group under T, in long positions. -/
def erase? (D : ℕ) (S : Finset T.P) (f : ∀ a, R a → Fin (C a).n → E) :
    Option (∀ a, R a → Fin (C a).k → E) :=
  if h : Fintype.card T.P < S.card + D ∧ ∃ M, T.AgreesOn E S f M then some h.2.choose else none

open Classical in
/-- The set of all long positions at which f agrees with the codewords of M. -/
def agr (f : ∀ a, R a → Fin (C a).n → E) (M : ∀ a, R a → Fin (C a).k → E) :
    Finset T.P :=
  Finset.univ.filter fun x => ¬ T.Off E f M x

end Reading

namespace Spec

section Mat
variable (E : Type) [Field E]

def agreesOn_unique : Prop :=
  ∀ (ι κ R : Type) [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (d : ℕ), HasDist G d →
    ∀ (S : Finset ι), Fintype.card ι < S.card + d →
      ∀ (f : R → ι → E) (M M' : R → κ → E), AgreesOn G S f M → AgreesOn G S f M' → M = M'

/-- What erasure correction returns. -/
def erase_iff : Prop :=
  ∀ (ι κ R : Type) [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (d : ℕ), HasDist G d →
    ∀ (S : Finset ι) (f : R → ι → E) (M : R → κ → E),
      erase? G d S f = some M ↔ Fintype.card ι < S.card + d ∧ AgreesOn G S f M

def erase_none_iff : Prop :=
  ∀ (ι κ R : Type) [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (d : ℕ)
      (S : Finset ι) (f : R → ι → E),
    erase? G d S f = none ↔ ¬ (Fintype.card ι < S.card + d ∧ ∃ M, AgreesOn G S f M)

def agreesOn_iff_subset : Prop :=
  ∀ (ι κ R : Type) [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (S : Finset ι)
      (f : R → ι → E) (M : R → κ → E),
    AgreesOn G S f M ↔ S ⊆ agr G f M

def decodesTo_iff_agr : Prop :=
  ∀ (ι κ R : Type) [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (e : ℕ)
      (f : R → ι → E) (M : R → κ → E),
    DecodesTo G e f M ↔ Fintype.card ι ≤ (agr G f M).card + e

/-- If G has the distance d, a large set inside the agreement set with M gives M. -/
def erase_of_subset : Prop :=
  ∀ (ι κ R : Type) [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (d : ℕ), HasDist G d →
    ∀ (S : Finset ι) (f : R → ι → E) (M : R → κ → E),
      S ⊆ agr G f M → Fintype.card ι < S.card + d → erase? G d S f = some M

/-- If G has the distance d, every member of a list at a radius e < d is erasure correction on its
own agreement set. -/
def erase_agr : Prop :=
  ∀ (ι κ R : Type) [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (d e : ℕ), HasDist G d → e < d →
    ∀ (f : R → ι → E) (M : R → κ → E), DecodesTo G e f M → erase? G d (agr G f M) f = some M

/-- If G has the distance d, what erasure correction returns on a set that omits at most e positions
is a member of the list at e. -/
def erase_decodesTo : Prop :=
  ∀ (ι κ R : Type) [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (d e : ℕ), HasDist G d →
    ∀ (S : Finset ι) (f : R → ι → E) (M : R → κ → E),
      erase? G d S f = some M → Fintype.card ι ≤ S.card + e → DecodesTo G e f M

def erase_combs : Prop :=
  ∀ (ι κ R R' : Type) [Fintype ι] [Fintype κ] [Fintype R] (G : Matrix ι κ E) (d : ℕ), HasDist G d →
    ∀ (S : Finset ι) (f : R → ι → E) (M : R → κ → E) (c : R' → R → E), erase? G d S f = some M →
      erase? G d S (fun b => ∑ a, c b a • f a) = some fun b => ∑ a, c b a • M a

def erase_line : Prop :=
  ∀ (ι κ R : Type) [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (d : ℕ), HasDist G d →
    ∀ (S : Finset ι) (f₀ f₁ : R → ι → E) (M₀ M₁ : R → κ → E) (c₀ c₁ : E), erase? G d S f₀ =
        some M₀ →
      erase? G d S f₁ = some M₁ →
      erase? G d S (fun a => c₀ • f₀ a + c₁ • f₁ a) = some fun a => c₀ • M₀ a + c₁ • M₁ a

def erase_comp : Prop :=
  ∀ (ι κ R R' : Type) [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (d : ℕ), HasDist G d →
    ∀ (S : Finset ι) (f : R → ι → E) (M : R → κ → E) (σ : R' → R),
      erase? G d S f = some M → erase? G d S (fun b => f (σ b)) = some fun b => M (σ b)

def erase_anti : Prop :=
  ∀ (ι κ R : Type) [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (d : ℕ), HasDist G d →
    ∀ (S S' : Finset ι) (f : R → ι → E) (M : R → κ → E),
      S ⊆ S' → Fintype.card ι < S.card + d → erase? G d S' f = some M → erase? G d S f = some M

end Mat

/-- Tables over the small field: if G has the distance d, erasure correction over E is erasure
correction over F. -/
def erase_lift : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (ι κ R : Type) [Fintype ι] [Fintype κ]
      (G : Matrix ι κ F) (d : ℕ),
    HasDist G d →
    ∀ (S : Finset ι) (f : R → ι → F),
      erase? (G.map (algebraMap F E)) d S (fun a => Code.liftWord E (f a)) =
        (erase? G d S f).map fun M a => Code.liftWord E (M a)

section Rd
variable (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]

/-- The standing hypotheses under a reading: it is even, the codes have their distances, and D
bounds the distance of the group from below.

A condition with parameters, which other statements and theorems use; it is not itself a claim. -/
def RdOK {A : Type} {C : A → Code.Enc F} (T : Reading C) (D : ℕ) : Prop :=
  T.Even ∧ (∀ a, HasDist (C a).G (C a).d) ∧ ∀ a, D ≤ T.mult a * (C a).d

def rd_erase_iff : Prop :=
  ∀ (A : Type) (C : A → Code.Enc F) (T : Reading C) (D : ℕ), RdOK F T D →
    ∀ (R : A → Type) (S : Finset T.P) (f : ∀ a, R a → Fin (C a).n → E)
        (M : ∀ a, R a → Fin (C a).k → E),
      T.erase? E D S f = some M ↔ Fintype.card T.P < S.card + D ∧ T.AgreesOn E S f M

def rd_decodesTo_iff_agr : Prop :=
  ∀ (A : Type) (C : A → Code.Enc F) (T : Reading C) (R : A → Type) (e : ℕ)
      (f : ∀ a, R a → Fin (C a).n → E) (M : ∀ a, R a → Fin (C a).k → E),
    T.DecodesTo E e f M ↔ Fintype.card T.P ≤ (T.agr E f M).card + e

def rd_erase_agr : Prop :=
  ∀ (A : Type) (C : A → Code.Enc F) (T : Reading C) (D e : ℕ), RdOK F T D → e < D →
    ∀ (R : A → Type) (f : ∀ a, R a → Fin (C a).n → E) (M : ∀ a, R a → Fin (C a).k → E),
      T.DecodesTo E e f M → T.erase? E D (T.agr E f M) f = some M

def rd_erase_decodesTo : Prop :=
  ∀ (A : Type) (C : A → Code.Enc F) (T : Reading C) (D e : ℕ), RdOK F T D →
    ∀ (R : A → Type) (S : Finset T.P) (f : ∀ a, R a → Fin (C a).n → E)
        (M : ∀ a, R a → Fin (C a).k → E),
      T.erase? E D S f = some M → Fintype.card T.P ≤ S.card + e → T.DecodesTo E e f M

def rd_erase_line : Prop :=
  ∀ (A : Type) (C : A → Code.Enc F) (T : Reading C) (D : ℕ), RdOK F T D →
    ∀ (R : A → Type) (S : Finset T.P) (f₀ f₁ : ∀ a, R a → Fin (C a).n → E)
        (M₀ M₁ : ∀ a, R a → Fin (C a).k → E) (c₀ c₁ : E),
      T.erase? E D S f₀ = some M₀ → T.erase? E D S f₁ = some M₁ →
      T.erase? E D S (fun a r => c₀ • f₀ a r + c₁ • f₁ a r) =
        some fun a r => c₀ • M₀ a r + c₁ • M₁ a r

/-- Component by component: under `RdOK`, on a large set of long positions, erasure correction under
T is erasure correction of each component on the image of the set. -/
def rd_erase_comps : Prop :=
  ∀ (A : Type) (C : A → Code.Enc F) (T : Reading C) (D : ℕ), RdOK F T D →
    ∀ (R : A → Type) (S : Finset T.P), Fintype.card T.P < S.card + D →
      ∀ (f : ∀ a, R a → Fin (C a).n → E) (M : ∀ a, R a → Fin (C a).k → E),
        T.erase? E D S f = some M ↔ ∀ a, (C a).erase? E (S.image (T.pos a)) (f a) = some (M a)

/-- The guard: one code, read as it stands. -/
def rd_erase_one : Prop :=
  ∀ (C₀ : Code.Enc F), HasDist C₀.G C₀.d →
    ∀ (R₀ : Type) (S : Finset (Fin C₀.n)) (f : R₀ → Fin C₀.n → E) (M : R₀ → Fin C₀.k → E),
      (Reading.one C₀).erase? E (R := fun _ => R₀) C₀.d S (fun _ => f) = some (fun _ => M) ↔
      C₀.erase? E S f = some M

end Rd
end Spec
end Cb
