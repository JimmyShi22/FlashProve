-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/OnRange.lean: INDEX PRIVACY ON A RANGE OF INDICES, for schemes over a family of typed oracles
(ZKCP/Gen.lean) and over one hash function (ZKCP/Defs.lean); and THE TWO STEPS of the library that
carry index privacy upward, FOR A RANGE.

General definitions and theorems with their proofs. This file states no goal of the release.

Why. The library's property of index privacy speaks of every index of the scheme's type. An
environment that names no instance is valid at every index, so the key alone must be simulated at
every index. Where the type holds indices at which the honest committer cannot make a key that a
simulator could make, the property fails for a reason that is of no interest. So here the property
is asked on a range ok, a property of indices.

How. A scheme's index type stands in its committer alone. The scheme with its committer read through
the inclusion of the indices with ok (rangeArg) has the same types of keys and proofs, the same
prover and the same verifier; at an index of the range its real experiment IS the scheme's
(realLoop_range, by an induction on the adversary; realExp_range), and the ideal experiment reads of
the index its public parameters alone. So index privacy on the range IS the library's property of
that scheme (privacyFor_range, privacyOn_iff), and a theorem of the library
that carries its property from one scheme to another carries the property on a range, if it commutes
with that reading. Both steps do, by unfolding.

  Gen.PrivacyOn R A B Sim ζ ok     at every index of ok, every valid environment:
                                   Gen.PrivacyFor. At ok := all: Gen.HasIndexPrivacyWith.
  Gen.rangeRel, Gen.rangeArg, Gen.realLoop_range, Gen.realExp_range, Gen.privacyFor_range,
  Gen.privacyOn_iff, Gen.privacyOn_all
  Gen.privacyOn_congr, privacyOn_toPair   index privacy reads a pair of relations through "yes" and
                                   the public parameters alone.
  StrongPrivacyOn R A S ζ ok       the same over one hash function, one request a call.
  rangeRel, rangeArg, realLoop_range, realExp_range, privacyFor_range, strongPrivacyOn_iff
  privacyOn_overOne    THE STEP TO ONE HASH FUNCTION (Rom.privacy_overOne, Rom/ExitPriv.lean).
  strongPrivacyOn_of_gen   THE STEP TO THE FORM OF ZKCP/Defs.lean
                       (ZKCP.SpecialAny.strongPrivacy_of_gen, ZKCP/SpecialAny.lean).

Sources. The proof of Gen.realLoop_range is that of the library's realLoop_withC (Rom/Blocks.lean),
which lays another committer into a scheme: the same induction on the adversary, word for word.
realLoop_range over one hash function is the same induction in the form of ZKCP/Defs.lean.

Limits. The range is a letter: at the empty range, or at a range with one index, the property is
idle. The simulator is an argument: whoever writes "there is a simulator" must write it OUTSIDE the
range (one simulator for all indices of the range).
Terms: lean/GLOSSARY.md.

-/
import Rom.ExitPriv
import ZKCP.SpecialAny

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace ZKCP

variable {I X W PP IVK ISK Pf : Type}

namespace Gen
variable {S : Rom.OSpec}

/-- **Index privacy on a range of indices**, simulator named. -/
def PrivacyOn (R : RelPair I X W PP) (A : Arg S I X W IVK ISK Pf) (B : ℕ)
    (Sim : Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) : Prop :=
  ∀ i, ok i → ∀ Z : ViewEnv S IVK X W Pf, Z.IsValid R B i → PrivacyFor R A Sim ζ i Z

/-- The relations on the indices with ok. -/
def rangeRel (R : RelPair I X W PP) (ok : I → Prop) : RelPair {i // ok i} X W PP :=
  ⟨fun j => R.yes j.1, fun j => R.no j.1, fun j => R.sub j.1, fun j => R.pp j.1⟩

/-- The scheme on the indices with ok: the committer read through the inclusion; prover, verifier
and all types of keys and proofs are A's. -/
def rangeArg (A : Arg S I X W IVK ISK Pf) (ok : I → Prop) : Arg S {i // ok i} X W IVK ISK Pf :=
  ⟨fun j => A.C j.1, A.P, A.V⟩

/-- Behind the key the two real experiments are one program. -/
theorem realLoop_range (A : Arg S I X W IVK ISK Pf) (ok : I → Prop) (Z : ViewEnv S IVK X W Pf)
    (isk : ISK) (V : AdvVerifier S X Pf) : ∀ (n : ℕ) (v : View S IVK X Pf),
    realLoop (rangeArg A ok) Z isk V n v = realLoop A Z isk V n v := by
  induction V with
  | halt => intro n v; rfl
  | query o q k ih =>
    intro n v
    simp only [realLoop]
    exact congrArg _ (funext fun r => ih r n _)
  | sample m k ih =>
    intro n v
    simp only [realLoop]
    exact congrArg _ (funext fun r => ih r n _)
  | request k ih =>
    intro n v
    cases n with
    | zero => rfl
    | succ n =>
      simp only [realLoop]
      cases Z v with
      | none => rfl
      | some b => exact congrArg _ (funext fun πs => ih _ n _)

/-- At an index of the range the real experiment of the scheme on the range is the scheme's. -/
theorem realExp_range (A : Arg S I X W IVK ISK Pf) (ok : I → Prop)
    (Vt : IVK → AdvVerifier S X Pf) (Z : ViewEnv S IVK X W Pf) (j : {i // ok i}) (N : ℕ) :
    realExp (rangeArg A ok) Vt Z j N = realExp A Vt Z j.1 N := by
  show (A.C j.1).bind (fun key =>
      realLoop (rangeArg A ok) Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩) =
    (A.C j.1).bind fun key => realLoop A Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩
  exact congrArg _ (funext fun key => realLoop_range A ok Z key.2 _ N _)

/-- The requirement for one index and one environment is the same for the two schemes. -/
theorem privacyFor_range (R : RelPair I X W PP) (A : Arg S I X W IVK ISK Pf)
    (Sim : Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) (j : {i // ok i})
    (Z : ViewEnv S IVK X W Pf) :
    PrivacyFor (rangeRel R ok) (rangeArg A ok) Sim ζ j Z ↔ PrivacyFor R A Sim ζ j.1 Z := by
  unfold PrivacyFor
  simp only [realExp_range]
  rfl

/-- **Index privacy on a range is the library's property of the scheme on the range.** -/
theorem privacyOn_iff (R : RelPair I X W PP) (A : Arg S I X W IVK ISK Pf) (B : ℕ)
    (Sim : Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) :
    PrivacyOn R A B Sim ζ ok ↔ HasIndexPrivacyWith (rangeRel R ok) (rangeArg A ok) B Sim ζ :=
  ⟨fun h j Z hZ => (privacyFor_range R A Sim ζ ok j Z).2 (h j.1 j.2 Z hZ),
    fun h i hi Z hZ => (privacyFor_range R A Sim ζ ok ⟨i, hi⟩ Z).1 (h ⟨i, hi⟩ Z hZ)⟩

/-- At the range of all indices it is the library's property. -/
theorem privacyOn_all (R : RelPair I X W PP) (A : Arg S I X W IVK ISK Pf) (B : ℕ)
    (Sim : Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) :
    PrivacyOn R A B Sim ζ (fun _ => True) ↔ HasIndexPrivacyWith R A B Sim ζ :=
  ⟨fun h i Z hZ => h i trivial Z hZ, fun h i _ Z hZ => h i Z hZ⟩

/-- **Index privacy reads a pair of relations through "yes" and the public parameters alone.** -/
theorem privacyOn_congr (R R' : RelPair I X W PP) (hy : ∀ i x w, R.yes i x w ↔ R'.yes i x w)
    (hp : ∀ i, R.pp i = R'.pp i) (A : Arg S I X W IVK ISK Pf) (B : ℕ)
    (Sim : Simulator S PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) :
    PrivacyOn R A B Sim ζ ok ↔ PrivacyOn R' A B Sim ζ ok := by
  have hv : ∀ (Z : ViewEnv S IVK X W Pf) (i : I), Z.IsValid R B i ↔ Z.IsValid R' B i :=
    fun Z i =>
      ⟨fun h v b hb => ⟨(h v b hb).1, fun xw hx => (hy i xw.1 xw.2).1 ((h v b hb).2 xw hx)⟩,
        fun h v b hb => ⟨(h v b hb).1, fun xw hx => (hy i xw.1 xw.2).2 ((h v b hb).2 xw hx)⟩⟩
  have hf : ∀ (i : I) (Z : ViewEnv S IVK X W Pf),
      PrivacyFor R A Sim ζ i Z ↔ PrivacyFor R' A Sim ζ i Z := by
    intro i Z
    unfold PrivacyFor idealExp
    rw [hp i]
  exact ⟨fun h i hi Z hZ => (hf i Z).1 (h i hi Z ((hv Z i).2 hZ)),
    fun h i hi Z hZ => (hf i Z).2 (h i hi Z ((hv Z i).1 hZ))⟩

end Gen

variable {lam : ℕ}

/-- **Strong index privacy on a range of indices**, over one hash function, simulator named. -/
def StrongPrivacyOn (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)
    (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) : Prop :=
  ∀ i, ok i → ∀ Z : ViewEnv lam IVK X W Pf, Z.IsValid R i → PrivacyFor R A S ζ i Z

/-- The relation on the indices with ok. -/
def rangeRel (R : IndexedRelation I X W PP) (ok : I → Prop) : IndexedRelation {i // ok i} X W PP :=
  ⟨fun j => R.rel j.1, fun j => R.pp j.1⟩

/-- The scheme on the indices with ok. -/
def rangeArg (A : Arg lam I X W IVK ISK Pf) (ok : I → Prop) : Arg lam {i // ok i} X W IVK ISK Pf :=
  ⟨fun j => A.C j.1, A.P, A.V⟩

theorem realLoop_range (A : Arg lam I X W IVK ISK Pf) (ok : I → Prop)
    (Z : ViewEnv lam IVK X W Pf) (isk : ISK) (V : AdvVerifier lam X Pf) :
    ∀ (n : ℕ) (v : View lam IVK X Pf),
      realLoop (rangeArg A ok) Z isk V n v = realLoop A Z isk V n v := by
  induction V with
  | halt => intro n v; rfl
  | query q k ih =>
    intro n v
    simp only [realLoop]
    exact congrArg _ (funext fun r => ih r n _)
  | sample m k ih =>
    intro n v
    simp only [realLoop]
    exact congrArg _ (funext fun r => ih r n _)
  | request k ih =>
    intro n v
    cases n with
    | zero => rfl
    | succ n =>
      simp only [realLoop]
      cases Z v with
      | none => rfl
      | some xw => exact congrArg _ (funext fun π => ih _ _ n _)

theorem realExp_range (A : Arg lam I X W IVK ISK Pf) (ok : I → Prop)
    (Vt : IVK → AdvVerifier lam X Pf) (Z : ViewEnv lam IVK X W Pf) (j : {i // ok i}) (N : ℕ) :
    realExp (rangeArg A ok) Vt Z j N = realExp A Vt Z j.1 N := by
  show (A.C j.1).bind (fun key =>
      realLoop (rangeArg A ok) Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩) =
    (A.C j.1).bind fun key => realLoop A Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩
  exact congrArg _ (funext fun key => realLoop_range A ok Z key.2 _ N _)

theorem privacyFor_range (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)
    (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) (j : {i // ok i})
    (Z : ViewEnv lam IVK X W Pf) :
    PrivacyFor (rangeRel R ok) (rangeArg A ok) S ζ j Z ↔ PrivacyFor R A S ζ j.1 Z := by
  unfold PrivacyFor
  simp only [realExp_range]
  rfl

theorem strongPrivacyOn_iff (R : IndexedRelation I X W PP) (A : Arg lam I X W IVK ISK Pf)
    (S : Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) :
    StrongPrivacyOn R A S ζ ok ↔ HasStrongIndexPrivacyWith (rangeRel R ok) (rangeArg A ok) S ζ :=
  ⟨fun h j Z hZ => (privacyFor_range R A S ζ ok j Z).2 (h j.1 j.2 Z hZ),
    fun h i hi Z hZ => (privacyFor_range R A S ζ ok ⟨i, hi⟩ Z).1 (h ⟨i, hi⟩ Z hZ)⟩

/-- **The step to one hash function, on a range.** -/
theorem privacyOn_overOne {S : Rom.OSpec} (m : Rom.OracleCoding S lam) (R : Gen.RelPair I X W PP)
    (A : Gen.Arg S I X W IVK ISK Pf) (B : ℕ) (Sim : Gen.Simulator S PP IVK X Pf)
    (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) (h : Gen.PrivacyOn R A B Sim ζ ok) :
    Gen.PrivacyOn R (Rom.schemeOverOneHashFunction m A) B (Rom.simOne m Sim) ζ ok :=
  (Gen.privacyOn_iff R (Rom.schemeOverOneHashFunction m A) B (Rom.simOne m Sim) ζ ok).2
    (Rom.privacy_overOne m (Gen.rangeRel R ok) (Gen.rangeArg A ok) B Sim ζ
      ((Gen.privacyOn_iff R A B Sim ζ ok).1 h))

/-- At a pair of relations, index privacy on a range is that at the one relation "yes" taken twice:
the form in which the step to ZKCP/Defs.lean takes it. -/
theorem privacyOn_toPair {S : Rom.OSpec} (R : Gen.RelPair I X W PP)
    (A : Gen.Arg S I X W IVK ISK Pf) (B : ℕ) (Sim : Gen.Simulator S PP IVK X Pf)
    (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) :
    Gen.PrivacyOn R A B Sim ζ ok ↔ Gen.PrivacyOn (Special.toPair ⟨R.yes, R.pp⟩) A B Sim ζ ok :=
  Gen.privacyOn_congr R _ (fun _ _ _ => Iff.rfl) (fun _ => rfl) A B Sim ζ ok

/-- If G, called with one request, is A, the same holds of the two schemes on the range. -/
theorem agrees_range {G : Gen.Arg (Rom.rom lam) I X W IVK ISK Pf} {A : Arg lam I X W IVK ISK Pf}
    (h : SpecialAny.Agrees G A) (ok : I → Prop) :
    SpecialAny.Agrees (Gen.rangeArg G ok) (rangeArg A ok) :=
  ⟨fun j => h.C j.1, h.V, h.P⟩

/-- **The step to the form of ZKCP/Defs.lean, on a range.** -/
theorem strongPrivacyOn_of_gen (R : IndexedRelation I X W PP)
    {G : Gen.Arg (Rom.rom lam) I X W IVK ISK Pf} {A : Arg lam I X W IVK ISK Pf}
    (h : SpecialAny.Agrees G A) (Sim : Gen.Simulator (Rom.rom lam) PP IVK X Pf)
    (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop)
    (H : Gen.PrivacyOn (Special.toPair R) G 1 Sim ζ ok) :
    StrongPrivacyOn R A (Special.simOf Sim) ζ ok :=
  (strongPrivacyOn_iff R A (Special.simOf Sim) ζ ok).2
    (SpecialAny.strongPrivacy_of_gen (rangeRel R ok) (agrees_range h ok) Sim ζ
      ((Gen.privacyOn_iff (Special.toPair R) G 1 Sim ζ ok).1 H))

end ZKCP

#print axioms ZKCP.Gen.privacyOn_iff
#print axioms ZKCP.strongPrivacyOn_iff
#print axioms ZKCP.Gen.privacyOn_congr
#print axioms ZKCP.privacyOn_toPair
#print axioms ZKCP.privacyOn_overOne
#print axioms ZKCP.strongPrivacyOn_of_gen
