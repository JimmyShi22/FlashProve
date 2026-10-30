-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/Guards.lean: AGAINST EMPTINESS, AS FAR AS IT GOES: there are files in scope that
are read, weights and randomness (member); the coins miss only other first bits (reach); a committer
that asks nothing and returns one constant fails the tie (constant_fails). Some letters meet the tie
at every Z: the written committer read off the table (tie_has_member, Johnson/Bind/Cpp/Vapid.lean).
The running committer meets the tie wherever the frame's salts have 40 bytes
(Johnson/Bind/Cpp/TheTie.lean); that they have 40 bytes at any files is no theorem of the main
library: there, at theTwin g, every theorem under the tie has a member by evaluation alone.
Statements and proofs; five statements stand as definitions of propositions: two are proved in
Johnson/Bind/Cpp/Controls.lean; no theorem proves the other three.
NOTHING HERE SAYS THAT A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM CAN BE OPENED ONLY TO THE
EXTRACTOR'S WEIGHTS, OR THAT THE EXTRACTOR GIVES THE WEIGHTS THAT THE PROGRAM COMMITTED TO.
"Binding" in this file is the opening form, BindsWith (VerifiableInference/MoreStatements.lean):
nobody opens a commitment, by naming weights and randomness from which the committer gives it, to
weights that the extractor does not give; at fixed randomness it yields that the extractor gives the
committed weights back (BindsWith.atRandomness). It is not the index binding of ZKCP/Defs.lean's
HasIndexBinding: soundness under the files' policy (G8bits, Ladder/Bits.lean) has that form, for the
claim "meets the policy" (the tie is typed at exact match: sound_iff,
VerifiableInference/Agreement.lean), and speaks of every commitment, whoever made it.

Main names (namespace Bind.Cpp).
  member: the domain is not empty: zGap is in scope and read, and there are weights and randomness.
  **reach**: THE OPENER WHO NAMES COINS NAMES EVERY pads, encoding randomness and salt bytes of the
    frame's length: each is the typed form of some coins.
  extracts_cpp: CORRECTNESS OF EXTRACTION AT EVERY RANDOMNESS: from the ID and the committer's own
    queries the extractor gives the committer's own weights back, but with probability bindingErrorInQueries
    (2^35 + 2), about 2^-89. extracts_cpp_square: at the square form, about 2^-156.
  noTwoOpenings_cpp: nobody opens one ID to two different weights, but with probability 2 ·
    bindingErrorInQueries t (about 2^-100 at t = 0): so the ID hangs on the weights.
  **constant_fails**: A NEGATIVE TEST: a committer that asks nothing and returns one constant does
    not meet the tie, at any files that are read.
  STATED HERE, PROVED IN Johnson/Bind/Cpp/Controls.lean: BlindDoesNotBind (a negative test at the
    conclusion: a committer whose value does not feel the weights does not bind) · BlindFails (a
    committer that does not read the table's entries fails the tie). PROVED NOWHERE: Feels (the ID
    feels each kind of coin) · ReachesAll (the reach in the form "every member of the written
    committer's coins whose salts begin with c"). NO THEOREM OF THE MAIN LIBRARY: NamedTests (closed
    tests at the two named sets of files, which can be evaluated and can fail).
Limits. extracts_cpp, extracts_cpp_square and noTwoOpenings_cpp take the tie and the count as
hypotheses. The tie, whole (Tie, Defs.lean), says nothing unless some Z has salts of 40 bytes in its
frame: that is NamedTests' second half, no theorem of the main library. constant_fails tries the
tie, not the conclusions. No test is run in this file.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.OfTie
import VerifiableInference.BindsAtRandomness
import VerifiableInference.NoTwoOpenings
import Fmt.Rules23Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice
open Bind.Twin (Shape Table)

/-- **THE REACH.** -/
theorem reach (Z : PublicFiles) (r : (R₀ Z).protocol.EncodingRandomness) (u : ℕ → ByteArray) (hu : ∀ j, (u j).size = saltLen Z) :
    ∃ x : Coins, riOf Z x = r ∧
      ∀ c j, saltOf Z c x j = _root_.Run.leafSalt (_root_.Run.digToBytes c) (u j) := by
  refine ⟨⟨fun b q => if h : b < 2 ^ frS.P.v ∧ q < frS.P.T.r then ofF (r.2 ⟨b, h.1⟩ ⟨q, h.2⟩)
      else 0,
    fun b j => if h : b < 2 ^ frS.P.v ∧ j < frS.P.T.l - 402653181 then ofF (r.1 ⟨b, h.1⟩ ⟨j, h.2⟩)
      else 0, u⟩, ?_, fun c j => ?_⟩
  · refine Prod.ext (funext fun b => funext fun j => ?_) (funext fun b => funext fun q => ?_)
    · show toF (if h : b.val < 2 ^ frS.P.v ∧ j.val < frS.P.T.l - 402653181 then
        ofF (r.1 ⟨b.val, h.1⟩ ⟨j.val, h.2⟩) else 0) = r.1 b j
      rw [dif_pos ⟨b.isLt, j.isLt⟩, toF_ofF]
    · show toF (if h : b.val < 2 ^ frS.P.v ∧ q.val < frS.P.T.r then
        ofF (r.2 ⟨b.val, h.1⟩ ⟨q.val, h.2⟩) else 0) = r.2 b q
      rw [dif_pos ⟨b.isLt, q.isLt⟩, toF_ofF]
  · show _root_.Run.leafSalt _ (Fmt.fit (saltLen Z) (u j)) = _
    rw [Fmt.fit_self _ _ (hu j)]

/-- The reach in the form of the written committer's coins: every member whose typed salts begin
with c is the typed form of some coins: the opener's "any coins" leaves out nothing but other first
256 bits. -/
def ReachesAll : Prop :=
  ∀ (Z : PublicFiles) (c : Digest) (y : Coins₀ Z),
    (∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → (y.1.2 j).take 256 = _root_.Run.bytesToBits
      (_root_.Run.digToBytes c)) →
    ∃ x : Coins, riOf Z x = y.1.1 ∧ ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → saltOf Z c x j = y.1.2 j

/-- **PROVED NOWHERE: the ID feels each kind of coin**: under the tie's core, two settings of coins
that part at one address that the shape has (words modulo the prime; salts on the frame's bytes)
give two IDs at some hash function, at every matrix of cells. -/
def Feels : Prop :=
  ∀ (T : Letters) (Z : PublicFiles), TieCellsAt T Z → ∀ (M : (R₀ Z).Index) (x x' : Coins),
    ((∃ b q, b < 2 ^ 11 ∧ q < 44040191 ∧ toF (x.tail b q) ≠ toF (x'.tail b q)) ∨
      (∃ b j, b < 2 ^ 11 ∧ j < 3 ∧ toF (x.pad b j) ≠ toF (x'.pad b j)) ∨
      (∃ j, j < 2 ^ 32 ∧ Fmt.fit (saltLen Z) (x.salt j) ≠ Fmt.fit (saltLen Z) (x'.salt j))) →
    ∃ hash, (T.id shapeFull Z.pol Z.lay Z.KL (x.table (entryOfCells M))).evaluate hash ≠
      (T.id shapeFull Z.pol Z.lay Z.KL (x'.table (entryOfCells M))).evaluate hash

/- From here on Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀
  FlashProve.thePlan FlashProve.theItem LayoutsByPublicReading.commitAtCoins

variable (T : Letters)
  (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- The domain is not empty: files in scope that are read, weights, randomness. -/
theorem member : ∃ pp, InScope zGap = true ∧ readFiles zGap = .ok pp ∧
    Nonempty (ModelWeights (settingsOfRead pp) × Rand) :=
  let ⟨sc, pp, hr, _⟩ := VerifierAndGoals.filesRead.other
  ⟨pp, sc, hr, ⟨(nonempty_modelWeights (valid_of_read hr)).some, .inl 0⟩⟩

/-- **The extractor gives the committer's own weights back**, from the commitment and that run's
queries, at every weights and every randomness, but with probability bindingErrorInQueries at the run's
count. -/
theorem extracts_cpp (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (tie : TieAt T Z) (cnt : CountAt T Z) (w : ModelWeights (settingsOfRead pp)) (ρ : Rand) :
    Prob ((atSecondHashFunction (theCpp T prove)).commit Z (settingsOfRead pp) w ρ).toRandomized.withQueryLog
        {o | (atSecondHashFunction (theCpp T prove)).extractor Z (settingsOfRead pp) o.1 o.2 ≠ some w}
      ≤ bindingErrorInQueries (twinBudget + 2) :=
  (bindsAtZ_cpp T prove Z pp hr tie cnt).2.atRandomness w ρ (twinBudget + 2)
    (commit_count T Z cnt (settingsOfRead pp) w ρ)

/-- The same at the square form: 3 (2^35 + 4 + 2 · 2^48 + 2)² / 2^256, about 2^-156. -/
theorem extracts_cpp_square (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (tie : TieAt T Z) (cnt : CountAt T Z) (w : ModelWeights (settingsOfRead pp)) (ρ : Rand) :
    Prob ((atSecondHashFunction (theCpp T prove)).commit Z (settingsOfRead pp) w ρ).toRandomized.withQueryLog
        {o | (atSecondHashFunction (theCpp T prove)).extractor Z (settingsOfRead pp) o.1 o.2 ≠ some w}
      ≤ epsBind honestBudget (twinBudget + 2 + 2) :=
  (bindsWith_of_tieAt T prove Z pp hr tie).atRandomness w ρ (twinBudget + 2)
    (commit_count T Z cnt (settingsOfRead pp) w ρ)

/-- Nobody opens one ID to two different weights, each at a seed or coins of its own pick, but with
probability 2 · bindingErrorInQueries t. -/
theorem noTwoOpenings_cpp (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (tie : TieAt T Z) (cnt : CountAt T Z) :
    NoTwoOpenings (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z (settingsOfRead pp))
      fun t => 2 * bindingErrorInQueries t :=
  (bindsAtZ_cpp T prove Z pp hr tie cnt).2.noTwoOpenings

/-- **A NEGATIVE TEST: a committer that asks nothing and returns one constant does not meet the
tie**, at files that are read: at the hash function whose every answer is the complement of its
constant, the written committer's value is that complement. -/
theorem constant_fails (k : Commitment) (hk : ∀ sh p l K t, T.id sh p l K t = .done k)
    (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) : ¬ TieAt T Z := by
  intro tie
  have h := tie (settingsOfRead pp) (nonempty_modelWeights (valid_of_read hr)).some
    ⟨fun _ _ => 0, fun _ _ => 0, fun _ => ByteArray.empty⟩ (placeHolderNumberCoins.b₀ Z)
    (fun _ i => !(k i))
  rw [hk, evaluate_commitAtCoins] at h
  generalize ((T₀ Z).keyAtCoins _ _ _ _).det _ = key at h
  have ht := (bindLaws_the placeHolderNumberCoins hE_the Z pp hr).total key
  rw [T_the] at ht
  unfold ZKCP.digestUnder at h
  cases he : (T₀ Z).encT key with
  | none => exact ht he
  | some code =>
    rw [he] at h
    have h0 : (!(k 0)) = k 0 := congrFun h 0
    cases hk0 : k 0 <;> simp [hk0] at h0

/-- **A NEGATIVE TEST AT THE CONCLUSION: a committer whose value does not feel the weights does not
bind**, at a Z that is read. Proved: blindDoesNotBind (Johnson/Bind/Cpp/Controls.lean). -/
def BlindDoesNotBind : Prop :=
  ∀ (T : Letters)
    (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
      List Token → RandomizedAlgorithm flashProveDescription.Form)
    (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), readFiles Z = .ok pp → CountAt T Z →
    (∀ (w w' : ModelWeights (settingsOfRead pp)) (ρ : Rand) (hash : Hash),
      (cppCommit T Z (settingsOfRead pp) w ρ).evaluate hash =
        (cppCommit T Z (settingsOfRead pp) w' ρ).evaluate hash) →
    ¬ BindsWith (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z (settingsOfRead pp))
      ((atSecondHashFunction (theCpp T prove)).extractor Z (settingsOfRead pp)) bindingErrorInQueries

/-- **A NEGATIVE TEST: a committer that does not read the table's entries does not meet the tie
together with the count**, at a Z that is read. Proved: blindFails (Johnson/Bind/Cpp/Controls.lean).
-/
def BlindFails : Prop :=
  ∀ (T : Letters), (∀ sh p l K (t t' : Table), t.tail = t'.tail → t.pad = t'.pad →
      t.salt = t'.salt → T.id sh p l K t = T.id sh p l K t') →
    ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), readFiles Z = .ok pp → CountAt T Z → ¬ TieAt T Z

/-- **NO THEOREM OF THE MAIN LIBRARY: closed tests that can be evaluated, and can fail**: at the
two named sets of public files protocolDataWellFormed passes, and the frame's salts have 40 bytes. -/
def NamedTests : Prop :=
  (protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true ∧ protocolDataWellFormed (asDescriptionFiles zGap) = true) ∧ SaltAt storedPublicFiles ∧ SaltAt zGap

end Bind.Cpp

end

#print axioms Bind.Cpp.reach
#print axioms Bind.Cpp.member
#print axioms Bind.Cpp.extracts_cpp
#print axioms Bind.Cpp.extracts_cpp_square
#print axioms Bind.Cpp.noTwoOpenings_cpp
#print axioms Bind.Cpp.constant_fails
