-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Idle.lean: AN IDLE MEMBER of the structure of the honest side's letters
(HonestSide, Johnson/WholeKey/Defs.lean), at every object with out-of-domain samples; and A FOE: the
statement that index privacy of the scheme with the whole key published FAILS at an object whose
out-of-domain answers tell two indices apart.

General definitions and one statement (Spec.told_not_private), whose proof is in
Johnson/WholeKey/Foes.lean. This file states no goal of the release.

Why an idle member. A structure that nothing can fill makes every statement over it true and empty.
The structure HonestSide asks no law, so it is filled at every object, given a body of a leaf:
strategies that send each round's fixed message, no stop, one nonce a search, one copy, coins with
one value each. The scheme at it is a scheme, and it proves nothing: a statement on completeness or
on index privacy that is to say something must ask laws that this member does not meet, or must be
worthless at it in a way that its bound shows.

Why a foe. A statement of index privacy has to be able to fail. Here the committer publishes the
honest out-of-domain answers in the key. At an object whose answers tell the index i from the index
i' (the plainest case: the answer IS the index), the key alone tells them apart, while a simulator
is handed nothing that hangs on the index. So no simulator and no bound below 1/2 at (0 queries, 0
sessions) meets the definition, whatever the honest side's other letters are: that is the statement
below (proved: told_not_private, Johnson/WholeKey/Foes.lean). A theorem that concludes index privacy
of argW from premises on the object must therefore have a premise that such an object fails: in the
interface it is the clause that the answers together with a bounded number of positions of the
encoded index have a law that does not hang on the index (ReadsR.hidE, Hiop/RecInterface.lean).

Main names (namespace OnBytes.WholeKey).
  Plays.idle, coinsIdle, HonestSide.idle   the idle member.
  Spec.told_not_private   the foe, as a statement.

Limits. The foe is a committer's leak. A prover's leak: said_not_private,
Johnson/WholeKey/Foes.lean.
Sources. The form of Spec.told_not_private's conclusion, "1 ≤ ζ + ζ at named numbers of queries and
requests", is that of the library's negative tests (nosy_not_private, ZKCP/GenSanity.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Defs
import ZKCP.OnRange

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ}

/-- Strategies that send each round's fixed message, whatever they are handed; they never stop. -/
def Plays.idle (L : HolographicProtocol I X) : Plays L Unit Unit Unit where
  T := fun _ _ _ _ => Strat.dflt _ ()
  Lk := fun _ _ _ _ => Strat.dflt _ ()
  B := fun _ _ _ _ _ _ => Strat.dflt _ ()
  stopT := fun _ _ _ _ => false
  stopL := fun _ _ _ _ => false
  stopB := fun _ _ _ _ _ _ => false

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}

/-- Coins of a compiled run with nothing in them: empty salts, the given body as padding, slot 0, no
sibling digest. -/
def coinsIdle (b₀ : Bd) : Coins lam (typedOracleCarrier L Bd aT aL) :=
  ⟨[], fun _ _ _ _ => [], b₀, 0, [], []⟩

/-- **The idle member**, from a body of a leaf. -/
def HonestSide.idle (b₀ : Bd) : HonestSide lam L Bd aT aL where
  KT := Unit
  KL := Unit
  KB := Unit
  st := Plays.idle L
  b₀ := b₀
  capT := fun _ => 0
  capL := fun _ => 0
  capB := fun _ => 0
  M := 0
  nm := id
  RV := Unit
  rvT := fun _ => ()
  rvL := fun _ => ()
  rvB := fun _ => ()
  startT := fun _ _ _ _ => []
  startL := fun _ _ _ _ => []
  startB := fun _ _ _ _ => []
  pvT := fun _ => ()
  pvL := fun _ => ()
  pvB := fun _ => ()
  rtail := fun _ => []
  nR := 0
  nK := 0
  nJ := 0
  fill := []
  ri := ⟨0, fun _ => Classical.arbitrary L.EncodingRandomness⟩
  sl := ⟨0, fun _ _ => []⟩
  kT := ⟨0, fun _ => ()⟩
  kL := ⟨0, fun _ => ()⟩
  kB := ⟨0, fun _ => ()⟩
  coT := ⟨0, fun _ => coinsIdle b₀⟩
  coL := ⟨0, fun _ => coinsIdle b₀⟩
  coB := ⟨0, fun _ => coinsIdle b₀⟩

/-- **The foe**, as a statement (its proof: told_not_private, Johnson/WholeKey/Foes.lean). If a test
on out-of-domain answers says yes to every honest answer of the index i and no to every honest
answer of the index i', then the scheme with the whole key published has index privacy ON NO RANGE
THAT HOLDS BOTH, with no simulator, at a bound below 1/2 at (0, 0): for all wires, all letters of
the honest side, all relations, all bounds on a batch. -/
def Spec.told_not_private : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (h : HonestSide lam L Bd aT aL)
    (Ryes Rno : I → X → Prop) (sub : ∀ i x, Ryes i x → Rno i x) (B : ℕ)
    (Sim : ZKCP.Gen.Simulator (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) Unit (FullKey lam L aT aL) X
      (RequestProof lam L))
    (ζ : ℕ → ℕ → ℝ≥0∞) (φ : L.OutOfDomainAnswer → Bool) (ok : I → Prop) (i i' : I),
    ok i → ok i' →
    (∀ r s, φ (L.honestOutOfDomainAnswer i r s) = true) → (∀ r s, φ (L.honestOutOfDomainAnswer i' r s) = false) →
    ZKCP.Gen.PrivacyOn (relPair Ryes Rno sub) (argW W S cA r₀ p h) B Sim ζ ok →
      1 ≤ ζ 0 0 + ζ 0 0

end OnBytes.WholeKey
