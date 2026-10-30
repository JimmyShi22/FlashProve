-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/KeySeat.lean: the key file's seat of the description (`FlashProve.keyDataAndDecisionOrRefusalAt`,
Johnson/Goal/Description/KeyFold.lean) is the same at two parameter files whose public parts differ
only in the three numbers C, theta, cap of the acceptance policy.

The seat is `Key.keyDataAndDecisionAtFixedDigest X lay` (Johnson/Desc/Key/Slot.lean) at the public part X that
`publicOfO o` returns. `keyDataAndDecisionAtFixedDigest` makes the chains and the links' records of X, cuts the sendings,
and lays the key file's description of them.

How. The chains: `Verify.chainsOf` is its plain copy (`ProofFile.Law.chainsOf_eq`,
Johnson/Desc/ProofFile/Law/PlainIsPlanned.lean), and the copy does not read the three numbers
(`chainsOf_wp`, Johnson/LPFPol/PubPlain.lean). The links' records: `Verify.builtOf` returns at both
or refuses at both with one name (`ProofFile.Law.builtOf_eq`, `builtOf_wp`); the records themselves are
not compared. The key file's piece gives one value at two planner's records that differ in the
links' records and in the three numbers alone (`laidOfMade_free`: by unfolding).

Main names.
* `laidFixed_withPol`: `Key.keyDataAndDecisionAtFixedDigest (X.withPol C theta cap) lay = Key.keyDataAndDecisionAtFixedDigest X lay`, at every
  X, lay and all numbers: values and refusals alike. No premise.
* `theKeyLaidAt_withPol`: THE LAW. Premises: hX, `publicOfO o` returns X at Zk's three files; hX',
  it returns `X.withPol C theta cap` at pol' with Zk's two other files. Then the seat at
  `{ Zk with pol := pol' }` is the seat at Zk. o: any function in the second hash function's place.
* `chainsOf_pol`, `builtOf_pol`, `laidOfMade_door`, `laidOfMade_free`: the steps.
* `bind_same`, `bind_of_map`, `bind_bind`, `bind_pure`: on steps of `Except`.

Limits.
* hX and hX' are premises. Nothing here shows that `publicOfO` returns at any file.
* The law is an equation of two values of the seat. It does not say that the seat returns.
* Nothing on what the seat's decision says. Nothing on soundness, on hiding or on a security level.

For proofs only; no program imports this file.


-/
import Johnson.LPFPol.PubPlain
import Johnson.Desc.ProofFile.Law.PlainIsPlanned
import Johnson.Goal.Description.KeyFold

set_option autoImplicit false

namespace LPFPol

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Key.keyDataAndDecisionAtFixedDigest Key.keyDataAndDecisionAtDigest Key.madeAt Key.keyDataAndDecisionOfPlannerAnswer)
open VerifiableInference.PlanWritten (publicOfO)

/-- The seven chains do not read the three numbers: values and refusals alike. -/
theorem chainsOf_pol (X : Verify.Public) (C theta cap : Nat) (lay : Option ByteArray)
    (c : ByteArray) : Verify.chainsOf (X.withPol C theta cap) lay c = Verify.chainsOf X lay c := by
  rw [← ProofFile.Law.chainsOf_eq, ← ProofFile.Law.chainsOf_eq, chainsOf_wp]

/-- The links' records, each with a fixed value in the place of its check, do not read the three
numbers: values and refusals alike. -/
theorem builtOf_pol (X : Verify.Public) (C theta cap : Nat) (ch : Verify.Chains) :
    (Verify.builtOf (X.withPol C theta cap) ch).map ProofFile.Law.blankB =
      (Verify.builtOf X ch).map ProofFile.Law.blankB := by
  rw [← ProofFile.Law.builtOf_eq, ← ProofFile.Law.builtOf_eq, builtOf_wp]

/-! ### steps of `Except` -/

/-- Two runs of one first step, whose second steps agree at every value. -/
theorem bind_same {ε α β : Type} {x : Except ε α} {k k' : α → Except ε β}
    (hk : ∀ a, k' a = k a) : (x >>= k') = (x >>= k) := by
  cases x with
  | error e => rfl
  | ok a => exact hk a

/-- Two runs whose first steps agree after a map m, and whose second steps agree at all pairs of
values. -/
theorem bind_of_map {ε α β γ : Type} {x x' : Except ε α} {m : α → γ} {k k' : α → Except ε β}
    (hm : x'.map m = x.map m) (hk : ∀ a a', k' a' = k a) : (x' >>= k') = (x >>= k) := by
  cases x with
  | error e =>
    cases x' with
    | error e' =>
      cases hm
      rfl
    | ok a' => cases hm
  | ok a =>
    cases x' with
    | error e' => cases hm
    | ok a' => exact hk a a'

/-- A step behind two steps is a step behind the second. -/
theorem bind_bind {ε α β γ : Type} (x : Except ε α) (g : α → Except ε β) (K : β → Except ε γ) :
    Except.bind (x >>= g) K = (x >>= fun a => Except.bind (g a) K) := by
  cases x <;> rfl

/-- A step behind a value. -/
theorem bind_pure {ε β γ : Type} (b : β) (K : β → Except ε γ) :
    Except.bind (pure b) K = K b := rfl

/-! ### the key file's piece -/

/-- The key file's piece does not read the public part that is handed to the door. -/
theorem laidOfMade_door (X1 X2 : Verify.Public) (lay : ByteArray) :
    Key.keyDataAndDecisionOfPlannerAnswer X1 lay = Key.keyDataAndDecisionOfPlannerAnswer X2 lay := rfl

/-- The key file's piece reads neither the links' records nor the three numbers. -/
theorem laidOfMade_free (X0 : Verify.Public) (lay : ByteArray) (X : Verify.Public)
    (C theta cap : Nat) (cfg : ByteArray) (ch : Verify.Chains) (b b' : Stages.LinksH)
    (k p : Johnson.G.ChainSends × Johnson.G.ChainSends × Johnson.G.ChainSends) :
    Key.keyDataAndDecisionOfPlannerAnswer X0 lay
        ⟨{ X := X.withPol C theta cap, cfg := cfg, chains := ch, built := b' }, k, p⟩ =
      Key.keyDataAndDecisionOfPlannerAnswer X0 lay ⟨{ X := X, cfg := cfg, chains := ch, built := b }, k, p⟩ := rfl

/-- **The key file's piece at the fixed digest does not read the three numbers.** -/
theorem laidFixed_withPol (X : Verify.Public) (C theta cap : Nat) (lay : ByteArray) :
    Key.keyDataAndDecisionAtFixedDigest (X.withPol C theta cap) lay = Key.keyDataAndDecisionAtFixedDigest X lay := by
  unfold Key.keyDataAndDecisionAtFixedDigest Key.keyDataAndDecisionAtDigest
  rw [laidOfMade_door (X.withPol C theta cap) X lay]
  unfold Key.madeAt
  rw [chainsOf_pol, bind_bind, bind_bind]
  refine bind_same fun ch => ?_
  try dsimp only
  rw [bind_bind, bind_bind]
  refine bind_of_map (builtOf_pol X C theta cap ch) fun b b' => ?_
  try dsimp only
  rw [bind_bind, bind_bind]
  refine bind_same fun l => ?_
  try dsimp only
  rcases l with
    _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, t⟩⟩⟩⟩⟩⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · try dsimp only
    rw [bind_pure, bind_pure]
    exact laidOfMade_free X lay X C theta cap _ ch b b' (a0, a1, a2) (a4, a5, a6)
  · rfl

/-- **THE LAW.** Premises: hX, `publicOfO o` returns X at Zk's three files; hX', it returns
`X.withPol C theta cap` at pol' with Zk's scale file and layout file. Then the key file's seat at
`{ Zk with pol := pol' }` is the seat at Zk. -/
theorem theKeyLaidAt_withPol {o : VerifierAndGoals.SecondHashFunctionType} {Zk : OnBytes.K.Pub} {pol' : ByteArray}
    {X : Verify.Public} {C theta cap : Nat}
    (hX : publicOfO o Zk.pol Zk.KL (some Zk.lay) = .ok X)
    (hX' : publicOfO o pol' Zk.KL (some Zk.lay) = .ok (X.withPol C theta cap)) :
    FlashProve.keyDataAndDecisionOrRefusalAt o { Zk with pol := pol' } = FlashProve.keyDataAndDecisionOrRefusalAt o Zk := by
  unfold FlashProve.keyDataAndDecisionOrRefusalAt
  show (publicOfO o pol' Zk.KL (some Zk.lay)).bind (fun X => Key.keyDataAndDecisionAtFixedDigest X Zk.lay) = _
  rw [hX, hX']
  exact laidFixed_withPol X C theta cap Zk.lay

end LPFPol

#print axioms LPFPol.laidFixed_withPol
#print axioms LPFPol.theKeyLaidAt_withPol
