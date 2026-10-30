-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeySeatAt.lean: the key file's description as a value of the three public files, made by the calls that
make the verifier's seat, with the one theorem that ties the two where the seat is live.

Why. `key_sourced` (E2E/KeyPublic.lean) says that where the seat is live there are X, N, P with `KeySourced`:
an existence. A file that must write the key file's prover at every value Z has no term for that description.
The seat's own text (`keyDataAndDecisionAtFixedDigest`) keeps the data and the decision and drops the description, so it cannot be
read off that value: it has to be made by the same calls.

Main names.
  `KeySeat`: what the description is made of: the source, the numbers of the ranges' place, the later places.
  `keySeatAt`: those, from Z, by `publicOfO`, `madeAt` at `fixedDigest`, `sourceOf`, `rangesNumbers`,
    `laterPlaces`: the calls and the order of `KeySourced`'s field `source`; an error where one refuses.
  `KeySeat.description`, `.start`, `.testU`, `.testOmega`: the description, the shared chain's first state
    as a function of the key, and the numbers of the two shared tests' places.
  `keySeatAt_live`: where the seat is live, `keySeatAt` returns, and at what it returns `KeySourced` holds.
  `keySeatAt_of_sourced`, `keySourced_unique`, `KeySeat.ext_sourced`: at most one seat is sourced at Z, and it is what
    `keySeatAt` returns.
  `keyDesc_of_named`: a seat that is only named has the sourced seat's description; its letters may differ.

What stays open. `keySeatAt` runs none of the tests of `KeyNamed` (`planOk`, `wantedOk`, `owedOk`, `lawsAsk`), so
it may return where the seat refuses: `keySeatAt_live` speaks of the live case alone. The description stands at
`fixedDigest`, as the verifier's seat does, so the source's parameter bytes are spelled at that constant. The
values are of use at the full size alone: `KeySourced` says no more. No prover is named here.

No statement here names a coin, and none is a law over coins.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyPublic
import E2E.KeyHonest
import Johnson.Desc.K12.AtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLay
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Source LaterPlaces madeAt fixedDigest sourceOf rangesNumbers laterPlaces)
open AtPublicFiles.AtFiles (KeyInst keyFileDescription keyFirst KeySourced key_sourced)

/-- What the key file's description is made of, at three public files. -/
structure KeySeat where
  source : Source
  nums : H2U.PlaceNums
  later : LaterPlaces

/-- **The key file's description as the verifier's seat makes it**: the same calls, in the same order, at the
same constant in the digest's place; the words of the call that refuses, where one does. -/
def keySeatAt (Z : VerifierAndGoals.PublicFiles) : Except String KeySeat := do
  let X₀ ← VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay)
  let m ← madeAt X₀ Z.lay fixedDigest
  pure ⟨← sourceOf m, ← rangesNumbers m, ← laterPlaces m⟩

/-- The description. -/
abbrev KeySeat.description (S : KeySeat) : FileDescription KeyInst := keyFileDescription S.source S.nums S.later

/-- The shared chain's first state, as a function of the table's key. -/
abbrev KeySeat.start (S : KeySeat) := keyFirst S.source S.nums S.later

/-- The numbers of the test on G_u's place. -/
def KeySeat.testU (S : KeySeat) : P12 := H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ S.later.U

/-- The numbers of the test on G_omega's place. -/
def KeySeat.testOmega (S : KeySeat) : P12 :=
  H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (S.later.O.getD S.later.U)

/-- **Where the seat is live, `keySeatAt` returns, and what it returns is the seat's.** -/
theorem keySeatAt_live {Z : VerifierAndGoals.PublicFiles} (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∃ S, keySeatAt Z = .ok S ∧ KeySourced Z S.source S.nums S.later := by
  obtain ⟨X, N, P, hs⟩ := key_sourced Z live
  obtain ⟨X₀, m, h0, hm, hX, hN, hP⟩ := hs.source
  refine ⟨⟨X, N, P⟩, ?_, hs⟩
  simp only [keySeatAt, h0, hm, hX, hN, hP, bind, Except.bind, pure, Except.pure]

/-- **What is sourced at Z is what `keySeatAt` returns.** -/
theorem keySeatAt_of_sourced {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (hs : KeySourced Z X N P) : keySeatAt Z = .ok ⟨X, N, P⟩ := by
  obtain ⟨X₀, m, h0, hm, hX, hN, hP⟩ := hs.source
  simp only [keySeatAt, h0, hm, hX, hN, hP, bind, Except.bind, pure, Except.pure]

/-- **Two seats sourced at Z are one**: the calls are functions. -/
theorem KeySeat.ext_sourced {Z : VerifierAndGoals.PublicFiles} {S S' : KeySeat}
    (h : KeySourced Z S.source S.nums S.later) (h' : KeySourced Z S'.source S'.nums S'.later) :
    S = S' := by
  have e := (keySeatAt_of_sourced h).symm.trans (keySeatAt_of_sourced h')
  injection e with e

/-- The same of the three letters. -/
theorem keySourced_unique {Z : VerifierAndGoals.PublicFiles} {X X' : Source} {N N' : H2U.PlaceNums}
    {P P' : LaterPlaces} (h : KeySourced Z X N P) (h' : KeySourced Z X' N' P') :
    X = X' ∧ N = N' ∧ P = P' := by
  have e : (⟨X, N, P⟩ : KeySeat) = ⟨X', N', P'⟩ := KeySeat.ext_sourced (Z := Z) h h'
  injection e with a b c
  exact ⟨a, b, c⟩

/-- **A seat that is named, not sourced, has the same description.** `KeyNamed` holds the description and no
source, so its three letters are not pinned by this. -/
theorem keyDesc_of_named {Z : VerifierAndGoals.PublicFiles} {X X' : Source} {N N' : H2U.PlaceNums}
    {P P' : LaterPlaces} (h : AtPublicFiles.AtFiles.KeyNamed Z X N P) (h' : AtPublicFiles.AtFiles.KeyNamed Z X' N' P') :
    keyFileDescription X N P = keyFileDescription X' N' P' := by
  obtain ⟨X₀, m, h0, -, hd, -⟩ := h.named
  obtain ⟨X₀', m', h0', -, hd', -⟩ := h'.named
  have e := h0.symm.trans h0'
  injection e with e
  subst e
  have e₂ := hd.symm.trans hd'
  injection e₂ with e₃

end AtPublicFiles.KeyLay

#print axioms AtPublicFiles.KeyLay.keySeatAt_of_sourced
#print axioms AtPublicFiles.KeyLay.KeySeat.ext_sourced
#print axioms AtPublicFiles.KeyLay.keySourced_unique
#print axioms AtPublicFiles.KeyLay.keyDesc_of_named
#print axioms AtPublicFiles.KeyLay.keySeatAt
#print axioms AtPublicFiles.KeyLay.keySeatAt_live
