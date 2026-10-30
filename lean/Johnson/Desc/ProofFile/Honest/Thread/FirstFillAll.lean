-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstFillAll.lean: WiderKinds (Honest/Thread/FirstFill.lean:
"every side of each of the filling's lists is at a place of the list's kind") HOLDS AT EVERY PUBLIC
PART AND GROUND, WITH NO PREMISE; AND SO, CONDITIONAL ON "onlineProverFromPublicFiles RETURNS" ALONE: where in the prover
that onlineProverFromPublicFiles returns at the filling widerFillAt NO side stands. Statements with their proofs: calls.

  widerKinds            **WiderKinds I o S O Z G: no premise**: widerKinds_of_one
                        (Honest/Thread/FirstFillKinds.lean) at the one field that was left, K6's:
                        its authors' own K6.headLot_kind (Honest/K6/LotKind.lean)
  first_find_all        CONDITIONAL: wider_first_find without its premise K
  first_none_all        CONDITIONAL: **at a place of none of the ten kinds nothing is found**
  first_none_in_all     CONDITIONAL: at a place of a list's kind at which that list holds nothing,
                        nothing is found
  no_frame_all          CONDITIONAL: **no side of the first chain is at a place of the kind
                        "frame"**
  k1_none_behind_all    CONDITIONAL: no side at a place of the kind K1 behind the segments

The one premise of the last five: h: onlineProverFromPublicFiles returns A at the filling (and, in the two on a list, the
list's own: q, hp, hg).

The other files' statements on single kinds (Honest/Thread/FirstFillK5.lean and its like) keep their
premise K: widerKinds I o S O A.Z A.G pays it.

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. THAT onlineProverFromPublicFiles RETURNS AT ANY FILES IS A HYPOTHESIS. WiderKinds speaks of the sides that a list
holds: A LIST MAY HOLD NONE, and its field is then true for nothing: so K6's where its public test
rejects or its lot seats no sub-protocol (Honest/K6/LotKind.lean's own head). "No premise" is said
of the statement: the lemmas that are called stand in files of several authors beside the library.
The statements are about lists and places: at which kind of place a side stands, and where none
stands: not that a sub-protocol stands at a side's place, nor what a side sends. No property of a
prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillK1
import Johnson.Desc.ProofFile.Honest.K6.LotKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstFill
open VerifiableInference.Desc (Place KindName)

variable {W₀ : Type}

/-- **EVERY SIDE OF EACH OF THE FILLING's TEN LISTS IS AT A PLACE OF THE LIST's KIND.** No
premise. -/
theorem widerKinds (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Z : Pub) (G : Ground) : WiderKinds I o S O Z G :=
  widerKinds_of_one (K6.headLot_kind _ _ Z G)

variable {I : WiderIn W₀} {o o' : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- At a place of a list's kind, what is found among the first chain's sides is what is found in
that list. CONDITIONAL: onlineProverFromPublicFiles returns A at the filling; q is one of the ten pairs; the place is of
its kind; hg: what the list's own sides hold there. -/
theorem first_find_all (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A)
    {q : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit × KindName}
    (hq : q ∈ widerPairs I o S O) {p : Place} (hp : p.kind = q.2)
    {g : Placed (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit}
    (hg : (q.1.halves A.Z A.G).find? (fun x => x.place == p) = some g) :
    A.H.first.find? (fun x => x.place == p) = some g :=
  wider_first_find h (widerKinds I o S O A.Z A.G) hq hp hg

/-- **AT A PLACE OF NONE OF THE TEN KINDS NOTHING IS FOUND.** CONDITIONAL: onlineProverFromPublicFiles returns A at the
filling; the place's kind is none of the ten. -/
theorem first_none_all (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A) {p : Place}
    (hp : p.kind ∉ ([.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8] : List KindName)) :
    A.H.first.find? (fun x => x.place == p) = none :=
  wider_first_none h (widerKinds I o S O A.Z A.G) hp

/-- At a place of a list's kind at which that list holds nothing, nothing is found. CONDITIONAL:
onlineProverFromPublicFiles returns A at the filling; q is one of the ten pairs; the place is of its kind; hg: the list's
own sides hold nothing there. -/
theorem first_none_in_all (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A)
    {q : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit × KindName}
    (hq : q ∈ widerPairs I o S O) {p : Place} (hp : p.kind = q.2)
    (hg : (q.1.halves A.Z A.G).find? (fun x => x.place == p) = none) :
    A.H.first.find? (fun x => x.place == p) = none :=
  wider_first_none_in h (widerKinds I o S O A.Z A.G) hq hp hg

/-- **NO SIDE OF THE FIRST CHAIN IS AT A PLACE OF THE KIND "frame".** CONDITIONAL: onlineProverFromPublicFiles returns A
at the filling. -/
theorem no_frame_all (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A) :
    ∀ g ∈ A.H.first, g.place.kind ≠ .frame :=
  wider_no_frame h (widerKinds I o S O A.Z A.G)

/-- No side at a place of the kind K1 behind the segments. CONDITIONAL: onlineProverFromPublicFiles returns A at the
filling. -/
theorem k1_none_behind_all (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A) (c pc : Nat) :
    A.H.first.find? (fun g => g.place == ⟨c, none, pc, .K1⟩) = none :=
  k1_none_behind h (widerKinds I o S O A.Z A.G) c pc

end ProofFile.Honest.FirstFill

#print axioms ProofFile.Honest.FirstFill.widerKinds
#print axioms ProofFile.Honest.FirstFill.first_find_all
#print axioms ProofFile.Honest.FirstFill.first_none_all
#print axioms ProofFile.Honest.FirstFill.first_none_in_all
#print axioms ProofFile.Honest.FirstFill.no_frame_all
#print axioms ProofFile.Honest.FirstFill.k1_none_behind_all
