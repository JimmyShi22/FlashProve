-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FindAtBase.lean: the kind K5's pair among the thirteen lots of
the filling `onlineProverPartsInUse` (Honest/Law/FillPairs.lean), and what a search in the maker's first
chain finds at K5's places, at that filling itself, before anything is read through. No definition;
three theorems.

  `k5_pair_mem`       K5's pair is among the thirteen
  `k5_pair_only`      it is the only one of its kind
  `k5_find_at_base`   under the library's head, at a return of the maker at this filling: a search at
                      the place of group j finds K5's side there

Limits.
  * `k5_find_at_base` is conditional on the library's head and on the maker's return.
  * Nothing here says what a side sends, or that a verifier accepts it.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.FillPairs
import Johnson.Desc.ProofFile.Honest.K5.Law.LotFind
import Johnson.Desc.ProofFile.Honest.FirstFindKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open VerifiableInference.Desc (Chain KindName)
open P5J (AtMgA TS)

variable {W₀ : Type}

/-- **K5's pair is among the thirteen.** -/
theorem k5_pair_mem (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (k5LotK id O.keyOf, KindName.K5) ∈ fillPairs I o S O :=
  List.mem_append_left _ (by simp [widerPairs])

/-- **K5's pair is the only one of its kind.** -/
theorem k5_pair_only (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∀ M, (M, KindName.K5) ∈ fillPairs I o S O → M = k5LotK id O.keyOf :=
  pair_only I o S O (by simp [widerPairs]) (by decide)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **At the filling itself: a search at the place of group j finds K5's side there.** Conditional:
h; hO; hA; ha: the plan of group j. -/
theorem k5_find_at_base (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (I : WiderIn W₀)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (hO : O.keyOf = keyOfK3)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A) {j : Nat}
    (hj : j < 12) {a : OnBytes.Attention.Plan} (ha : (P5J.At.X Zp).A[j]? = some a) :
    A.H.first.find? (fun q => q.place == placeOf j) =
      some (k5Half id (seatOf keyOfK3 Zp A.G cF j a)) := by
  obtain ⟨e1, eG, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    rw [← eZ]
    exact eG
  have hfind := k5LotK_find_K3 (W₀ := W₀) (Rc := IndexCommitterCoins) (X := Unit) h hj hG id ha
  have hlot : k5LotK id O.keyOf ∈ (onlineProverPartsInUse I o' S O).lots := by
    rw [fillPairs_lots]
    exact List.mem_map.2 ⟨_, k5_pair_mem I o' S O, rfl⟩
  exact atPure_first_find_kind hA hlot
    (fun M hM => ((lot_alone I o' S O (k5_pair_only I o' S O) A.Z A.G) M hM).symm.imp id
      fun e => by rw [e])
    (by rw [hO, eZ]; exact hfind)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_pair_mem
#print axioms ProofFile.Honest.K5.k5_pair_only
#print axioms ProofFile.Honest.K5.k5_find_at_base
