-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/FirstFindPairs.lean: the lemma of Honest/FirstFindKind.lean for a list
of lots each of which has its prover's sides at places of one kind, no two lots at the same kind.
Then what is found at a place of a lot's kind, in the whole list, is what is found in that lot. Two
lemmas; no definition.

  1  `firstOf_find_pairs`   `ps` lists each lot with its kind. Hypotheses: every side of a lot is at
     a place of the lot's kind; no kind is listed twice; the pair `q` is in the list; the place is
     of the kind of `q`
  2  `atPure_first_find_pairs`   the same for the prover that `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns,
     if the filling's list of lots is the list of the pairs' lots

Limits.
  * What a lot's own list holds at the place (the hypothesis `hg`) is for the caller to prove.
  * A lot that has sides at places of two kinds does not fit the first hypothesis.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.FirstFindKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName)

theorem firstOf_find_pairs {V W X : Type} {Z : Pub} {G : Ground}
    {ps : List (HLot V W X × KindName)}
    (hk : ∀ r ∈ ps, ∀ x ∈ r.1.halves Z G, x.place.kind = r.2) (hn : (ps.map (·.2)).Nodup)
    {q : HLot V W X × KindName} (hq : q ∈ ps) {p : Place} (hp : p.kind = q.2) {g : Placed V W X}
    (hg : (q.1.halves Z G).find? (fun x => x.place == p) = some g) :
    (firstOf Z G (ps.map (·.1))).find? (fun x => x.place == p) = some g := by
  refine firstOf_find_kind (List.mem_map.2 ⟨q, hq, rfl⟩) (fun M hM => ?_) hg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  by_cases e : r.2 = q.2
  · rw [List.inj_on_of_nodup_map hn hr hq e]
    exact Or.inr rfl
  · refine Or.inl fun x hx => ?_
    rw [hk r hr x hx, hp]
    exact e

theorem atPure_first_find_pairs {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    {ps : List (HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X × KindName)}
    (hl : P.lots = ps.map (·.1))
    (hk : ∀ r ∈ ps, ∀ x ∈ r.1.halves A.Z A.G, x.place.kind = r.2) (hn : (ps.map (·.2)).Nodup)
    {q : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X × KindName} (hq : q ∈ ps) {p : Place}
    (hp : p.kind = q.2) {g : Placed (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X}
    (hg : (q.1.halves A.Z A.G).find? (fun x => x.place == p) = some g) :
    A.H.first.find? (fun x => x.place == p) = some g := by
  rw [(atPure_ok h).2.2.2.2.2.2.2.1, hl]
  exact firstOf_find_pairs hk hn hq hp hg

end ProofFile.Honest

#print axioms ProofFile.Honest.firstOf_find_pairs
#print axioms ProofFile.Honest.atPure_first_find_pairs
