-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstFillPairs.lean: CONDITIONAL: WHICH SIDE STANDS AT A PLACE
IN THE PROVER THAT onlineProverFromPublicFiles RETURNS, WITH THE FILLING A LETTER P: GENERAL IN THE LOT, IN ITS KIND AND
IN THE LIST OF LOTS. No filling and no kind is named. Of a side the statements read its place alone.
Five statements with their proofs.

  fill_find_eq        at a place of the kind k the first chain finds what the lot L's own list finds
                      there: a side, or none
  pairs_hex · pairs_ho   its two premises on the filling, from a list ps of lots, each with its kind
  pairs_kind_of · pairs_first_none   every side of the first chain stands at one of the list's
                      kinds; at a place of another kind there is none

The premises. h: onlineProverFromPublicFiles returns A at P · hex: some lot of P's list has, at A's public part and
ground, the halves of L · ho: every lot of that list has there either no half at a place of the kind
k, or L's halves · hp: the place's kind · hl: P's lots are the pairs' first halves · hq: q is one of
the pairs · hk: every side of each pair's lot stands at a place of the pair's kind · hu: a pair of
q's kind has q's list of sides.

hu ASKS THAT q's OWN KIND STANDS ONCE AMONG THE PAIRS, NOT THAT ALL KINDS DO: a list in which
another kind stands twice still serves q. At a kind that stands twice with two lists of sides hu and
ho fail.

Called, of other authors: atPure_first_find_kind (Honest/FirstFindKind.lean), find_none_of_places
(Honest/FirstFind.lean), atPure_ok (Honest/AtPureLaw.lean). atPure_first_find_pairs
(Honest/FirstFindPairs.lean) gives the case "a side" under the premise that no kind stands twice in
the whole list.

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. Conditional. That onlineProverFromPublicFiles returns at any filling is not proved here. hex, ho, hl, hk and hu
are proved here at no filling. What a side does is not said. The first chain alone. No property of a
prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.FirstFindKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstFill
open VerifiableInference.Desc (Place KindName)

variable {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
  {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-! ## 1 At a place of a lot's kind the prover's first chain has what the lot has there -/

/-- **At a place of the kind k the first chain of the prover that onlineProverFromPublicFiles returns finds what the lot
L's own list finds there: a side, or none.** CONDITIONAL: h; hex; ho; hp. -/
theorem fill_find_eq (h : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    {L : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X} {k : KindName}
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = L.halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ k) ∨
      M.halves A.Z A.G = L.halves A.Z A.G)
    {p : Place} (hp : p.kind = k) :
    A.H.first.find? (fun x => x.place == p) =
      (L.halves A.Z A.G).find? (fun x => x.place == p) := by
  obtain ⟨M, hM, hMh⟩ := hex
  rw [← hMh]
  cases hg : (M.halves A.Z A.G).find? (fun x => x.place == p) with
  | some g =>
    exact atPure_first_find_kind h hM
      (fun M' h' => (ho M' h').imp (fun e => by rw [hp]; exact e) (·.trans hMh.symm)) hg
  | none =>
    refine find_none_of_places fun y hy e => ?_
    rw [(atPure_ok h).2.2.2.2.2.2.2.1] at hy
    obtain ⟨M', hM', hyM⟩ := List.mem_flatMap.1 hy
    rcases ho M' hM' with h1 | h2
    · exact h1 y hyM (by rw [e]; exact hp)
    · rw [h2, ← hMh] at hyM
      exact List.find?_eq_none.1 hg y hyM (beq_iff_eq.2 e)

/-! ## 2 From a list of lots, each with its kind, to hex and ho -/

variable {ps : List (HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X × KindName)}
  {q : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X × KindName}

/-- **hex for a pair of the list.** CONDITIONAL: hl; hq. -/
theorem pairs_hex (hl : P.lots = ps.map (·.1)) (hq : q ∈ ps) (Z : Pub) (G : Ground) :
    ∃ M ∈ P.lots, M.halves Z G = q.1.halves Z G :=
  ⟨q.1, by rw [hl]; exact List.mem_map_of_mem hq, rfl⟩

/-- **ho for a lot and its kind.** CONDITIONAL: hl; hk; hu: q's OWN kind stands once among the
pairs, or again with the same list of sides. That other kinds stand once is not asked. -/
theorem pairs_ho {Z : Pub} {G : Ground} (hl : P.lots = ps.map (·.1))
    (hk : ∀ r ∈ ps, ∀ x ∈ r.1.halves Z G, x.place.kind = r.2)
    (hu : ∀ r ∈ ps, r.2 = q.2 → r.1.halves Z G = q.1.halves Z G) :
    ∀ M ∈ P.lots, (∀ y ∈ M.halves Z G, y.place.kind ≠ q.2) ∨
      M.halves Z G = q.1.halves Z G := by
  intro M hM
  rw [hl] at hM
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  by_cases e : r.2 = q.2
  · exact Or.inr (hu r hr e)
  · exact Or.inl fun y hy e' => e ((hk r hr y hy).symm.trans e')

/-! ## 3 No side at a kind that the list does not have -/

/-- **Every side of the first chain stands at a place of one of the list's kinds.** CONDITIONAL: h;
hl; hk. -/
theorem pairs_kind_of (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) (hl : P.lots = ps.map (·.1))
    (hk : ∀ r ∈ ps, ∀ x ∈ r.1.halves A.Z A.G, x.place.kind = r.2) :
    ∀ g ∈ A.H.first, g.place.kind ∈ ps.map (·.2) := by
  intro g hg
  rw [(atPure_ok h).2.2.2.2.2.2.2.1, hl] at hg
  obtain ⟨M, hM, hgM⟩ := List.mem_flatMap.1 hg
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  rw [hk r hr g hgM]
  exact List.mem_map_of_mem hr

/-- **At a place of another kind the first chain has no side.** CONDITIONAL: h; hl; hk; hp. -/
theorem pairs_first_none (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) (hl : P.lots = ps.map (·.1))
    (hk : ∀ r ∈ ps, ∀ x ∈ r.1.halves A.Z A.G, x.place.kind = r.2) {p : Place}
    (hp : p.kind ∉ ps.map (·.2)) : A.H.first.find? (fun x => x.place == p) = none :=
  find_none_of_places fun g hg e => hp (e ▸ pairs_kind_of h hl hk g hg)

end ProofFile.Honest.FirstFill

#print axioms ProofFile.Honest.FirstFill.fill_find_eq
#print axioms ProofFile.Honest.FirstFill.pairs_hex
#print axioms ProofFile.Honest.FirstFill.pairs_ho
#print axioms ProofFile.Honest.FirstFill.pairs_kind_of
#print axioms ProofFile.Honest.FirstFill.pairs_first_none
