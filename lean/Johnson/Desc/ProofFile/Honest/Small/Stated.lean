-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/Stated.lean: eight small general laws. Three are on the frame's
own definitions (Honest/Frame.lean): a row's Steps, a member at whose place a half stands, the
sealed digest of a challenge that passes `drawsFit`. Two are on what declared rounds state
(`StatedBy`, Honest/SumLaw/Fits.lean). Three are on the library's definitions on the verifier's
side: rounds as shown against the entries (`itemOf`, `roundsFit`, `noDigest`,
Johnson/Desc/Block.lean; `scalars`, Johnson/Desc/Part/MaskedSum4.lean; `Fits`,
Johnson/Desc/Part/MaskedSumShape.lean). No statement names a kind; nothing of a kind's row is
imported.
Statements with their proofs.
Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

  `statedBy_length`, `statedBy_split`   the sentence `StatedBy` (Honest/SumLaw/Fits.lean): as many
      declared rounds as numbers; the sentence cut in two
  `rowSteps_cons`   a row's Steps at its first part and the rest
  `half_counts`   where `chainSteps` returns at one member at whose place a half stands: the counts
  `scalars_of_items`, `fits_of_roundsFit`   **rounds that pass the general step's test on shapes
      (`roundsFit`) fit the entries as the masked sumcheck's hearing reads them (`Fits`)**
  `digest_of_fit`, `noDigest_of_none`   a challenge of a round that is no sealing round has no
      sealed digest; taking the digest out then changes nothing

Every statement but `rowSteps_cons`, which is the definition's own text, has premises: see each
docstring.
Limits. Shapes and counts alone. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Fits
import Johnson.Desc.ProofFile.Honest.Law.Play
import Johnson.Desc.Part.MaskedSumShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Block Place Oracle roundsFit noDigest itemOf)
open VerifiableInference.Desc.Part.MaskedSum (Fits scalars)
open ProofFile.Honest.SumLaw (StatedBy)

/-! ## 1 What declared rounds state -/

/-- As many declared rounds as numbers. -/
theorem statedBy_length : ∀ (ns : List Nat) (rs : List (Fmt.DeclaredRound × List Oracle)),
    StatedBy ns rs → rs.length = ns.length
  | [], [], _ => rfl
  | _ :: ns, _ :: rs, h => congrArg (· + 1) (statedBy_length ns rs h.2.2)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- That sentence, cut in two. -/
theorem statedBy_split : ∀ (n₁ n₂ : List Nat) (rs : List (Fmt.DeclaredRound × List Oracle)),
    StatedBy (n₁ ++ n₂) rs → StatedBy n₁ (rs.take n₁.length) ∧ StatedBy n₂ (rs.drop n₁.length)
  | [], _, _, h => ⟨trivial, h⟩
  | _ :: n₁, n₂, _ :: rs, ⟨a, b, h⟩ =>
    ⟨⟨a, b, (statedBy_split n₁ n₂ rs h).1⟩, (statedBy_split n₁ n₂ rs h).2⟩
  | _ :: _, _, [], h => h.elim

/-! ## 2 A row's Steps; a member at whose place a half stands -/

/-- A row's Steps, at its first part and the rest: the text of `rowSteps` (Honest/Frame.lean). -/
theorem rowSteps_cons {V W X : Type} (nm : String) (a : Place) (v : Option V) (p : Part V W X)
    (ps : List (Part V W X)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
    (c : RowCoins (p :: ps)) :
    rowSteps nm a v (p :: ps) j rs c =
      p.steps nm ⟨a, j⟩ (rs.take p.moves.length) v c.1 ++
        rowSteps nm a v ps (j + 1) (rs.drop p.moves.length) c.2 := rfl

/-- Where `chainSteps` returns at one member at whose place a half stands: the member has a list of
oracle messages for each round, and the half as many rounds as the member. General in the half. -/
theorem half_counts {Bk : ProverCoinCounts} {S Cl V W Y : Type} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d}
    {v : Option V} {b : Block S Cl} {hs : List (Placed V W Y)} {l : List (Step W Y)}
    {g : Placed V W Y} (hf : (hs.find? fun g => g.place == b.place) = some g)
    (h : chainSteps Bk rows look v [b] hs = .ok l) :
    b.oracles.length = b.rounds.length ∧ g.rounds = b.rounds.length := by
  simp only [chainSteps, hf] at h
  obtain ⟨h1, h⟩ := exIte_ok h
  obtain ⟨h2, -⟩ := exIte_ok h
  exact ⟨by simpa using h1, by simpa using h2⟩

/-! ## 3 Rounds as shown against the entries -/

/-- Items that are all elements of the extension field are scalars, as many. -/
theorem scalars_of_items : ∀ (vals : List Fmt.ItemValue) (n : Nat),
    vals.map itemOf = List.replicate n .e → ∃ s, scalars vals = some s ∧ s.length = n
  | [], 0, _ => ⟨[], rfl, rfl⟩
  | .e x :: l, n + 1, h => by
    rw [List.map_cons, List.replicate_succ, List.cons.injEq] at h
    obtain ⟨s, h1, h2⟩ := scalars_of_items l n h.2
    exact ⟨OnBytes.E.ofTriple x :: s, by show (scalars l).map _ = _; rw [h1]; rfl,
      congrArg (· + 1) h2⟩
  | [], _ + 1, h => by cases h
  | _ :: _, 0, h => by cases h
  | .f _ :: _, _ + 1, h => by cases h
  | .word _ :: _, _ + 1, h => by cases h
  | .root _ :: _, _ + 1, h => by cases h
  | .answer _ :: _, _ + 1, h => by cases h

/-- **Rounds that pass the general step's test on shapes (`roundsFit`, Johnson/Desc/Block.lean) fit
the entries as the masked sumcheck's hearing reads them (`Fits`,
Johnson/Desc/Part/MaskedSumShape.lean).** Conditional: no entry has a root or an answer, and each
message is whole scalars. General in the declared rounds. -/
theorem fits_of_roundsFit : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds rs = true →
    (∀ d ∈ ds, d.entry.roots = 0 ∧ d.entry.answers = 0 ∧ 24 ∣ d.entry.msg) →
    Fits (ds.map (·.entry)) (rs.map noDigest)
  | [], [], _, _ => trivial
  | d :: ds, r :: rs, h, hp => by
    simp only [roundsFit, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, h8⟩ := h
    obtain ⟨p1, p2, q, p3⟩ := hp d List.mem_cons_self
    have hi : d.items.filter (· != .root) = List.replicate q .e := by
      simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, p1, p2, p3]
    obtain ⟨s, s1, s2⟩ := scalars_of_items r.vals q (h1.trans hi)
    exact ⟨⟨⟨s, s1, by rw [p3, s2]⟩, h2⟩,
      fits_of_roundsFit ds rs h8 fun x hx => hp x (List.mem_cons_of_mem _ hx)⟩
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h

/-! ## 4 The sealed digest -/

/-- A challenge that a round of another kind than the sealing one can draw has no sealed digest. -/
theorem digest_of_fit : ∀ (zs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn),
    drawsFit zs ds = true → (∀ z ∈ zs, Fmt.kindOf z.entry.name ≠ some .sealed) →
    ∀ d ∈ ds, d.digest = none
  | [], [], _, _, _, h => by cases h
  | z :: zs, R :: Rs, h, hk, d, hd => by
    simp only [drawsFit, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hd with rfl | hd
    · have h1 := h.1
      simp only [drawFit, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h1
      rcases h1.2 with h2 | h2
      · exact Option.isNone_iff_eq_none.1 h2
      · exact absurd h2 (hk z List.mem_cons_self)
    · exact digest_of_fit zs Rs h.2 (fun x hx => hk x (List.mem_cons_of_mem _ hx)) d hd
  | [], _ :: _, h, _, _, _ => by cases h
  | _ :: _, [], h, _, _, _ => by cases h

/-- Taking the sealed digest out of rounds (`noDigest`) changes nothing where no challenge has one.
-/
theorem noDigest_of_none : ∀ rs : List Fmt.RoundView, (∀ r ∈ rs, r.drawn.digest = none) →
    rs.map noDigest = rs
  | [], _ => rfl
  | r :: rs, h => by
    have h1 : noDigest r = r := by
      obtain ⟨vals, elems, poss, trits, digest⟩ := r
      obtain rfl : digest = none := h _ List.mem_cons_self
      rfl
    rw [List.map_cons, h1, noDigest_of_none rs fun x hx => h x (List.mem_cons_of_mem _ hx)]

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.statedBy_length
#print axioms ProofFile.Honest.Small.statedBy_split
#print axioms ProofFile.Honest.Small.rowSteps_cons
#print axioms ProofFile.Honest.Small.half_counts
#print axioms ProofFile.Honest.Small.scalars_of_items
#print axioms ProofFile.Honest.Small.fits_of_roundsFit
#print axioms ProofFile.Honest.Small.digest_of_fit
#print axioms ProofFile.Honest.Small.noDigest_of_none
