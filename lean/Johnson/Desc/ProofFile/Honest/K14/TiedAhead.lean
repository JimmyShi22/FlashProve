-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/TiedAhead.lean: the linear claim's second part ("K14, second
part", the first member of a proof file's last chain): WHAT HAS TO HOLD IN FRONT OF THE MEMBER SO
THAT, BEHIND ITS YES, THE NEXT MEMBER's TEST SAYS YES. The next member ("the taken trees' sources",
Johnson/Desc/Third/TakenSources.lean) compares the sources that the own proximity test's rounds
declare as taken over with the numbers of the trees, in the book, of the own group's members and of
the mask (Tied, Johnson/Desc/Third/Law/Sources.lean). The second part takes Omega over, with its
tree, and lets it join the own group; it turns no other tree and no other place. So the comparison
can be made one member earlier, on the record that the chain's start returns.

  takenAhead      the pairs (chain, tree's number) as the next member will read them, read off the
                  record in front: Omega's, out of the shared chain's book as the record's border
                  holds it, under the chain 1; then the own group's members' and the mask's, out of
                  the record's own book, under the chain 0
  sourcesB        the next member's two clauses at a list of pairs: each pair is declared as taken;
                  no other tree is declared as taken
  tiedAheadB      **the test, with code**: sourcesB at the pairs of takenAhead
  tied_of_ahead   **where the test says yes in front, Tied holds behind**, of whatever record the
                  second part has laid (Laid, Johnson/Desc/Third/Law/LaidDef.lean)
  tied_behind_yes   the same from the member's own yes
  tiedAheadRider  the test as a clause of a thread's rider that speaks at border 0 alone

What is not claimed. That the test says yes at any record: it reads four pairs of a chain and a
tree's NUMBER, which neither the member's yes nor its own tests fix. The four pairs need not name
four trees: two messages can lie in one tree. Nothing on completeness, soundness or hiding.
Terms. border: lean/GLOSSARY.md. A rider is a list of clauses on the verifier's state, each from one
border to another (Johnson/Desc/ProofFile/Honest/Thread/Riders.lean).
-/
import Johnson.Desc.Third.Law.Sources
import Johnson.Desc.Third.Law.Laid
import Johnson.Desc.K14.Law.MeansDot
import Johnson.Desc.K14.Honest.YesState
import Johnson.Desc.ProofFile.Honest.Thread.Riders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Third (S₃ P₁₄ Border Laid takenOf opensTaken batchLinearConstraintsSecondPart)
open VerifiableInference.Desc.Third.Law (Tied laid_k14Second)

/-- **The pairs that the next member will read, read off the record in front.** -/
def takenAhead (s : S₃) : Option (List (Nat × Nat)) :=
  s.loc.border.bind fun b =>
  (s.st.groups[s.loc.own]?).bind fun G =>
  (b.shared.book.place[b.shared.omega]?).bind fun q =>
  (b.shared.book.trees[q.1]?).bind fun t =>
    ((G.members.toList ++ s.loc.mask.toList).mapM fun i =>
      ((s.book.place[i]?).bind fun q => s.book.trees[q.1]?).map fun T => (0, T.number)).map
        fun l => (1, t.number) :: l

/-- The next member's two clauses, at a list of pairs. ownRounds: the own test's declared rounds. -/
def sourcesB (ownRounds : List Fmt.DeclaredRound) (ts : List (Nat × Nat)) : Bool :=
  (ts.all fun x => opensTaken ownRounds x.1 x.2) &&
    (ownRounds.flatMap (·.opens)).all fun o =>
      match o.2 with
      | .own _ => true
      | .taken c n => ts.contains (c, n)

/-- **The next member's two clauses at the pairs read off the record in front.** -/
def tiedAheadB (ownRounds : List Fmt.DeclaredRound) (s : S₃) : Bool :=
  match takenAhead s with
  | some ts => sourcesB ownRounds ts
  | none => false

/-- **Where the test says yes in front, Tied holds behind.** L: what the second part has laid. -/
theorem tied_of_ahead {Cl : Type} (own : Block S₃ Cl) {S : OnBytes.Params.LinShape} {s s' : S₃}
    {b : Border} {y : OnBytes.Oracle} {G : OnBytes.Group} {dot : OnBytes.Row}
    (L : Laid S s s' b y G dot) (h : tiedAheadB own.rounds s = true) : Tied own s' := by
  unfold tiedAheadB at h
  cases hts : takenAhead s with
  | none =>
    rw [hts] at h
    cases h
  | some ts =>
    rw [hts] at h
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.1 (show sourcesB own.rounds ts = true from h)
    unfold takenAhead at hts
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hts
    obtain ⟨b', hb', G', hG', q, hq, t, ht, l, hl, rfl⟩ := hts
    obtain rfl : b = b' := Option.some.inj (L.border.symm.trans hb')
    obtain rfl : G = G' := Option.some.inj (L.group.symm.trans hG')
    obtain ⟨q₂, t₂, tO, hq₂, ht₂, -, htO, hnum, -⟩ := L.tree
    obtain rfl : q = q₂ := Option.some.inj (hq.symm.trans hq₂)
    obtain rfl : t = t₂ := Option.some.inj (ht.symm.trans ht₂)
    have hom : s'.loc.omega = s.st.oracles.size := by rw [L.loc]
    have hown : s'.loc.own = s.loc.own := by rw [L.loc]
    have hmask : s'.loc.mask = s.loc.mask := by rw [L.loc]
    -- an old message is read behind as in front
    have hA : ∀ i x,
        (((s.book.place[i]?).bind fun q => s.book.trees[q.1]?).map fun T => (0, T.number)) =
          some x →
        (((s'.book.place[i]?).bind fun q => s'.book.trees[q.1]?).map fun t =>
          (if i == s'.loc.omega then 1 else 0, t.number)) = some x := by
      intro i x hx
      simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at hx
      obtain ⟨T, ⟨qi, hqi, hT⟩, rfl⟩ := hx
      have h1 : i < s.book.place.size := (Array.getElem?_eq_some_iff.1 hqi).1
      have h2 : qi.1 < s.book.trees.size := (Array.getElem?_eq_some_iff.1 hT).1
      have hne : (i == s'.loc.omega) = false := by
        rw [hom, L.step]
        exact beq_false_of_ne (Nat.ne_of_lt h1)
      rw [L.oldPlaces i h1, hqi, hne]
      show (s'.book.trees[qi.1]?).map _ = _
      rw [L.oldTrees _ h2, hT]
      rfl
    -- Omega's copy
    have hB : (((s'.book.place[s.st.oracles.size]?).bind fun q => s'.book.trees[q.1]?).map fun t =>
        (if s.st.oracles.size == s'.loc.omega then 1 else 0, t.number)) = some (1, t.number) := by
      rw [L.place, hom, beq_self_eq_true]
      show (s'.book.trees[s.book.trees.size]?).map _ = _
      rw [htO, ← hnum]
      rfl
    have hpos : (G.members.filter (· < s.st.oracles.size)).size ≤ G.members.toList.length := by
      rw [Array.length_toList]
      exact Array.size_filter_le
    have hmem : ∀ a, a ∈ (G.members.insertIdxIfInBounds
          (G.members.filter (· < s.st.oracles.size)).size s.st.oracles.size).toList ++
          s.loc.mask.toList ↔
        a = s.st.oracles.size ∨ a ∈ G.members.toList ++ s.loc.mask.toList := by
      intro a
      rw [List.mem_append, OnBytes.Means.toList_insertIdxIfInBounds, List.mem_insertIdx hpos,
        List.mem_append]
      tauto
    obtain ⟨ts', hts'⟩ := Desc.K14.Honest.mapM_makes (fun i =>
      ((s'.book.place[i]?).bind fun q => s'.book.trees[q.1]?).map fun t =>
        (if i == s'.loc.omega then 1 else 0, t.number)) _ (fun a ha => by
      rcases (hmem a).1 ha with rfl | ha
      · exact ⟨_, hB⟩
      · obtain ⟨x, -, hx⟩ := Desc.K14.Law.mem_mapM _ _ l hl a ha
        exact ⟨x, hA a x hx⟩)
    have hsub : ∀ x, x ∈ ts' ↔ x ∈ (1, t.number) :: l := by
      intro x
      constructor
      · intro hx
        obtain ⟨a, ha, hfa⟩ := Desc.K14.Law.mem_mapM_back _ _ ts' hts' x hx
        rcases (hmem a).1 ha with rfl | ha
        · rw [hB] at hfa
          obtain rfl := Option.some.inj hfa
          exact List.mem_cons_self
        · obtain ⟨z, hz, hfz⟩ := Desc.K14.Law.mem_mapM _ _ l hl a ha
          rw [hA a z hfz] at hfa
          obtain rfl := Option.some.inj hfa
          exact List.mem_cons_of_mem _ hz
      · intro hx
        rcases List.mem_cons.1 hx with rfl | hx
        · obtain ⟨z, hz, hfz⟩ := Desc.K14.Law.mem_mapM _ _ ts' hts' _ ((hmem _).2 (Or.inl rfl))
          rw [hB] at hfz
          obtain rfl := Option.some.inj hfz
          exact hz
        · obtain ⟨a, ha, hfa⟩ := Desc.K14.Law.mem_mapM_back _ _ l hl x hx
          obtain ⟨z, hz, hfz⟩ := Desc.K14.Law.mem_mapM _ _ ts' hts' a ((hmem a).2 (Or.inr ha))
          rw [hA a x hfa] at hfz
          obtain rfl := Option.some.inj hfz
          exact hz
    refine ⟨ts', ?_, ?_, ?_⟩
    · unfold takenOf
      rw [hown, L.group', hmask]
      exact hts'
    · rw [List.all_eq_true] at ha ⊢
      exact fun x hx => ha x ((hsub x).1 hx)
    · rw [List.all_eq_true] at hb ⊢
      rintro ⟨o1, o2⟩ ho
      have h1 := hb _ ho
      cases o2 with
      | own _ => rfl
      | taken c n =>
        have h2 : (c, n) ∈ (1, t.number) :: l := List.contains_iff_mem.1 h1
        exact List.contains_iff_mem.2 ((hsub _).2 h2)

/-- **The same from the member's own yes.** -/
theorem tied_behind_yes {Cl Cl' : Type} (own : Block S₃ Cl) (p : P₁₄) (s s' : S₃)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (batchLinearConstraintsSecondPart (Cl := Cl') p).decide s rs gs = .ok s')
    (h : tiedAheadB own.rounds s = true) : Tied own s' := by
  obtain ⟨b, y, G, dot, L⟩ := laid_k14Second p s s' rs gs hd
  exact tied_of_ahead own L h

/-- **The test as a clause of the rider that speaks at border 0 alone.** -/
def tiedAheadRider (W : Type) (ownRounds : List Fmt.DeclaredRound) : RiderCl W S₃ :=
  ⟨0, 0, fun _ _ s => tiedAheadB ownRounds s = true⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.tied_of_ahead
#print axioms ProofFile.Honest.K14.tied_behind_yes
