-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastSits.lean: WHERE THE GROUP UNDER THE LAST CHAIN's OWN TEST SITS:
`GroupSits` (LastSeamRows.lean: what is left of the seam's cover) AT THE CLOSED seatAt THAT
THE WORDS' TABLES READ (`seatBy (noLast t₁ t₂ firstTree) book`, Johnson/Desc/Sound/TabAt.lean), FROM
TWO FACTS AT THE ENDS OF THE TWO EARLIER CHAINS. Inside the book-keeping's yes at border 2.
  `start_own`: the start's yes lays the own group's number that was handed, and the count of roots
    that was handed is the handed book's number of trees.
  `groupSits_of_ends`: **by the record's own book every member of the group under test sits at the
    seat of one of mine, with its shape, FROM: (H1) at what was handed of the FIRST chain's last
    record: each member of the own group sits, by that chain's own book (`seatBy noFirst`), at the
    seat of one of mine, with its shape; (H2) at the SHARED chain's end: Omega sits, by that chain's
    book (`seatBy (noShared t₁)`), at the seat of one of mine, whose shape is the plan's for
    Omega.** By `three_members` (the group is the two that were handed, then Omega's copy) and the
    fields of `Laid` (older messages, places and trees are as they were; the copy's place, tree and
    shape), `seat_older` and `seat_taken`, `placed_of_fits`, and the laws on the start.

Limits. (H1) and (H2) are shown nowhere: they are facts on public records at the two tables' last
borders: whoever holds these tables' promises. Nothing on soundness.
-/
import Johnson.LLT25R.LastSeamRows
import Johnson.LLT25R.LastYesLays
import Johnson.Desc.Third.Law.Start
import Johnson.Desc.Third.Law.StartBook
import Johnson.Desc.Tidy.Third

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Last VerifiableInference.Desc.Third
open VerifiableInference.Desc.Third.Law (start₃E_st start₃E_book start₃E_border)
open VerifiableInference.Desc.Book (placed_of_fits)
open VerifiableInference.Desc.K12.Seat (enterOwn)

/-- What the start's yes says of the own group's number and of the count of roots. -/
theorem start_own {codes : Codes} {S : LinShape} {st₁ : Statement} {book₁ : TreeBook}
    {roots₁ w₁ own₁ : ℕ} {mask₁ : Option ℕ} {pile₁ : List TensorRow} {o : SharedOut} {s₀ : S₃}
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    s₀.loc.own = own₁ ∧ roots₁ = book₁.trees.size := by
  unfold start₃E at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i f hf
      split at h
      · cases h
      · rename_i s₁ hs
        obtain rfl := Except.ok.inj h
        unfold start₃ at hs
        split at hs
        · rename_i hk
          obtain rfl := Option.some.inj hs
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
          unfold firstOutFrom at hf
          split at hf
          · split at hf
            · dsimp only at hf
              split at hf
              · obtain rfl := Option.some.inj hf
                exact ⟨rfl, by simpa [rootsB] using hk.2⟩
              · cases hf
            · cases hf
          · cases hf
        · cases hs

/-- **WHERE THE GROUP UNDER TEST SITS, FROM THE TWO EARLIER CHAINS' ENDS.** -/
theorem groupSits_of_ends (p : P₁₄) (R : List Fmt.DeclaredRound) (f : Handed) (o : SharedOut) (s : S₃)
    (t : T12) (G0 : Group) (t₁ t₂ : ℕ) (mine : List Mem)
    (hk : shapeAt p R 2 f o s = true) (ht : enterOwn s = .ok t)
    (hG : t.st.groups[t.g]? = some G0)
    (H1 : ∀ Gh, f.st.groups[f.own]? = some Gh → ∀ i ∈ Gh.members.toList, ∃ x ∈ mine,
      seatBy noFirst f.book i = some (seatOf x) ∧
        (f.st.oracles[i]?).map (·.shape) = some (x.1.l.get x.2).1)
    (H2 : ∃ x ∈ mine, seatBy (noShared t₁) o.book o.omega = some (seatOf x) ∧
      p.S.omega = (x.1.l.get x.2).1) :
    ∀ i ∈ G0.members.toList, ∃ x ∈ mine,
      seatBy (noLast t₁ t₂ s.loc.firstTree) s.book i = some (seatOf x) ∧
        (t.st.oracles[i]?).map (·.shape) = some (x.1.l.get x.2).1 := by
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hk
  have hst := start₃E_st _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain ⟨hbk, -, hft⟩ := start₃E_book _ _ _ _ _ _ _ _ _ _ _ B.start
  have hbd := start₃E_border _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain ⟨hown, hroots⟩ := start_own B.start
  obtain ⟨Gh, G, hGh, hGs, hmem, -, -⟩ := three_members B hst hbd
  obtain ⟨b, y, Gx, dot, L⟩ := B.laid
  have e0 : t.st = s.st ∧ t.g = s.loc.own := by
    obtain rfl : _ = t := Except.ok.inj ht
    exact ⟨rfl, rfl⟩
  obtain rfl : G = G0 := by
    rw [e0.1, e0.2, hGs] at hG
    exact Option.some.inj hG
  have hfirst : s.loc.firstTree = s₀.book.trees.size + 1 := by
    rw [L.loc]
    show s₀.loc.firstTree = _
    rw [hft, hbk, hroots]
  intro i hi
  rw [hmem] at hi
  have hi' : i ∈ Gh.members ∨ i = s.loc.omega := by simpa using hi
  rcases hi' with c | c
  · have c' : i ∈ Gh.members.toList := Array.mem_toList_iff.2 c
    have hlt : i < s₀.st.oracles.size := by
      have T : Means.Tidy s₀.st := by rw [hst]; exact B.handed.tidy
      exact (T.inOrder.groups _ _ hGh).there i c'
    obtain ⟨x, hx, hs, hsh⟩ := H1 Gh (by rw [← hst, ← hown]; exact hGh) i c'
    refine ⟨x, hx, ?_, ?_⟩
    · rw [← hs, ← hbk]
      refine seat_older t₁ t₂ s.loc.firstTree s₀.book s.book i (L.oldPlaces i (L.step ▸ hlt))
        (fun q hq => L.oldTrees q.1 (placed_of_fits (hbk ▸ B.handed.fits₁) i q hq))
        (fun q _ hq _ => ?_)
      have := placed_of_fits (hbk ▸ B.handed.fits₁) i q hq
      omega
    · rw [e0.1, L.old i hlt, hst]
      exact hsh
  · obtain ⟨x, hx, hs, hsh⟩ := H2
    obtain ⟨g, hg⟩ := hbd
    obtain rfl : (⟨g, o⟩ : Border) = b := Option.some.inj (hg.symm.trans L.border)
    have em : s.loc.omega = s₀.st.oracles.size := by rw [L.loc]
    obtain ⟨q, tr, tO, hq, htr, -, htO, hnum, -⟩ := L.tree
    refine ⟨x, hx, ?_, ?_⟩
    · rw [c, em, ← hs]
      exact seat_taken t₁ t₂ s.loc.firstTree o.book s.book o.omega s₀.st.oracles.size q
        (s₀.book.trees.size, 0) tr tO hq htr L.place htO hfirst.symm hnum
        (B.handed.tenant q hq).symm
    · obtain ⟨y', hy', hsy⟩ := B.handed.omega
      obtain rfl : y' = y := Option.some.inj (hy'.symm.trans L.there)
      rw [c, em, e0.1, L.copy, ← hsh, ← hsy]
      rfl

end LLT25

#print axioms LLT25.start_own
#print axioms LLT25.groupSits_of_ends
