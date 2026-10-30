-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/K03KeySits.lean: It stands on files of Johnson/RunOne/Sound/.
THE KIND'S OWN BLOCK SITS IN THE KEY FILE'S WRITTEN
DESCRIPTION: at each place of the kind in Key.descriptionFromSource X N P's first chain the entry of the flat list of
blocks IS lookupKind at the seat lookupSeat and the place of that lookup, under no wrapper; its yes
gives the premises of the kind's law K03key_law : Law hearE
(Johnson/Desc/First/Look/KeyLaw/TotalB.lean; Law.out: Statement.lean) at the plan's numbers.

Main names:
  k03key_sits: for every lookup number l of the plan:
    (1) (Key.descriptionFromSource X N P).first.blocksInOrder[2 + (6 l + 2)]? is that block;
    (2) the place's face is the face of the plan's lookup; it is the face of the typed lookup datK
        at any riding type, table of homes and state (FaceIs); the typed lookup is admitted (Adm);
    (3) the block's yes from s to s' gives: an open ledger F with F.next = the place's first number
        and F.ns = its room; the place's entries; hearE face entries F rounds = some (g, G); and s'
        is s with g and G put: hearE is the constant of which K03key_law speaks;
    (4) at a record with the record's half of the row in front (RecK X l 2; of a record that was
        reached: RecOfHist.lean): the open ledger is sized, and the record's table of homes has
        HomeIs at the place's first number.
    (5) the seventh premise: the block as a piece holds it (held: "below", then the lift to the
        pair): its yes ⊢ viewWordsBelowPrime ⟨rs, []⟩ = true at the very rounds that it decides on (held_words);
    (6) the block's own place is ⟨1, some l, 2, K3⟩. (In the statement (5) and (6) stand in front of
        (4).)
  held_words, words_nil: the three lines on the split in "below".
  k3_places: under planOk and wantedOk: the places of the description's blocks that bear the tag K3
    are just ⟨1, some l, 2⟩, l below the number of lookups; none in the two later chains
    (wantedFirst_k3, wantedShared_k3, wantedSecond_k3; desc_lists, in Johnson/RunOne/Sound/).

Object: Key.descriptionFromSource X N P's first chain's flat list; lookupKind; hearE.
User: held_words: k03key_out (K03KeyOut.lean). k03key_sits: none by name (its parts are spent in
k3_relLaw, SeatK3.lean, keeps_k3, KeepsAtRows.lean, and k03key_out).
Letters: X, N, P. Premise: the description's tests on the plan.

Limits. A joining of proved parts under one statement. "All the places of the kind" is said of the
TAGS: a tag is the block's own word for its kind: that no block with another tag calls hearE is not
said. That two blocks of the description do not bear one place is not said here. Nothing on
soundness.

-/
import Johnson.RunOne.Law.WalkAtFK
import Johnson.RunOne.Sound.KeyListsAtFK
import Johnson.Desc.Sound.PaidAtDesc
import OnBytes.Slice.KeyLeavesTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K03KeySits
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc (Block Place KindName viewWordsBelowPrime)
open VerifiableInference.Desc.Sound (held)
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState Claim Source lookupSeat)
open Johnson.RunOne.Sound (FK fk_K3_at rowsOf desc_lists)
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.FrontSteps
open Johnson.RunOne.Law.WalkAtFK

/-- A view whose words pass the test passes it with no opened column. -/
theorem words_nil {rs : List Fmt.RoundView} {cols : List (ℕ × ℕ × List UInt64)}
    (h : viewWordsBelowPrime ⟨rs, cols⟩ = true) : viewWordsBelowPrime ⟨rs, []⟩ = true := by
  unfold viewWordsBelowPrime at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  exact ⟨h.1, rfl⟩

/-- **THE SEVENTH PREMISE'S PAYER**: a held block's yes says that the rounds' words pass the test:
"held" is "below", which makes that test, then the lift to the pair. -/
theorem held_words {Q S Cl : Type} (b : Block S Cl) (a a' : Q × S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (h : (held b : Block (Q × S) Cl).decide a rs gs = .ok a') : viewWordsBelowPrime ⟨rs, []⟩ = true := by
  have h' : ((if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide a.2 rs gs
      else .error "a word is not below the prime").map fun s => (a.1, s)) = .ok a' := h
  split at h'
  · rename_i hw
    exact words_nil hw
  · cases h'

/-- The first chain's table of wanted places bears the tag K3 at piece 2 of a lookup's link alone.
-/
theorem wantedFirst_k3 (one : OneTime) : ∀ r ∈ VerifiableInference.Desc.Key.wantedFirst one,
    r.1.kind = KindName.K3 → ∃ l < one.ranges.lookups.length, r.1 = ⟨1, some l, 2, .K3⟩ := by
  intro r hr hk
  simp only [VerifiableInference.Desc.Key.wantedFirst, List.mem_append] at hr
  rcases hr with (((h | h) | h) | h) | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact absurd hk (by simp)
  · obtain ⟨x, hx, h⟩ := List.mem_flatMap.1 h
    have hlt := Leaves.snd_lt_of_mem_zipIdx _ 0 x hx
    simp only [VerifiableInference.Desc.Key.wantedLink, List.mem_cons, List.not_mem_nil,
      or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hk (by simp)
    · exact absurd hk (by simp)
    · refine ⟨x.2, ?_, rfl⟩
      have e : (Wf.lookupsOf one.ranges (Wf.matrixOf one.lin)).length =
          one.ranges.lookups.length := List.length_map _
      omega
    · exact absurd hk (by simp)
    · exact absurd hk (by simp)
    · exact absurd hk (by simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> exact absurd hk (by simp)
  · split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact absurd hk (by simp)
    · cases h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact absurd hk (by simp)

/-- The two later chains' tables bear it nowhere. -/
theorem wantedShared_k3 (S : LinShape) : ∀ r ∈ VerifiableInference.Desc.Key.wantedShared S,
    r.1.kind ≠ KindName.K3 := by
  intro r hr
  simp only [VerifiableInference.Desc.Key.wantedShared, List.mem_append] at hr
  rcases hr with (h | h) | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      simp
    · cases h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    simp

theorem wantedSecond_k3 (S : LinShape) : ∀ r ∈ VerifiableInference.Desc.Key.wantedSecond S,
    r.1.kind ≠ KindName.K3 := by
  intro r hr
  simp only [VerifiableInference.Desc.Key.wantedSecond, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **THE PLACES OF THE DESCRIPTION'S BLOCKS THAT BEAR THE TAG K3 ARE JUST ⟨1, some l, 2⟩, l BELOW
THE NUMBER OF LOOKUPS**: under the tests on the plan and wantedOk. A tag is the block's own word for
its kind. -/
theorem k3_places (hp : (VerifiableInference.Desc.Key.descriptionFromSource X N P).planOk = true)
    (hw : (VerifiableInference.Desc.Key.descriptionFromSource X N P).wantedOk = true) :
    (∀ b ∈ (VerifiableInference.Desc.Key.descriptionFromSource X N P).first.blocksInOrder, b.place.kind = KindName.K3 →
      ∃ l < X.Y.k.oneTime.ranges.lookups.length, b.place = ⟨1, some l, 2, .K3⟩) ∧
    (∀ b ∈ (VerifiableInference.Desc.Key.descriptionFromSource X N P).shared.blocksInOrder, b.place.kind ≠ KindName.K3) ∧
    ∀ b ∈ (VerifiableInference.Desc.Key.descriptionFromSource X N P).second.blocksInOrder, b.place.kind ≠ KindName.K3 := by
  obtain ⟨h₁, h₂, h₃⟩ := desc_lists X N P hp hw
  have mem : ∀ {S Cl : Type} (bs : List (Block S Cl)) (b : Block S Cl), b ∈ bs →
      (b.place, b.rounds.length) ∈ rowsOf bs := fun bs b hb => List.mem_map.2 ⟨b, hb, rfl⟩
  refine ⟨fun b hb hk => wantedFirst_k3 _ _ (by rw [← h₁]; exact mem _ b hb) hk,
    fun b hb => wantedShared_k3 _ _ (by rw [← h₂]; exact mem _ b hb),
    fun b hb => wantedSecond_k3 _ _ (by rw [← h₃]; exact mem _ b hb)⟩

/-- **THE KIND'S OWN BLOCK SITS IN THE KEY FILE'S WRITTEN DESCRIPTION.** The row's text in the list
of what is owed ("K03key_sits"): "in the key file's written description: the entry
of the description's list of blocks at each place of the kind is the constant of which K03key_law
speaks, at the plan's numbers, under the seat's wrappers alone, or its yes gives that law's premise.
The row says nothing before its law has a Lean statement". Here: the entry is lookupKind at the plan's
numbers, under no wrapper; K03key_law speaks of hearE; the block's yes gives hearE's yes; with the
record's half in front, and with the yes of the block as a piece holds it, ALL SEVEN premises of
Law.out are given. That they compose to Law.out's conclusion: k03key_out (K03KeyOut.lean). -/
theorem k03key_sits (hp : (VerifiableInference.Desc.Key.descriptionFromSource X N P).planOk = true) (l : ℕ)
    (hl : l < X.Y.k.oneTime.ranges.lookups.length) :
    (VerifiableInference.Desc.Key.descriptionFromSource X N P).first.blocksInOrder[2 + (6 * l + 2)]? =
      some (lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (VerifiableInference.Desc.Key.lookupPlace X.set
              l
          (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
              l)))) ∧
    ((VerifiableInference.Desc.Key.lookupPlace X.set l
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
          l))).face = faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
              X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l)) ∧
      (∀ (T : Type) (hs : List Slot) (st : T), FaceIs (datK T X.Y.k.oneTime.ranges.messageId
        (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l) hs) st (faceOfLkp (Wf.lookupOf
            X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))))
                ∧
      (Lk6.pubOf (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof
          X.Y.k.oneTime l))).Adm Cb.Gl.p) ∧
    (∀ (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      (lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (VerifiableInference.Desc.Key.lookupPlace X.set l
          (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
              l)))).decide s rs gs = .ok s' →
      ∃ F g G es, lookupSeat.fork s = some F ∧ F.next = (VerifiableInference.Desc.Key.lookupPlace
          X.set l
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
          l))).first ∧
        F.ns = (VerifiableInference.Desc.Key.lookupPlace X.set l
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
          l))).ns ∧ (VerifiableInference.Desc.Key.lookupPlace X.set l
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
          l))).entries = some es ∧
        hearE (VerifiableInference.Desc.Key.lookupPlace X.set l
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
          l))).face es F rs = some (g, G) ∧ s' = lookupSeat.put s g G) ∧
    (∀ (Q : Type) (a a' : Q × FirstState) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      (held (lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (VerifiableInference.Desc.Key.lookupPlace X.set
              l
          (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
              l)))) :
        Block (Q × FirstState) Claim).decide a rs gs = .ok a' → viewWordsBelowPrime ⟨rs, []⟩ = true) ∧
    (lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (VerifiableInference.Desc.Key.lookupPlace X.set l
          (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
              l))) :
      Block FirstState Claim).place = ⟨1, some l, 2, .K3⟩ ∧
    ∀ s : FirstState, RecK X l 2 s →
      (∀ F0, lookupSeat.fork s = some F0 → PscRun.Sized F0) ∧
        ∃ o k : ℕ → Slot, HomeIs (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf
            X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))) 0 o k fun j => s.base.home.getD j default :=
                by
  have hW := fk_admitted X N P hp
  have hadm := Lk6.adm_of_tests X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) _
    (tests_at hW hl).2.1 (tests_at hW hl).2.2
  refine ⟨fk_K3_at X N P l _ (look_at X.Y.k.oneTime l hl), ⟨rfl, fun T hs st =>
    faceIsK T _ _ _ hs st hadm (d_le (tests_at hW hl).2.1), hadm⟩,
    fun s s' rs gs h => block_law _ _ _ _ _ h, fun Q a a' rs gs h => held_words _ a a' rs gs h, rfl,
    fun s hr => ?_⟩
  obtain ⟨⟨hS, hhome, -, -, -, hsz⟩, -⟩ := hr
  refine ⟨hS, ?_⟩
  rw [hhome]
  exact ⟨_, _, homeIs_of_size _ _ _ hsz⟩

end Johnson.RunOne.Law.K03KeySits

#print axioms Johnson.RunOne.Law.K03KeySits.held_words
#print axioms Johnson.RunOne.Law.K03KeySits.k3_places
#print axioms Johnson.RunOne.Law.K03KeySits.k03key_sits
