-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/K3FitsOfStated.lean: FROM ONE EQUATION ON A BOOK's LIST OF ENTRIES TO THE LOOKUPS'
THREE PUBLIC TESTS ON THE BOOK (bookFits, placeFits: Honest/K3/Law/RowLends.lean; startsFit:
Honest/K3/Law/MasksBook.lean), AT EVERY ONE OF A LIST OF LOOKUPS' PLACES. General in the book, the
table of rows, the counts and the list; nothing is evaluated. Written by the authors of the honest
side of the linear claim's shared rounds (K14), not by the lookups' authors; the three tests are
theirs and are called, not written anew. A structure, six definitions with code, statements with
their proofs.

Limits.
  * IT SAYS NOTHING OF ANY BOOK UNTIL ITS FIRST PREMISE hE IS SHOWN THERE: that the book's entries
    whose spender stands at one of the places are, in the book's own order, the runs that the parts
    state, place by place and stage by stage. No file shows hE at any book.
  * AT A STAGE THAT SENDS NOTHING (shift, alpha, join, the lines, zero: Stage.call is none) THE PART
    STATES NO RUN, AND bookFits AND startsFit SAY THERE ONLY THAT NO ENTRY NAMES THE PART AND THAT
    IT HAS NO COIN OF ITS OWN. At a face with one part of v levels and a table of d levels these are
    4 + v + d of 37 + 2 (v + d) stages: some two fifths.
  * owner and base are the caller's letters (K3At.o, K3At.base). That a sender lays its mask row at
    the coins of these numbers is not spoken of.
  * The tests read of a face five numbers alone (tests_face_congr): of the face's three functions
    nothing follows.
  * Numbers and addresses on public data: nothing on soundness, completeness or hiding.

  K3At            what the tests read at a place: the place with its face; the lookup's first
                  scalar; the mask row's owner; where the row's entries begin among the owner's
                  coins
  K3At.block, K3At.stated, k3Stated   the runs that the parts state, each as an entry of a book: of
                  one stage; of one place, stage by stage; of all places: the names and counts are
                  runsAt's, the owners and starts are the right side of startsFit
  noRowAt, insideAll, cutsAt   three lesser premises, as tests with code
  filter_blocks, filter_sites   a filter by one address, over a list that is laid block by block,
                  each block's entries bearing its own address, no address twice: it is that block
  entries_of_stated   **under hE, and where no two members stand at one place: the entries that name
                  the part of a stage (entriesAt) are that stage's block**
  fits_of_stated  **THE LAW: under hE, no place twice, no row at a place, every stated run inside
                  its owner's coins, the cuts the stages' rounds: all three tests accept at every
                  member**
  tests_face_congr   the three tests' answers are the same at two faces with the same shifted, mu,
                  planes, parts and d, whatever their rounds in front
  fits_at_every_face   the law's conclusion at every such face

No option is raised. The file stands in this side library because what will call it does.
What is assumed. Nothing beside each statement's own premises.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.MasksBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Place)

/-- What the three tests read at a lookup's place: the place with its face; the lookup's first
scalar; the mask row's owner; where that row's entries begin among the owner's coins. -/
structure K3At where
  at_ : At
  first : Nat
  o : Addr
  base : Due

/-- The runs that the part of one stage states, each as an entry of a book. x: the stage and its
number in the row. -/
def K3At.block (s : K3At) (x : Stage × Nat) : List Ahead :=
  (runsAt s.at_ x.1 x.2).zipIdx.map fun y =>
    ⟨y.1.1, s.o, s.base.plus ⟨0, s.first + firstSlot s.at_.face x.1 +
      (if y.2 == 0 then 0 else x.1.own s.at_.face)⟩, y.1.2, ⟨s.at_.place, x.2⟩, true⟩

/-- All stages' runs, stage by stage. -/
def K3At.stated (s : K3At) : List Ahead := (stages s.at_.face).zipIdx.flatMap s.block

/-- All sites' runs, site by site. -/
def k3Stated (S : List K3At) : List Ahead := S.flatMap K3At.stated

/-! ## 1 Lists laid block by block -/

theorem snd_ge_of_mem_zipIdx {α : Type} : ∀ (l : List α) (k : Nat) (x : α × Nat),
    x ∈ l.zipIdx k → k ≤ x.2
  | [], _, _, h => by simp at h
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with rfl | h'
    · exact Nat.le_refl _
    · exact Nat.le_of_succ_le (snd_ge_of_mem_zipIdx l (k + 1) x h')

/-- A filter by one address, over a list that is laid block by block, each block's entries bearing
the block's own number: it is that block. -/
theorem filter_blocks {α : Type} (blk : α × Nat → List Ahead) (p : Place)
    (hb : ∀ x e, e ∈ blk x → e.spender = ⟨p, x.2⟩) :
    ∀ (l : List α) (k : Nat) (x : α × Nat), x ∈ l.zipIdx k →
      ((l.zipIdx k).flatMap blk).filter (fun e => e.spender == ⟨p, x.2⟩) = blk x
  | [], _, _, h => by simp at h
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h ⊢
    rw [List.flatMap_cons, List.filter_append]
    rcases List.mem_cons.1 h with rfl | h'
    · have h1 : (blk (a, k)).filter (fun e => e.spender == ⟨p, (a, k).2⟩) = blk (a, k) :=
        List.filter_eq_self.2 fun e he => by rw [hb _ e he]; exact beq_self_eq_true _
      have h2 : ((l.zipIdx (k + 1)).flatMap blk).filter
          (fun e => e.spender == ⟨p, (a, k).2⟩) = [] :=
        List.filter_eq_nil_iff.2 fun e he hq => by
          obtain ⟨y, hy, hey⟩ := List.mem_flatMap.1 he
          rw [hb y e hey] at hq
          have h3 := snd_ge_of_mem_zipIdx l (k + 1) y hy
          have h4 : y.2 = k := congrArg Addr.part (beq_iff_eq.1 hq)
          omega
      rw [h1, h2, List.append_nil]
    · have hk := snd_ge_of_mem_zipIdx l (k + 1) x h'
      have h1 : (blk (a, k)).filter (fun e => e.spender == ⟨p, x.2⟩) = [] :=
        List.filter_eq_nil_iff.2 fun e he hq => by
          rw [hb _ e he] at hq
          have h4 : k = x.2 := congrArg Addr.part (beq_iff_eq.1 hq)
          omega
      rw [h1, List.nil_append]
      exact filter_blocks blk p hb l (k + 1) x h'

theorem block_spender (s : K3At) (x : Stage × Nat) (e : Ahead) (h : e ∈ s.block x) :
    e.spender = ⟨s.at_.place, x.2⟩ := by
  unfold K3At.block at h
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 h
  rfl

theorem stated_place {s : K3At} {e : Ahead} (h : e ∈ s.stated) :
    e.spender.place = s.at_.place := by
  unfold K3At.stated at h
  obtain ⟨x, -, hx⟩ := List.mem_flatMap.1 h
  rw [block_spender s x e hx]

/-- Where no two sites stand at one place: of all sites' runs those at a site's address are among
that site's own. -/
theorem filter_sites : ∀ (S : List K3At), (S.map (·.at_.place)).Nodup → ∀ s ∈ S, ∀ i : Nat,
    (k3Stated S).filter (fun e => e.spender == ⟨s.at_.place, i⟩) =
      s.stated.filter (fun e => e.spender == ⟨s.at_.place, i⟩)
  | [], _, _, h, _ => by simp at h
  | t :: S, hn, s, hs, i => by
    unfold k3Stated
    rw [List.flatMap_cons, List.filter_append]
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hs with rfl | hs'
    · have h2 : (S.flatMap K3At.stated).filter (fun e => e.spender == ⟨s.at_.place, i⟩) = [] :=
        List.filter_eq_nil_iff.2 fun e he hq => by
          obtain ⟨u, hu, heu⟩ := List.mem_flatMap.1 he
          have h3 := stated_place heu
          have h4 : e.spender.place = s.at_.place := congrArg Addr.place (beq_iff_eq.1 hq)
          exact hn.1 (List.mem_map.2 ⟨u, hu, h3.symm.trans h4⟩)
      rw [h2, List.append_nil]
    · have h1 : t.stated.filter (fun e => e.spender == ⟨s.at_.place, i⟩) = [] :=
        List.filter_eq_nil_iff.2 fun e he hq => by
          have h3 := stated_place he
          have h4 : e.spender.place = s.at_.place := congrArg Addr.place (beq_iff_eq.1 hq)
          exact hn.1 (List.mem_map.2 ⟨s, hs', h4.symm.trans h3⟩)
      rw [h1, List.nil_append]
      exact filter_sites S hn.2 s hs' i

/-! ## 2 The book's entries at a part of a site -/

/-- **Where the book's entries at the sites' places are the stated runs: the entries that name the
part of a stage are that stage's block.** -/
theorem entries_of_stated {B : ProverCoinCounts} {S : List K3At}
    (hE : B.ahead.filter (fun e => S.any fun s => s.at_.place == e.spender.place) = k3Stated S)
    (hN : (S.map (·.at_.place)).Nodup) {s : K3At} (hs : s ∈ S) {x : Stage × Nat}
    (hx : x ∈ (stages s.at_.face).zipIdx) : entriesAt B s.at_.place x.2 = s.block x := by
  have h1 : entriesAt B s.at_.place x.2 =
      (B.ahead.filter (fun e => S.any fun t => t.at_.place == e.spender.place)).filter
        (fun e => e.spender == ⟨s.at_.place, x.2⟩) := by
    unfold entriesAt
    rw [List.filter_filter]
    apply List.filter_congr
    intro e _
    show (e.spender == (⟨s.at_.place, x.2⟩ : Addr)) =
      ((e.spender == (⟨s.at_.place, x.2⟩ : Addr)) &&
        (S.any fun t => t.at_.place == e.spender.place))
    cases hq : (e.spender == (⟨s.at_.place, x.2⟩ : Addr)) with
    | false => rfl
    | true =>
      have h2 : e.spender.place = s.at_.place := congrArg Addr.place (beq_iff_eq.1 hq)
      have h3 : (S.any fun t => t.at_.place == e.spender.place) = true :=
        List.any_eq_true.2 ⟨s, hs, by rw [h2]; exact beq_self_eq_true _⟩
      rw [h3]
      rfl
  rw [h1, hE, filter_sites S hN s hs x.2]
  exact filter_blocks s.block s.at_.place (block_spender s) _ 0 x hx

theorem block_mem_stated {S : List K3At} {s : K3At} (hs : s ∈ S) {x : Stage × Nat}
    (hx : x ∈ (stages s.at_.face).zipIdx) {e : Ahead} (he : e ∈ s.block x) : e ∈ k3Stated S :=
  List.mem_flatMap.2 ⟨s, hs, List.mem_flatMap.2 ⟨x, hx, he⟩⟩

theorem snd_lt_of_mem_zipIdx {α : Type} : ∀ (l : List α) (k : Nat) (x : α × Nat),
    x ∈ l.zipIdx k → x.2 < k + l.length
  | [], _, _, h => by simp at h
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with rfl | h'
    · show k < k + (l.length + 1)
      omega
    · have := snd_lt_of_mem_zipIdx l (k + 1) x h'
      show x.2 < k + (l.length + 1)
      omega

/-- Where no two sites stand at one place, two members at one place are one. -/
theorem site_unique : ∀ {S : List K3At}, (S.map (·.at_.place)).Nodup → ∀ {t s : K3At}, t ∈ S →
    s ∈ S → t.at_.place = s.at_.place → t ≠ s → False
  | [], _, _, _, ht, _, _, _ => by simp at ht
  | u :: S, hn, t, s, ht, hs, hp, hne => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 ht with rfl | ht'
    · rcases List.mem_cons.1 hs with rfl | hs'
      · exact hne rfl
      · exact hn.1 (List.mem_map.2 ⟨s, hs', hp.symm⟩)
    · rcases List.mem_cons.1 hs with rfl | hs'
      · exact hn.1 (List.mem_map.2 ⟨t, ht', hp⟩)
      · exact site_unique hn.2 ht' hs' hp hne

/-! ## 3 The tests' other clauses -/

/-- A table without a row at a place has the count 0 at each of its addresses. -/
theorem dueAt_of_no_place : ∀ (rows : List (Addr × Due)) (a : Addr),
    (∀ r ∈ rows, r.1.place ≠ a.place) → dueAt rows a = ⟨0, 0⟩
  | [], _, _ => rfl
  | (k, v) :: l, a, h => by
    have h1 : (a == k) = false := by
      cases hq : (a == k) with
      | false => rfl
      | true =>
        exact absurd (congrArg Addr.place (beq_iff_eq.1 hq)).symm (h (k, v) List.mem_cons_self)
    have h2 := dueAt_of_no_place l a fun r hr => h r (List.mem_cons_of_mem _ hr)
    unfold dueAt at h2 ⊢
    rw [List.lookup_cons, h1]
    exact h2

/-- No row of the table stands at a site's place: as a test with code. -/
def noRowAt (rows : List (Addr × Due)) (S : List K3At) : Bool :=
  rows.all fun r => !S.any fun s => s.at_.place == r.1.place

theorem noRowAt_ne {rows : List (Addr × Due)} {S : List K3At} (h : noRowAt rows S = true)
    {s : K3At} (hs : s ∈ S) : ∀ r ∈ rows, r.1.place ≠ s.at_.place := by
  intro r hr e
  have h1 := List.all_eq_true.1 h r hr
  have h2 : (S.any fun t => t.at_.place == r.1.place) = true :=
    List.any_eq_true.2 ⟨s, hs, by rw [e]; exact beq_self_eq_true _⟩
  rw [h2] at h1
  cases h1

/-- Every stated run lies inside its owner's coins: as a test with code. -/
def insideAll (due : Addr → Due) (l : List Ahead) : Bool :=
  l.all fun e => decide (e.start.f + e.count.f ≤ (due e.owner).f) &&
    decide (e.start.e + e.count.e ≤ (due e.owner).e)

/-- At every site the book's cut is the stages' rounds: as a test with code. -/
def cutsAt (B : ProverCoinCounts) (S : List K3At) : Bool :=
  S.all fun s => B.cuts.lookup s.at_.place ==
    some ((stages s.at_.face).map (Stage.rounds s.at_.face))

/-! ## 4 The law -/

/-- **WHERE THE BOOK's ENTRIES AT THE SITES' PLACES ARE THE PARTS' STATED RUNS, SITE BY SITE AND
STAGE BY STAGE; NO TWO SITES STAND AT ONE PLACE; THE TABLE HAS NO ROW AT A SITE's PLACE; EVERY
STATED RUN LIES INSIDE ITS OWNER's COINS; AND THE CUTS ARE THE STAGES' ROUNDS: THE LOOKUPS' THREE
TESTS ON THE BOOK ACCEPT AT EVERY SITE.** -/
theorem fits_of_stated {B : ProverCoinCounts} {rows : List (Addr × Due)} {due : Addr → Due} {S : List K3At}
    (hE : B.ahead.filter (fun e => S.any fun s => s.at_.place == e.spender.place) = k3Stated S)
    (hN : (S.map (·.at_.place)).Nodup) (hR : noRowAt rows S = true)
    (hI : insideAll due (k3Stated S) = true) (hC : cutsAt B S = true) :
    ∀ s ∈ S, bookFits B rows due s.at_ = true ∧ startsFit B s.at_ s.first s.o s.base = true ∧
      placeFits B rows s.at_ = true := by
  intro s hs
  refine ⟨?_, ?_, ?_⟩
  · unfold bookFits
    refine List.all_eq_true.2 fun x hx => ?_
    rw [entries_of_stated hE hN hs hx]
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [dueAt_of_no_place rows ⟨s.at_.place, x.2⟩ (noRowAt_ne hR hs)]
      exact beq_self_eq_true _
    · refine List.all_eq_true.2 fun e he => ?_
      unfold K3At.block at he
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 he
      rfl
    · apply beq_iff_eq.2
      unfold K3At.block
      rw [List.map_map]
      exact List.zipIdx_map_fst 0 (runsAt s.at_ x.1 x.2)
    · refine List.all_eq_true.2 fun e he => ?_
      exact List.all_eq_true.1 hI e (block_mem_stated hs hx he)
  · unfold startsFit
    refine List.all_eq_true.2 fun x hx => ?_
    rw [entries_of_stated hE hN hs hx]
    apply beq_iff_eq.2
    unfold K3At.block
    rw [List.map_map]
    rfl
  · unfold placeFits
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨⟨List.all_eq_true.1 hC s hs, ?_⟩, ?_⟩
    · refine List.any_eq_false.2 fun r hr hq => ?_
      rw [Bool.and_eq_true] at hq
      exact noRowAt_ne hR hs r hr (beq_iff_eq.1 hq.1)
    · refine List.any_eq_false.2 fun e he hq => ?_
      rw [Bool.and_eq_true] at hq
      have hp : e.spender.place = s.at_.place := beq_iff_eq.1 hq.1
      have hm : e ∈ k3Stated S := by
        rw [← hE]
        exact List.mem_filter.2
          ⟨he, List.any_eq_true.2 ⟨s, hs, by rw [hp]; exact beq_self_eq_true _⟩⟩
      obtain ⟨t, ht, het⟩ := List.mem_flatMap.1 hm
      have hts : t.at_.place = s.at_.place := (stated_place het).symm.trans hp
      have hEq : t = s := by
        by_contra hne
        exact site_unique hN ht hs hts hne
      subst hEq
      obtain ⟨x, hx, hex⟩ := List.mem_flatMap.1 het
      have h1 := snd_lt_of_mem_zipIdx _ 0 x hx
      rw [block_spender t x e hex] at hq
      have h2 : (stages t.at_.face).length ≤ x.2 := of_decide_eq_true hq.2
      omega

/-! ## 5 What the tests read of a face -/

/-- **The three tests read of a face its five numbers alone**; of the place's record, the place and
the face. -/
theorem tests_face_congr {f g : LFace} (h1 : f.shifted = g.shifted) (h2 : f.mu = g.mu)
    (h3 : f.planes = g.planes) (h4 : f.parts = g.parts) (h5 : f.d = g.d) (B : ProverCoinCounts)
    (rows : List (Addr × Due)) (due : Addr → Due) (p : Place) (n m first : Nat) (o : Addr)
    (base : Due) :
    bookFits B rows due ⟨p, f, n⟩ = bookFits B rows due ⟨p, g, m⟩ ∧
      startsFit B ⟨p, f, n⟩ first o base = startsFit B ⟨p, g, m⟩ first o base ∧
      placeFits B rows ⟨p, f, n⟩ = placeFits B rows ⟨p, g, m⟩ := by
  cases f
  cases g
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  exact ⟨rfl, rfl, rfl⟩

/-- **The law's conclusion at every face with a member's five numbers.** -/
theorem fits_at_every_face {B : ProverCoinCounts} {rows : List (Addr × Due)} {due : Addr → Due}
    {S : List K3At}
    (hE : B.ahead.filter (fun e => S.any fun s => s.at_.place == e.spender.place) = k3Stated S)
    (hN : (S.map (·.at_.place)).Nodup) (hR : noRowAt rows S = true)
    (hI : insideAll due (k3Stated S) = true) (hC : cutsAt B S = true) :
    ∀ s ∈ S, ∀ (f : LFace) (n : Nat), f.shifted = s.at_.face.shifted → f.mu = s.at_.face.mu →
      f.planes = s.at_.face.planes → f.parts = s.at_.face.parts → f.d = s.at_.face.d →
      bookFits B rows due ⟨s.at_.place, f, n⟩ = true ∧
        startsFit B ⟨s.at_.place, f, n⟩ s.first s.o s.base = true ∧
        placeFits B rows ⟨s.at_.place, f, n⟩ = true := by
  intro s hs f n h1 h2 h3 h4 h5
  obtain ⟨a, b, c⟩ := fits_of_stated hE hN hR hI hC s hs
  obtain ⟨e1, e2, e3⟩ := tests_face_congr h1 h2 h3 h4 h5 B rows due s.at_.place n s.at_.base
    s.first s.o s.base
  exact ⟨e1.trans a, e2.trans b, e3.trans c⟩

end AtFullSide.K14

#print axioms AtFullSide.K14.filter_blocks
#print axioms AtFullSide.K14.filter_sites
#print axioms AtFullSide.K14.entries_of_stated
#print axioms AtFullSide.K14.dueAt_of_no_place
#print axioms AtFullSide.K14.site_unique
#print axioms AtFullSide.K14.fits_of_stated
#print axioms AtFullSide.K14.tests_face_congr
#print axioms AtFullSide.K14.fits_at_every_face
