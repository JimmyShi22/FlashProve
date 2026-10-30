-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/OpensAtW.lean: no soundness is claimed.
The law «opens» of the last chain's ledger (Johnson/LLT25R/LastLedger.lean): the promise FirstOpens at the proximity test's own record, from the book-keeping at border 2.
firstOpens_at_last (Johnson/Desc/K12/Coin/FirstOpensAtLast.lean) has the promise under the two clauses of the test on taken sources, «the mask has come», and the named premises seated · first · alone · up; firstOpens_at_book brings its letter «no» to one public book under a fifth, book. The table's book-keeping at border 2 (shapeAt … 2, Johnson/Desc/Last/ShapeAt.lean) holds the test on taken sources itself and what K14's second part has laid (behindOk_of_two, ShapeGives.lean). Here these are joined:
  enterOwn_is        what the seat's door returns: the record's statement, book, own group's number and mask
  tied_a | tied_b    the two clauses (a) | (b), off Tied (Johnson/Desc/Third/Law/Sources.lean)
  alone_of_laid      paid: «alone»: Omega's copy lies in a new tree; every other message's place is an old one, and an old place's tree lies below the old number of trees (BookFits of the book that was handed)
  omega_place        paid: Omega's copy's place is the old number of trees
  last_of_laid       paid: no place of D.ts lies behind it
  BookAt B₀ ω₀ s     the one premise on the record that is left: the record names Omega's copy ω₀; its book agrees with the public book B₀ on the tree in which ω₀ lies, and every tree that the record's book has has B₀'s number at its place (B₀ may be longer)
  RisesBelow B₀ ω₀   a condition on the public book alone: below Omega's tree the trees' numbers rise strictly (risesBelow_of_numbered: a book in which a number is its place is such a one) · up_of_rise: «up» from that
  **opens_at_shape** shapeAt p ‹the block's rounds› 2 f o s = true → enterOwn s = .ok t → BookAt B₀ ω₀ s → RisesBelow B₀ ω₀ → FirstOpens π (numAt F.t₁ F.t₂ 2) (fun z => wholeNo F.t₁ F.t₂ (plOf B₀ ω₀ z)) base t, under F.data's yes · F.treeSharingOk · the block's test on the plan · seated · first · ownMask = false · two stages at least
  **opens_at_W**     the same at the description that onlineDescription makes and the place W: seated and first are paid (FirstAtW.lean)
  **opens_field**    the ledger's field's form, general in the table's letters: (∀ a, onQ₃ … (fillAt p R hand ended) … 2 a → BookAt B₀ ω₀ a.1.2) → ∀ a t, onQ₃ … 2 a → enterOwn a.1.2 = .ok t → FirstOpens π (numAt t₁ t₂ 2) (fun z => wholeNo t₁ t₂ (plOf B₀ ω₀ z)) base t (shapeAt_of_onL, Johnson/Desc/Last/ShapeAtTable.lean)
  HandedNumbers n₁ ft nΩ f o   the same debt in numbers, of what was handed alone: the first chain's book has n₁ trees · the tree at place j has the number ft + j (the second clause of Numbered ft, Johnson/Desc/Book/BookNumbers.lean) · Omega's tree in the shared chain's book has the number nΩ
  start₃E_roots · HandedRoots · handedNumbers_of_roots   the first clause can be said of the roots that were handed (f.roots = n₁): the start's own running test rootsB ties them to the book's number of trees
  noAt t₁ t₂ n₁ ft nΩ   the letter «no» as a closed function of five public numbers: wholeNo t₁ t₂ (if z = n₁ then (1, nΩ) else (0, ft + z))
  **opens_at_numbers** | **opens_field_numbers**   the law at noAt from HandedNumbers, and the ledger's field's form from HandedRoots: no public book, no RisesBelow (opens_at_shape is called at the record's own book; FirstOpens.congr_no brings «no» to noAt)
Left, by name. On the record: BookAt, or HandedNumbers, or HandedRoots. On the plan (tests with code or values): the block's planOk · π.nums.ownMask = false · 2 ≤ π.nums.stages.length · RisesBelow · F.data's yes · F.treeSharingOk · F.t₁ + F.t₂ ≤ base.
Does not show. That any record inside the promise meets BookAt at a public book: that a tree's number in the first chain's book is fixed by the plan is the rows' on the books' numbers. No member. Nothing on soundness.
-/
import Johnson.ToldDescR.FirstAtW
import Johnson.ToldDescR.TiesOne
import Johnson.Desc.K12.Coin.FirstOpensAtLast
import Johnson.Desc.K12.Coin.FirstOpensUp
import Johnson.Desc.Last.ShapeGives
import Johnson.Desc.Last.ShapeAtTable
import Johnson.Desc.Sound.BordersLastQ
import Johnson.Desc.Third.Law.StartBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.K12.Seat (onOwn enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut Border Laid takenOf opensTaken)
open VerifiableInference.Desc.Third.Law (Tied start₃E_book start₃E_border start₃E_inv
  firstOutFrom_book)
open VerifiableInference.Desc.Last (Handed shapeAt fillAt BehindOk behindOk_of_two tied_of
  shapeAt_of_onL)
open VerifiableInference.Desc.Sound (Frame onQ₃)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Book (BookFits placed_of_fits)

/-- What the seat's door returns. -/
theorem enterOwn_is {s : S₃} {t : T12} (h : enterOwn s = .ok t) :
    t = { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
          mask := s.loc.mask } := (Except.ok.inj h).symm

/-- Clause (a) of the test on taken sources. -/
theorem tied_a {R : List Fmt.DeclaredRound} {ts : List (ℕ × ℕ)}
    (h : (ts.all fun x => opensTaken R x.1 x.2) = true) :
    ∀ x ∈ ts, ∃ r ∈ R, ∃ o ∈ r.opens, o.2 = .taken x.1 x.2 := by
  intro x hx
  have h1 := List.all_eq_true.1 h x hx
  unfold opensTaken at h1
  obtain ⟨r, hr, h2⟩ := List.any_eq_true.1 h1
  obtain ⟨o, ho, h3⟩ := List.any_eq_true.1 h2
  rw [Bool.and_eq_true] at h3
  exact ⟨r, hr, o, ho, of_decide_eq_true h3.1⟩

/-- Clause (b). -/
theorem tied_b {R : List Fmt.DeclaredRound} {ts : List (ℕ × ℕ)}
    (h : ((R.flatMap (·.opens)).all fun o =>
      match o.2 with
      | .own _ => true
      | .taken c n => ts.contains (c, n)) = true) :
    ∀ r ∈ R, ∀ o ∈ r.opens, ∀ c n, o.2 = .taken c n → (c, n) ∈ ts := by
  intro r hr o ho c n e
  have h1 := List.all_eq_true.1 h o (List.mem_flatMap.2 ⟨r, hr, ho⟩)
  rw [e] at h1
  simpa using h1

section
variable {S : Params.LinShape} {s₀ s : S₃} {b : Border} {y : OnBytes.Oracle} {G : OnBytes.Group}
  {dot : OnBytes.Row}

theorem omega_is (L : Laid S s₀ s b y G dot) : s.loc.omega = s₀.st.oracles.size := by
  rw [L.loc]

/-- Omega's copy's place: the old number of trees. -/
theorem omega_place (L : Laid S s₀ s b y G dot) :
    (s.book.place[s.loc.omega]?).map (·.1) = some s₀.book.trees.size := by
  rw [omega_is L, L.place]
  rfl

/-- **«alone»**: no other message lies in the tree of Omega's copy. -/
theorem alone_of_laid (L : Laid S s₀ s b y G dot) (hf : BookFits s₀.book) (i : ℕ) (q : ℕ × ℕ)
    (pp z : ℕ) (hq : s.book.place[s.loc.omega]? = some q) (hi : s.book.place[i]? = some (z, pp))
    (e : q.1 = z) : i = s.loc.omega := by
  rw [omega_is L] at hq ⊢
  rw [L.place] at hq
  obtain rfl := Option.some.inj hq
  by_contra hne
  have h1 : i < s.book.place.size := (Array.getElem?_eq_some_iff.1 hi).1
  rw [L.places] at h1
  have h2 : i < s₀.book.place.size := by
    have := L.step
    omega
  rw [L.oldPlaces i h2] at hi
  have h3 := placed_of_fits hf i (z, pp) hi
  have e' : s₀.book.trees.size = z := e
  have h3' : z < s₀.book.trees.size := h3
  omega

end

/-- **The one premise on the record that is left**: it names Omega's copy ω₀, and its book agrees
with the public book B₀ on the tree in which ω₀ lies and on every tree's number. -/
structure BookAt (B₀ : TreeBook) (ω₀ : ℕ) (s : S₃) : Prop where
  omega : s.loc.omega = ω₀
  place : (B₀.place[ω₀]?).map (·.1) = (s.book.place[ω₀]?).map (·.1)
  numbers : ∀ (z : ℕ) (T : Tree), s.book.trees[z]? = some T →
    (B₀.trees[z]?).map (·.number) = some T.number

/-- On the public book alone: below Omega's tree the trees' numbers rise strictly. -/
def RisesBelow (B₀ : TreeBook) (ω₀ : ℕ) : Prop :=
  ∀ zω, (B₀.place[ω₀]?).map (·.1) = some zω → ∀ z z', z < z' → z' < zω →
    ((B₀.trees[z]?).map (·.number)).getD 0 < ((B₀.trees[z']?).map (·.number)).getD 0

/-- A book in which a tree's number is its place, below Omega's tree, is such a one. -/
theorem risesBelow_of_numbered {B₀ : TreeBook} {ω₀ : ℕ}
    (h : ∀ zω, (B₀.place[ω₀]?).map (·.1) = some zω → ∀ z, z < zω →
      ((B₀.trees[z]?).map (·.number)).getD 0 = z) : RisesBelow B₀ ω₀ := fun zω hω z z' h1 h2 => by
  rw [h zω hω z (by omega), h zω hω z' h2]
  exact h1

/-- **The places rise**, from numbers that rise below Omega's tree (`up_of_numbers`,
Johnson/Desc/K12/Coin/FirstOpensUp.lean, asks that each number be its place). -/
theorem up_of_rise (B : TreeBook) (ω zω : ℕ) (hω : (B.place[ω]?).map (·.1) = some zω)
    (ts : List ℕ) (hts : ts.Pairwise (· < ·)) (last : ∀ z ∈ ts, z ≤ zω)
    (rise : ∀ z ∈ ts, ∀ z' ∈ ts, z < z' → z' < zω →
      ((B.trees[z]?).map (·.number)).getD 0 < ((B.trees[z']?).map (·.number)).getD 0) :
    (ts.map (plOf B ω)).Pairwise Before := by
  refine List.pairwise_map.2 (hts.imp_of_mem fun {z z'} hz hz' hlt => ?_)
  have h1 : z ≠ zω := by
    have := last z' hz'
    omega
  rw [before_iff, plOf_other hω h1]
  by_cases h2 : z' = zω
  · subst h2
    exact Or.inl (by rw [plOf_omega hω]; exact Nat.zero_lt_one)
  · rw [plOf_other hω h2]
    exact Or.inr ⟨rfl, rise z hz z' hz' hlt (by have := last z' hz'; omega)⟩

/-- **The law «opens», at the record.** -/
theorem opens_at_shape {Xi : Type} {F : FileDescription Xi} {file : String} {D₀ : WholeD}
    (h : F.data file = .ok D₀) (hk : F.treeSharingOk = true) (π : P12)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (seated : ∀ r ∈ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds, r ∈ F.roundsDeclaredByBlocks.2.2)
    (base : ℕ) (hb : F.t₁ + F.t₂ ≤ base)
    (ho : π.nums.ownMask = false) (h2 : 2 ≤ π.nums.stages.length)
    (first : ∀ o ∈ π.nums.first, ∃ c n, o.2 = .taken c n)
    {p : P₁₄} {f : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds 2 f o s = true)
    {t : T12} (he : enterOwn s = .ok t)
    (B₀ : TreeBook) (ω₀ : ℕ) (hB : BookAt B₀ ω₀ s) (hN : RisesBelow B₀ ω₀) :
    FirstOpens π (VerifiableInference.Desc.numAt F.t₁ F.t₂ 2)
      (fun z => Three.wholeNo F.t₁ F.t₂ (plOf B₀ ω₀ z)) base t := by
  obtain ⟨⟨s₀, B⟩, hT⟩ := behindOk_of_two hs
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  obtain ⟨ts, hts, ca, cb⟩ := tied_of (onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Unit)) hT
  have hbook : s₀.book = f.book := (start₃E_book _ _ _ _ _ _ _ _ _ _ _ B.start).1
  have hfit : BookFits s₀.book := by
    rw [hbook]
    exact B.handed.fits₁
  have htk : tkOf t s.loc.omega = some ts := (takenOf_tkOf s t he).symm.trans hts
  have et := enterOwn_is he
  have eb : t.book = s.book := by rw [et]
  have em : t.mask = s.loc.mask := by rw [et]
  obtain ⟨id, hid0⟩ := Option.isSome_iff_exists.1 B.mask
  have hid : t.mask = some id := em.trans hid0
  have hω : (t.book.place[s.loc.omega]?).map (·.1) = some s₀.book.trees.size := by
    rw [eb]
    exact omega_place L
  have last : ∀ a rest G0 Ly D, Fixes π t a rest G0 Ly D → ∀ z ∈ D.ts, z ≤ s₀.book.trees.size := by
    intro a rest G0 Ly D hF z hz
    obtain ⟨i, _, n, pp, T, _, hT', _⟩ := member_of_ts hF hid z hz
    rw [eb] at hT'
    have h1 : z < s.book.trees.size := (Array.getElem?_eq_some_iff.1 hT').1
    rw [L.trees] at h1
    omega
  have hplace : (B₀.place[ω₀]?).map (·.1) = some s₀.book.trees.size := by
    rw [hB.place, ← hB.omega]
    exact omega_place L
  have same : ∀ a rest G0 Ly D, Fixes π t a rest G0 Ly D → ∀ z ∈ D.ts,
      (B₀.trees[z]?).map (·.number) = (t.book.trees[z]?).map (·.number) := by
    intro a rest G0 Ly D hF z hz
    obtain ⟨i, _, n, pp, T, _, hT', _⟩ := member_of_ts hF hid z hz
    rw [hT']
    rw [eb] at hT'
    exact hB.numbers z T hT'
  have key := firstOpens_at_last h hk π hp seated base hb t hid s.loc.omega ts htk (tied_a ca)
    (tied_b cb) ho h2 first
    (fun G0 _ i _ q pp z hq hi e => alone_of_laid L hfit i q pp z (eb ▸ hq) (eb ▸ hi) e)
    (fun a rest G0 Ly D hF => up_of_rise t.book s.loc.omega s₀.book.trees.size hω D.ts
      (ts_rise hF) (last a rest G0 Ly D hF) fun z hz z' hz' h1 h2' => by
        rw [← same a rest G0 Ly D hF z hz, ← same a rest G0 Ly D hF z' hz']
        exact hN _ hplace z z' h1 h2')
  rw [hB.omega] at key
  exact firstOpens_at_book B₀ key (by rw [eb]; exact hB.place) same

/-- Every place of D.ts has a tree in the record's book, and none lies behind Omega's copy's. -/
theorem ts_le {S : Params.LinShape} {s₀ s : S₃} {b : Border} {y : OnBytes.Oracle}
    {G : OnBytes.Group} {dot : OnBytes.Row} (L : Laid S s₀ s b y G dot) {t : T12}
    (he : enterOwn s = .ok t) {id : ℕ} (hid : t.mask = some id) {π : P12} {a : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout} {D : H2K.First.Plain}
    (hF : Fixes π t a rest G0 Ly D) : ∀ z ∈ D.ts, z ≤ s₀.book.trees.size := by
  intro z hz
  have eb : t.book = s.book := by rw [enterOwn_is he]
  obtain ⟨i, _, n, pp, T, _, hT', _⟩ := member_of_ts hF hid z hz
  rw [eb] at hT'
  have h1 : z < s.book.trees.size := (Array.getElem?_eq_some_iff.1 hT').1
  rw [L.trees] at h1
  omega

/-- **What is asked of what was handed, in numbers**: the first chain's book has n₁ trees; the tree
at place j has the number ft + j (the second clause of `Numbered ft`,
Johnson/Desc/Book/BookNumbers.lean); Omega's tree in the shared chain's book has the number nΩ. -/
structure HandedNumbers (n₁ ft nΩ : ℕ) (f : Handed) (o : SharedOut) : Prop where
  trees : f.book.trees.size = n₁
  first : ∀ (j : ℕ) (T : Tree), f.book.trees[j]? = some T → T.number = ft + j
  omega : ∀ (q : ℕ × ℕ) (T : Tree), o.book.place[o.omega]? = some q →
    o.book.trees[q.1]? = some T → T.number = nΩ

/-- **The start's own test**: at the first chain's end as many roots are received as its book has
trees (`rootsB`, Johnson/Desc/Third/State.lean). -/
theorem start₃E_roots (codes : Codes) (S : Params.LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : ℕ) (mask₁ : Option ℕ) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : VerifiableInference.Desc.Third.start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o =
      .ok s₀) : roots₁ = book₁.trees.size := by
  obtain ⟨f, hf, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨eb, er⟩ := firstOutFrom_book _ _ _ _ _ _ _ _ _ hf
  unfold VerifiableInference.Desc.Third.start₃ at hst
  split at hst
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    have h1 : (f.roots == f.book.trees.size) = true := hc.2
    rw [eb, er] at h1
    exact beq_iff_eq.1 h1
  · cases hst

/-- **The same debt with the ROOTS in the trees' place**: the first chain has received n₁ roots (the
second law of the row on the first chain's book's numbers speaks of these). -/
structure HandedRoots (n₁ ft nΩ : ℕ) (f : Handed) (o : SharedOut) : Prop where
  roots : f.roots = n₁
  first : ∀ (j : ℕ) (T : Tree), f.book.trees[j]? = some T → T.number = ft + j
  omega : ∀ (q : ℕ × ℕ) (T : Tree), o.book.place[o.omega]? = some q →
    o.book.trees[q.1]? = some T → T.number = nΩ

/-- Inside the book-keeping the second gives the first: by the start's own test. -/
theorem handedNumbers_of_roots {p : P₁₄} {R : List Fmt.DeclaredRound} {f : Handed} {o : SharedOut}
    {s : S₃} (hs : shapeAt p R 2 f o s = true) {n₁ ft nΩ : ℕ} (h : HandedRoots n₁ ft nΩ f o) :
    HandedNumbers n₁ ft nΩ f o := by
  obtain ⟨⟨s₀, B⟩, _⟩ := behindOk_of_two hs
  exact ⟨(start₃E_roots _ _ _ _ _ _ _ _ _ _ _ B.start).symm.trans h.roots, h.first, h.omega⟩

/-- The letter «no» as a closed function of five public numbers. -/
def noAt (t₁ t₂ n₁ ft nΩ z : ℕ) : ℕ :=
  Three.wholeNo t₁ t₂ (if z = n₁ then (1, nΩ) else (0, ft + z))

/-- **The law «opens», with «no» closed**: no public book; what is left on the records is
`HandedNumbers`, of what was handed alone. -/
theorem opens_at_numbers {Xi : Type} {F : FileDescription Xi} {file : String} {D₀ : WholeD}
    (h : F.data file = .ok D₀) (hk : F.treeSharingOk = true) (π : P12)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (seated : ∀ r ∈ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds, r ∈ F.roundsDeclaredByBlocks.2.2)
    (base : ℕ) (hb : F.t₁ + F.t₂ ≤ base)
    (ho : π.nums.ownMask = false) (h2 : 2 ≤ π.nums.stages.length)
    (first : ∀ o ∈ π.nums.first, ∃ c n, o.2 = .taken c n)
    {p : P₁₄} {f : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds 2 f o s = true)
    {t : T12} (he : enterOwn s = .ok t)
    (n₁ ft nΩ : ℕ) (hH : HandedNumbers n₁ ft nΩ f o) :
    FirstOpens π (VerifiableInference.Desc.numAt F.t₁ F.t₂ 2) (noAt F.t₁ F.t₂ n₁ ft nΩ) base t := by
  obtain ⟨⟨s₀, B⟩, _⟩ := behindOk_of_two hs
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  have hbook : s₀.book = f.book := (start₃E_book _ _ _ _ _ _ _ _ _ _ _ B.start).1
  obtain ⟨g, hg⟩ := start₃E_border _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain rfl : (⟨g, o⟩ : Border) = b := Option.some.inj (hg.symm.trans L.border)
  have hsz : s₀.book.trees.size = n₁ := by
    rw [hbook]
    exact hH.trees
  have old : ∀ z, z < n₁ → ((s.book.trees[z]?).map (·.number)).getD 0 = ft + z := by
    intro z hz
    rw [L.oldTrees z (by rw [hsz]; exact hz), hbook]
    have hz' : z < f.book.trees.size := by
      rw [hH.trees]
      exact hz
    have hT : f.book.trees[z]? = some f.book.trees[z] := Array.getElem?_eq_getElem hz'
    rw [hT]
    exact hH.first z _ hT
  have om : ((s.book.trees[n₁]?).map (·.number)).getD 0 = nΩ := by
    obtain ⟨q, T, tO, h1, h2', _, h4, h5, _⟩ := L.tree
    rw [← hsz, h4]
    show tO.number = nΩ
    rw [h5]
    exact hH.omega q T h1 h2'
  have hω : (s.book.place[s.loc.omega]?).map (·.1) = some n₁ := by
    rw [← hsz]
    exact omega_place L
  have em : t.mask = s.loc.mask := by rw [enterOwn_is he]
  obtain ⟨id, hid0⟩ := Option.isSome_iff_exists.1 B.mask
  have hid : t.mask = some id := em.trans hid0
  have k := opens_at_shape h hk π hp seated base hb ho h2 first hs he s.book s.loc.omega
    ⟨rfl, rfl, fun z T hT => by rw [hT]; rfl⟩
    (fun zω hz z z' h1 h2' => by
      have e : n₁ = zω := Option.some.inj (hω.symm.trans hz)
      subst e
      rw [old z (by omega), old z' h2']
      omega)
  refine k.congr_no fun a rest G0 Ly D hF z hz => ?_
  have hle : z ≤ n₁ := hsz ▸ ts_le L he hid hF z hz
  show Three.wholeNo F.t₁ F.t₂ (if z = n₁ then (1, nΩ) else (0, ft + z)) =
    Three.wholeNo F.t₁ F.t₂ (plOf s.book s.loc.omega z)
  by_cases hzn : z = n₁
  · subst hzn
    rw [if_pos rfl]
    unfold plOf
    rw [hω, if_pos rfl, om]
  · rw [if_neg hzn, plOf_other hω hzn, old z (by omega)]

/-- **The law «opens», at the description that `onlineDescription` makes and the place W.** -/
theorem opens_at_W (oh : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (A : ProofFile.SharedSeat)
    (N : H2U.Places4) (c : Chain VerifiableInference.Desc.First.S ProofFile.Cl)
    (hNp : H2U.placesOfMade Z.made = .ok N) {file : String} {D₀ : WholeD}
    (h : (ProofFile.fileDescBy oh mk Z A (P2Third.secondSeatOf Z N) (fun s => s) (ProofFile.startS Z) c).data
      file = .ok D₀)
    (hk : (ProofFile.fileDescBy oh mk Z A (P2Third.secondSeatOf Z N) (fun s => s) (ProofFile.startS Z)
      c).treeSharingOk = true)
    (hp : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Unit).planOk = true)
    (base : ℕ)
    (hb : (ProofFile.fileDescBy oh mk Z A (P2Third.secondSeatOf Z N) (fun s => s) (ProofFile.startS Z) c).t₁ +
      (ProofFile.fileDescBy oh mk Z A (P2Third.secondSeatOf Z N) (fun s => s) (ProofFile.startS Z) c).t₂ ≤ base)
    (ho : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.ownMask = false)
    (h2 : 2 ≤ (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.stages.length)
    {p : P₁₄} {f : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Unit).rounds 2 f o
      s = true)
    {t : T12} (he : enterOwn s = .ok t)
    (B₀ : TreeBook) (ω₀ : ℕ) (hB : BookAt B₀ ω₀ s) (hN : RisesBelow B₀ ω₀) :
    FirstOpens (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W)
      (VerifiableInference.Desc.numAt
        (ProofFile.fileDescBy oh mk Z A (P2Third.secondSeatOf Z N) (fun s => s) (ProofFile.startS Z) c).t₁
        (ProofFile.fileDescBy oh mk Z A (P2Third.secondSeatOf Z N) (fun s => s) (ProofFile.startS Z) c).t₂ 2)
      (fun z => Three.wholeNo
        (ProofFile.fileDescBy oh mk Z A (P2Third.secondSeatOf Z N) (fun s => s) (ProofFile.startS Z) c).t₁
        (ProofFile.fileDescBy oh mk Z A (P2Third.secondSeatOf Z N) (fun s => s) (ProofFile.startS Z) c).t₂
        (plOf B₀ ω₀ z)) base t :=
  opens_at_shape h hk _ hp (seated_at oh mk Z A N c) base hb ho h2 (first_at_W hNp) hs he B₀ ω₀ hB
    hN

section
variable {P S₁ S₂ Wt : Type} {Fr : Frame} (Nn : NumbersS) (Mg : MeaningS S₂ (P × S₁) Wt)
  (Pm : PromMeaning S₂) (Oc : P × S₁ → Strs → Prop) (p : P₁₄) (hand : P × S₁ → Option Handed)
  (ended : S₂ → Option SharedOut)

/-- **The ledger's field «opens», from `BookAt` at every record inside the promise at border 2**:
general in the table's letters; t₁, t₂: the description's two counts of trees under the ledger's own
names. -/
theorem opens_field {Xi : Type} {F : FileDescription Xi} {file : String} {D₀ : WholeD}
    (h : F.data file = .ok D₀) (hk : F.treeSharingOk = true) (π : P12)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (seated : ∀ r ∈ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds, r ∈ F.roundsDeclaredByBlocks.2.2)
    (t₁ t₂ : ℕ) (e₁ : F.t₁ = t₁) (e₂ : F.t₂ = t₂) (base : ℕ) (hb : t₁ + t₂ ≤ base)
    (ho : π.nums.ownMask = false) (h2 : 2 ≤ π.nums.stages.length)
    (first : ∀ o ∈ π.nums.first, ∃ c n, o.2 = .taken c n)
    (R : List Fmt.DeclaredRound) (hR : R = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (B₀ : TreeBook) (ω₀ : ℕ) (hN : RisesBelow B₀ ω₀)
    (hB : ∀ a, onQ₃ (Fr := Fr) Nn Mg Pm (fillAt p R hand ended) Oc 2 a → BookAt B₀ ω₀ a.1.2) :
    ∀ a t, onQ₃ (Fr := Fr) Nn Mg Pm (fillAt p R hand ended) Oc 2 a → enterOwn a.1.2 = .ok t →
      FirstOpens π (VerifiableInference.Desc.numAt t₁ t₂ 2)
        (fun z => Three.wholeNo t₁ t₂ (plOf B₀ ω₀ z)) base t := by
  intro a t ha he
  obtain ⟨f, o, _, _, hs⟩ := shapeAt_of_onL (h := ha)
  subst hR e₁ e₂
  exact opens_at_shape h hk π hp seated base hb ho h2 first hs he B₀ ω₀ (hB a ha) hN

/-- **The ledger's field «opens», with «no» closed**: what is left on the records is said of what
was handed alone: of the first chain's last record and the shared chain's end. -/
theorem opens_field_numbers {Xi : Type} {F : FileDescription Xi} {file : String} {D₀ : WholeD}
    (h : F.data file = .ok D₀) (hk : F.treeSharingOk = true) (π : P12)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (seated : ∀ r ∈ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds, r ∈ F.roundsDeclaredByBlocks.2.2)
    (t₁ t₂ : ℕ) (e₁ : F.t₁ = t₁) (e₂ : F.t₂ = t₂) (base : ℕ) (hb : t₁ + t₂ ≤ base)
    (ho : π.nums.ownMask = false) (h2 : 2 ≤ π.nums.stages.length)
    (first : ∀ o ∈ π.nums.first, ∃ c n, o.2 = .taken c n)
    (R : List Fmt.DeclaredRound) (hR : R = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (n₁ ft nΩ : ℕ)
    (hH : ∀ a, onQ₃ (Fr := Fr) Nn Mg Pm (fillAt p R hand ended) Oc 2 a → ∀ f o,
      hand (a.1.1.1, a.1.1.2.1) = some f → ended a.1.1.2.2 = some o →
      HandedRoots n₁ ft nΩ f o) :
    ∀ a t, onQ₃ (Fr := Fr) Nn Mg Pm (fillAt p R hand ended) Oc 2 a → enterOwn a.1.2 = .ok t →
      FirstOpens π (VerifiableInference.Desc.numAt t₁ t₂ 2) (noAt t₁ t₂ n₁ ft nΩ) base t := by
  intro a t ha he
  obtain ⟨f, o, hf, ho', hs⟩ := shapeAt_of_onL (h := ha)
  subst hR e₁ e₂
  exact opens_at_numbers h hk π hp seated base hb ho h2 first hs he n₁ ft nΩ
    (handedNumbers_of_roots hs (hH a ha f o hf ho'))

end

end ToldDesc

#print axioms ToldDesc.start₃E_roots
#print axioms ToldDesc.handedNumbers_of_roots
#print axioms ToldDesc.opens_field_numbers
#print axioms ToldDesc.opens_at_numbers
#print axioms ToldDesc.opens_field
#print axioms ToldDesc.up_of_rise
#print axioms ToldDesc.risesBelow_of_numbered
#print axioms ToldDesc.tied_a
#print axioms ToldDesc.tied_b
#print axioms ToldDesc.omega_place
#print axioms ToldDesc.alone_of_laid
#print axioms ToldDesc.opens_at_shape
#print axioms ToldDesc.opens_at_W
