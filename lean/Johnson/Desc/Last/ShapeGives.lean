-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeGives.lean: WHAT A YES OF THE LAST CHAIN's BOOK-KEEPING GIVES, AND THE FOUR
STEPS FROM BORDER TO BORDER. The laws of Johnson/Desc/Last/ShapeAt.lean. Statements and proofs.
`start₃E` TAKES THE NUMBERS OF W, OF THE OWN GROUP AND OF THE MASK BY NAME
(`Handed` := `FirstEnd₃`). Over `Laid` with twenty-five fields; `step_two` takes four named
hypotheses (loc, run, codes, tidy), the other three steps none beyond the promise in front and the
block's yes; the chain's end gives its own test, not `fin₃`.

Why. The rows of the table of the last chain's joints take premises of the form "the promise at
border k gives …" and "the promise in front and the block's yes give the promise behind". Here each
such premise that is a test on public records is had from `shapeAt k`'s yes, by its files' own
name; and the four steps are stated, with what is not shown here as named premises.

Main names (namespace `VerifiableInference.Desc.Last`).
  `shapeAt_inv`, `shapeAt_of`: a yes is: the start returns s₀ of what was handed; the clauses on
    what was handed; the border's clauses at s₀ and s. `HandedOk`, `handedOk_of`: the first chain's
    last statement is tidy · the shared chain's is in order · both books fit · Omega is part 0 of
    its tree · Omega is there with the plan's shape · one pending row with lawful weights.
    `MembersOk`, `membersOk_of`: the own group that was handed has two members, each with one sample
    row; Omega has one at the shared chain's end.
  BORDER 0. `started_of_shape`: THE RECORD IS THE START's. **`atDot_of_shape`**: `AtDot
    p s` (Johnson/Desc/Third/Law/AtDot.lean). `names_of`: the premise "names" of `old_rows_back`
    (Johnson/Desc/Third/Law/RowsOfEarlierMessages.lean). **`frontOk_of_shape`**: the words' fence on the record in
    front (`FrontOk`, Johnson/Desc/Sound/WordsUsers.lean).
  THE TEST AND `Laid`. **`laid_of`**, **`laidB_of`**: `laidB S s s'` says yes just where
    `Laid S s s' b y G dot` holds of some b, y, G, dot. **`laid_pins`**: WHAT IT PINS: two records
    laid from one have one statement, one set of named values, one count of roots, the same places,
    as many trees and the same older trees.
  BORDERS 1, 2. `BehindOk`, `behindOk_of_one`, `behindOk_of_two`: the start · `HandedOk` ·
    `MembersOk` · `Laid` from s₀ · `Means.Tidy` (so `InOrder` and `OpenKinds`) · the book fits · the
    mask has come; at 2 beside: `tiedB`. `tied_of`, `tiedB_of`: it says yes just where `Tied own s`
    (Sources.lean) holds. `rows_there`: the own group is there, has an open row, and no test has
    begun. **`three_members`**: its members are the two that were handed, then Omega's copy; each
    has one sample row.
  THE STEPS. `fits_k14Second`: K14's second part keeps "the book fits". **`step_zero`** (K14's
    second part): NO FURTHER HYPOTHESIS (`laid_k14Second`; `k14Second_tidy`,
    Johnson/Desc/Tidy/Third.lean). **`step_one`** (the taken trees' sources): NO FURTHER HYPOTHESIS.
    **`step_two`** (the own test's block): FOUR HYPOTHESES on what its yes lays: the named values
    stay · the own group's test has begun · the codes stay · the statement is tidy. `end₃_yes`,
    **`step_three`** (the chain's last block): NO FURTHER HYPOTHESIS; it gives the filling's
    `nothingLeft` too.

Every "there is", walked. s₀ (`shapeAt_inv`, `behindOk_of_…`): tied by `start₃E … = .ok s₀`: at most
one. b, y, G, dot (`laid_of`, `BehindOk.laid`): tied by `Laid`'s fields border, there, group, dotIs:
at most one each; q, t, tO inside `Laid.tree`: by an equation each. y, r (`HandedOk`): tied by an
equation each. G (`started_of_shape`, `rows_there`, `step_two`'s premise run): the group at the own
number.
NOT HAD FROM shape, AND WHY. The rows' premises that read the prover's strings or the witness: the
head of ShapeAt.lean. "The seat's enter returns": no clause: the seat that the last chain's files
and the fold's lay (`enterOwn`) asks nothing and
returns the record's statement, book, roots, own group's number and mask: by reading; not typed
here. The trees that the first switch's openings name (`FirstOpens`), the members' cover: they read
K12's files' plain data: not typed here.
Limits. NO MEMBER: no record is shown at which `shapeAt` says yes: the tries of ShapeAtTable.lean
show only that it can say no. `step_two`'s four hypotheses. THE DOOR: that border 0's promise
follows from the shared chain's last promise and the start is stated in
Johnson/Desc/Last/ShapeDoor.lean, where the promise is filled by `fillZ`, from three named
conditions (`door_fillZ`, from `DoorOwed`), none of which is proved in that file. Laws over the
texts of the
last chain (Johnson/Desc/Third/). Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeAt
import Johnson.Desc.Sound.BookTestsLaw
import Johnson.Desc.Sound.WordsUsers
import Johnson.Desc.Third.Law.AtDotStart
import Johnson.Desc.Third.Law.Laid
import Johnson.Desc.Third.Law.Sharp
import Johnson.Desc.Third.Law.Sources
import Johnson.Desc.Third.Chain
import Johnson.Desc.Tidy.Third
import Johnson.Desc.Book.BookFitsGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.Sound (bookFitsB tenantB bookFitsB_iff tenantB_iff FrontOk
  frontOk_of_start)
open VerifiableInference.Desc.Book (BookFits placed_of_fits)

/-! ## 1 The small tests -/

theorem names_of {s : S₃} (h : namesB s = true) :
    ∀ G, s.st.groups[s.loc.own]? = some G → ∀ r ∈ G.rows.toList, ∀ o ∈ r.oracles,
      o < s.st.oracles.size := by
  intro G hG r hr o ho
  unfold namesB at h
  rw [hG] at h
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h r hr o ho

theorem tied_of {Cl : Type} (own : Block S₃ Cl) {s : S₃} (h : tiedB own.rounds s = true) :
    Tied own s := by
  unfold tiedB at h
  split at h
  · rename_i ts hts
    simp only [Bool.and_eq_true] at h
    exact ⟨ts, hts, h.1, h.2⟩
  · cases h

theorem tiedB_of {Cl : Type} (own : Block S₃ Cl) {s : S₃} (h : Tied own s) :
    tiedB own.rounds s = true := by
  obtain ⟨ts, h1, h2, h3⟩ := h
  unfold tiedB
  rw [h1]
  simp only [Bool.and_eq_true]
  exact ⟨h2, h3⟩

/-! ## 2 The test's yes, opened -/

/-- What a yes of the book-keeping's test holds, at every border. -/
theorem shapeAt_inv {p : P₁₄} {R : List Fmt.DeclaredRound} {k : Nat} {h : Handed} {o : SharedOut}
    {s : S₃} (hs : shapeAt p R k h o s = true) :
    ∃ s₀, start₃E p.codes p.S h.st h.book h.roots h.w h.own h.mask h.pending o = .ok s₀ ∧
      ((handedClauses p h o).all (·.2) = true ∧ (memberClauses s₀ o).all (·.2) = true) ∧
      (clausesAt p R k s₀ s).all (·.2) = true := by
  unfold shapeAt allClauses at hs
  split at hs
  · rename_i s₀ h₀
    rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true] at hs
    exact ⟨s₀, h₀, hs.1, hs.2⟩
  · simp at hs

/-- And back. -/
theorem shapeAt_of {p : P₁₄} {R : List Fmt.DeclaredRound} {k : Nat} {h : Handed} {o : SharedOut}
    {s s₀ : S₃} (h₀ : start₃E p.codes p.S h.st h.book h.roots h.w h.own h.mask h.pending o = .ok s₀)
    (h₁ : (handedClauses p h o).all (·.2) = true ∧ (memberClauses s₀ o).all (·.2) = true)
    (h₂ : (clausesAt p R k s₀ s).all (·.2) = true) : shapeAt p R k h o s = true := by
  unfold shapeAt allClauses
  rw [h₀]
  show ((handedClauses p h o ++ memberClauses s₀ o ++ clausesAt p R k s₀ s).all (·.2)) = true
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨h₁, h₂⟩

/-- **What the clauses on what was handed give.** -/
structure HandedOk (p : P₁₄) (h : Handed) (o : SharedOut) : Prop where
  tidy : Means.Tidy h.st
  order₂ : Means.InOrder o.st
  fits₁ : BookFits h.book
  fits₂ : BookFits o.book
  tenant : ∀ q : Nat × Nat, o.book.place[o.omega]? = some q → q.2 = 0
  omega : ∃ y, o.st.oracles[o.omega]? = some y ∧ y.shape = p.S.omega
  weights : ∃ r, h.pending = [r] ∧ ∀ g ∈ r.g, g.ok = true

theorem handedOk_of {p : P₁₄} {h : Handed} {o : SharedOut}
    (hh : (handedClauses p h o).all (·.2) = true) : HandedOk p h o := by
  unfold handedClauses at hh
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hh
  obtain ⟨c1, c0, c2, c3, c4, c5, c6⟩ := hh
  refine ⟨Means.tidy4B_iff.1 c1, Means.inOrderB_iff.1 c0, (bookFitsB_iff _).1 c2,
    (bookFitsB_iff _).1 c3, (tenantB_iff _).1 c4, ?_, ?_⟩
  · split at c5
    · rename_i y hy
      exact ⟨y, hy, of_decide_eq_true c5⟩
    · cases c5
  · split at c6
    · rename_i r hr
      exact ⟨r, hr, fun g hg => List.all_eq_true.1 c6 g hg⟩
    · cases c6

/-- **What the clauses on the members give.** -/
structure MembersOk (s₀ : S₃) (o : SharedOut) : Prop where
  two : ∃ G, s₀.st.groups[s₀.loc.own]? = some G ∧ G.members.size = 2 ∧
    ∀ i ∈ G.members.toList, ∃ x, s₀.st.oracles[i]? = some x ∧ x.sampleRows.size = 1
  omega : ∃ y, o.st.oracles[o.omega]? = some y ∧ y.sampleRows.size = 1

theorem membersOk_of {s₀ : S₃} {o : SharedOut} (hm : (memberClauses s₀ o).all (·.2) = true) :
    MembersOk s₀ o := by
  unfold memberClauses at hm
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hm
  obtain ⟨c1, c2, c3⟩ := hm
  refine ⟨?_, ?_⟩
  · cases hG : s₀.st.groups[s₀.loc.own]? with
    | none => rw [hG] at c1; cases c1
    | some G =>
      rw [hG] at c1 c2
      refine ⟨G, rfl, by simpa using c1, fun i hi => ?_⟩
      have c := List.all_eq_true.1 c2 i hi
      cases hx : s₀.st.oracles[i]? with
      | none => rw [hx] at c; cases c
      | some x => rw [hx] at c; exact ⟨x, rfl, by simpa using c⟩
  · cases hy : o.st.oracles[o.omega]? with
    | none => rw [hy] at c3; cases c3
    | some y => rw [hy] at c3; exact ⟨y, rfl, by simpa using c3⟩

/-! ## 3 Border 0 -/

/-- **At border 0 the record is the start's of what was handed.** -/
theorem started_of_shape {p : P₁₄} {R : List Fmt.DeclaredRound} {h : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p R 0 h o s = true) :
    start₃E p.codes p.S h.st h.book h.roots h.w h.own h.mask h.pending o = .ok s ∧ HandedOk p h o ∧
        namesB s = true ∧
      (∃ G, s.st.groups[s.loc.own]? = some G ∧ G.rows.isEmpty = false) ∧
      s.loc.mask.isSome = true := by
  obtain ⟨s₀, h₀, hh, hc⟩ := shapeAt_inv hs
  simp only [clausesAt, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hc
  obtain ⟨c1, c2, c3, c4⟩ := hc
  have e : s = s₀ := of_decide_eq_true c1
  refine ⟨by rw [e]; exact h₀, handedOk_of hh.1, c2, ?_, c4⟩
  split at c3
  · rename_i G hG
    exact ⟨G, hG, by simpa using c3⟩
  · cases c3

/-- **`AtDot` (Johnson/Desc/Third/Law/AtDot.lean).** -/
theorem atDot_of_shape {p : P₁₄} {R : List Fmt.DeclaredRound} {h : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p R 0 h o s = true) : AtDot p s := by
  obtain ⟨h₀, H, _⟩ := started_of_shape hs
  obtain ⟨y, hy, ey⟩ := H.omega
  obtain ⟨r, hr, hg⟩ := H.weights
  refine atDot_of_start p _ _ _ _ _ _ _ o s h₀ (fun y' hy' => ?_) (fun r' hr' g hg' => ?_)
  · obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
    exact ey
  · obtain rfl : r = r' := by
      have := hr.symm.trans hr'
      simpa using this
    exact hg g hg'

/-- **Our words' fence, the part on the record in front.** -/
theorem frontOk_of_shape {p : P₁₄} {R : List Fmt.DeclaredRound} {h : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p R 0 h o s = true) : FrontOk h.st h.book s.loc.w o s := by
  obtain ⟨h₀, H, _⟩ := started_of_shape hs
  exact frontOk_of_start p.codes p.S _ _ _ _ _ _ _ o s h₀
    (fun i q hq => placed_of_fits H.fits₁ i q hq)
    H.tenant

/-! ## 4 What K14's second part has laid: the test and `Laid` -/

/-- **The test's yes gives `Laid`.** -/
theorem laid_of {S : Params.LinShape} {s s' : S₃} (h : laidB S s s' = true) :
    ∃ b y G dot, Laid S s s' b y G dot := by
  unfold laidB laidClauses at h
  split at h
  · simp at h
  · rename_i b hb
    split at h
    · rename_i y G dot hy hG hd
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21⟩ := h
      refine ⟨b, y, G, dot, hb, c1, hy, c2, c3, c4, hG, c5, hd, c6, c7, Means.rowIn_of c8, c9, c10,
        fun i hi => ?_, c12, c13, c14, c15, c16, c17, c18, c19, ?_, fun o1 o2 => ?_⟩
      · by_cases hlt : i < s.st.groups.size
        · exact (c11 i hlt).resolve_left hi
        · rw [Array.getElem?_eq_none (by rw [c12]; exact Nat.le_of_not_lt hlt),
            Array.getElem?_eq_none (Nat.le_of_not_lt hlt)]
      · split at c20
        · rename_i q hq
          split at c20
          · rename_i t tO ht htO
            simp only [Bool.and_eq_true, decide_eq_true_eq] at c20
            exact ⟨q, t, tO, hq, ht, c20.1.1, htO, c20.1.2, c20.2⟩
          · cases c20
        · cases c20
      · rcases c21 with (c | c) | c
        · rw [Means.inOrderB_iff.2 o1] at c
          cases c
        · rw [Means.inOrderB_iff.2 o2] at c
          cases c
        · exact Means.inOrderB_iff.1 c
    · simp at h

/-- **And `Laid` gives the test's yes.** -/
theorem laidB_of {S : Params.LinShape} {s s' : S₃} {b : Border} {y : OnBytes.Oracle}
    {G : OnBytes.Group} {dot : OnBytes.Row} (L : Laid S s s' b y G dot) : laidB S s s' = true := by
  obtain ⟨q, t, tO, hq, ht, h1, htO, h2, h3⟩ := L.tree
  unfold laidB laidClauses
  rw [L.border]
  simp only [L.there, L.group, L.dotIs, hq, ht, htO]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
  refine ⟨L.loc, L.sampled, L.size, L.copy, L.notBegun, L.plain, L.group', Means.rowInB_of L.dotIn,
    L.codes,
    fun i hi => L.old i hi, fun i _ => (Decidable.em (i = s.loc.own)).imp id (L.oldGroups i),
    L.groups, L.roots, L.trees, L.step, L.place, fun i hi => L.oldPlaces i hi, L.places,
    fun i hi => L.oldTrees i hi, ⟨⟨h1, h2⟩, h3⟩, ?_⟩
  cases c1 : Means.inOrderB s.st with
  | false => exact Or.inl (Or.inl rfl)
  | true =>
    cases c2 : Means.inOrderB b.shared.st with
    | false => exact Or.inl (Or.inr rfl)
    | true => exact Or.inr (Means.inOrderB_iff.2
        (L.order (Means.inOrderB_iff.1 c1) (Means.inOrderB_iff.1 c2)))

/-- Two arrays of one size that agree below it are one. -/
theorem array_eq_of {α : Type} {A B : Array α} (hs : A.size = B.size)
    (h : ∀ i, i < A.size → A[i]? = B[i]?) : A = B := by
  refine Array.ext_getElem? fun i => ?_
  by_cases hi : i < A.size
  · exact h i hi
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hi),
      Array.getElem?_eq_none (by rw [← hs]; exact Nat.le_of_not_lt hi)]

/-- **WHAT `Laid` PINS**: two records that K14's second part may have laid from one record have one
statement, one set of named values, one count of roots, the same places, as many trees, and the
same older trees. (Of the one new tree `Laid.tree` fixes the number and the source.) -/
theorem laid_pins {S : Params.LinShape} {s₀ s s' : S₃} {b b' : Border} {y y' : OnBytes.Oracle}
    {G G' : OnBytes.Group} {dot dot' : OnBytes.Row} (L : Laid S s₀ s b y G dot)
    (L' : Laid S s₀ s' b' y' G' dot') :
    s.st = s'.st ∧ s.loc = s'.loc ∧ s.roots = s'.roots ∧ s.book.place = s'.book.place ∧
      s.book.trees.size = s'.book.trees.size ∧
      ∀ i, i < s₀.book.trees.size → s.book.trees[i]? = s'.book.trees[i]? := by
  obtain rfl : b = b' := Option.some.inj (L.border.symm.trans L'.border)
  obtain rfl : y = y' := Option.some.inj (L.there.symm.trans L'.there)
  obtain rfl : G = G' := Option.some.inj (L.group.symm.trans L'.group)
  obtain rfl : dot = dot' := Option.some.inj (L.dotIs.symm.trans L'.dotIs)
  have ho : s.st.oracles = s'.st.oracles := by
    refine array_eq_of (L.size.trans L'.size.symm) fun i hi => ?_
    rw [L.size] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with c | c
    · rw [L.old i c, L'.old i c]
    · rw [c, L.copy, L'.copy]
  have hg : s.st.groups = s'.st.groups := by
    refine array_eq_of (L.groups.trans L'.groups.symm) fun i _ => ?_
    by_cases c : i = s₀.loc.own
    · rw [c, L.group', L'.group']
    · rw [L.oldGroups i c, L'.oldGroups i c]
  have hp : s.book.place = s'.book.place := by
    refine array_eq_of (L.places.trans L'.places.symm) fun i hi => ?_
    rw [L.places] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with c | c
    · rw [L.oldPlaces i c, L'.oldPlaces i c]
    · rw [c, ← L.step, L.place, L'.place]
  have hst : ∀ A B : Statement, A.codes = B.codes → A.oracles = B.oracles →
      A.groups = B.groups → A = B := by
    intro A B h1 h2 h3
    cases A
    cases B
    simp_all
  exact ⟨hst _ _ (L.codes.trans L'.codes.symm) ho hg, L.loc.trans L'.loc.symm,
    L.roots.trans L'.roots.symm, hp, L.trees.trans L'.trees.symm,
    fun i hi => (L.oldTrees i hi).trans (L'.oldTrees i hi).symm⟩

/-! ## 5 Borders 1 and 2 -/

/-- **What a yes at border 1 or 2 holds.** s₀: the start's record of what was handed. -/
structure BehindOk (p : P₁₄) (h : Handed) (o : SharedOut) (s₀ s : S₃) : Prop where
  start : start₃E p.codes p.S h.st h.book h.roots h.w h.own h.mask h.pending o = .ok s₀
  handed : HandedOk p h o
  members : MembersOk s₀ o
  laid : ∃ b y G dot, Laid p.S s₀ s b y G dot
  tidy : Means.Tidy s.st
  fits : BookFits s.book
  mask : s.loc.mask.isSome = true

theorem behindOk_of_one {p : P₁₄} {R : List Fmt.DeclaredRound} {h : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p R 1 h o s = true) : ∃ s₀, BehindOk p h o s₀ s := by
  obtain ⟨s₀, h₀, hh, hc⟩ := shapeAt_inv hs
  simp only [clausesAt, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hc
  obtain ⟨⟨c1, c2, c3, c4⟩, _⟩ := hc
  exact ⟨s₀, h₀, handedOk_of hh.1, membersOk_of hh.2, laid_of c1, Means.tidy4B_iff.1 c2,
    (bookFitsB_iff _).1 c3, c4⟩

theorem behindOk_of_two {p : P₁₄} {R : List Fmt.DeclaredRound} {h : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p R 2 h o s = true) : (∃ s₀, BehindOk p h o s₀ s) ∧ tiedB R s = true := by
  obtain ⟨s₀, h₀, hh, hc⟩ := shapeAt_inv hs
  simp only [clausesAt, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hc
  obtain ⟨⟨c1, c2, c3, c4⟩, c5⟩ := hc
  exact ⟨⟨s₀, h₀, handedOk_of hh.1, membersOk_of hh.2, laid_of c1, Means.tidy4B_iff.1 c2,
    (bookFitsB_iff _).1 c3, c4⟩, by simpa using c5⟩

/-- Behind K14's second part the own group is there and has an open row: (Dot) is its last. -/
theorem rows_there {p : P₁₄} {h : Handed} {o : SharedOut} {s₀ s : S₃} (B : BehindOk p h o s₀ s) :
    ∃ G, s.st.groups[s.loc.own]? = some G ∧ G.rows.toList ≠ [] ∧ G.inRun = false := by
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  have e : s.loc.own = s₀.loc.own := by rw [L.loc]
  refine ⟨groupBehind s₀ G dot, by rw [e]; exact L.group', ?_, L.notBegun⟩
  show (G.rows.push dot).toList ≠ []
  simp

/-- **Behind K14's second part the own group has three members: the two that were handed, then
Omega's copy; each has one sample row.** -/
theorem three_members {p : P₁₄} {h : Handed} {o : SharedOut} {s₀ s : S₃}
    (B : BehindOk p h o s₀ s) (hst : s₀.st = h.st) (hbd : ∃ g, s₀.loc.border = some ⟨g, o⟩) :
    ∃ G₀ G, s₀.st.groups[s₀.loc.own]? = some G₀ ∧ s.st.groups[s.loc.own]? = some G ∧
      G.members = G₀.members.push s.loc.omega ∧ G.members.size = 3 ∧
      ∀ i ∈ G.members.toList, ∃ x, s.st.oracles[i]? = some x ∧ x.sampleRows.size = 1 := by
  obtain ⟨b, y, G₀, dot, L⟩ := B.laid
  obtain ⟨G₁, hG₁, h2, hrows⟩ := B.members.two
  obtain rfl : G₀ = G₁ := Option.some.inj (L.group.symm.trans hG₁)
  obtain ⟨yo, hyo, h1⟩ := B.members.omega
  obtain ⟨g, hg⟩ := hbd
  obtain rfl : (⟨g, o⟩ : Border) = b := Option.some.inj (hg.symm.trans L.border)
  obtain rfl : yo = y := Option.some.inj (hyo.symm.trans L.there)
  have hlt : ∀ i ∈ G₀.members.toList, i < s₀.st.oracles.size := by
    have T : Means.Tidy s₀.st := by rw [hst]; exact B.handed.tidy
    exact (T.inOrder.groups _ _ L.group).there
  have eo : s.loc.own = s₀.loc.own := by rw [L.loc]
  have em : s.loc.omega = s₀.st.oracles.size := by rw [L.loc]
  have hm : (groupBehind s₀ G₀ dot).members = G₀.members.push s₀.st.oracles.size :=
    insert_at_end _ _ hlt
  refine ⟨G₀, groupBehind s₀ G₀ dot, L.group, by rw [eo]; exact L.group', by rw [em]; exact hm, ?_,
    fun i hi => ?_⟩
  · rw [hm, Array.size_push, h2]
  · rw [hm] at hi
    have hi' : i ∈ G₀.members ∨ i = s₀.st.oracles.size := by simpa using hi
    rcases hi' with c | c
    · have c' : i ∈ G₀.members.toList := Array.mem_toList_iff.2 c
      obtain ⟨x, hx, hx1⟩ := hrows i c'
      exact ⟨x, by rw [L.old i (hlt i c')]; exact hx, hx1⟩
    · subst c
      exact ⟨_, L.copy, by simpa using h1⟩

/-! ## 6 The steps -/

/-- **K14's second part keeps "the book fits".** By `adoptP_fits`
(Johnson/Desc/Book/BookFitsGround.lean) along the block's own text. -/
theorem fits_k14Second {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (hB : BookFits s.book) : BookFits s'.book := by
  obtain ⟨x, a, dot, b, _, ha, _, hb, e⟩ := k14Second_inv p s s' rs gs h
  subst e
  obtain ⟨q, t, y, a0, d₁, _, _, _, h0, _, h1, h2⟩ := takeOver_inv _ _ _ _ _ ha
  have eb : b.book = a0.2.book :=
    (Law.addRowP_book _ _ _ _ hb).trans
      ((Law.joinP_book _ _ _ _ _ h2).trans (Law.elsewhereP_book _ _ _ _ _ h1))
  show BookFits b.book
  rw [eb]
  exact VerifiableInference.Desc.Book.adoptP_fits (s.withCols []) a0.2 _ _ a0.1 h0 hB

/-- **0 → 1: K14's second part.** NO FURTHER HYPOTHESIS: `laid_k14Second`
(Johnson/Desc/Third/Law/Laid.lean);
`k14Second_tidy` (Johnson/Desc/Tidy/Third.lean); `fits_k14Second`. -/
theorem step_zero {Cl : Type} {p : P₁₄} {R : List Fmt.DeclaredRound} {h : Handed} {o : SharedOut}
    {s s' : S₃} (hs : shapeAt p R 0 h o s = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hy : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') :
    shapeAt p R 1 h o s' = true := by
  obtain ⟨s₀, h₀, hh, hc⟩ := shapeAt_inv hs
  obtain ⟨h₀', H, _, _, hm⟩ := started_of_shape hs
  obtain rfl : s₀ = s := Except.ok.inj (h₀.symm.trans h₀')
  obtain ⟨b, y, G, dot, L⟩ := laid_k14Second p s₀ s' rs gs hy
  refine shapeAt_of h₀ hh ?_
  simp only [clausesAt, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  have F := frontOk_of_shape hs
  have hb : s₀.book = h.book := F.book
  have tidy : Means.Tidy s'.st := by
    refine k14Second_tidy p s₀ s' rs gs hy (fun x hx => ?_) (by rw [F.st]; exact H.tidy)
    obtain ⟨g, hg⟩ := F.border
    obtain rfl : (⟨g, o⟩ : Border) = x := Option.some.inj (hg.symm.trans hx)
    exact H.order₂
  refine ⟨⟨laidB_of L, Means.tidy4B_iff.2 tidy,
    (bookFitsB_iff _).2 (fits_k14Second p s₀ s' rs gs hy (by rw [hb]; exact H.fits₁)), ?_⟩, by simp⟩
  rw [L.loc]
  exact hm

/-- **1 → 2: the taken trees' sources.** No further hypothesis: the block turns no record, and its
yes is the
clause that border 2 adds. -/
theorem step_one {Cl : Type} {p : P₁₄} (own : Block S₃ Cl) {h : Handed} {o : SharedOut}
    {s s' : S₃} (hs : shapeAt p own.rounds 1 h o s = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hy : (takenSources own).decide s rs gs = .ok s') :
    shapeAt p own.rounds 2 h o s' = true := by
  obtain ⟨e, ht⟩ := (takenSources_exact own s rs gs s').1 hy
  subst e
  obtain ⟨s₀, h₀, hh, hc⟩ := shapeAt_inv hs
  refine shapeAt_of h₀ hh ?_
  simp only [clausesAt, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hc ⊢
  exact ⟨hc.1, by simpa using tiedB_of own ht⟩

/-- **2 → 3: the own test's block.** FOUR HYPOTHESES on what its yes lays, by name: loc: the named
values
stay (at a seat that lays back the statement, the book and the roots alone: by its text); run: the
own group's test has begun; codes: the codes stay; tidy: the statement behind is tidy. -/
theorem step_two {p : P₁₄} {R : List Fmt.DeclaredRound} {h : Handed} {o : SharedOut} {s s' : S₃}
    (hs : shapeAt p R 2 h o s = true) (loc : s'.loc = s.loc)
    (run : ∃ G, s'.st.groups[s.loc.own]? = some G ∧ G.inRun = true)
    (codes : s'.st.codes = s.st.codes) (tidy : Means.Tidy s'.st) :
    shapeAt p R 3 h o s' = true := by
  obtain ⟨s₀, h₀, hh, _⟩ := shapeAt_inv hs
  obtain ⟨⟨s₁, B⟩, _⟩ := behindOk_of_two hs
  obtain rfl : s₀ = s₁ := Except.ok.inj (h₀.symm.trans B.start)
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  obtain ⟨G', hG', hr⟩ := run
  refine shapeAt_of h₀ hh ?_
  simp only [clausesAt, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨?_, by rw [loc]; exact L.loc, by rw [codes]; exact L.codes, Means.tidy4B_iff.2 tidy⟩
  rw [loc, hG']
  exact hr

/-- The yes of the chain's last block: the record stays, and its own test says yes. -/
theorem end₃_yes {Cl : Type} (inFront : List (Block S₃ Cl)) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hy : (end₃ inFront).decide s rs gs = .ok s') :
    s' = s ∧ (ChainEnd.untestedL s.st).all (·.2) = true := by
  have hy' : ((ChainEnd.refuse (ChainEnd.untestedL s.st)).map fun _ => s) = .ok s' := hy
  unfold ChainEnd.refuse at hy'
  split at hy'
  · cases hy'
  · rename_i hn
    refine ⟨(Except.ok.inj hy').symm, List.all_eq_true.2 fun c hc => ?_⟩
    have := List.find?_eq_none.1 hn c hc
    simpa using this

/-- **3 → 4: the chain's last block.** No further hypothesis: and "nothing is left". -/
theorem step_three {Cl : Type} {p : P₁₄} {R : List Fmt.DeclaredRound} {h : Handed} {o : SharedOut}
    {s s' : S₃} (hs : shapeAt p R 3 h o s = true) (inFront : List (Block S₃ Cl))
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hy : (end₃ inFront).decide s rs gs = .ok s') :
    shapeAt p R 4 h o s' = true ∧ (ChainEnd.untestedL s'.st).all (·.2) = true := by
  obtain ⟨e, hf⟩ := end₃_yes inFront s s' rs gs hy
  subst e
  obtain ⟨s₀, h₀, hh, hc⟩ := shapeAt_inv hs
  exact ⟨shapeAt_of h₀ hh hc, hf⟩

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.names_of
#print axioms VerifiableInference.Desc.Last.tied_of
#print axioms VerifiableInference.Desc.Last.tiedB_of
#print axioms VerifiableInference.Desc.Last.shapeAt_inv
#print axioms VerifiableInference.Desc.Last.shapeAt_of
#print axioms VerifiableInference.Desc.Last.handedOk_of
#print axioms VerifiableInference.Desc.Last.membersOk_of
#print axioms VerifiableInference.Desc.Last.started_of_shape
#print axioms VerifiableInference.Desc.Last.atDot_of_shape
#print axioms VerifiableInference.Desc.Last.frontOk_of_shape
#print axioms VerifiableInference.Desc.Last.laid_of
#print axioms VerifiableInference.Desc.Last.laidB_of
#print axioms VerifiableInference.Desc.Last.array_eq_of
#print axioms VerifiableInference.Desc.Last.laid_pins
#print axioms VerifiableInference.Desc.Last.behindOk_of_one
#print axioms VerifiableInference.Desc.Last.behindOk_of_two
#print axioms VerifiableInference.Desc.Last.rows_there
#print axioms VerifiableInference.Desc.Last.three_members
#print axioms VerifiableInference.Desc.Last.fits_k14Second
#print axioms VerifiableInference.Desc.Last.step_zero
#print axioms VerifiableInference.Desc.Last.step_one
#print axioms VerifiableInference.Desc.Last.step_two
#print axioms VerifiableInference.Desc.Last.end₃_yes
#print axioms VerifiableInference.Desc.Last.step_three
