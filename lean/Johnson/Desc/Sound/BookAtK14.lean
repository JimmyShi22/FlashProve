-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BookAtK14.lean: **"THE BOOK IS IN ORDER" ALONG THE SHARED CHAIN's EIGHT BLOCKS OF THE KIND K14.** Statements and proofs.

BookStep (Johnson/Desc/Sound/BookInOrder.lean): the record counts as many roots as the book has trees, and the tree at the place z bears the number first + z. It
is what the law of the proximity test wants of the record in front of it (Johnson/Desc/K12/Coin/FirstBook.lean).
  newGroupP_bk · joinP_bk · addRowP_bk · addRowsP_bk · takeMaskP_bk   the ground's five effects that K14's own places call leave the book, the count of roots and
                   the small record.
  linPoint_bk · laysRec_bk · loc_bk · joins_bk · linZeta_bk · split_bk   the six places' functions, at every list of rounds and columns, leave the book and the count
                   of roots; four leave the small record; "LIN point" and "LIN zeta" leave its note of the first mask.
  why_some         a yes of a place's decision is its function's "some".
  own_leave        the first, third, fourth, sixth, seventh and eighth of blocks P leave the book, the count of roots and the note of the first mask at a yes.
  send_first       the second and the fifth are sendings that count their trees from P.par.toGPar.firstTree.
  **bookStep_k14**     AT A YES OF ANY OF THE EIGHT, BookStep P.par.toGPar.firstTree goes from the record in front to the record behind.
  mask_at_two · mask_kept   "THE FIRST FOLD's MASK HAS COME": where the plan's masks go ahead, the second block notes it; the third to the eighth leave the note.
  bookStep_first   the chain's first record (first codes key) has it.
  bookStep_front   the chain's front block leaves the record.
Limits. Book-keeping at the kind's own blocks at the chain's own record St: not at a description's pieces (decide_below_lift, FenceK14AtDesc.lean, carries a yes over). THE TWO
PROXIMITY TESTS AND THE CHAIN's END ARE NOT HERE. It closes no row. NO SOUNDNESS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BookInOrder
import Johnson.Desc.Sound.FenceK14Sends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Sound (Received BookStep bookStep_received bookStep_empty)

section
variable {L : Type}

theorem newGroupP_bk (d d' : DState L) (c z g : Nat) (h : newGroupP d c z = some (g, d')) :
    d'.book = d.book ∧ d'.roots = d.roots ∧ d'.loc = d.loc := by
  unfold newGroupP at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

theorem joinP_bk (d d' : DState L) (g o : Nat) (kept : Bool) (h : joinP d g o kept = some d') :
    d'.book = d.book ∧ d'.roots = d.roots ∧ d'.loc = d.loc := by
  unfold joinP at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨G, _, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

theorem addRowP_bk (d d' : DState L) (g : Nat) (row : Row) (h : addRowP d g row = some d') :
    d'.book = d.book ∧ d'.roots = d.roots ∧ d'.loc = d.loc := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

theorem addRowsFrom_bk (g : Nat) : ∀ (l : List Row) (d d' : DState L),
    addRowsFrom g l d = some d' → d'.book = d.book ∧ d'.roots = d.roots ∧ d'.loc = d.loc
  | [], d, d', h => by
    simp only [addRowsFrom, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩
  | row :: l, d, d', h => by
    simp only [addRowsFrom, Option.bind_eq_some_iff] at h
    obtain ⟨d1, h1, h2⟩ := h
    obtain ⟨a1, a2, a3⟩ := addRowP_bk d d1 g row h1
    obtain ⟨b1, b2, b3⟩ := addRowsFrom_bk g l d1 d' h2
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3⟩

theorem addRowsP_bk (d d' : DState L) (g : Nat) (rows : List Row)
    (h : addRowsP d g rows = some d') : d'.book = d.book ∧ d'.roots = d.roots ∧ d'.loc = d.loc := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_bk g rows d d' h
  · cases h

theorem takeMaskP_bk (d d' : DState L) (o k : Nat) (h : takeMaskP d o = some (k, d')) :
    d'.book = d.book ∧ d'.roots = d.roots ∧ d'.loc = d.loc := by
  unfold takeMaskP at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨l, _, _, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

end

/-! ## The six places -/

theorem linPoint_bk (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : linPoint p d rs = some d') :
    d'.book = d.book ∧ d'.roots = d.roots ∧ d'.loc.firstMask = d.loc.firstMask := by
  unfold linPoint at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u0, _, ⟨gU, d1⟩, h1, h2⟩ := h
    obtain ⟨a1, a2, a3⟩ := newGroupP_bk d d1 _ _ gU h1
    split at h2
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      obtain ⟨b1, b2, b3⟩ := newGroupP_bk d1 d2 _ _ gO h3
      exact ⟨b1.trans a1, b2.trans a2, congrArg (·.firstMask) (b3.trans a3)⟩
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      simp only [Prod.mk.injEq] at h3
      obtain ⟨_, rfl⟩ := h3
      exact ⟨a1, a2, congrArg (·.firstMask) a3⟩
  · cases h

theorem laysRec_bk (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d') :
    d'.book = d.book ∧ d'.roots = d.roots ∧ d'.loc = d.loc := by
  unfold laysRec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, hj, rows, _, ha⟩ := h
  obtain ⟨a1, a2, a3⟩ := joinP_bk d d1 _ _ _ hj
  obtain ⟨b1, b2, b3⟩ := addRowsP_bk d1 d' _ rows ha
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3⟩

theorem loc_bk (p : Par) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : loc p d rs gs = some d') : d'.book = d.book ∧ d'.roots = d.roots ∧ d'.loc = d.loc := by
  unfold loc at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨rows, _, ha⟩ := h
    exact addRowsP_bk d d' _ rows ha
  · cases h

theorem joins_bk (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : joins p d rs = some d') :
    d'.book = d.book ∧ d'.roots = d.roots ∧ d'.loc = d.loc := by
  unfold joins at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, h1, h2⟩ := h
  obtain ⟨a1, a2, a3⟩ := joinP_bk d d1 _ _ _ h1
  split at h2
  · simp only [Option.bind_eq_some_iff] at h2
    obtain ⟨d2, h3, h4⟩ := h2
    obtain ⟨b1, b2, b3⟩ := joinP_bk d1 d2 _ _ _ h3
    obtain ⟨c1, c2, c3⟩ := joinP_bk d2 d' _ _ _ h4
    exact ⟨(c1.trans b1).trans a1, (c2.trans b2).trans a2, (c3.trans b3).trans a3⟩
  · simp only [Option.some.injEq] at h2
    subst h2
    exact ⟨a1, a2, a3⟩

theorem linZeta_bk (d d' : St) (rs : List Fmt.RoundView) (h : linZeta d rs = some d') :
    d'.book = d.book ∧ d'.roots = d.roots ∧ d'.loc.firstMask = d.loc.firstMask := by
  unfold linZeta at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

theorem split_bk (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : split p d rs = some d') :
    d'.book = d.book ∧ d'.roots = d.roots ∧ d'.loc = d.loc := by
  cases hS : p.S.sharedSplitNeeded with
  | true =>
    rcases rs with _ | ⟨r, _ | ⟨r2, rs⟩⟩
    · unfold split at h
      simp [hS] at h
    · obtain ⟨row, x, G, kappa, d₁, d₂, _, _, _, _, hk, h2, h3⟩ := split_inv p d d' r hS h
      obtain ⟨a1, a2, a3⟩ := takeMaskP_bk d d₁ _ _ hk
      obtain ⟨b1, b2, b3⟩ := addRowP_bk d₁ d₂ _ _ h2
      obtain ⟨c1, c2, c3⟩ := addRowP_bk d₂ d' _ _ h3
      exact ⟨(c1.trans b1).trans a1, (c2.trans b2).trans a2, (c3.trans b3).trans a3⟩
    · unfold split at h
      simp [hS] at h
  | false =>
    rcases rs with _ | ⟨r, rs⟩
    · unfold split at h
      simp only [hS, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨row, _, h⟩ := h
      exact addRowP_bk d d' _ _ h
    · unfold split at h
      simp [hS] at h

/-! ## What the two sendings note -/

/-- A yes of a sending at this chain's state: what it notes behind is noted at a record with the small record in front. -/
theorem sendAt_behind (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') :
    ∃ a ids, a.loc = d.loc ∧ behind a ids = some d' := by
  simp only [sendAt, Block.inside] at h
  obtain ⟨t, ht, h⟩ := ebind_ok h
  cases ht
  obtain ⟨t', ht', h⟩ := ebind_ok h
  have hb := named_some h
  refine ⟨{ st := t'.held.st, book := t'.held.book, roots := t'.held.roots,
            opened := t'.held.opened, loc := d.loc }, t'.held.loc, rfl, hb⟩

/-- Where the masks go ahead, the first mask is noted behind o_u's sending. -/
theorem behindU_mask (p : Par) (d d' : St) (ids : Array Nat) (hm : p.S.masksAhead = true)
    (h : behindU p d ids = some d') : d'.loc.firstMask.isSome = true := by
  unfold behindU at h
  simp only [Option.bind_eq_bind, hm, if_true, Option.bind_eq_some_iff, Option.some.injEq,
    Option.map_eq_some_iff] at h
  obtain ⟨mask, ⟨id, _, rfl⟩, o, _, rfl⟩ := h
  rfl

/-- o_omega's sending leaves that note. -/
theorem behindOmega_mask (p : Par) (d d' : St) (ids : Array Nat)
    (h : behindOmega p d ids = some d') : d'.loc.firstMask = d.loc.firstMask := by
  obtain ⟨_, o, sp, _, e⟩ := behindOmega_inv p d d' ids h
  rw [e]

/-! ## The eight blocks -/

/-- A yes of a place's decision is its function's "some". -/
theorem why_some (l : Clauses) (x : Option St) (d' : St) (h : why l x = .ok d') : x = some d' := by
  unfold why at h
  split at h
  · rw [Except.ok.inj h]
  · cases h

/-- **K14's six own blocks leave the book and the count of roots.** -/
theorem own_leave (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ b, b = b1 ∨ b = b3 ∨ b = b4 ∨ b = b6 ∨ b = b7 ∨ b = b8 → ∀ d rs gs d',
      b.decide d rs gs = .ok d' →
        d'.book = d.book ∧ d'.roots = d.roots ∧ d'.loc.firstMask = d.loc.firstMask := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  rintro b (rfl | rfl | rfl | rfl | rfl | rfl) d rs gs d' h
  · exact linPoint_bk _ d d' rs (why_some _ _ _ h)
  · obtain ⟨e1, e2, e3⟩ := laysRec_bk _ d d' rs (why_some _ _ _ h)
    exact ⟨e1, e2, congrArg (·.firstMask) e3⟩
  · obtain ⟨e1, e2, e3⟩ := loc_bk _ d d' rs gs (why_some _ _ _ h)
    exact ⟨e1, e2, congrArg (·.firstMask) e3⟩
  · obtain ⟨e1, e2, e3⟩ := joins_bk _ d d' rs (why_some _ _ _ h)
    exact ⟨e1, e2, congrArg (·.firstMask) e3⟩
  · exact linZeta_bk d d' rs (why_some _ _ _ h)
  · obtain ⟨e1, e2, e3⟩ := split_bk _ d d' rs (why_some _ _ _ h)
    exact ⟨e1, e2, congrArg (·.firstMask) e3⟩

/-- The two sendings count their trees from one number. -/
theorem send_first (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ b, b = b2 ∨ b = b5 → ∀ d rs gs d', b.decide d rs gs = .ok d' →
      ∃ sent lay, Received P.par.toGPar.firstTree sent lay d.st d.book d.roots d'.st d'.book
        d'.roots := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  rintro b (rfl | rfl) d rs gs d' h
  · exact ⟨_, sendAt_received P _ _ _ _ _ (behindU_book P.par) d d' rs gs h⟩
  · exact ⟨_, sendAt_received P _ _ _ _ _ (behindOmega_book P.par) d d' rs gs h⟩

/-- **AT A YES OF ANY OF THE EIGHT THE BOOK STAYS IN ORDER.** -/
theorem bookStep_k14 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St Unit)
    (hb : b ∈ [b1, b2, b3, b4, b5, b6, b7, b8]) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : b.decide d rs gs = .ok d')
    (hB : BookStep P.par.toGPar.firstTree d.book d.roots) :
    BookStep P.par.toGPar.firstTree d'.book d'.roots := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  have own : (b = b1 ∨ b = b3 ∨ b = b4 ∨ b = b6 ∨ b = b7 ∨ b = b8) →
      BookStep P.par.toGPar.firstTree d'.book d'.roots := fun hq => by
    obtain ⟨e1, e2, _⟩ := own_leave P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hq d rs gs d' h
    rw [e1, e2]
    exact hB
  have snd : (b = b2 ∨ b = b5) → BookStep P.par.toGPar.firstTree d'.book d'.roots := fun hq => by
    obtain ⟨sent, lay, hr⟩ := send_first P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hq d rs gs d' h
    exact bookStep_received _ sent lay _ _ _ _ _ _ hr hB
  rcases hb with e | e | e | e | e | e | e | e
  · exact own (.inl e)
  · exact snd (.inl e)
  · exact own (.inr (.inl e))
  · exact own (.inr (.inr (.inl e)))
  · exact snd (.inr e)
  · exact own (.inr (.inr (.inr (.inl e))))
  · exact own (.inr (.inr (.inr (.inr (.inl e)))))
  · exact own (.inr (.inr (.inr (.inr (.inr e)))))

/-- **Where the masks go ahead, the first mask is noted behind the second block.** -/
theorem mask_at_two (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hm : P.par.S.masksAhead = true)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : b2.decide d rs gs = .ok d') : d'.loc.firstMask.isSome = true := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  obtain ⟨a, ids, _, hb⟩ := sendAt_behind P _ _ _ _ _ d d' rs gs h
  exact behindU_mask P.par a d' ids hm hb

/-- **And the note stays up to the eighth.** -/
theorem mask_kept (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St Unit)
    (hb : b ∈ [b3, b4, b5, b6, b7, b8]) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : b.decide d rs gs = .ok d') :
    d'.loc.firstMask = d.loc.firstMask := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  have own : (b = b1 ∨ b = b3 ∨ b = b4 ∨ b = b6 ∨ b = b7 ∨ b = b8) →
      d'.loc.firstMask = d.loc.firstMask := fun hq =>
    (own_leave P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hq d rs gs d' h).2.2
  rcases hb with e | e | e | e | e | e
  · exact own (.inr (.inl e))
  · exact own (.inr (.inr (.inl e)))
  · subst e
    unfold blocks at hbl
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
      List.cons.injEq, and_true] at hbl
    obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
    obtain ⟨a, ids, ea, hb⟩ := sendAt_behind P _ _ _ _ _ d d' rs gs h
    rw [behindOmega_mask P.par a d' ids hb, ea]
  · exact own (.inr (.inr (.inr (.inl e))))
  · exact own (.inr (.inr (.inr (.inr (.inl e)))))
  · exact own (.inr (.inr (.inr (.inr (.inr e)))))

/-- The chain's first record has it. -/
theorem bookStep_first (ft : ℕ) (codes : Codes) (key : TableKey) :
    BookStep ft (first codes key).book (first codes key).roots := bookStep_empty ft

/-- The chain's front block leaves the record. -/
theorem bookStep_front (c : Model.Verify.Chains) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (frontBlock c).decide d rs gs = .ok d') : d' = d :=
  (Except.ok.inj h).symm

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.own_leave
#print axioms Desc.K14.Law.Fence.send_first
#print axioms Desc.K14.Law.Fence.bookStep_k14
#print axioms Desc.K14.Law.Fence.mask_at_two
#print axioms Desc.K14.Law.Fence.mask_kept
#print axioms Desc.K14.Law.Fence.bookStep_first
#print axioms Desc.K14.Law.Fence.bookStep_front
