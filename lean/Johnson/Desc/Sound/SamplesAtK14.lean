-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SamplesAtK14.lean: **THE SHARED CHAIN's EIGHT BLOCKS OF THE KIND K14 LEAVE EVERY OLDER MESSAGE's SAMPLE.** Statements and proofs, in the blocks' own decide-form.

A message's pin and its promise "no collision" read the record's sample of it. They ride past a block only if the block leaves that sample (pin_rides | noColl_rides,
Johnson/Desc/Sound/LedgerRides.lean: the premise hsm). Here: what a reader of a sample reads of a message (smpPart: shape, mark, sample rows: Johnson/Desc/K12/Coin/SamplesThrough.lean), and the
codes, stand at a yes of each of the eight.
  KeepsSmp d d'    the codes stand; no message is lost; smpPart of every message of d stands.
  newGroupP_smp · joinP_smp · addRowP_smp · addRowsP_smp · takeMaskP_smp   the ground's five effects.
  linPoint_smp … split_smp   the six places' functions.
  own_smp          the six own blocks.     send_smp   the two sendings (an older message stands whole: decideSend_kept, Johnson/Desc/K1/Law/KeptAtRecord.lean).
  **keepsSmp_k14**     any of the eight.
Limits. Of the messages that a sending brings nothing is said. At the chain's own record St. It closes no row. NO SOUNDNESS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BookAtK14
import Johnson.Desc.K12.Coin.SamplesThrough
import Johnson.Desc.K1.Law.KeptAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (decideSend sendOwn)
open VerifiableInference.Desc.K12.Coin (smpPart)

section
variable {L : Type}

/-- The codes stand; no message is lost; what a reader of a sample reads of each message stands. -/
def KeepsSmp (d d' : DState L) : Prop :=
  d'.st.codes = d.st.codes ∧ d.st.oracles.size ≤ d'.st.oracles.size ∧
    ∀ j, j < d.st.oracles.size → (d'.st.oracles[j]?).map smpPart = (d.st.oracles[j]?).map smpPart

theorem KeepsSmp.refl (d : DState L) : KeepsSmp d d := ⟨rfl, Nat.le_refl _, fun _ _ => rfl⟩

theorem KeepsSmp.trans {a b c : DState L} (h : KeepsSmp a b) (k : KeepsSmp b c) : KeepsSmp a c :=
  ⟨k.1.trans h.1, h.2.1.trans k.2.1,
    fun j hj => (k.2.2 j (Nat.lt_of_lt_of_le hj h.2.1)).trans (h.2.2 j hj)⟩

theorem KeepsSmp.of_st {d d' : DState L} (h : d'.st = d.st) : KeepsSmp d d' := by
  unfold KeepsSmp
  rw [h]
  exact ⟨rfl, Nat.le_refl _, fun _ _ => rfl⟩

/-- A turn of one message that leaves the three fields. -/
theorem keeps_modify (d d' : DState L) (o : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, smpPart (f x) = smpPart x) (hc : d'.st.codes = d.st.codes)
    (ho : d'.st.oracles = d.st.oracles.modify o f) : KeepsSmp d d' := by
  refine ⟨hc, by rw [ho, Array.size_modify], fun j _ => ?_⟩
  rw [ho, Array.getElem?_modify]
  split
  · rw [Option.map_map]
    congr 1
    funext x
    exact hf x
  · rfl

theorem newGroupP_smp (d d' : DState L) (c z g : Nat) (h : newGroupP d c z = some (g, d')) :
    KeepsSmp d d' := by
  unfold newGroupP at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨rfl, Nat.le_refl _, fun _ _ => rfl⟩
  · cases h

theorem joinP_smp (d d' : DState L) (g o : Nat) (kept : Bool) (h : joinP d g o kept = some d') :
    KeepsSmp d d' := by
  unfold joinP at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨G, _, rfl⟩ := h
    exact keeps_modify d _ o (fun x => { x with groups := x.groups ++ [g] }) (fun _ => rfl) rfl rfl
  · cases h

theorem addRowP_smp (d d' : DState L) (g : Nat) (row : Row) (h : addRowP d g row = some d') :
    KeepsSmp d d' := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, Nat.le_refl _, fun _ _ => rfl⟩
  · cases h

theorem addRowsFrom_smp (g : Nat) : ∀ (l : List Row) (d d' : DState L),
    addRowsFrom g l d = some d' → KeepsSmp d d'
  | [], d, d', h => by
    simp only [addRowsFrom, Option.some.injEq] at h
    subst h
    exact KeepsSmp.refl d
  | row :: l, d, d', h => by
    simp only [addRowsFrom, Option.bind_eq_some_iff] at h
    obtain ⟨d1, h1, h2⟩ := h
    exact (addRowP_smp d d1 g row h1).trans (addRowsFrom_smp g l d1 d' h2)

theorem addRowsP_smp (d d' : DState L) (g : Nat) (rows : List Row)
    (h : addRowsP d g rows = some d') : KeepsSmp d d' := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_smp g rows d d' h
  · cases h

theorem takeMaskP_smp (d d' : DState L) (o k : Nat) (h : takeMaskP d o = some (k, d')) :
    KeepsSmp d d' := by
  unfold takeMaskP at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨l, _, _, rfl⟩ := h
    exact keeps_modify d _ o (fun x => { x with ledger := some { l with
      next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1, left := l.left - 1 } })
      (fun _ => rfl) rfl rfl
  · cases h

end

/-! ## The six places -/

theorem linPoint_smp (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : linPoint p d rs = some d') :
    KeepsSmp d d' := by
  unfold linPoint at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u0, _, ⟨gU, d1⟩, h1, h2⟩ := h
    have a := newGroupP_smp d d1 _ _ gU h1
    split at h2
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      exact (a.trans (newGroupP_smp d1 d2 _ _ gO h3)).trans (KeepsSmp.of_st rfl)
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      simp only [Prod.mk.injEq] at h3
      obtain ⟨_, rfl⟩ := h3
      exact a.trans (KeepsSmp.of_st rfl)
  · cases h

theorem laysRec_smp (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d') :
    KeepsSmp d d' := by
  unfold laysRec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, hj, rows, _, ha⟩ := h
  exact (joinP_smp d d1 _ _ _ hj).trans (addRowsP_smp d1 d' _ rows ha)

theorem loc_smp (p : Par) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : loc p d rs gs = some d') : KeepsSmp d d' := by
  unfold loc at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨rows, _, ha⟩ := h
    exact addRowsP_smp d d' _ rows ha
  · cases h

theorem joins_smp (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : joins p d rs = some d') :
    KeepsSmp d d' := by
  unfold joins at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, h1, h2⟩ := h
  have a := joinP_smp d d1 _ _ _ h1
  split at h2
  · simp only [Option.bind_eq_some_iff] at h2
    obtain ⟨d2, h3, h4⟩ := h2
    exact (a.trans (joinP_smp d1 d2 _ _ _ h3)).trans (joinP_smp d2 d' _ _ _ h4)
  · simp only [Option.some.injEq] at h2
    subst h2
    exact a

theorem linZeta_smp (d d' : St) (rs : List Fmt.RoundView) (h : linZeta d rs = some d') :
    KeepsSmp d d' := by
  unfold linZeta at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact KeepsSmp.of_st rfl
  · cases h

theorem split_smp (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : split p d rs = some d') :
    KeepsSmp d d' := by
  cases hS : p.S.sharedSplitNeeded with
  | true =>
    rcases rs with _ | ⟨r, _ | ⟨r2, rs⟩⟩
    · unfold split at h
      simp [hS] at h
    · obtain ⟨row, x, G, kappa, d₁, d₂, _, _, _, _, hk, h2, h3⟩ := split_inv p d d' r hS h
      exact ((takeMaskP_smp d d₁ _ _ hk).trans (addRowP_smp d₁ d₂ _ _ h2)).trans
        (addRowP_smp d₂ d' _ _ h3)
    · unfold split at h
      simp [hS] at h
  | false =>
    rcases rs with _ | ⟨r, rs⟩
    · unfold split at h
      simp only [hS, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨row, _, h⟩ := h
      exact addRowP_smp d d' _ _ h
    · unfold split at h
      simp [hS] at h

/-! ## The eight blocks -/

theorem own_smp (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ b, b = b1 ∨ b = b3 ∨ b = b4 ∨ b = b6 ∨ b = b7 ∨ b = b8 → ∀ d rs gs d',
      b.decide d rs gs = .ok d' → KeepsSmp d d' := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  rintro b (rfl | rfl | rfl | rfl | rfl | rfl) d rs gs d' h
  · exact linPoint_smp _ d d' rs (why_some _ _ _ h)
  · exact laysRec_smp _ d d' rs (why_some _ _ _ h)
  · exact loc_smp _ d d' rs gs (why_some _ _ _ h)
  · exact joins_smp _ d d' rs (why_some _ _ _ h)
  · exact linZeta_smp d d' rs (why_some _ _ _ h)
  · exact split_smp _ d d' rs (why_some _ _ _ h)

/-- A yes of a sending at this chain's state leaves every older message whole. -/
theorem sendAt_smp (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') : KeepsSmp d d' := by
  simp only [sendAt, Block.inside] at h
  obtain ⟨t, ht, h⟩ := ebind_ok h
  cases ht
  obtain ⟨t', ht', h⟩ := ebind_ok h
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx, rfl⟩ := emap_ok ht'
  obtain ⟨k1, _, k3⟩ := VerifiableInference.Desc.K1.decideSend_kept Q none _ x2 rs ids hx
  obtain ⟨x1, hr, _, _, es⟩ := decideSend_book Q none _ rs ids x2 hx
  obtain ⟨lay, _, _, r3, _, _⟩ := VerifiableInference.Desc.K1.recvP_received _ _ _ _ _ hr
  obtain ⟨e1, _, _⟩ := hb _ _ _ (named_some h)
  refine ⟨by rw [e1]; exact k1, ?_, fun j hj => ?_⟩
  · rw [e1]
    have : x2.st.oracles.size = d.st.oracles.size + Q.sent.size := es.trans r3
    show d.st.oracles.size ≤ x2.st.oracles.size
    omega
  · rw [e1]
    exact congrArg (Option.map smpPart) (k3 j hj)

theorem send_smp (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ b, b = b2 ∨ b = b5 → ∀ d rs gs d', b.decide d rs gs = .ok d' → KeepsSmp d d' := by
  intro b hb d rs gs d' h
  obtain ⟨n, Q, inFront, groups, behind, rfl, _, hbk⟩ := sends_are P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb
  exact sendAt_smp P n Q inFront groups behind hbk d d' rs gs h

/-- **ANY OF THE EIGHT.** -/
theorem keepsSmp_k14 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St Unit)
    (hb : b ∈ [b1, b2, b3, b4, b5, b6, b7, b8]) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : b.decide d rs gs = .ok d') : KeepsSmp d d' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  have own := fun hq => own_smp P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hq d rs gs d' h
  have snd := fun hq => send_smp P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hq d rs gs d' h
  rcases hb with e | e | e | e | e | e | e | e
  · exact own (.inl e)
  · exact snd (.inl e)
  · exact own (.inr (.inl e))
  · exact own (.inr (.inr (.inl e)))
  · exact snd (.inr e)
  · exact own (.inr (.inr (.inr (.inl e))))
  · exact own (.inr (.inr (.inr (.inr (.inl e)))))
  · exact own (.inr (.inr (.inr (.inr (.inr e)))))

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.own_smp
#print axioms Desc.K14.Law.Fence.send_smp
#print axioms Desc.K14.Law.Fence.keepsSmp_k14
