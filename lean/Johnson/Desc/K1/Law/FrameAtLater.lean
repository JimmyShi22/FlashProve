-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/FrameAtLater.lean: WHICH OF THE FRAME's LISTS A LATER MOMENT's SENDING OF KIND
K1 WRITES, at the first chain's record: behind a yes of `commitAtS` the open link's frame is the
frame in front with its moment one higher and THE NEW MESSAGES' NUMBERS APPENDED TO ITS LIST "own";
every other field of the frame is as it was; the walk's list "sent" is just these numbers; and the
numbers are n₀, n₀ + 1, …, one for each message of the place, n₀ the number of the statement's
messages in front. Statements with their proofs. It names no table of joints.
  `idsOf P n₀`: the numbers.
  `joinOwnP_frame`: the joining writes of the frame its list "own" alone. `commitOwn_frame`: the
    kind's block. `link_put`: what `putLink` and `putFork` leave of the open link.
  `commitAtS_frame`: **the block at the record.** `commitAtS_own`, `commitAtS_keptBefore`: read off
    it.
What is not claimed. At which moment a message of "own" was sent. What stands between this sending
and a later draw. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.LaterAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP)
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- The numbers of a place's messages, where n₀ messages stand in front. -/
def idsOf (P : Par) (n₀ : Nat) : Array Nat := (Array.range P.sent.size).map (· + n₀)

/-- The joining writes of the frame its list "own" alone. -/
theorem joinOwnP_frame {L : Type} (p : GPar) (d : DState L) (f : ReqFrame) (sent : List ReqMessage)
    (ids : Array Nat) (y : ReqFrame × DState L) (h : joinOwnP groundG p d f sent ids = some y) :
    y.1 = { f with own := f.own ++ ids } := by
  unfold joinOwnP at h
  split at h
  · obtain ⟨d', _, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · cases h

/-- **The kind's block**: the link's record behind. -/
theorem commitOwn_frame (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : Owing (L3.St (DState Unit))) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitOwn P link moment arrays : Block _ Cl).decide s [r₁, r₂] gs = .ok s') :
    s'.held.L.check.frame =
        { s.held.L.check.frame with
          moment := s.held.L.check.frame.moment + 1
          own := s.held.L.check.frame.own ++ idsOf P s.held.w.st.oracles.size } ∧
      s'.held.L.check.sent = idsOf P s.held.w.st.oracles.size := by
  unfold commitOwn at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · obtain ⟨t, ht, rfl⟩ := (map_ok _ _ _).1 h
      unfold L3.commitStep at ht
      obtain ⟨_, _, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨check, w⟩, h2, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨L, F⟩, h3, ht⟩ := (bind_ok _ _ _).1 ht
      have e : ({ s.held with L := L, F := F, w := w } : L3.St (DState Unit)) = t := by
        simpa [pure, Except.pure] using ht
      obtain ⟨ids, d₁, f', a1, a2, a3⟩ := laterOwn_ok P s.owed _ _ _ _ _ h2
      obtain ⟨_, hids, _⟩ := (decideSend_iff P s.owed _ d₁ r₁ r₂ ids).1 a1
      have hf : f' = _ := joinOwnP_frame _ _ _ _ _ _ a2
      unfold L3.commitBehind at h3
      obtain ⟨F₁, _, h3⟩ := (bind_ok _ _ _).1 h3
      split at h3
      · have e3 := (Prod.mk.inj (Except.ok.inj h3)).1
        rw [← e, ← e3, a3, hf, hids]
        exact ⟨rfl, rfl⟩
      · cases h3
  · cases h

/-- Where a link is open, laying a link's record and then a ledger leaves that record open. -/
theorem link_put (s : S) (w : DState Unit) (L L' : LinkCtx) (F' : Fork) (hL : s.link? = some L) :
    (((laid s w).putLink L').putFork F').link? = some L' := by
  cases hs : s.here with
  | lay a => simp [S.putFork, S.putLink, S.link?, laid, hs]
  | att a => simp [S.putFork, S.putLink, S.link?, laid, hs]
  | head a =>
    have ho : a.opened = true := by
      by_contra hn
      simp [S.link?, hs, hn] at hL
    simp [S.putFork, S.putLink, S.link?, laid, hs, ho]
  | between => simp [S.link?, hs] at hL
  | fin a => simp [S.link?, hs] at hL
  | mem a => simp [S.link?, hs] at hL

/-- **THE BLOCK AT THE RECORD.** -/
theorem commitAtS_frame (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    ∃ L L', s.link? = some L ∧ s'.link? = some L' ∧
      L'.check.frame =
        { L.check.frame with
          moment := L.check.frame.moment + 1
          own := L.check.frame.own ++ idsOf P s.st.oracles.size } ∧
      L'.check.sent = idsOf P s.st.oracles.size := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · rename_i L F tl hL _ _
    obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    obtain ⟨e1, e2⟩ := commitOwn_frame P link moment arrays _ y r₁ r₂ gs hy
    exact ⟨L, y.held.L, hL, link_put s _ L _ _ hL, e1, e2⟩
  · cases h

/-- The list "own" behind. -/
theorem commitAtS_own (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    ∃ L L', s.link? = some L ∧ s'.link? = some L' ∧
      L'.check.frame.own = L.check.frame.own ++ idsOf P s.st.oracles.size := by
  obtain ⟨L, L', a, b, e, _⟩ := commitAtS_frame P link moment arrays s s' r₁ r₂ gs h
  exact ⟨L, L', a, b, by rw [e]⟩

/-- The list of kept copies is as it was. -/
theorem commitAtS_keptBefore (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    ∃ L L', s.link? = some L ∧ s'.link? = some L' ∧
      L'.check.frame.keptBefore = L.check.frame.keptBefore := by
  obtain ⟨L, L', a, b, e, _⟩ := commitAtS_frame P link moment arrays s s' r₁ r₂ gs h
  exact ⟨L, L', a, b, by rw [e]⟩

/-- The i-th of the numbers. -/
theorem idsOf_get (P : Par) (n₀ i : Nat) (hi : i < P.sent.size) :
    (idsOf P n₀)[i]? = some (n₀ + i) := by
  unfold idsOf
  rw [Array.getElem?_map, Array.getElem?_range, if_pos hi, Option.map_some, Nat.add_comm]

theorem idsOf_size (P : Par) (n₀ : Nat) : (idsOf P n₀).size = P.sent.size := by
  simp [idsOf]

end VerifiableInference.Desc.K1
