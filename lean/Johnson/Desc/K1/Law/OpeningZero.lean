-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/OpeningZero.lean: THE FIRST SEGMENT's OPENING WITH "LINK 0: OPENED" JOINED
BEHIND IT: one block of a chain's blocksInOrder list, of two texts: kind K1's `firstSegmentOpening`
(Johnson/Desc/K1/First.lean) and the link's frame's `openLayZero`
(Johnson/Desc/First/Walk/FrameZero.lean). Between the two halves stands a record of which no border
speaks: so what the joined block does is said here from the record in front of both to the record
behind both. A definition, and statements with their proofs.
Main names:
  `openingZero q gp nm X fvs kCol`: the joined block, bare.
  `openingZero_mid`: its yes, cut in two.
  `isSend_openingZero`: **it is a sending** (`IsSend`, Johnson/Desc/K1/Law/GoodSend3.lean): so the
    law of a sending holds of it.
  `firstAtS_atStart`: what the opening lays "at the start": the numbers of its last messages.
  `openingZero_rec`: **what a yes does to the record**: the chain stands in a layers' segment, the
    link's number is 0; a mark stays and none is laid; no count of rows waits; the book and the
    number of messages as a sending leaves them (`Booked`,
    Johnson/Desc/K1/Law/BookAtRecord.lean); of what the links leave, the index masks' number alone
    is turned, and the message with that number stands in the statement.
  `openingZero_index`: **which number**: where nothing was laid "at the start" in front, it is the
    number of the LAST message that the block has sent.
  `firstAtS_retype`: the opening typed at no claims and carried to another type of claims
    (`Block.retype`) says yes only where the opening at that type does.

Used of another file: `openedZeroGives` (Johnson/Top/H0/Walk/FrameTiedRec.lean).
What is not claimed. That a chain holds this block (as a chain holds it each half is guarded:
`andThen_underR`, Johnson/Desc/Sound/SeatedPiece.lean). That nothing was laid "at the start" in
front. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.BookAtRecord
import Johnson.Desc.K1.Law.GoodSend4
import Johnson.Top.H0.Walk.FrameTiedRec
import Johnson.Desc.Sound.SeatGuardChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc.First.Send (joinOwnP)
open VerifiableInference.Desc.First (S ModelPart Stand standOf)
open Johnson.Desc.First.Walk (openLayZero LayPar roomOf)
open Johnson.Desc.First.Walk.Tied (openedZeroGives)

variable {Cl : Type}

/-- **The joined block**, bare. -/
def openingZero (q : Params.First) (gp : GPar) (nm : String) (X : LayPar) (fvs : List Bool)
    (kCol : Nat) : Block S Cl :=
  (firstSegmentOpening q gp).andThen nm (roundlessBlock "link 0: opened" 1 (some 0) 1 (openLayZero X fvs kCol))

/-- Its yes, cut in two. -/
theorem openingZero_mid {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : Nat} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t) :
    ∃ s₁ g₁, (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] g₁ = .ok s₁ ∧
      openLayZero X fvs kCol s₁ = .ok t := by
  have h' : ((firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] _) >>= (fun m =>
                 openLayZero X fvs kCol m) = .ok t := h
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
  exact ⟨s₁, _, h1, h2⟩

/-- **It is a sending.** -/
theorem isSend_openingZero (q : Params.First) (gp : GPar) (nm : String) (X : LayPar)
    (fvs : List Bool) (kCol : Nat) :
    IsSend (firstPar q gp) (fun s : S => s.st) (openingZero q gp nm X fvs kCol : Block S Cl) :=
  isSend_andThen _ _ _ _ _ (isSend_firstAtS q gp) rfl fun s s' _ _ h => by
    have e : s'.st = s.st := (openedZeroGives X fvs kCol s s' h).2.2.1.2.2.1
    show SameMsgs s.st s'.st
    rw [e]
    exact ⟨rfl, fun _ => rfl⟩

/-- What the opening's decision lays "at the start". -/
theorem firstOwn_atStart (P : Par) (owed : Option Nat) (c c' : ChainCheck) (d d' : DState Unit)
    (r₁ r₂ : Fmt.RoundView) (h : firstOwn P owed c d [r₁, r₂] = .ok (c', d')) :
    c'.frame.atStart = c.frame.atStart ++
      ((Array.range P.sent.size).map (· + d.st.oracles.size)).extract
        ((c.frame.atMoment 0).length + 1) P.sent.size := by
  unfold firstOwn at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨g, d₁⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨ids, d₂⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨f₂, d₃⟩, h3, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, hids, _⟩ := (decideSend_iff P owed d₁ d₂ r₁ r₂ ids).1 h2
  have hn := (newGroupP_book _ _ _ _ _ ((named_ok _ _ _).1 h1)).2
  have hj := (named_ok _ _ _).1 h3
  unfold joinOwnP at hj
  split at hj
  · obtain ⟨d₄, _, e⟩ := Option.map_eq_some_iff.1 hj
    have ef := (Prod.mk.inj e).1
    have ec := (Prod.mk.inj (Except.ok.inj h)).1
    rw [← ec, ← ef, hids, hn]
    simp
  · cases hj

/-- The same of the block at the record. -/
theorem firstAtS_atStart (q : Params.First) (gp : GPar) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    s'.check.frame.atStart = s.check.frame.atStart ++
      ((Array.range (firstPar q gp).sent.size).map (· + s.st.oracles.size)).extract
        ((s.check.frame.atMoment 0).length + 1) (firstPar q gp).sent.size := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  exact firstOwn_atStart _ _ _ c _ d' r₁ r₂ h2

/-- **What a yes of the joined block does to the record.** -/
theorem openingZero_rec {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : Nat} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t) :
    standOf t = Stand.link ModelPart.layers ∧ (∃ L, t.link? = some L ∧ L.link = 0) ∧
      t.failed = s.failed ∧ t.rowsOwed = none ∧
      Booked (firstPar q gp) s.book s.st.oracles.size t.book t.st.oracles.size ∧
      t.out = { s.out with indexMasks := t.out.indexMasks } ∧
      (t.st.oracles[t.out.indexMasks]?).isSome = true := by
  obtain ⟨s₁, g₁, h1, h2⟩ := openingZero_mid h
  obtain ⟨a1, a2, ⟨_, _, e3, e4, _, e6, e7, _⟩, ⟨im, hi, ho⟩, _⟩ :=
    openedZeroGives X fvs kCol s₁ t h2
  obtain ⟨b1, b2⟩ := firstAtS_left q gp s s₁ _ g₁ h1
  have hb := firstAtS_booked q gp s s₁ r₁ r₂ g₁ h1
  have hw : s₁.rowsOwed = none := by
    unfold firstSegmentOpening at h1
    dsimp only at h1
    obtain ⟨_, _, h1⟩ := (bind_ok _ _ _).1 h1
    obtain ⟨⟨c, d'⟩, _, h1⟩ := (bind_ok _ _ _).1 h1
    obtain rfl := Except.ok.inj h1
    rfl
  obtain ⟨_, _, x, l, hx, _⟩ := hi
  refine ⟨a1, a2, e7.trans b1, e6.trans hw, by rw [e3, e4]; exact hb, ?_, ?_⟩
  · rw [ho, b2]
  · rw [ho, e3]
    show (s₁.st.oracles[im]?).isSome = true
    rw [hx]
    rfl

/-- **Which number**: where nothing was laid "at the start" in front: the last message's. -/
theorem openingZero_index {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : Nat} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (h0 : s.check.frame.atStart = #[]) :
    t.out.indexMasks + 1 = s.st.oracles.size + (firstPar q gp).sent.size := by
  obtain ⟨s₁, g₁, h1, h2⟩ := openingZero_mid h
  obtain ⟨_, _, _, ⟨im, ⟨hs, hg, _⟩, ho⟩, _⟩ := openedZeroGives X fvs kCol s₁ t h2
  have ha := firstAtS_atStart q gp s s₁ r₁ r₂ g₁ h1
  rw [h0, Array.empty_append] at ha
  rw [ha] at hs hg
  rw [ho]
  show im + 1 = _
  simp only [Array.size_extract, Array.size_map, Array.size_range, Nat.min_self] at hs
  rw [Array.getElem?_extract] at hg
  simp only [Array.size_map, Array.size_range, Nat.min_self, hs, Nat.lt_one_iff, if_true,
    Nat.add_zero, Array.getElem?_map, Array.getElem?_range] at hg
  split at hg
  · have e : (s.check.frame.atMoment 0).length + 1 + s.st.oracles.size = im :=
      Option.some.inj hg
    omega
  · cases hg

theorem firstAtS_retype (q : Params.First) (gp : GPar) :
    ((firstSegmentOpening (Cl := Unit) q gp).retype : Block S Cl).UnderR (firstSegmentOpening q gp) :=
  ⟨rfl, fun _ _ _ _ h => h⟩

end VerifiableInference.Desc.K1
