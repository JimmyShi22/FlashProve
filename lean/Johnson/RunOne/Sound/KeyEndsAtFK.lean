-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Sound/KeyEndsAtFK.lean: It stands on Johnson/Desc/Key/Desc.lean.
THE THREE CHAINS' LAST SEATS AT THE KEY FILE'S OWN DESCRIPTION.

What is said.
  `flat_last`: a chain's flat list ends in the last block of its `back`.
  `asks₁`, `asks₂`, `asks₃`: the three chains' own clauses at their ends, as the description's text
    has them.
  `fk_last₁`, `fk_last₂`, `fk_last₃`: AT `FK X N P` each chain's flat list has a last block, and
    it hands the record on just where these clauses hold. `fk_sealLast`: the first chain's last
    block has a round.
  `fk_end₁`, `fk_end₂`, `fk_end₃`: SO THE LAST SEAT OF EACH CHAIN IS FILLED (`seat_of_end`,
    Johnson/Desc/Sound/KeySeatsAt.lean), at whatever pieces hold the description's own blocks,
    between the row in front of it and the same row with the clauses passed.

Limits. What each still asks: that the row behind is the row in front with the clauses passed;
that it reads no tree from the piece's place on; that the piece's errors are shares of at most εs;
that no two trees of the frame's list have one number.
Terms: lean/GLOSSARY.md.

-/
import Johnson.RunOne.Sound.KeyAtFK
import Johnson.Desc.Sound.KeySeatsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Sound
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.ChainEnd
open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.Key (descriptionFromSource Source FirstState firstChain)
open _root_.Run (ckP)
open _root_.Iop (Err)

/-- A chain's flat list ends in its last block. -/
theorem flat_last {S Cl : Type} (c : Chain S Cl) :
    c.blocksInOrder.getLast? = some { c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter } := by
  unfold Chain.blocksInOrder
  exact List.getLast?_concat

variable (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)

/-- The first chain's own clauses at its end. -/
def asks₁ (s : Key.FirstState) : Clauses :=
  [("end: no count of rows is owed", s.noneWaits)] ++
    Key.untestedButOwn s

theorem fk_last₁ : ∃ e, (FK X N P).first.blocksInOrder.getLast? = some e ∧
    ∀ s rs gs s', e.decide s rs gs = .ok s' → (∀ c ∈ asks₁ s, c.2 = true) ∧ s' = s := by
  obtain ⟨inF, hb⟩ : ∃ inF, (FK X N P).first.last = Key.firstChainEnd Key.pieces inF := ⟨_, rfl⟩
  refine ⟨_, flat_last _, fun s rs gs s' h => ?_⟩
  have h' : (FK X N P).first.last.decide s rs gs = .ok s' := h
  rw [hb] at h'
  exact ((chainEnd_decide_iff (Cl := Key.Claim) 1 Key.pieces.sealAt true inF (asks₁) s s' rs
    gs).1 h').symm

/-- **The first chain's last block has a round** (the sealing round): one of the two facts on values
that the maker of the pieces asks. -/
theorem fk_sealLast : (FK X N P).sealLast = true := by
  obtain ⟨inF, hb⟩ : ∃ inF, (FK X N P).first.last = Key.firstChainEnd Key.pieces inF := ⟨_, rfl⟩
  unfold FileDescription.sealLast
  rw [hb]
  rfl

/-- The shared chain's. -/
def asks₂ (s : _root_.Desc.K14.St) : Clauses := ChainEnd.untestedL s.st

theorem fk_last₂ :
    ∃ e, (FK X N P).shared.blocksInOrder.getLast? = some e ∧
    ∀ s rs gs s', e.decide s rs gs = .ok s' → (∀ c ∈ asks₂ s, c.2 = true) ∧ s' = s := by
  obtain ⟨inF, hb⟩ : ∃ inF, (FK X N P).shared.last =
      (VerifiableInference.Desc.K12.Seat.last inF).retype := ⟨_, rfl⟩
  refine ⟨_, flat_last _, fun s rs gs s' h => ?_⟩
  have h' : (FK X N P).shared.last.decide s rs gs = .ok s' := h
  rw [hb] at h'
  exact ((chainEnd_decide_iff (Cl := Unit) 2 11 true (inF.flatMap (·.rounds)) asks₂ s s' rs
    gs).1 h').symm

/-- The last chain's. -/
def asks₃ (s : VerifiableInference.Desc.Third.S₃) : Clauses := ChainEnd.untestedL s.st

theorem fk_last₃ :
    ∃ e, (FK X N P).second.blocksInOrder.getLast? = some e ∧
    ∀ s rs gs s', e.decide s rs gs = .ok s' → (∀ c ∈ asks₃ s, c.2 = true) ∧ s' = s := by
  obtain ⟨inF, hb⟩ : ∃ inF, (FK X N P).second.last =
      (VerifiableInference.Desc.Third.end₃ (Cl := Unit) inF).retype := ⟨_, rfl⟩
  refine ⟨_, flat_last _, fun s rs gs s' h => ?_⟩
  have h' : (FK X N P).second.last.decide s rs gs = .ok s' := h
  rw [hb] at h'
  exact ((chainEnd_decide_iff (Cl := Unit) 3 3 false (inF.flatMap (·.rounds)) asks₃ s s' rs
    gs).1 h').symm

/-- What is handed to each chain. -/
abbrev H₁ : Type := (FK X N P).XiPub
abbrev H₂ : Type := (FK X N P).XiPub × (FK X N P).S₁
abbrev H₃ : Type := (FK X N P).XiPub × (FK X N P).S₁ × (FK X N P).S₂

/-- **The first chain's last seat is filled.** -/
theorem fk_end₁ {F : Frame} {W : Type} (εs : ℝ≥0∞)
    (A : JointRow (H₁ X N P × (FK X N P).S₁) F)
    (p₀ : Piece (ckP .two) F (H₁ X N P × (FK X N P).S₁) (FK X N P).Cl W)
    (l : List (Piece (ckP .two) F (H₁ X N P × (FK X N P).S₁) (FK X N P).Cl W))
    (rs : List (JointRow (H₁ X N P × (FK X N P).S₁) F))
    (hbs : (p₀ :: l).map (·.b) =
      ((FK X N P).first.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hrow : keyRowAt A rs (l.length + 1) = (keyRowAt A rs l.length).passed fun t => asks₁ t.2)
    (hnd : (F.all.map (·.no)).Nodup)
    (hp : ∀ p, (p₀ :: l)[l.length]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).rel) :
    SeatGood εs A (p₀ :: l) rs l.length := by
  obtain ⟨e, he, hd⟩ := fk_last₁ X N P
  exact seat_of_end εs A p₀ l rs _ hbs e he (asks₁) hd hrow hnd hp

/-- **The shared chain's last seat is filled.** -/
theorem fk_end₂ {F : Frame} {W : Type} (εs : ℝ≥0∞)
    (A : JointRow (H₂ X N P × (FK X N P).S₂) F)
    (p₀ : Piece (ckP .two) F (H₂ X N P × (FK X N P).S₂) (FK X N P).Cl W)
    (l : List (Piece (ckP .two) F (H₂ X N P × (FK X N P).S₂) (FK X N P).Cl W))
    (rs : List (JointRow (H₂ X N P × (FK X N P).S₂) F))
    (hbs : (p₀ :: l).map (·.b) =
      ((FK X N P).shared.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hrow : keyRowAt A rs (l.length + 1) = (keyRowAt A rs l.length).passed fun t => asks₂ t.2)
    (hnd : (F.all.map (·.no)).Nodup)
    (hp : ∀ p, (p₀ :: l)[l.length]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).rel) :
    SeatGood εs A (p₀ :: l) rs l.length := by
  obtain ⟨e, he, hd⟩ := fk_last₂ X N P
  exact seat_of_end εs A p₀ l rs _ hbs e he (asks₂) hd hrow hnd hp

/-- **The last chain's last seat is filled.** -/
theorem fk_end₃ {F : Frame} {W : Type} (εs : ℝ≥0∞)
    (A : JointRow (H₃ X N P × (FK X N P).S₃) F)
    (p₀ : Piece (ckP .two) F (H₃ X N P × (FK X N P).S₃) (FK X N P).Cl W)
    (l : List (Piece (ckP .two) F (H₃ X N P × (FK X N P).S₃) (FK X N P).Cl W))
    (rs : List (JointRow (H₃ X N P × (FK X N P).S₃) F))
    (hbs : (p₀ :: l).map (·.b) =
      ((FK X N P).second.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hrow : keyRowAt A rs (l.length + 1) = (keyRowAt A rs l.length).passed fun t => asks₃ t.2)
    (hnd : (F.all.map (·.no)).Nodup)
    (hp : ∀ p, (p₀ :: l)[l.length]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (l.length + 1)).rel) :
    SeatGood εs A (p₀ :: l) rs l.length := by
  obtain ⟨e, he, hd⟩ := fk_last₃ X N P
  exact seat_of_end εs A p₀ l rs _ hbs e he (asks₃) hd hrow hnd hp

end Johnson.RunOne.Sound

#print axioms Johnson.RunOne.Sound.fk_end₁
#print axioms Johnson.RunOne.Sound.fk_end₂
#print axioms Johnson.RunOne.Sound.fk_end₃
#print axioms Johnson.RunOne.Sound.fk_sealLast
#print axioms Johnson.RunOne.Sound.fk_last₁
#print axioms Johnson.RunOne.Sound.fk_last₂
#print axioms Johnson.RunOne.Sound.fk_last₃
#print axioms Johnson.RunOne.Sound.flat_last
