-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05T2Piece.lean: KIND K5 AT THE TABLE OF JOINTS: `k5_t2`
(Johnson/Desc/First/Att/K05T2.lean) JOINED TO THE KIND's PIECE of the rule of composition: the
second implication of the table's door ("t2"), and the door's two facts on the block's text, AT
EVERY PIECE WHOSE BLOCK DECIDES AS THE KIND's DOES.

Main names:
  `piece_yes_lay`: where such a piece puts out b at (a, τ): an attention segment att is open in a.1;
    the hearing returned from att.F; b.1 is the record behind the lay; the oracles are the same
    below the piece's base. (piece_out_step, piece_same_below:
    Johnson/Desc/First/Att/K05SeamOut.lean; step_fit: Johnson/Desc/StepKeeps.lean; decide_lays:
    Johnson/Desc/First/Att/K5Shape.lean; lay_is: Johnson/Desc/First/Att/K05BehindLay.lean.)
  `k5_mark_stays`: THE DOOR's FIRST FACT: a mark in front is a mark behind. (In truth the lay
    refuses a marked record: the statement holds for nothing there.)
  `k5_unmarked_stays`: and no mark in front, none behind.
  `k5_decodes_rides`: THE DOOR's SECOND FACT, from K5Fill.decodes.
  `k5_t2_piece`: **t2**: onAt in front · no mark · the piece's yes ⟹ onAt behind.
  `decides_k5`, `decides_k5_ok`: the blocks attentionKind seatSO claims p and { … with planOk := ok } decide
    so.
Premises of k5_t2_piece: those of k5_t2, the three that speak of a record (keptForms, madeForms,
madeMore) now asked at every record with the promise in front and every return of the hearing.
Limits: as at Johnson/Desc/First/Att/K05T2.lean: A RULE OVER LETTERS. The piece stands over the
carried record alone (get s := (π, s)): no guard, no lift. Stated at onAt, not at onQ: openSets_succ
| pubSets_succ (Johnson/Desc/First/BordersSucc.lean) carry it there.
No soundness of the protocol is claimed. Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05T2
import Johnson.Desc.First.Att.K05Piece
import Johnson.Desc.StepKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.First (Item Pub Meaning Numbers ModelPart onAt stepOpen pubStep rowOf pubRowOf
  pubRowM moreItem tiesOf)
open VerifiableInference.Desc.Sound (Frame Piece strsOf)
open _root_.Run (ckP)

section
variable {Cl W : Type} {Fr : Frame}

/-- The piece's block decides as the kind's does, and no round is put behind its stretch. -/
structure DecidesK5 (Pc : Piece (ckP .two) Fr First.S Cl W) (p : Par) : Prop where
  back : Pc.back = []
  decide : ∀ s rs gs, Pc.b.decide s rs gs = P.decide seatSO p s rs

/-- **What a yes of such a piece is.** -/
theorem piece_yes_lay (Pc : Piece (ckP .two) Fr First.S Cl W) (p : Par) (D : DecidesK5 Pc p)
    (a b : First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) Pc.ds)) (h : Pc.ior.red.out a τ = some b) :
    ∃ (att : First.AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView), a.1.here = .att att ∧
      hear p.own (att.F, rs, 0) = some (hd, G, [], 0) ∧ b.1 = behind a.1 att hd G ∧
      SameBelow Fr Pc.base a.2 b.2 := by
  obtain ⟨_, ⟨cols, k, hs⟩, _⟩ := piece_out_step Pc D.back a b τ h
  obtain ⟨_, gs, hdc⟩ := VerifiableInference.Desc.Keeps.step_fit _ _ _ _ _ _ _ hs
  rw [D.decide] at hdc
  obtain ⟨_, F0, hd, G, hl, hr, hy⟩ := (decide_lays seatSO p a.1 b.1 _).1 hdc
  obtain ⟨att, e, rfl, eb⟩ := lay_is hl hy
  exact ⟨att, hd, G, _, e, hr, eb, piece_same_below Pc a b τ h⟩

theorem k5_mark_stays (Pc : Piece (ckP .two) Fr First.S Cl W) (p : Par) (D : DecidesK5 Pc p)
    (a b : First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) Pc.ds)) (h : Pc.ior.red.out a τ = some b)
    (hm : a.1.failed ≠ none) : b.1.failed ≠ none := by
  obtain ⟨att, hd, G, rs, _, _, eb, _⟩ := piece_yes_lay Pc p D a b τ h
  rw [eb]
  exact hm

theorem k5_unmarked_stays (Pc : Piece (ckP .two) Fr First.S Cl W) (p : Par) (D : DecidesK5 Pc p)
    (a b : First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) Pc.ds)) (h : Pc.ior.red.out a τ = some b)
    (hm : a.1.failed = none) : b.1.failed = none := by
  obtain ⟨att, hd, G, rs, _, _, eb, _⟩ := piece_yes_lay Pc p D a b τ h
  rw [eb]
  exact hm

variable {Pp Wt : Type} (N : Numbers) (Mg : Meaning Pp Wt) (links : List ModelPart) (π : Pp)

theorem k5_decodes_rides (Pc : Piece (ckP .two) Fr First.S Cl W) (p : Par) (D : DecidesK5 Pc p)
    {m : ℕ} {O : List Item} {Q : List Pub} {pC pD : Look.P} {arr : Array (ℕ × String)}
    {first nsPlan : ℕ} (Fi : K5Fill Mg N π Fr Pc.base m O Q p.own pC pD arr first nsPlan)
    (a b : First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) Pc.ds)) (h : Pc.ior.red.out a τ = some b)
    (hd : Mg.decodes (π, a.1) (strsOf Fr a.2)) : Mg.decodes (π, b.1) (strsOf Fr b.2) := by
  obtain ⟨att, hh, G, rs, e, hr, eb, hy⟩ := piece_yes_lay Pc p D a b τ h
  rw [eb]
  exact Fi.decodes _ _ _ _ _ _ _ e hr hy hd

/-- **t2 AT THE KIND's PIECE.** -/
theorem k5_t2_piece (Pc : Piece (ckP .two) Fr First.S Cl W) (p : Par) (D : DecidesK5 Pc p)
    (m : ℕ) (pl pl' : Place) (O : List Item) (Q : List Pub) (pC pD : Look.P) (hS : Forest.Shape)
    (arr : Array (ℕ × String)) (first kr nsPlan : ℕ) (Ix : K5Place links m pl pl')
    (Bk : K5Book N pl pl') (Pn : K5Plan p.own m pC pD hS first kr nsPlan)
    (Fi : K5Fill Mg N π Fr Pc.base m O Q p.own pC pD arr first nsPlan)
    (hQ : ∀ q ∈ (pubRowOf links pl).asks, q ∈ Q)
    (keptForms : ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear p.own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ i ∈ O, (rowOf links pl).ins.contains i = false → i ≠ .pinI → ∀ q ∈ tiesOf i,
        Mg.pub q (π, s) = true → Mg.pub q (π, behind s att hd G) = true)
    (madeForms : ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear p.own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ q ∈ [Pub.formsInT m 3 "own", Pub.formsInT m 2 "planes", Pub.formsInT m 2 "join"],
        Mg.pub q (π, behind s att hd G) = true)
    (madeMore : ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear p.own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ x ∈ (Mg.more.rows links pl).makes, Mg.pub (moreItem x) (π, behind s att hd G) = true ∧
        Mg.pubP (moreItem x) (π, behind s att hd G))
    (a b : First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) Pc.ds))
    (hon : onAt N Mg links (some pl) O Q (π, a.1) (strsOf Fr a.2)) (hu : a.1.failed = none)
    (h : Pc.ior.red.out a τ = some b) :
    onAt N Mg links (some pl') (stepOpen O (rowOf links pl)) (pubStep Q (pubRowM Mg.more links pl))
      (π, b.1) (strsOf Fr b.2) := by
  obtain ⟨att, hd, G, rs, e, hr, eb, hy⟩ := piece_yes_lay Pc p D a b τ h
  rw [eb]
  exact k5_t2 N Mg links π m Pc.base pl pl' O Q p.own pC pD hS arr first kr nsPlan Ix Bk Pn Fi hQ e hr hy hu
    hon (keptForms _ _ _ _ _ _ hon hu e hr) (madeForms _ _ _ _ _ _ hon hu e hr)
    (madeMore _ _ _ _ _ _ hon hu e hr)

end

/-- The kind's own block decides so. -/
theorem decides_k5 {Cl W : Type} {Fr : Frame}
    (claims : List (String × (Nat → First.S → Except String (List Cl × First.S)))) (p : Par)
    (base : ℕ) (ds : List RDT) (err : Err (uLT (ckP .two) ds)) :
    DecidesK5 (k5Piece (W := W) (ckP .two) Fr seatSO claims p base ds err) p :=
  ⟨rfl, fun _ _ _ => rfl⟩

/-- And so does it with any test on the plan: the law's own piece
(Johnson/Desc/First/Att/K05LawOne.lean). -/
theorem decides_k5_ok {Cl W : Type} {Fr : Frame} (ok : Bool)
    (claims : List (String × (Nat → First.S → Except String (List Cl × First.S)))) (p : Par)
    (base : ℕ) (ds : List RDT) (err : Err (uLT (ckP .two) ds)) :
    DecidesK5 (⟨{ attentionKind seatSO claims p with planOk := ok }, base, ds, [], fun _ _ w => w, err⟩ :
      Piece (ckP .two) Fr First.S Cl W) p :=
  ⟨rfl, fun _ _ _ => rfl⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.piece_yes_lay
#print axioms VerifiableInference.Desc.First.Att.P.k5_mark_stays
#print axioms VerifiableInference.Desc.First.Att.P.k5_decodes_rides
#print axioms VerifiableInference.Desc.First.Att.P.k5_t2_piece
#print axioms VerifiableInference.Desc.First.Att.P.decides_k5
#print axioms VerifiableInference.Desc.First.Att.P.decides_k5_ok
