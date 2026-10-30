-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3RoundsLaw.lean: THE LOT OF THE KIND "LOOKUP" (K3Lot.lot): WHAT A BLOCK's
DECLARED ROUNDS READ. No kernel fact. Joinings over the first row's files (K3Skel.lean,
K3Strip.lean, K3Row.lean).
  `rounds_ownOf`: the kind's own sub-protocol has the parameters' rounds (`P.rounds`,
    Johnson/Desc/First/Look/LookKind.lean).
  `rounds_theStated`: so has what `theStated` makes at a lookup's address: the quiet block behind it
    has no round; the caller's run adds claims alone.
  `rounds_core`: `P.rounds` reads four fields: set, calls, lid, pub.
  `rounds_at`: **under the first row's hypotheses (`Reads Z`, K3Row.lean) the rounds at link i are
    those of the written parameters `coreW (sortOf i) d`.**
  `block_at`: every block of the lot stands at a lookup's address, with these rounds.
Limits. What the written parameters' rounds are is not said here. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.K3 (theStated theWhole theOwn pieceAt quietAt withCaller)
open VerifiableInference.Desc.First.Look (P lookAt placeAt beforeAt laidAt padKeyAt)
open Johnson.AtFull.ProofRows.K3 (strip)
open ProofFile.Sk (skel)

theorem rounds_ownOf {Cl : Type} (claim : Aff → Cl) (piece : Nat) (d : Bool) (p : P)
    (sent : List (Nat × Nat)) (laid : Array Nat) (key : Bool) :
    (ownOf claim piece d p sent laid key).rounds = p.rounds := rfl

/-- **THE ROUNDS OF WHAT `theStated` MAKES AT A LOOKUP's ADDRESS.** -/
theorem rounds_theStated {Cl : Type} (claim : Aff → Cl)
    (readers : Nat → Option (K3.Readers First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (i : Nat) (d : Bool) {b : Block First.S Cl}
    (h : theStated claim readers X codes shape ⟨1, some i, pieceAt X i d, .K3⟩ = some b) :
    ∃ p, placeAt X i d = some p ∧ b.rounds = p.rounds := by
  unfold theStated theWhole at h
  rw [own_at] at h
  cases hp : placeAt X i d with
  | none => simp [hp] at h
  | some p =>
    refine ⟨p, rfl, ?_⟩
    cases hs : beforeAt codes shape i d with
    | none => simp [hp, hs] at h
    | some sent =>
      cases hl : laidAt X i d with
      | none => simp [hp, hs, hl] at h
      | some laid =>
        cases hk : padKeyAt X i d with
        | none => simp [hp, hs, hl, hk] at h
        | some key =>
          simp only [hp, hs, hl, hk, Option.bind_some, Option.map_some, piece_beq, piece_bne] at h
          cases hq : quietAt X i d <;> cases hr : readers i <;> cases d <;>
            simp [hq, hr, hp] at h <;> subst h <;>
            simp [Block.andThen, roundlessBlock, withCaller, rounds_ownOf]

/-- `P.rounds` reads four fields. -/
theorem rounds_core (p : P) :
    p.rounds =
      ({ name := "", set := p.set, link := 0, digits := false, calls := p.calls, pub := p.pub
         lid := p.lid, first := 0, ns := 0, lm := 0 } : P).rounds := rfl

/-- **UNDER THE FIRST ROW's HYPOTHESES: THE WRITTEN PARAMETERS' ROUNDS.** -/
theorem rounds_at {Z : ProofFile.Pub} (R : Reads Z) {i : Nat} (hi : i < 25) (d : Bool) {p : P}
    (hp : placeAt Z.p.X i d = some p) : p.rounds = (coreW (sortOf i) d).rounds := by
  cases d with
  | false =>
    obtain ⟨x, hx, hv, hOk⟩ := R.calls i hi
    obtain ⟨-, -, e3, e4, e5, -, -, -⟩ :
        x.name = nameW i false ∧ x.link = i ∧ x.calls.map strip = callsW (sortOf i) false ∧
        x.pub = pubW (sortOf i) false ∧ x.lid = 28 ∧ x.F.next = firstW (sortOf i) false ∧
        x.ns = nsW (sortOf i) ∧ x.lm = lmW (sortOf i) false := by
      simpa [viewOf, viewW, Prod.mk.injEq] using hv
    obtain rfl : P.ofPlace (Params.settingOf Z.p.X.P.frame) false x = p := by
      unfold placeAt at hp
      rw [hx] at hp
      exact Option.some.inj hp
    rw [← rounds_strip (p := P.ofPlace (Params.settingOf Z.p.X.P.frame) false x) hOk, rounds_core,
      rounds_core (coreW (sortOf i) false)]
    show (⟨"", Params.settingOf Z.p.X.P.frame, 0, false, x.calls.map strip, x.pub, x.lid, 0, 0,
      0⟩ : P).rounds = _
    rw [R.setting, e3, e4, e5]
    rfl
  | true =>
    obtain ⟨x, hx, hv⟩ := R.digits i hi
    obtain ⟨-, -, e3, e4, e5, -, -, -⟩ :
        x.name = nameW i true ∧ x.link = i ∧ x.calls = callsW (sortOf i) true ∧
        x.pub = pubW (sortOf i) true ∧ x.lid = 28 ∧ x.F.next = firstW (sortOf i) true ∧
        x.ns = nsW (sortOf i) ∧ x.lm = lmW (sortOf i) true := by
      simpa [viewOf, viewW, Prod.mk.injEq] using hv
    obtain rfl : P.ofPlace (Params.settingOf Z.p.X.P.frame) true x = p := by
      unfold placeAt at hp
      rw [hx] at hp
      exact Option.some.inj hp
    rw [rounds_core, rounds_core (coreW (sortOf i) true)]
    show (⟨"", Params.settingOf Z.p.X.P.frame, 0, false, x.calls, x.pub, x.lid, 0, 0, 0⟩ :
      P).rounds = _
    rw [R.setting, e3, e4, e5]
    rfl

theorem rowW_place (i : Nat) (d : Bool) : (rowW i d).place = ⟨1, some i, pieceW i d, .K3⟩ := by
  unfold rowW dress
  dsimp only
  cases quietW i d <;> cases (!d && callerW i) <;> rfl

/-- **EVERY BLOCK OF THE LOT: ITS ADDRESS AND ITS ROUNDS.** -/
theorem block_at {Z : ProofFile.Pub} (R : Reads Z) (G : ProofFile.Ground) {b : Block First.S ProofFile.Cl}
    (hb : b ∈ (K3Lot.lot Z).blocks G) :
    ∃ i < 25, ∃ d, b.place = ⟨1, some i, pieceW i d, .K3⟩ ∧
      b.rounds = (coreW (sortOf i) d).rounds := by
  have hb' : b ∈ K3Lot.hear Z := hb
  unfold K3Lot.hear at hb'
  obtain ⟨x, hx, hs⟩ := List.mem_filterMap.1 hb'
  unfold K3Lot.addresses at hx
  obtain ⟨i, hi, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hx
  have hi' : i < 25 := by
    have := List.mem_range.1 hi
    rwa [R.links] at this
  obtain ⟨p, hp, hr⟩ := rounds_theStated K3Lot.ofForm (K3Lot.readersAt Z.p.X) Z.p.X
    Z.first.codes Z.first.shape i d hs
  have hk := skel_theStated K3Lot.ofForm (K3Lot.readersAt Z.p.X) Z.p.X Z.first.codes
    Z.first.shape i d
  rw [hs, sk_at R hi' d] at hk
  have hpl : (skel b).place = (rowW i d).place := congrArg (·.place) (Option.some.inj hk)
  exact ⟨i, hi', d, hpl.trans (rowW_place i d), hr.trans (rounds_at R hi' d hp)⟩

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.rounds_ownOf
#print axioms Johnson.AtFull.Lots.K3.rounds_theStated
#print axioms Johnson.AtFull.Lots.K3.rounds_core
#print axioms Johnson.AtFull.Lots.K3.rounds_at
#print axioms Johnson.AtFull.Lots.K3.rowW_place
#print axioms Johnson.AtFull.Lots.K3.block_at
