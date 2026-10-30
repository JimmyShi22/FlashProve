-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Foes2.lean: TESTS THAT CAN FAIL, for two premises of the statement of index privacy
(Johnson/WholeKey/Statement.lean): the simulators are good for the honest sides (Sims.Good) and the
stops that hang on the private input are rare (StopsSmall), both of Johnson/WholeKey/Premises.lean.

General theorems with their proofs, and instances at two small objects. This file states no goal of
the release. The numbers (7), (8) go on from the tests (1) to (6) of Johnson/WholeKey/Foes.lean.

Why. The error zetaW (Johnson/WholeKey/Zeta.lean) has a summand for the simulators' errors (zT, zL,
zO) and one for the stops (hT, hL, hO). These letters are bounded from below by nothing in the
statement itself. Here: honest sides that leak FORCE them to be large, so the statement says nothing
of such honest sides, as it ought.
  (7) AN HONEST SIDE THAT TELLS. Two indices of ok, at randomness at which their out-of-domain (OOD)
      samples and their encoded indices are the same, so that a simulator is handed the same at
      both; the honest outputs differ at every value of the verifier's randomness. Then 1 ≤ (z + h)
      + (z + h), whatever the simulators are: good_forces_T for the first table's protocol,
      good_forces_B for a session.
  (8) AN HONEST SIDE THAT STOPS AT ONE INDEX. If at an index of ok every value of the verifier's
      randomness is a stop that hangs on the private input, then 1 ≤ h: stops_forces_T, _Lk, _B.
      (There Sims.Good holds idly at that index, since it is asked outside these stops: without the
      summand for the stops the error would miss the leak.)
  At the object pad (Hiop/Seeded/Pad.lean) and the wires of Johnson/WholeKey/Member.lean, for the
  first table's protocol: tell_forces (the honest side sends the index in a plain part) and
  stop_forces (it stops just when the index is 1).
That both do leak, at the level of the game: tell_not_hides, stop_not_hides (Hiop/Seeded/Pad.lean).

  At the object pad2 (Hiop/Seeded/Pad2.lean) and the wires of Johnson/WholeKey/Member2.lean, FOR A
  SESSION: tell_forces_B (the session's honest side sends the index in the plain part of its first
  round: 1 ≤ (zO + hO) + (zO + hO)) and stop_forces_B (it stops just when the index is 1: 1 ≤ hO).
  And stops_all_forces: THE GUARD ok IS NEEDED at that member: its own honest sides stop at the
  index out of range, so a range that holds that index forces 1 ≤ hT, 1 ≤ hL, 1 ≤ hO.

Limits. (7) asks that the honest outputs differ at EVERY value of the verifier's randomness: an
honest side that tells at some values alone is not covered. These are tests of two premises; none
names PremW or zetaW, and they do not touch the summands of zetaW for an overrun, for the seeds and
for the hashes, nor the budgets.
The SCHEME with an honest side that leaks: Johnson/WholeKey/FoeScheme.lean.
Tests that hold PremW and zetaW: Johnson/WholeKey/FoeZeta.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Member2

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The count -/

/-- If every point lies in A or in A', and each of the two is small outside a small set, then the
four numbers add up to at least 1. -/
theorem one_le_of_cover {Ω : Type} (p : PMF Ω) (A A' H H' : Set Ω) (hc : ∀ ω, ω ∈ A ∨ ω ∈ A')
    {z h : ℝ≥0∞} (h1 : pr p {ω | ω ∉ H ∧ ω ∈ A} ≤ z) (h2 : pr p H ≤ h)
    (h1' : pr p {ω | ω ∉ H' ∧ ω ∈ A'} ≤ z) (h2' : pr p H' ≤ h) : 1 ≤ (z + h) + (z + h) := by
  classical
  have e : pr p Set.univ ≤
      pr p ({ω | ω ∉ H ∧ ω ∈ A} ∪ H) + pr p ({ω | ω ∉ H' ∧ ω ∈ A'} ∪ H') :=
    pr_le_add p fun ω _ => by
      rcases hc ω with ha | ha
      · by_cases hh : ω ∈ H
        · exact Or.inl (Or.inr hh)
        · exact Or.inl (Or.inl ⟨hh, ha⟩)
      · by_cases hh : ω ∈ H'
        · exact Or.inr (Or.inr hh)
        · exact Or.inr (Or.inl ⟨hh, ha⟩)
  rw [pr_univ] at e
  exact e.trans (add_le_add ((pr_union_le p _ _).trans (add_le_add h1 h2))
    ((pr_union_le p _ _).trans (add_le_add h1' h2')))

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {Sm : Sims L} {Hs : ThreeProvers L} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}
  {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {zT zL zO hT hL hO : ℝ≥0∞}

/-! ## (7) An honest side that tells -/

/-- The first table's protocol. -/
theorem good_forces_T (hG : Sm.Good Hs W ok Gs Ryes zT zL zO)
    (hS : StopsSmall Hs W ok Gs Ryes hT hL hO) {i i' : I} {r r' : L.EncodingRandomness} {e : L.OutOfDomainSeed} (hi : ok i)
    (hi' : ok i') (he : Gs e) (hrec : L.recOf i' r' e = L.recOf i r e)
    (henc : L.encodeIndex i' r' = L.encodeIndex i r)
    (hne : ∀ ρ, Hs.T.output (i, r, e) (L.recOf i r e) ρ ≠
      Hs.T.output (i', r', e) (L.recOf i r e) ρ) : 1 ≤ (zT + hT) + (zT + hT) := by
  have g := hG.T i r e hi he
  have s := hS.T i r e hi he
  have g' := hG.T i' r' e hi' he
  have s' := hS.T i' r' e hi' he
  rw [hrec, henc] at g'
  rw [hrec] at s'
  refine one_le_of_cover _
    {ρ | Hs.T.output (i, r, e) (L.recOf i r e) (RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ) ≠
      Sm.T (L.recOf i r e) (RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ)
        (L.offline.extAns (L.recOf i r e) (RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ) (L.encodeIndex i r))}
    {ρ | Hs.T.output (i', r', e) (L.recOf i r e) (RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ) ≠
      Sm.T (L.recOf i r e) (RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ)
        (L.offline.extAns (L.recOf i r e) (RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ) (L.encodeIndex i r))}
    _ _ (fun ρ => ?_) g s g' s'
  by_contra hc
  rw [not_or] at hc
  exact hne _ ((not_not.1 hc.1).trans (not_not.1 hc.2).symm)

/-- A session, on the copy with the number n. -/
theorem good_forces_B (hG : Sm.Good Hs W ok Gs Ryes zT zL zO)
    (hS : StopsSmall Hs W ok Gs Ryes hT hL hO) (n : ℕ) {i i' : I} {r r' : L.EncodingRandomness} {e : L.OutOfDomainSeed}
    {x : X} (hi : ok i) (hi' : ok i') (he : Gs e) (hx : Ryes i x) (hx' : Ryes i' x)
    (hrec : L.recOf i' r' e = L.recOf i r e) (henc : L.encodeIndex i' r' = L.encodeIndex i r)
    (hne : ∀ ρ, (sessionAt Hs n).output (i, r, e) (x, L.recOf i r e) ρ ≠
      (sessionAt Hs n).output (i', r', e) (x, L.recOf i r e) ρ) : 1 ≤ (zO + hO) + (zO + hO) := by
  have g := hG.B n i r e x hi he hx
  have s := hS.B n i r e x hi he hx
  have g' := hG.B n i' r' e x hi' he hx'
  have s' := hS.B n i' r' e x hi' he hx'
  rw [hrec, henc] at g'
  rw [hrec] at s'
  refine one_le_of_cover _
    {ρ | (sessionAt Hs n).output (i, r, e) (x, L.recOf i r e)
        (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ) ≠
      Sm.B n (x, L.recOf i r e) (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ)
        (L.onlineBatch.loc.extAns (x, L.recOf i r e)
          (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ) (L.encodeIndex i r))}
    {ρ | (sessionAt Hs n).output (i', r', e) (x, L.recOf i r e)
        (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ) ≠
      Sm.B n (x, L.recOf i r e) (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ)
        (L.onlineBatch.loc.extAns (x, L.recOf i r e)
          (RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ) (L.encodeIndex i r))}
    _ _ (fun ρ => ?_) g s g' s'
  by_contra hc
  rw [not_or] at hc
  exact hne _ ((not_not.1 hc.1).trans (not_not.1 hc.2).symm)

/-! ## (8) An honest side that stops at one index -/

theorem stops_forces_T (hS : StopsSmall Hs W ok Gs Ryes hT hL hO) {i : I} {r : L.EncodingRandomness} {e : L.OutOfDomainSeed}
    (hi : ok i) (he : Gs e) (hH : ∀ ρ, ρ ∈ Hs.T.Hid (i, r, e) (L.recOf i r e)) : 1 ≤ hT := by
  have s := hS.T i r e hi he
  rwa [show {ρ | RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ Hs.T.Hid (i, r, e) (L.recOf i r e)} =
    Set.univ from Set.eq_univ_of_forall fun ρ => hH _, pr_univ] at s

theorem stops_forces_Lk (hS : StopsSmall Hs W ok Gs Ryes hT hL hO) {i : I} {r r' : L.EncodingRandomness}
    {e e' : L.OutOfDomainSeed} (hi : ok i) (he : Gs e) (he' : Gs e')
    (hH : ∀ ρ, ρ ∈ Hs.Lk.Hid (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e')) :
    1 ≤ hL := by
  have s := hS.Lk i r e r' e' hi he he'
  rwa [show {ρ | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈
      Hs.Lk.Hid (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e')} =
    Set.univ from Set.eq_univ_of_forall fun ρ => hH _, pr_univ] at s

theorem stops_forces_B (hS : StopsSmall Hs W ok Gs Ryes hT hL hO) (n : ℕ) {i : I} {r : L.EncodingRandomness}
    {e : L.OutOfDomainSeed} {x : X} (hi : ok i) (he : Gs e) (hx : Ryes i x)
    (hH : ∀ ρ, ρ ∈ (sessionAt Hs n).Hid (i, r, e) (x, L.recOf i r e)) : 1 ≤ hO := by
  have s := hS.B n i r e x hi he hx
  rwa [show {ρ | RoundsQueryLayout.zero L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ρ ∈
      (sessionAt Hs n).Hid (i, r, e) (x, L.recOf i r e)} =
    Set.univ from Set.eq_univ_of_forall fun ρ => hH _, pr_univ] at s

/-! ## At the object pad -/

namespace Member
open Hiop.Seeded (pad bitSide bitView bitOf output_bitSide tv_pure_ne)

/-- Honest sides on pad, the first of which sends say w and stops where stop w. -/
def recsBit (say stop : Bool × (Bool × Bool) × Bool → Bool) : ThreeProvers pad :=
  ⟨bitSide (fun w => xor w.1 w.2.1.1) say stop, pad.honestLinkProver, nilB⟩

/-- The honest side sends the index in a plain part: whatever the simulators are, the error of the
first table's simulator and the measure of its stops add up to at least 1/2. -/
theorem tell_forces {Sm : Sims pad} {ok : Bool → Prop} {Gs : Bool → Prop}
    {Ryes : Bool → Unit → Prop} {zT zL zO hT hL hO : ℝ≥0∞}
    (hG : Sm.Good (recsBit (fun w => w.1) fun _ => false) WP ok Gs Ryes zT zL zO)
    (hS : StopsSmall (recsBit (fun w => w.1) fun _ => false) WP ok Gs Ryes hT hL hO)
    (h1 : ok true) (h0 : ok false) (he : Gs false) : 1 ≤ (zT + hT) + (zT + hT) := by
  refine good_forces_T hG hS (i := true) (i' := false) (r := (false, false)) (r' := (true, false))
    (e := false) h1 h0 he rfl rfl fun ρ hEq => ?_
  have e1 := output_bitSide (Y := pad.Rec)
    (fun w : Bool × (Bool × Bool) × Bool => xor w.1 w.2.1.1) (fun w => w.1) (fun _ => false)
    (true, (false, false), false) (pad.recOf true (false, false) false) ρ
  have e2 := output_bitSide (Y := pad.Rec)
    (fun w : Bool × (Bool × Bool) × Bool => xor w.1 w.2.1.1) (fun w => w.1) (fun _ => false)
    (false, (true, false), false) (pad.recOf true (false, false) false) ρ
  rw [if_neg (by simp)] at e1 e2
  have h := congrArg (PMF.map bitOf) (e1.symm.trans (hEq.trans e2))
  have h' : (PMF.pure (some true) : PMF (Option Bool)) = PMF.pure (some false) :=
    ((PMF.pure_map _ _).symm.trans h).trans (PMF.pure_map _ _)
  have h2 := tv_pure_ne (a := some true) (b := some false) (by simp)
  rw [h', tv_self] at h2
  exact zero_ne_one h2

/-- The honest side stops just when the index is 1: the measure of the first table's stops is 1. -/
theorem stop_forces {ok : Bool → Prop} {Gs : Bool → Prop} {Ryes : Bool → Unit → Prop}
    {hT hL hO : ℝ≥0∞}
    (hS : StopsSmall (recsBit (fun w => xor w.1 w.2.1.1) fun w => w.1) WP ok Gs Ryes hT hL hO)
    (h1 : ok true) {e : Bool} (he : Gs e) : 1 ≤ hT :=
  stops_forces_T hS (i := true) (r := (false, false)) h1 he fun _ => rfl

end Member

/-! ## At the object pad2: a session -/

namespace Member2
open Hiop.Seeded (tv_pure_ne)
open Hiop.Seeded.Two

/-- A block of 32 bits (Hiop/Seeded/Pad2.lean). -/
local notation "Blk₂" => Hiop.Seeded.Two.Blk

/-- The session's honest side of pad2, but that it sends say w in the symbol's place and stops where
stop w. -/
def sideSay (Y : Type) (say stop : WB → Bool) : Honest (sessP Y) WB where
  Coin := Bool
  ext := fun w _ => xor (bit w.1) w.2.1.1
  strat := fun w _ κ =>
    ((((), ((say w, κ), 0)), fun c => (((), c 0 1), fun _ => ())) :
      (Unit × ((Bool × Bool) × ℕ)) × (Blk₂ → (Unit × Bool) × (Unit → Unit)))
  Bad := ∅
  Hid := fun w _ => {_ρ | stop w = true}

/-- the first bit of round 1's plain part, if anything is shown -/
def saidOf {Y : Type} : Option (DView (sessP Y)) → Option Bool
  | none => none
  | some v => some (show ((Bool × Bool) × ℕ) × (Bool × Unit) from v.plains).1.1.1

/-- Where it does not stop, what it shows holds say w. -/
theorem said_sideSay {Y : Type} (say : WB → Bool) (w : WB) (y : Y) (ρ : Rho (sessP Y).shape) :
    ((sideSay Y say fun _ => false).output w y ρ).map saidOf = PMF.pure (some (say w)) := by
  unfold Honest.output
  have hm : ρ ∉ (sideSay Y say fun _ => false).withheld w y := fun hh =>
    ((Set.mem_union ρ _ _).1 hh).elim (fun h0 => h0) fun h0 => Bool.noConfusion h0
  rw [if_neg hm, PMF.map_comp]
  have hc : (saidOf ∘ fun c : Bool => some ((sessP Y).dview y
      ((sideSay Y say fun _ => false).ext w)
      (((sideSay Y say fun _ => false).strat w y c).run ρ).1)) =
      Function.const _ (some (say w)) := by
    funext κ
    obtain ⟨c, c', ρ'⟩ := (ρ : Blk₂ × Unit × Unit)
    rfl
  exact (congrArg (fun f => PMF.map f (unif Bool)) hc).trans (PMF.map_const _ _)

def recsSay (say stop : WB → Bool) : ThreeProvers pad2 := ⟨sideT _, sideL _, sideSay _ say stop⟩

/-- The session's honest side sends the index in a plain part: whatever the simulators are, the
error of the session's simulator and the measure of its stops add up to at least 1/2. -/
theorem tell_forces_B {Sm : Sims pad2} {ok : Option Bool → Prop} {Gs : Bool → Prop}
    {Ryes : Option Bool → Unit → Prop} {zT zL zO hT hL hO : ℝ≥0∞}
    (hG : Sm.Good (recsSay (fun w => bit w.1) fun _ => false) W2 ok Gs Ryes zT zL zO)
    (hS : StopsSmall (recsSay (fun w => bit w.1) fun _ => false) W2 ok Gs Ryes hT hL hO)
    (h1 : ok (some true)) (h0 : ok (some false)) (he : Gs false) (hx : Ryes (some true) ())
    (hx' : Ryes (some false) ()) : 1 ≤ (zO + hO) + (zO + hO) := by
  refine good_forces_B hG hS 0 (i := some true) (i' := some false) (r := (false, false))
    (r' := (true, false)) (e := false) (x := ()) h1 h0 he hx hx' rfl rfl fun ρ hEq => ?_
  have e1 := said_sideSay (Y := Unit × pad2.Rec) (fun w => bit w.1)
    (some true, (false, false), false, 0) ((), pad2.recOf (some true) (false, false) false) ρ
  have e2 := said_sideSay (Y := Unit × pad2.Rec) (fun w => bit w.1)
    (some false, (true, false), false, 0) ((), pad2.recOf (some true) (false, false) false) ρ
  have h' : (PMF.pure (some true) : PMF (Option Bool)) = PMF.pure (some false) :=
    (e1.symm.trans (congrArg (PMF.map saidOf) hEq)).trans e2
  have h2 := tv_pure_ne (a := some true) (b := some false) (by simp)
  rw [h', tv_self] at h2
  exact zero_ne_one h2

/-- The session's honest side stops just when the index is 1: the measure of a session's stops
is 1. -/
theorem stop_forces_B {ok : Option Bool → Prop} {Gs : Bool → Prop}
    {Ryes : Option Bool → Unit → Prop} {hT hL hO : ℝ≥0∞}
    (hS : StopsSmall (recsSay (fun w => xor (bit w.1) w.2.1.1) fun w => bit w.1) W2 ok Gs Ryes hT hL
      hO)
    (h1 : ok (some true)) {e : Bool} (he : Gs e) (hx : Ryes (some true) ()) : 1 ≤ hO :=
  stops_forces_B hS 0 (i := some true) (r := (false, false)) (x := ()) h1 he hx fun _ => rfl

/-- **THE GUARD ok IS NEEDED AT THE MEMBER.** The honest sides of Johnson/WholeKey/Member2.lean meet
StopsSmall with all measures 0 at the range ok2 (stops2). At a range that holds the index out of
range too, they force all three measures to be 1. -/
theorem stops_all_forces {ok : Option Bool → Prop} {Gs : Bool → Prop}
    {Ryes : Option Bool → Unit → Prop} {hT hL hO : ℝ≥0∞}
    (hS : StopsSmall recs2 W2 ok Gs Ryes hT hL hO) (h : ok none) {e : Bool} (he : Gs e) :
    1 ≤ hT ∧ 1 ≤ hL ∧ (Ryes none () → 1 ≤ hO) :=
  ⟨stops_forces_T hS (i := none) (r := (false, false)) h he fun _ => rfl,
    stops_forces_Lk hS (i := none) (r := (false, false)) (r' := (false, false)) h he he
      fun _ => rfl,
    fun hx => stops_forces_B hS 0 (i := none) (r := (false, false)) (x := ()) h he hx fun _ => rfl⟩

end Member2

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.good_forces_T
#print axioms OnBytes.WholeKey.good_forces_B
#print axioms OnBytes.WholeKey.stops_forces_T
#print axioms OnBytes.WholeKey.stops_forces_Lk
#print axioms OnBytes.WholeKey.stops_forces_B
#print axioms OnBytes.WholeKey.Member.tell_forces
#print axioms OnBytes.WholeKey.Member.stop_forces
#print axioms OnBytes.WholeKey.Member2.tell_forces_B
#print axioms OnBytes.WholeKey.Member2.stop_forces_B
#print axioms OnBytes.WholeKey.Member2.stops_all_forces
