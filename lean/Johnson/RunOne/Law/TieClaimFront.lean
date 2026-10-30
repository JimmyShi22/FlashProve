-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieClaimFront.lean: THE
CLAIMS' TIE IN FRONT OF THE KIND'S OWN BLOCK OF THE FIRST LOOKUP (border 4 of the key file's first
chain), ONE WAY: the relation of the links' row at the filling from the table's letters gives the
table's claim: the second of the four implications that a tie by Leads.conseq asks at the field
r1_4.

Main names:
  sameTables_stm: the riding part's statement has the record's statement's tables.
  srow_atSt: the table's item "the sample rows of message k hold" at the riding part's record gives
    it at the record.
  decT_some: what the decoder gives is pinned.
  claim_front₀: On₁' … 4 a, (rowT 0 2).rel a ⊢ Cl₁ … 4 a.

Object: the links' rows and the table of the first chain (TieStated.lean).
User: FieldR14.lean and TieClaimBack.lean.
Letters: the table's B (under SmReads), at_, R (its letter same: two elements are the same where
they read alike), coll. Premises: the plan's tests · two lookups.

Limits. One way, one border. Nothing on soundness.

-/
import Johnson.RunOne.Law.TiePromise
import Johnson.RunOne.Law.TieKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieClaimFront
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Source KRead Where KItem rowHolds_congr)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ Cl₁)
open Johnson.RunOne.KeyRows1 (open₁ n₁ on₁_two plan₁ meaning₁At)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.LettersAt
open Johnson.RunOne.Law.TieStated
open Johnson.RunOne.Law.TiePromise
open Johnson.RunOne.Law.TieKeys
open LPFD (On₁')

/-- The riding part's statement has the record's statement's tables. -/
theorem sameTables_stm {P : Type} (p₀ : P) (i : ℕ) (s : FirstState) :
    VerifiableInference.Desc.Key.SameTables (stm (stK p₀ i s)) s.d.st := by
  refine ⟨Array.size_map .., fun o part => ?_⟩
  have e : (stm (stK p₀ i s)).oracles[o]? = (s.d.st.oracles[o]?).map bareO := Array.getElem?_map ..
  unfold Statement.tableBits Statement.rowBits Statement.placeBits
  rw [e]
  cases s.d.st.oracles[o]? <;> rfl

variable {Cells Mm Smp Rec : Type} {X : Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces} {D : WholeD} {B : BaseSt Cells Mm Smp Rec}
  {at_ : Where} {R : KRead Cells Mm} {coll : Strs → Rec → Prop}

/-- The sample rows' item at the riding part's record gives it at the record. -/
theorem srow_atSt (k : ℕ) (p₀ : Xi) (i : ℕ) (s : FirstState) (y y' : Strs)
    (w : Wit Cells Unit Mm)
    (h : (meaning₁At X.Y.k.oneTime R).srow k (atSt (pullK (stK p₀ i s))) y w) :
    (meaning₁At X.Y.k.oneTime R).srow k (p₀, s) y' w := by
  obtain ⟨o, x, h1, h2, h3, h4, h5⟩ := h
  have h2' : (s.d.st.oracles.map bareO)[o]? = some x := h2
  rw [Array.getElem?_map] at h2'
  obtain ⟨x0, hx0, rfl⟩ := Option.map_eq_some_iff.1 h2'
  exact ⟨o, x0, h1, hx0, h3, h4, fun r hr =>
    (rowHolds_congr R.same (sameTables_stm p₀ i s) _ r).1 (h5 r hr)⟩

/-- What the decoder gives is pinned. -/
theorem decT_some {a : (Xi × Statement) × (fr₁ D).E.Str} {u : Wit Cells Unit Mm}
    (h : decT X N P D B at_ a = some u) : PinsT X N P B at_ a.1 (strsOf (fr₁ D) a.2) u := by
  unfold decT at h
  split at h
  · rename_i hx
    obtain rfl := Option.some.inj h
    exact hx.choose_spec
  · cases h

/-- **THE CLAIMS' TIE IN FRONT OF THE KIND'S BLOCK OF LOOKUP 0, ONE WAY.** -/
theorem claim_front₀ (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b)
    (hp : (FK X N P).planOk = true) (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (a : (Xi × FirstState) × (fr₁ D).E.Str) (hon : On₁' X N P D B at_ R coll 4 a)
    (hrel : (rowT X N P D B at_ R coll 0 2).rel a) : Cl₁ X N P D B at_ R 4 a := by
  obtain ⟨⟨p₀, s⟩, y⟩ := a
  have h2 := on₁_two _ _ _ _ _ _ _ 4 _ hon.1
  have hW := fk_admitted X N P hp
  unfold rowT at hrel
  obtain ⟨w, ⟨hdec, -, hL, hO⟩, hIn⟩ := (upF_rel (Fr := fr₁ D) _ p₀ s y).1 hrel
  obtain ⟨q1, q2, q3⟩ := decT_some hdec
  have hK0 := (in_iff _ _ _ _ _ _ _).1 hIn
  rw [matOf_cut] at hK0
  have hK1 := hL 1 (Nat.le_refl _) (by rw [hn]; omega)
  have hmem : ∀ i ∈ open₁ 2 4, i = KItem.unmarked ∨ i = .pinT ∨ i = .inRange 0 ∨ i = .inRange 1 ∨
      i = .pin 0 ∨ i = .srow 0 ∨ i = .pin 1 ∨ i = .srow 1 := by decide
  refine ⟨w.1, ?_⟩
  show ∀ i ∈ open₁ (n₁ X.Y.k.oneTime) 4, _
  rw [h2]
  intro i hi
  have t0 := tests_at hW (i := 0) (by rw [hn]; omega)
  have t1 := tests_at hW (i := 1) (by rw [hn]; omega)
  rcases hmem i hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rfl
  · exact (pinw_atSt p₀ 0 s _ _).1 q1
  · refine ⟨_, t0.1, ?_⟩
    rw [hsame]
    exact (inRange_iff _ _ _ _ t0.2.1 t0.2.2).2 hK0
  · refine ⟨_, t1.1, ?_⟩
    rw [hsame]
    exact (inRange_iff _ _ _ _ t1.2.1 t1.2.2).2 hK1
  · exact (pin_atSt hS p₀ 0 s _ _ _ _).1 q2
  · exact srow_atSt 0 p₀ 0 s _ _ _ (hO (strsOf (fr₁ D) y)).1
  · exact (pin_atSt hS p₀ 0 s _ _ _ _).1 q3
  · exact srow_atSt 1 p₀ 0 s _ _ _ (hO (strsOf (fr₁ D) y)).2

end Johnson.RunOne.Law.TieClaimFront

#print axioms Johnson.RunOne.Law.TieClaimFront.sameTables_stm
#print axioms Johnson.RunOne.Law.TieClaimFront.srow_atSt
#print axioms Johnson.RunOne.Law.TieClaimFront.claim_front₀
