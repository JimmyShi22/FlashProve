-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/StepSide2.lean: THE STEPS AT 9 AND 10 OF THE TABLES' FILES' FOLD OF THE STATE's SIDE OF THE INVARIANT ALONG THE KEY FILE's SHARED CHAIN: ACROSS THE TWO PROXIMITY TESTS (on G_u, on G_omega): IN THE LETTER OF ITS FIELDS Left₂.g9 | Left₂.g10 (Johnson/Top/Fire/Code/KeyASide2Paid.lean). Statements with proofs; each proof is a joining of calls.
(Words: "invariant": "promise" in these files; "sub-protocol": "block"; "accepts": "says yes"; "the IOP as written in Lean": "the description".)

OBJECT. LPFD.StepInvP (Johnson/Top/Fire/Code/ReachedInvPair.lean) · LPFD.T₂ (KeyASide2AtFk.lean): Tests₂ (Johnson/RunOne/KeyOn2Parts.lean: sixteen facts on the state alone) at the tables' own letters · the sub-protocols at (Fk X N P).shared.blocksInOrder[9] | [10]. USER. The tables' files' aSide₂_of_left (Johnson/Top/Fire/Code/KeyASide2Paid.lean).
LETTERS. X N P at_ off₂: free. PREMISES: hp : (descriptionFromSource X N P).planOk = true · hft: the place's first tree's number is 0 (the maker's literal: Johnson/RunOne/Law/K12AtMaker.lean) · ha1: one answer to a sample (samples_in_scope, Johnson/RunOne/KeySamples.lean has it in scope) · at 10: P.O = some nO (the tables' files' hO_in_scope, Johnson/Top/Fire/Code/KeyPublicAtSeat.lean). NO PART OF THE STATE BEYOND Tests₂ IS WANTED IN FRONT (the letter H stays idle). roundsFit is not spent.
  tests₂_seat: the rule for both tests: field by field, as free₂_seat (Johnson/RunOne/Law/K12Free23.lean). table_eight: under the test on the list of rounds the eight sub-protocols of the test on the table stand in front of the two (desc_eight, Johnson/RunOne/Sound/KeyEightLight.lean). g9 · g10: the fields. g9_scope · g10_scope: from the scope's six equations alone. left₂_fit: the two laid into the structure's fields: the fit is Lean's word.
Limits. A sub-protocol that rejects everything meets every statement. Built over KeyOn2Parts.lean. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12FwdScope
import Johnson.RunOne.Sound.KeyEightLight
import Johnson.Top.Fire.Code.KeyASide2Paid
import Johnson.Top.Fire.Code.KeyPublicAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Johnson.RunOne.Law.StepSide2
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open H2K.JointK (Blk' Gs)
open LKFU.Shape23
open Johnson.RunOne.KeyRows1 (plan₁)
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.K12Shape29 (seat_yes shape₂_9_10)
open Johnson.RunOne.Law.K12Shape210 (shape₂_10_11)
open Johnson.RunOne.Law.K12Free23 (any_shape)
open Johnson.RunOne.Law.K12Order (k12_inOrder)
open Johnson.RunOne.Law.K12Fwd29 (pins_10_9)
open Johnson.RunOne.Law.K12Fwd210 (pins_11_10)
open Johnson.RunOne.Law.K12FwdAt (asks_U asks_O stages_U stages_O p12At_nums)
open Johnson.RunOne.Law.K12Join15 (lengths_of_fileOk)
open Johnson.RunOne.Law.K12SeatsAt (tableBlocks fk_U_at fk_O_at)
open Johnson.RunOne.Law.RngAsked (asksPlan_ok)
open LPFD (StepInvP T₂)

/-- **The facts on the state alone across a proximity test of the shared chain.** -/
theorem tests₂_seat (at_ : Where) (S : LinShape) (K₁ : KPlan) (a : Nat) (last₁ : FirstState → Bool) (off₂ : Nat → Nat) (k k' : Nat) (h6 : 6 ≤ k)
    (hpin : ∀ j ∈ pinned (open₂ k'), j ∈ pinned (open₂ k)) (g : _root_.Desc.K14.Lin → Nat) (mask : _root_.Desc.K14.Lin → Option Nat)
    (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (step : ∀ d d' rs gs, (Block.inside (K12.Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') K12.Seat.leave).decide d rs gs = .ok d' →
      ok (shape₂ S a k d) = true → ok (shape₂ S a k' d') = true)
    (hlen : ∀ z : P₂ × St₂, Tests₂ at_ S K₁ a last₁ off₂ k z → z.2.st.codes.lengthsOk = true)
    (q : P₂) (d d' : St₂) (rs : List Fmt.RoundView) (gs : Gs)
    (hy : (Block.inside (K12.Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') K12.Seat.leave).decide d rs gs = .ok d')
    (T : Tests₂ at_ S K₁ a last₁ off₂ k (q, d)) : Tests₂ at_ S K₁ a last₁ off₂ k' (q, d') := by
  have hsh := step d d' rs gs hy T.shape
  obtain ⟨tE, hk, rfl⟩ := seat_yes g mask p d d' rs gs hy
  have K1 := H2K.Out.k12_out p he ha _ tE rs gs hk
  have hc : tE.st.codes = d.st.codes := K1.codes
  exact
    { shape := hsh
      last := T.last
      eval := T.eval
      placed₁ := T.placed₁
      order₁ := T.order₁
      key := T.key
      codes := hc.trans T.codes
      lay := fun _ => by
        show d.loc.oU.lay = vectorLay tE.st.codes S.fold.u S.fold.rowsHigh
        rw [hc]
        exact T.lay (by omega)
      placed := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := List.mem_filter.1 hj
        obtain ⟨o, t, a1, a2, a3⟩ := T.placed j (List.mem_filter.2 ⟨hpin j hj1, hj2⟩)
        exact ⟨o, t, a1, K1.book.place o t a2, a3⟩
      order := k12_inOrder p _ tE rs gs hk (hlen _ T) T.order
      linOk := fun _ => by
        show OnBytes.linOk tE.st.codes S = true
        rw [hc]
        exact T.linOk (by omega)
      seatU := fun _ => any_shape _ _ K1.shapes 0 _ (T.seatU (by omega))
      seatOmega := fun _ => any_shape _ _ K1.shapes 2 _ (T.seatOmega h6)
      fits := T.fits
      mask₁ := T.mask₁
      maskU := fun _ => by
        obtain ⟨u, v, b1, b2⟩ := T.maskU (by omega)
        exact ⟨u, v, K1.book.place 0 _ b1, K1.book.place 1 _ b2⟩ }

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (at_ : Where) (off₂ : Nat → Nat)

/-- Under the test on the list of rounds eight sub-protocols stand between the shared chain's front and its two proximity tests. -/
theorem table_eight (hp : (descriptionFromSource X N P).planOk = true) : (tableBlocks X P).length = 8 := by
  obtain ⟨bl, hbl, h8, _⟩ := Johnson.RunOne.Sound.Light.desc_eight X N P hp
  have hor : tableBlocks X P = bl := by
    show _root_.Desc.K14.blocksOr (Johnson.RunOne.Sound.Light.parAt X P) = bl
    unfold _root_.Desc.K14.blocksOr
    rw [hbl]
    rfl
  rw [hor]
  exact h8

/-- The codes' lengths at the state's codes, out of Tests₂'s own fields. -/
theorem lengths_of_tests (hf : (descriptionFromSource X N P).fileOk = true) (k : Nat) (z : P₂ × St₂) (T : T₂ X at_ off₂ k z) : z.2.st.codes.lengthsOk = true := by
  rw [T.codes, codes_of_last (oneAt X) _ z.1.2 T.last]
  exact lengths_of_fileOk X N P hf

/-- **The field Left₂.g9 (Johnson/Top/Fire/Code/KeyASide2Paid.lean).** -/
theorem g9 (hp : (descriptionFromSource X N P).planOk = true) (hft : P.U.nums.firstTree = 0) (ha1 : (oneAt X).given.plan.samples = 1) :
    ∀ b, (Fk X N P).shared.blocksInOrder[9]? = some b → StepInvP b (T₂ X at_ off₂ 9) (T₂ X at_ off₂ 10) := by
  intro b hb q d d' rs gs _ hy T
  have hf := (((descriptionFromSource X N P).planOk_ok).1 hp).fileOk
  have hat := fk_U_at X N P
  rw [table_eight X N P hp] at hat
  obtain rfl := Option.some.inj (hat.symm.trans hb)
  obtain ⟨he, ha, _, _⟩ := asksPlan_ok (asks_U X N P hf)
  have en := p12At_nums _ _ he
  exact tests₂_seat at_ _ _ _ _ off₂ 9 10 (by omega) pins_10_9 (·.gU) (·.firstMask) _ he ha
    (fun d d' rs gs h h9 => shape₂_9_10 _ _ _ he ha d d' rs gs h (by rw [en]; exact stages_U X N P hf) (by rw [en]; exact hft) ha1 h9)
    (fun z T => lengths_of_tests X N P at_ off₂ hf 9 z T) q d d' _ gs hy T

/-- **The field Left₂.g10 (Johnson/Top/Fire/Code/KeyASide2Paid.lean).** -/
theorem g10 (hp : (descriptionFromSource X N P).planOk = true) (nO : H2U.PlaceNums) (hO : P.O = some nO) (hft : nO.nums.firstTree = 0) (ha1 : (oneAt X).given.plan.samples = 1) :
    ∀ b, (Fk X N P).shared.blocksInOrder[10]? = some b → StepInvP b (T₂ X at_ off₂ 10) (T₂ X at_ off₂ 11) := by
  intro b hb q d d' rs gs _ hy T
  have hf := (((descriptionFromSource X N P).planOk_ok).1 hp).fileOk
  have hat := fk_O_at X N P nO hO
  rw [table_eight X N P hp] at hat
  obtain rfl := Option.some.inj (hat.symm.trans hb)
  obtain ⟨he, ha, _, _⟩ := asksPlan_ok (asks_O X N P hf nO hO)
  have en := p12At_nums _ _ he
  exact tests₂_seat at_ _ _ _ _ off₂ 10 11 (by omega) pins_11_10 (·.gOmega) (fun _ => none) _ he ha
    (fun d d' rs gs h h10 => shape₂_10_11 _ _ _ he ha d d' rs gs h (by rw [en]; exact stages_O X N P hf nO hO) (by rw [en]; exact hft) ha1 h10)
    (fun z T => lengths_of_tests X N P at_ off₂ hf 10 z T) q d d' _ gs hy T

section
variable {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z) {cfg : ByteArray}
  {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hL : laterPlaces m = .ok P) (hp : (descriptionFromSource X N P).planOk = true)
include hZ hP hm hX hL hp

/-- **Left₂.g9 from the scope's six equations alone.** -/
theorem g9_scope : ∀ b, (Fk X N P).shared.blocksInOrder[9]? = some b → StepInvP b (T₂ X at_ off₂ 9) (T₂ X at_ off₂ 10) :=
  g9 X N P at_ off₂ hp (K12AtMaker.later_zero hL).1 (Johnson.RunOne.KeySendGood.samples_in_scope hZ hP hm hX hp)

/-- **Left₂.g10 from the scope's six equations alone.** -/
theorem g10_scope : ∀ b, (Fk X N P).shared.blocksInOrder[10]? = some b → StepInvP b (T₂ X at_ off₂ 10) (T₂ X at_ off₂ 11) := by
  obtain ⟨nO, hO⟩ := LPFD.hO_in_scope hZ hP hm hX hp
  exact g10 X N P at_ off₂ hp nO hO ((K12AtMaker.later_zero hL).2 nO hO) (Johnson.RunOne.KeySendGood.samples_in_scope hZ hP hm hX hp)

/-- That the two fit the fields is Lean's word: any Left₂ with its fields g9 | g10 laid anew by these. -/
theorem left₂_fit (D : WholeD) (L : LPFD.Left₂ X N P D at_ off₂) : LPFD.Left₂ X N P D at_ off₂ :=
  { L with
    g9 := g9_scope X N P at_ off₂ hZ hP hm hX hL hp
    g10 := g10_scope X N P at_ off₂ hZ hP hm hX hL hp }

end

end Johnson.RunOne.Law.StepSide2

#print axioms Johnson.RunOne.Law.StepSide2.tests₂_seat
#print axioms Johnson.RunOne.Law.StepSide2.table_eight
#print axioms Johnson.RunOne.Law.StepSide2.lengths_of_tests
#print axioms Johnson.RunOne.Law.StepSide2.g9
#print axioms Johnson.RunOne.Law.StepSide2.g10
#print axioms Johnson.RunOne.Law.StepSide2.g9_scope
#print axioms Johnson.RunOne.Law.StepSide2.g10_scope
#print axioms Johnson.RunOne.Law.StepSide2.left₂_fit
