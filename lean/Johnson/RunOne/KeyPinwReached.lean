-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyPinwReached.lean: THEOREMS; CALLS ALONE. **IN THE GOALS' SCOPE, AT ANY STATE THAT THE FIRST CHAIN's BLOCKS REACH BEHIND TWO OR MORE OF THEM: a member of PINW beside PIN · hasSmp · NoColl (at the index masks' and the lookups' own message) at the woven tables' one reading at its canonical filling.** No state is laid by hand.
IS IT EMPTY? IT HANGS ON THIS: THERE IS A HISTORY Hist₁ (Key.descriptionFromSource X N P) D' (2 + j) a WHOSE INSTANCE a.1 IS keyInstanceOfOutOfDomainSample OF M's TRUE OOD SAMPLE. No theorem shows one. The blocks hand the instance on, so it is a condition on the instance at which the history began. A history has been RUN at a stored set's instance; that this instance is such an keyInstanceOfOutOfDomainSample is unshown.
THE STRINGS y' ARE FITTED: code words chosen to fit the state's answers, not a run's own (the called theorem's limit).
WORDS. The out-of-domain (OOD) sample on the committed table, its seed and its answers (the library's files call it the record: recOf · recBack · recOfM · RecFull). What the verifier carries between two blocks: the verifier's state.
OBJECT: the premise hrec of member_pinw_name_rec (Johnson/RunOne/KeyPinwAtName.lean), «the state holds the sending kind's rows at the open pins», at a state of LPFD.Hist₁; then (baseAt X decN recBack).h₁ at that state. USER: none yet. LETTERS: scope's (as in seven_at) · D' · j · a · M · ρT · y₀.
  msg_shape_full'     by the kernel: the written ranges' own message has the shape shMul
  f3_written | f4_written | f5_written   holdsB (Johnson/RunOne/KeyFillMeet.lean) at the second frame, at the written data: from holds6 | holds7 | holds8 (Johnson/RunOne/KeyScopeNums23.lean): holdsB unfolds to their body
  hrec_reached        the premise, at the pins 0 and 1, at every state reached behind two or more blocks: from idx_seedIs_at | msg_seedIs_at and cond_idx_plan | cond_msg_plan (Johnson/RunOne/KeyMsgAll.lean)
  member_pinw_reached **the sentence above**
What is not claimed. The pin of W's message (open behind the eighteenth block): its number on a history is a count; no law on sizes is called. «In range». It names no o. A MEMBER, no law. Nothing on soundness.

-/
import Johnson.RunOne.KeyPinwInScope
import Johnson.RunOne.KeyMsgAll
import Johnson.RunOne.KeyScopeNums23

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyLetters
open Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState keyInstanceOfOutOfDomainSample)
open VerifiableInference.Desc.K1 (SeedIs)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice OnBytes.Flat
open OnBytes.Params VerifiableInference.Desc.Sound
open Johnson.G (writtenKFull)
open Johnson.Top.H (csKey shIdx shMul)
open Lk6.AtPlan (keyFull)
open LPFD (DN MsgN decN recBack recBack_instK baseAt Hist₁)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)

theorem msg_shape_full' : keyFull.ranges.x.message.shape = shMul := by decide +kernel

theorem f3_written : holdsB (fr₂ writtenKFull) 6 (aOf csKey Johnson.Top.H.shU) = true := holds6
theorem f4_written : holdsB (fr₂ writtenKFull) 7 (aOf csKey Johnson.Top.H.shO) = true := holds7
theorem f5_written : holdsB (fr₂ writtenKFull) 8 (aOf csKey Johnson.Top.H.shSp) = true := holds8

/-- **The state holds the sending kind's rows at the pins 0 and 1, behind two or more blocks.** -/
theorem hrec_reached (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) (hp : (Key.descriptionFromSource X N P).planOk = true)
    (hc : X.Y.k.oneTime.codes = keyFull.codes) (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x)
    (D' : WholeD) (j : ℕ) (a : Xi × FirstState) (h : Hist₁ (Key.descriptionFromSource X N P) D' (2 + j) a) :
    ∀ i : Fin six.length, numSix i < 2 → ∃ o ρ y, (KeyRows1.plan₁ (oneAt X)).orc (numSix i) = some o ∧ SeedIs csKey (six.get i).1 a.2.d.st o ρ y := by
  intro i hi2
  have h3 : numSix i < 3 := Nat.lt_succ_of_lt hi2
  have ho := orc_noSix (oneAt X) i h3
  rw [noSix_eq (oneAt X) i h3] at ho
  obtain ⟨v, hv⟩ := i
  have hv2 : v < 2 := hi2
  match v, hv, hv2, ho with
  | 0, _, _, ho =>
    obtain ⟨ρ, y, hs⟩ := Johnson.RunOne.KeyMsg.idx_seedIs_at (cs := csKey) (sh := shIdx) (hc.trans codes_full) (by rw [hi]; exact idx_shape_full) _
      (Johnson.RunOne.KeyMsg.cond_idx_plan hp hc hi) (by decide) D' (1 + j) a (by rw [← Nat.add_assoc]; exact h)
    exact ⟨0, ρ, y, by simpa using ho, hs⟩
  | 1, _, _, ho =>
    obtain ⟨ρ, y, hs⟩ := Johnson.RunOne.KeyMsg.msg_seedIs_at (cs := csKey) (sh := shMul) (hc.trans codes_full) (by rw [hr]; exact msg_shape_full') _
      (Johnson.RunOne.KeyMsg.cond_msg_plan hp hc hr) (by decide) D' j a h
    exact ⟨1, ρ, y, by simpa using ho, hs⟩

/-- **In scope, at any reached state behind two or more blocks: a member of PINW beside the three at the pins 0 and 1.** -/
theorem member_pinw_reached {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Johnson.G.OfPlan.Made} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}
    (hm : Key.madeAt Z Zp.lay cfg = .ok m) (hX : Key.sourceOf m = .ok X) (hp : (Key.descriptionFromSource X N P).planOk = true)
    (hw : (Key.descriptionFromSource X N P).wantedOk = true) (hD : (Key.descriptionFromSource X N P).data "key file" = .ok writtenKFull)
    (D' : WholeD) (j : ℕ) (a : Xi × FirstState) (h : Hist₁ (Key.descriptionFromSource X N P) D' (2 + j) a)
    (y₀ : (fr₁ (writtenKFull.at frS.P.T.a)).E.Str)
    (M : (Fin DF.v → Bool) → Fin (DF.T.r + DF.T.l) → GF) (ρT : DF.Z.D) (ha : a.1 = keyInstanceOfOutOfDomainSample (recOfM DF M ρT)) (h0 : y₀.1 = stored DF M) :
    ∃ (W : Wit MsgN Unit Fill.Tab) (y' : (fr₁ (writtenKFull.at frS.P.T.a)).E.Str),
      W.cells = DF.ix.view (upM DF M) ∧ y'.1 = stored DF M ∧
      PINW (baseAt X decN recBack).h₁ a (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') W ∧ ∀ i : Fin six.length, numSix i < 2 →
      PIN (Fk X N P) (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') W ∧
      hasSmp (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a = true ∧
      NoColl (Fk X N P) (baseAt X decN recBack).h₁ (atSix (numSix i)).1 (atSix (numSix i)).2 a (strsOf (fr₁ (writtenKFull.at frS.P.T.a)) y') := by
  obtain ⟨-, hr, -, hi, hc⟩ := five_in_scope hZ hP hm hX hp
  exact member_pinw_scope_rec hZ hP hm hX hp hw hD (fun i => numSix i < 2) (fun _ hi2 => Nat.lt_succ_of_lt hi2) y₀ a
    (hrec_reached X N P hp hc hi hr D' j a h) M ρT ha h0

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.msg_shape_full'
#print axioms Johnson.RunOne.KeyLetters.f3_written
#print axioms Johnson.RunOne.KeyLetters.f4_written
#print axioms Johnson.RunOne.KeyLetters.f5_written
#print axioms Johnson.RunOne.KeyLetters.hrec_reached
#print axioms Johnson.RunOne.KeyLetters.member_pinw_reached
