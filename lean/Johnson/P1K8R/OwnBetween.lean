-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/OwnBetween.lean: THE FIRST CHAIN, AT A LAYERS' SEGMENT, ALONG ONE FOLD: WHAT THE
SEGMENT's OWN KIND's SUB-PROTOCOL RETURNED, AS IT STANDS IN FRONT OF THE BATCHING, HOLDS IN ITS
FIELD H.fo JUST WHAT THE LOOKUP ON THE CALLS HAS HEARD. AT STEP LEVEL. UNDER THE SCOPE, THE FILES
READ, IM.Open AND THE DESCRIPTION's TEST ON ITS PLAN. Lemmas; NONE OF THE LIBRARY's GOALS. No prover
stands in them. Nothing on completeness, soundness or hiding.
Why. LinkJoin.k4_heard_at_front (Johnson/Desc/First/Link/Law/K4AtFront.lean) walks back along
"reached" to SOME predecessor and drops what was heard. The honest side's walk hands one fold from
one state.

  `four_decide`   `decides_at` (Johnson/P1K8R/KeepsBetween.lean); the ingredients of
      LinkJoin.stretch_back_layers, back_reads_layers
      (Johnson/Desc/First/Link/Law/StretchBack.lean): THEIR LINES STAND HERE A SECOND TIME, CUT AT
      THE DECISION
  **`own_behind_calls`**   LinkJoin.padNames_behind_calls, piece_at_calls
      (Johnson/Desc/First/Link/Law/K4AtFront.lean); OnPublicFiles.sized_upTo
      (Johnson/Desc/First/Look/K03RowsBare.lean); OnBytes.Road.K4.kept_atS
      (Johnson/Road/K4/KeptAtS.lean); LinkJoin.sameOwn_stretch, quietLayers_sameOwn
      (Johnson/Desc/First/Link/Law/OwnStay.lean); `rel_rides` (KeepsBetween.lean)
Limits. In scope alone. Nothing says that any fold returns or that any state is reached.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.KeepsBetween
import Johnson.Desc.First.Link.Law.K4AtFront
import Johnson.Desc.First.Link.Law.OwnStay
import Johnson.Desc.First.Look.K03RowsBare
import Johnson.Desc.K15.FoldInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Decides)
open Johnson.Desc.First.Walk.Tied (Reach StepYes step_less stepYes_decide)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT A LAYERS' SEGMENT: THE FOUR SUB-PROTOCOLS BETWEEN THE SEGMENT's OWN KIND's AND THE
BATCHING, EACH AT ITS OWN DECISION**, keep every relation that meets LinkJoin.StretchKeeps
(Johnson/Desc/First/Link/Law/StretchBack.lean) and is kept by the step that lays the tables. The
step-level form of that file's stretch_back_layers: its lines, and back_reads_layers', stand here a
second time, cut at the decision. -/
theorem four_decide {R : S → S → Prop} (K : LinkJoin.StretchKeeps R)
    (hq : ∀ Pg : K8.ReadsQuiet.PG, Decides R (K8.ReadsQuiet.layers Pg))
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    ∀ i, i < 4 → ∃ b, c.blocksInOrder[14 * (2 * g) + 5 + i]? = some b ∧ Decides R b := by
  have n24 : ¬ 2 * g = 24 := by omega
  intro i hi
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  · have hk0 : ∀ X, Bs.G₀.built[2 * g]? = some X → X.kind = 0 := by
      intro X hX
      obtain ⟨m, -, fm, km, -⟩ := (IM.ground_named hS hR O.pub O.blank).1 g hg
      rw [← Option.some.inj (fm.symm.trans hX)]
      exact km
    have i1 : IM.k1Ix (2 * g) false = 3 := by
      show (if false = true then 5 else 3) + (if 2 * g = 24 then 1 else 0) = 3
      rw [if_neg (by decide), if_neg n24]
    obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, hX, -, e4⟩ :=
      IM.k1_reads_of hS hR O (2 * g) (by omega)
    rw [i1] at e2
    refine decides_at hS hR O (l := 2 * g) (i := 3) (by omega) e1 e2 e4 (fun q => nomatch q) ?_
    intro s rs gs t hd
    have hd' : (IM.k1Reads Z Bs.G₀ (2 * g) Xl (IM.k1Ix (2 * g) false + 1) reads).decide s rs gs =
        .ok t := hd
    unfold IM.k1Reads at hd'
    obtain ⟨m, h1, h2⟩ := Keeps.ebind_ok hd'
    have q1 : R s m := K.k1 _ _ _ _ _ _ s _ _ m h1
    have q2 : R m t := by
      unfold IM.k1Quiet at h2
      rcases First.K8.Ready.quiet_arms Bs.G₀ (2 * g) Xl _ _ _ _ h2 with ⟨k1, _⟩ | ⟨_, Y, hY, hc⟩
      · rw [hk0 Xl hX] at k1
        exact absurd k1 (fun q => nomatch q)
      · rcases hc with ⟨_, hp, _, hq'⟩ | ⟨k2, _⟩
        · exact hq _ m _ _ t hq'
        · rw [hk0 Y hY] at k2
          exact absurd k2 (fun q => nomatch q)
    exact K.trans _ _ _ q1 q2
  · have i8 : LinkJoin.k8Ix (2 * g) = 4 := by
      show 4 + (if 2 * g = 24 then 1 else 0) = 4
      rw [if_neg n24]
    obtain ⟨Lk, b, Xl, e1, e2, -, -, e4⟩ := IM.k8_alone O (2 * g) (IM.subAt (2 * g))
      (IM.subs_scope hS hR O (2 * g) (by omega)) (LinkJoin.k8Ix (2 * g))
      (LinkJoin.k8_kind_at (2 * g)) (by
        rw [i8]
        omega)
    rw [i8] at e2
    exact decides_at hS hR O (l := 2 * g) (i := 4) (by omega) e1 e2 e4 (fun q => nomatch q)
      (K.k8 _)
  · have i1 : IM.k1Ix (2 * g) true = 5 := by
      show (if true = true then 5 else 3) + (if 2 * g = 24 then 1 else 0) = 5
      rw [if_pos rfl, if_neg n24]
    obtain ⟨Lk, b, Xl, pr, reads, digits, e1, e2, -, -, e4⟩ :=
      IM.k1_digits_of hS hR O (2 * g) (by omega)
    rw [i1] at e2
    exact decides_at hS hR O (l := 2 * g) (i := 5) (by omega) e1 e2 e4 (fun q => nomatch q)
      (fun s rs gs t hd => K.k1 _ _ _ _ _ _ s rs gs t hd)
  · have i3 : IM.k3Ix (2 * g) true = 6 := by
      show (if true = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) = 6
      rw [if_pos rfl, if_neg n24]
    obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O (2 * g) (by omega) true
    rw [i3] at e2
    exact decides_at hS hR O (l := 2 * g) (i := 6) (by omega) e1 e2 e4 (fun q => nomatch q)
      (K.k3 _ _ _ _ _ _ e3)

/-- **AT A LAYERS' SEGMENT, ALONG ONE FOLD: WHAT THE SEGMENT's OWN KIND's SUB-PROTOCOL RETURNED, AS
IT STANDS IN FRONT OF THE BATCHING, HOLDS IN ITS FIELD H.fo JUST WHAT THE LOOKUP ON THE CALLS HAS
HEARD.** blk: that lookup's sub-protocol; its own step takes sj to sk, which is reached behind it
and holds gH as heard; the fold over the five members between takes sk to s'. By the lines of
LinkJoin.k4_heard_at_front's proof (Johnson/Desc/First/Link/Law/K4AtFront.lean), which walks back
along "reached" and drops what was heard. -/
theorem own_behind_calls (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {Q : Type} {start : Q → S} {z : Q} {blk : Block S Claim}
    (hblk : c.blocksInOrder[14 * (2 * g) + 3]? = some blk) {sj sk s' : S} {R : List Fmt.RoundView}
    {cs : List Desc.OpenedColumn} (hst : blk.step 0 sj R cs = .ok (sk, cs.length))
    (hr1 : Reach 0 c.blocksInOrder start (14 * (2 * g) + 4) (z, sk)) {gH : Forest.Heard}
    (hgH : sk.lookHeard? = some gH) {r₂ r₃ : List Fmt.RoundView} {c₂ c₃ : List Desc.OpenedColumn}
    (hfold : foldBlocks 0 ((c.blocksInOrder.take (14 * (2 * g) + 9)).drop (14 * (2 * g) + 4)) sk r₂ c₂ =
      .ok (s', r₃, c₃)) : ∃ o, s'.own? = some o ∧ o.H.fo = gH := by
  have n24 : ¬ 2 * g = 24 := by omega
  -- the ledger behind the lookup has its sizes
  obtain ⟨-, Rr, Cc, hf0⟩ := hr1.fold
  obtain ⟨G, hG, hz⟩ := OnPublicFiles.sized_upTo hS hR O hOk (2 * g) (by omega) 1 (by omega)
    (show foldBlocks 0 (c.blocksInOrder.take (14 * (2 * g) + 1 + 2 + 1)) (start z) Rr Cc =
      .ok (sk, [], []) from hf0)
  -- the lookup's own step
  obtain ⟨Lk', b₃, b', f1, f2, f3, f4⟩ := IM.k3_of hS hR O (2 * g) (by omega) false
  have i3 : IM.k3Ix (2 * g) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) = 1
    rw [if_neg n24]
    rfl
  have hf3 : c.blocksInOrder[14 * (2 * g) + 3]? = some b₃ := by
    have k := IM.hear_at_flat f1 f2
    rw [IM.flatIx_scope hS hR O (by omega : 2 * g ≤ 24) (IM.k3Ix (2 * g) false), i3] at k
    exact k
  obtain rfl : b₃ = blk := Option.some.inj (hf3.symm.trans hblk)
  obtain ⟨b'', f3', hk⟩ := OnPublicFiles.k03_const_ok hS hR O hOk (2 * g) (by omega) false
  obtain rfl : b' = b'' := Option.some.inj (f3.symm.trans f3')
  have hd3 := ((Sound.step_ok_iff 0 b₃ sj sk R cs cs.length).1 hst).2.2.2
  have hd3' := ((IM.yes_alone f4 (fun q => nomatch q) sj sk _ _).1 hd3).1
  have hp3 : (IM.k3Place (2 * g) false).piece ≤ 3 := by
    show (if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) + 1 ≤ 3
    rw [if_neg n24]
    decide
  obtain ⟨fo', hlk, -, hlay⟩ := LinkJoin.padNames_behind_calls _ _ _ _ _ _ b' f3 hk (2 * g) rfl
    (LinkJoin.piece_at_calls _ _ _ _ _ _ b' f3 (2 * g) rfl hp3) sj sk _ _ hd3' hG hz
  obtain rfl : fo' = gH := Option.some.inj (hlk.symm.trans hgH)
  -- the segment's own kind's step: the first of the five
  obtain ⟨Lk, b₄, x, e1, e2, -, e4, -⟩ := IM.k4_of hS hR O g hg
  have hf4 : c.blocksInOrder[14 * (2 * g) + 4]? = some b₄ := by
    have k := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega : 2 * g ≤ 24) 2] at k
    exact k
  have hf4' : (c.blocksInOrder.take (14 * (2 * g) + 9))[14 * (2 * g) + 4]? = some b₄ := by
    rw [List.getElem?_take, if_pos (by omega)]
    exact hf4
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 hf4'
  rw [List.drop_eq_getElem_cons hi, e] at hfold
  obtain ⟨sm, k, hlen, st4, hrest⟩ := foldBlocks_cons 0 b₄ _ sk r₂ c₂ _ hfold
  obtain ⟨rs4, gs4, hd4⟩ := stepYes_decide (⟨_, _, hlen, step_less st4⟩ : StepYes 0 b₄ sk sm)
  obtain ⟨a, fo, o, -, ha, hfo, -, -, ho, -, -, -, -, hofo, -⟩ :=
    OnBytes.Road.K4.kept_atS ((IM.k4_yes e4 sk sm rs4 gs4).1 hd4).1
  obtain rfl : fo' = fo := Option.some.inj ((hlay a ha).symm.trans hfo)
  -- the four behind leave it
  have hown : LinkJoin.SameOwn sm s' :=
    rel_rides LinkJoin.sameOwn_refl LinkJoin.sameOwn_trans c.blocksInOrder (14 * (2 * g) + 5) 4
      (four_decide LinkJoin.sameOwn_stretch LinkJoin.quietLayers_sameOwn hS hR O hg) hrest
  exact ⟨o, hown.trans ho, hofo⟩

end

end P1K8

#print axioms P1K8.four_decide
#print axioms P1K8.own_behind_calls
