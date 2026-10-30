-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/LayFrontFold.lean: THE FIRST CHAIN, AT A FEED-FORWARD SEGMENT, ALONG ONE FOLD: FROM THE
OWN STEPS OF THE LOOKUP ON THE CALLS AND OF K4 TO THE STATE IN FRONT OF THE BATCHING. WHY: the
feed-forward layers have two theorems whose ends are two premises of our `liveLayers_of_clauses` (Honest/K9/GoodLayLive.lean); they
speak of K4's own step, at K4's own rounds, and ask beside it a CARRIAGE from the state behind that step to the part
that stands in front of the batching. That carriage is ours. AT STEP LEVEL; UNDER THE SCOPE, THE FILES READ, THE OPENING
AND THE DESCRIPTION's TEST ON ITS PLAN. Statements and proofs; no definition; no prover stands in them; no goal is
stated.
  `lay_of_own`   a state at which `S.own?` answers stands in a feed-forward segment, and its part holds K4's own
  **`k4_front_of_fold`**   blk, b₄: the members 14 (2 g) + 3 and + 4 · hst: blk's own step takes sj to sk · hst₄: b₄'s
      OWN STEP, AT ITS OWN ROUNDS R₂, takes sk to sm · hr1: sk is reached at 14 (2 g) + 4 · hfold: the verifier's fold
      over the four members between takes sm to s'. THE END: some p4, a, a₀, fo, o with: p4 is K4's parameters at 2 g
      (`LPFK9.k4ParAt`), with its P, hp and g · b₄ stands at K4's place of the group g and declares K4's own rounds at
      p4 (the sealed `OnBytes.Road.K4.Declares`) · R₂ fits b₄'s rounds · K4's block at p4 (the member's parameters with
      k3Runs set: `LPFK9.parOfMember`) decides sk to sm at R₂ without digests · sk stands at the part a, which holds fo
      as heard by the calls' lookup, in both fields (a.fo; sk.lookHeard?); a's ledger has its sizes; fo's names are the
      ledger's pads · sm holds o as K4's own (so sm stands at a part: the carriage is not idle) · s' stands at the part
      a₀, which holds o · **THE CARRIAGE**: whatever part a₁ stands at sm, a₀.own = a₁.own · **THE SECOND CARRIAGE**:
      a₀.lookHeard = some fo
HOW. The lines of `own_behind_calls` (Johnson/P1K8R/OwnBetween.lean), TYPED ONCE MORE WITH
A LONGER END: that lemma cuts K4's step out of a fold, so that K4's rounds are SOME rounds, and keeps of all this
"o.H.fo is what was heard" alone. Called: `OnPublicFiles.sized_upTo` · `IM.k3_of` · `OnPublicFiles.k03_const_ok` ·
`Sound.step_ok_iff` · `IM.yes_alone` · `LinkJoin.padNames_behind_calls`, `piece_at_calls` · `IM.k4_of`, `k4_yes` ·
`OnBytes.Road.K4.kept_atS` · `LPFK9.k4ParAt_of_mem` · `IM.alone_rounds`, `IM.alone_place` (the sealed library's) · that
house's `rel_rides`, `four_decide`, `keeps_five`, `look_rides`.
WHAT IS NOT CLAIMED. That any step accepts, any fold returns or any state is reached. Nothing on the ledger's free slots
above its next, nor on where that next stands (the lookups have both). No member. Called by
Honest/K9/LayFrontHanded.lean; `lay_of_own` by this file alone. In scope alone. Nothing on any property.
GROUND: beneath this file lie 3 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.P1K8R.OwnBetween
import Johnson.LPFK9R.K4Ties
import Johnson.Road.K4.PieceTiled

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Decides)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- A state at which `S.own?` answers stands in a feed-forward segment, and its part holds K4's own (a.own = some o). -/
theorem lay_of_own {s : S} {o : Layer.Own} (h : s.own? = some o) : ∃ a, s.here = .lay a ∧ a.own = some o := by
  unfold S.own? at h
  cases hh : s.here with
  | lay a => rw [hh] at h; exact ⟨a, rfl, h⟩
  | between => rw [hh] at h; exact nomatch h
  | att a => rw [hh] at h; exact nomatch h
  | head a => rw [hh] at h; exact nomatch h
  | fin a => rw [hh] at h; exact nomatch h
  | mem a => rw [hh] at h; exact nomatch h

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT A FEED-FORWARD SEGMENT, ALONG ONE FOLD: FROM THE LOOKUP ON THE CALLS AND K4's OWN STEP TO THE STATE IN FRONT OF
THE BATCHING.** blk: that lookup's member; its own step takes sj to sk, which is reached behind it; b₄: K4's member; ITS
OWN STEP, AT ITS OWN ROUNDS R₂, takes sk to sm; the fold over the four members between takes sm to s'. -/
theorem k4_front_of_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {Q : Type} {start : Q → S} {z : Q} {blk b₄ : Block S Claim}
    (hblk : c.blocksInOrder[14 * (2 * g) + 3]? = some blk) (hb₄ : c.blocksInOrder[14 * (2 * g) + 4]? = some b₄)
    {sj sk sm s' : S} {R R₂ : List Fmt.RoundView} {cs d₂ : List Desc.OpenedColumn}
    (hst : blk.step 0 sj R cs = .ok (sk, cs.length)) (hst₄ : b₄.step 0 sk R₂ d₂ = .ok (sm, d₂.length))
    (hr1 : Reach 0 c.blocksInOrder start (14 * (2 * g) + 4) (z, sk)) {r₂ r₃ : List Fmt.RoundView} {c₂ c₃ : List Desc.OpenedColumn}
    (hfold : foldBlocks 0 ((c.blocksInOrder.take (14 * (2 * g) + 9)).drop (14 * (2 * g) + 5)) sm r₂ c₂ =
      .ok (s', r₃, c₃)) :
    ∃ (p4 : OnBytes.Desc.First.K4.Par) (a a₀ : LayOwn) (fo : Forest.Heard) (o : Layer.Own),
      LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 ∧ p4.P = Bs.G₀.W.layers ∧ Bs.G₀.W.G[g]? = some p4.hp ∧ p4.g = g ∧
      b₄.place = IM.k4Place g ∧ OnBytes.Road.K4.Declares b₄ p4 ∧ roundsFit b₄.rounds R₂ = true ∧
      (OnBytes.Desc.First.K4.blockAtS p4).decide sk (R₂.map noDigest)
        (Sound.groupsAt 0 b₄ R₂ (d₂.take d₂.length)) = .ok sm ∧
      sk.here = .lay a ∧ a.fo = some fo ∧ sk.lookHeard? = some fo ∧ PscRun.Sized a.F ∧
      _root_.Fo.Tp.PadNames fo a.F ∧
      sm.own? = some o ∧ s'.here = .lay a₀ ∧ a₀.own = some o ∧ (∀ a₁, sm.here = .lay a₁ → a₀.own = a₁.own) ∧
      a₀.lookHeard = some fo := by
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
  obtain ⟨fo', hlk, hN, hlay⟩ := LinkJoin.padNames_behind_calls _ _ _ _ _ _ b' f3 hk (2 * g) rfl
    (LinkJoin.piece_at_calls _ _ _ _ _ _ b' f3 (2 * g) rfl hp3) sj sk _ _ hd3' hG hz
  -- K4's own step, at its own rounds
  obtain ⟨Lk, b₀, x, e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := IM.k4_of hS hR O g hg
  have hdecl : OnBytes.Road.K4.Declares b₀ (LPFK9.parOfMember x) := by
    show b₀.rounds = _
    rw [IM.alone_rounds e4]
    rfl
  have hf4 : c.blocksInOrder[14 * (2 * g) + 4]? = some b₀ := by
    have k := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega : 2 * g ≤ 24) 2] at k
    exact k
  obtain rfl : b₀ = b₄ := Option.some.inj (hf4.symm.trans hb₄)
  obtain ⟨hrf, -, -, hd4⟩ := (Sound.step_ok_iff 0 b₀ sk sm R₂ d₂ d₂.length).1 hst₄
  have hd4' := ((IM.k4_yes e4 sk sm _ _).1 hd4).1
  obtain ⟨a, fo, o, -, ha, hfo, -, -, ho, -⟩ := OnBytes.Road.K4.kept_atS hd4'
  obtain rfl : fo' = fo := Option.some.inj ((hlay a ha).symm.trans hfo)
  have hGa : sk.fork? = some a.F := by simp [S.fork?, ha]
  obtain rfl : G = a.F := Option.some.inj (hG.symm.trans hGa)
  -- the four behind leave what K4's rounds returned
  have hown : LinkJoin.SameOwn sm s' :=
    P1K8.rel_rides LinkJoin.sameOwn_refl LinkJoin.sameOwn_trans c.blocksInOrder (14 * (2 * g) + 5) 4
      (P1K8.four_decide LinkJoin.sameOwn_stretch LinkJoin.quietLayers_sameOwn hS hR O hg) hfold
  obtain ⟨a₀, ha₀, hoa⟩ := lay_of_own (hown.trans ho)
  -- the five behind the lookup keep what it has heard
  have K := P1K8.keeps_five hS hR O hOk (l := 2 * g) (by omega)
  obtain ⟨b₅, hb₅, D4⟩ := K 0 (by omega)
  obtain rfl : b₅ = b₀ := Option.some.inj (hb₅.symm.trans hf4)
  have keep : OnPublicFiles.KeepsLook sk s' :=
    (D4 sk _ _ sm hd4).trans (P1K8.look_rides c.blocksInOrder (14 * (2 * g) + 5) 4 (fun i hi => by
               have k := K (i + 1) (by omega)
               rwa [show 14 * (2 * g) + 4 + (i + 1) = 14 * (2 * g) + 5 + i by omega] at k) hfold)
  have hlk' : a₀.lookHeard = some fo' := by
    have k := keep fo' hlk
    simpa [S.lookHeard?, ha₀] using k
  refine ⟨LPFK9.parOfMember x, a, a₀, fo', o, LPFK9.k4ParAt_of_mem e3 e5, e7, e8, e6, IM.alone_place e4, hdecl, hrf,
    hd4', ha, hfo, hlk, hz, hN, ho, ha₀, hoa, ?_, hlk'⟩
  intro a₁ e
  have k := ho
  unfold S.own? at k
  rw [e] at k
  exact hoa.trans k.symm

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.lay_of_own
#print axioms ProofFile.Honest.K9.k4_front_of_fold
