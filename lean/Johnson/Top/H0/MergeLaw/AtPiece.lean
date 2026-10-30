-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/AtPiece.lean: the merge's law at a piece: of the block's own reduction over
its stretch, in the plain form. Theorems with their proofs.

`merge_plain` (Johnson/Top/H0/MergeLaw/Plain.lean) speaks of `headMergeDecide` at written rounds.
Here it is said of `Piece.ior.red` (Johnson/Desc/Sound/ChainRule.lean): the chain's own fold at the
list of this one block, behind the stage's tests, with the test on words in front (`below`).

Main names:
  `roundsFit_noDigest`: the step's test on rounds reads no sealed digest.
  `pass_of_passT`: where the stage's tests of work pass, the maps' do.
  `chainAt_one`: the chain's fold at one block says yes only where `Block.step` does, at all the
    rounds and all the columns.
  `piece_yes`: what a yes of the piece's reduction holds.
  `mergePiece`: the block with the test on words in front, at its stretch.
  `merge_leads`: for each fixed tuple of entries m: `Reduction.Leads`
    (Johnson/Desc/Plain/Leads.lean) of the piece's reduction, at every statement, towards
    `MergeSays` at the two records, at the maps' image of the proved block's errors.

Limits. The entries m stand outside the game; no pin is laid here. The piece's written rounds are
letters under `MergeDs`: none is taken from a plan. rd, which reads the typed statement off the
statement in front, is a letter. The premises inside `MergeSays` are paid by nobody here. The error
is held against no price. It is no soundness of the protocol. Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.Plain
import Johnson.Top.H0.StepLaws.StepLaws
import Johnson.Desc.Sound.ChainRule
import Johnson.Desc.Plain.Leads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (Block Claim roundsFit noDigest fieldPrimeWord viewWordsBelowPrime chainAt foldBlocks
  step_iff)
open VerifiableInference.Desc.Sound (Frame Piece below foldRun)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headClaimMergeKind)
open _root_.Run (ckP)

/-- The step's test on rounds reads no sealed digest. -/
theorem roundsFit_noDigest : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds (rs.map noDigest) = roundsFit ds rs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, r :: rs => by
    have ih := roundsFit_noDigest ds rs
    show (_ && roundsFit ds (rs.map noDigest)) = (_ && roundsFit ds rs)
    rw [ih]
    rfl

/-- Where the stage's tests of work pass, the maps' do. -/
theorem pass_of_passT : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s')
    (τ : Tr (uLT (ckP .two) ds)), passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true →
    M.pass τ = true
  | _, _, .nil, _, _ => rfl
  | _, _, .step _ rest, (_, _, τ), h =>
    Bool.and_eq_true_iff.2 ⟨(Bool.and_eq_true_iff.1 h).1,
      pass_of_passT rest τ (Bool.and_eq_true_iff.1 h).2⟩
  | _, _, .skip _ rest, (_, _, τ), h => pass_of_passT rest τ (Bool.and_eq_true_iff.1 h).2

/-- The chain's fold at one block says yes only where the block's step does, at all the rounds and
all the columns. -/
theorem chainAt_one {S Cl : Type} (name : String) (ft : Nat) (b : Block S Cl) (s s' : S)
    (v : Fmt.View) (h : chainAt name ft [b] s v = .ok s') :
    ∃ k, b.step ft s v.rounds v.opened = .ok (s', k) := by
  unfold chainAt at h
  simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at h
  cases hf : foldBlocks ft [b] s v.rounds v.opened with
  | error e => rw [hf] at h; exact absurd h (by simp)
  | ok t =>
    obtain ⟨s1, rs, cols⟩ := t
    rw [hf] at h
    cases rs with
    | cons r rs => exact absurd h (by simp)
    | nil =>
      cases cols with
      | cons c cols => exact absurd h (by simp)
      | nil =>
        have e1 : s1 = s' := Except.ok.inj h
        subst e1
        unfold foldBlocks at hf
        simp only [List.splitAt_eq] at hf
        split at hf
        · exact absurd hf (by simp)
        · split at hf
          · exact absurd hf (by simp)
          · rename_i s2 k hs
            unfold foldBlocks at hf
            have e2 := Except.ok.inj hf
            have e3 : s2 = s1 := (Prod.mk.inj e2).1
            have e4 : v.rounds.drop b.rounds.length = [] := (Prod.mk.inj (Prod.mk.inj e2).2).1
            subst e3
            rw [List.take_of_length_le (List.drop_eq_nil_iff.1 e4)] at hs
            exact ⟨k, hs⟩

variable {F : Frame} {W : Type}

/-- **What a yes of the piece's reduction holds**, at the block with the test on words in front. -/
theorem piece_yes {S Cl : Type} (b : Block S Cl) (p : Piece (ckP .two) F S Cl W)
    (hb : p.b = below b) (hback : p.back = []) (a a' : S × F.E.Str)
    (τ : Tr (uLT (ckP .two) p.ds)) (h : p.ior.red.out a τ = some a') :
    passT (ckP .two) p.ds (rhoT (ckP .two) p.ds τ) = true ∧
      roundsFit b.rounds (rvT (ckP .two) p.ds τ) = true ∧
      (∀ r ∈ (rvT (ckP .two) p.ds τ).map noDigest, ∀ x ∈ r.drawn.elems,
        x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧ x.2.2 < fieldPrimeWord) ∧
      ∃ gs, b.decide a.1 ((rvT (ckP .two) p.ds τ).map noDigest) gs = .ok a'.1 := by
  have h1 : (if sTests (ckP .two) p.stage a.2 τ = true
      then p.run a.1 (sView (ckP .two) p.stage a.2 τ) else none).map
        (fun xo => (xo, p.ior.imp a.2 τ)) = some a' := h
  obtain ⟨s', h2, h3⟩ := Option.map_eq_some_iff.1 h1
  split at h2
  · rename_i ht
    have hp : passT (ckP .two) p.ds (rhoT (ckP .two) p.ds τ) = true := by
      unfold sTests at ht
      simp only [Bool.and_eq_true] at ht
      exact ht.1.1
    have h4 : (chainAt p.b.name F.ft [p.b] a.1
        ⟨(sView (ckP .two) p.stage a.2 τ).rounds ++ p.back,
          (sView (ckP .two) p.stage a.2 τ).opened⟩).toOption = some s' := h2
    have h5 : chainAt p.b.name F.ft [p.b] a.1
        ⟨(sView (ckP .two) p.stage a.2 τ).rounds ++ p.back,
          (sView (ckP .two) p.stage a.2 τ).opened⟩ = .ok s' := by
      cases hc : chainAt p.b.name F.ft [p.b] a.1
          ⟨(sView (ckP .two) p.stage a.2 τ).rounds ++ p.back,
            (sView (ckP .two) p.stage a.2 τ).opened⟩ with
      | error e => rw [hc] at h4; exact absurd h4 (by simp [Except.toOption])
      | ok x =>
        rw [hc] at h4
        have : x = s' := by simpa [Except.toOption] using h4
        rw [this]
    obtain ⟨k, h6⟩ := chainAt_one _ _ _ _ _ _ h5
    rw [hb, hback, List.append_nil] at h6
    obtain ⟨hfit, hdec, _⟩ := (step_iff _ _ _ _ _ _ _).1 h6
    have hr : (sView (ckP .two) p.stage a.2 τ).rounds = rvT (ckP .two) p.ds τ := rfl
    rw [hr] at hfit hdec
    have hdec' : (if viewWordsBelowPrime ⟨(rvT (ckP .two) p.ds τ).map noDigest, _⟩ = true
        then b.decide a.1 ((rvT (ckP .two) p.ds τ).map noDigest) _
        else .error "a word is not below the prime") = .ok s' := hdec
    split at hdec'
    · rename_i hw
      subst h3
      exact ⟨hp, hfit.1, words_of_okViewW hw, _, hdec'⟩
    · exact absurd hdec' (by simp)
  · exact absurd h2 (by simp)

/-- The merge's block, with the test on words in front, at its stretch; its errors: the maps' image
of the proved block's. -/
noncomputable def mergePiece (F : Frame) (W : Type) (P : HeadMergeP) (G : WeightsL GE)
    (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT) (hk : ds.length = G.k) (base : ℕ)
    (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W) :
    Piece (ckP .two) F S Claim W :=
  ⟨below (headClaimMergeKind P), base, dZ :: d0 :: (ds ++ [dY, dV]), [], ext,
    (mergeMaps G F.E dZ d0 ds dY dV hk).err (G.eps (Kc := Unit) (G.L.V1 F.E))⟩

/-- **THE MERGE's LAW AT A PIECE, IN THE PLAIN FORM, THE ENTRIES OUTSIDE THE GAME.** -/
theorem merge_leads (P : HeadMergeP) (G : WeightsL GE) {dZ d0 : RDT} {ds : List RDT} {dY dV : RDT}
    (hk : ds.length = G.k) (hkP : G.k = P.lay.lk) (H : MergeDs dZ d0 ds dY dV) (base : ℕ)
    (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
    (rd : S × F.E.Str → G.St) (m : G.J → GE) :
    (mergePiece F W P G dZ d0 ds dY dV hk base ext).ior.red.Leads (fun _ => True)
      (fun a a' => MergeSays P G m (rd a) a.1 a'.1)
      (mergePiece F W P G dZ d0 ds dY dV hk base ext).err := by
  intro a _
  refine Doomed.mono _ _ ?_ (merge_plain P G F.E hk hkP H m (rd a, a.2) a.1)
  intro τ hτ a' ha'
  obtain ⟨hp, hfit, hw, gs, hdec⟩ := piece_yes (headClaimMergeKind P)
    (mergePiece F W P G dZ d0 ds dY dV hk base ext) rfl rfl a a' τ ha'
  exact hτ (pass_of_passT _ τ hp) (by rw [roundsFit_noDigest]; exact hfit) hw a'.1 hdec

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.piece_yes
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_leads
