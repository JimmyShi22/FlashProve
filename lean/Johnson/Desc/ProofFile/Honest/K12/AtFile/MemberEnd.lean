-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/MemberEnd.lean: NOT IN FRONT OF A LAW OVER COINS. The last
member of a shared thread: the five statements at 11, given what the end accepts, and what the end's
yes says of the state: the chain has ended.

  ended_of_last        behind the end's yes the state stands, and the chain's record of its end returns
  five_eleven          FiveAtBorder at 11
  ended_of_stand       at a stand at 12 the chain has ended: the door's line

By what. end₂_law (E2E/KeyShapeSharedChain.lean), untestedSh_eq (E2E/KeyShapeThird.lean), plays_sealed
(E2E/KeyPlaysQuiet.lean), exchange_of_nil (E2E/KeyExchangeEmpty.lean), open_seal
(E2E/KeySharedQuiet.lean).

Limits. A step at a stand; nothing on a run. hacc, the end's yes, is end_at_head's at the proof file.
Nothing on completeness, soundness or hiding.
-/
import E2E.KeyShapeSharedChain
import E2E.KeyPlaysQuiet
import E2E.KeyExchangeEmpty
import E2E.KeySharedQuiet
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder
import Johnson.Desc.ProofFile.Honest.Thread.Shared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open OnBytes (TableKey)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.Shared (ItemS sharedPlaces)
open Desc.K14 (St tested ended)
open ProofFile.Honest.SharedThread (Letters)

/-- **Behind the end's yes the state stands, and the chain has ended.** -/
theorem ended_of_last (front : List (Block St Unit)) {d d' : St} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K12.Seat.last front).decide d rs gs = .ok d') :
    d' = d ∧ (ended d).isSome = true := by
  obtain ⟨e, hu⟩ := (AtPublicFiles.AtFiles.end₂_law front d d' rs gs).1 h
  refine ⟨e, ?_⟩
  rw [AtPublicFiles.AtFiles.untestedSh_eq] at hu
  simp only [VerifiableInference.Desc.ChainEnd.untestedL, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hu
  have ht : tested d = true := by
    unfold tested
    rw [Bool.and_eq_true]
    refine ⟨hu.1, ?_⟩
    have h2 := hu.2
    rw [← Array.all_toList] at h2 ⊢
    rw [List.all_eq_true] at h2 ⊢
    intro x hx
    have h3 := h2 x hx
    by_cases hs : x.sampled = true
    · have h4 := h3
      simp only [hs, Bool.not_true, Bool.false_or] at h4
      obtain ⟨g, hg, -⟩ := List.any_eq_true.1 h4
      have h5 : x.groups ≠ [] := List.ne_nil_of_mem hg
      simp [h5]
    · simp [hs]
  unfold ended
  rw [if_pos ht]
  rfl

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc X₀ P₁ Wt : Type}
  (L : Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt)
  (Said : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (fall : Nat → St → List Fmt.Drawn → Option String)

/-- **The five at the end of the chain.** -/
theorem five_eleven (hsp : L.split = true) {b₁ : Block St Cl} (hb : L.thread.bs[11]? = some b₁)
    (hr : b₁.rounds = [VerifiableInference.Desc.ChainEnd.sealRound]) (ho : b₁.oracles = [[]])
    (hn : (L.thread.hs.find? fun g => g.place == b₁.place) = none)
    (hd : ∀ d rs gs d', b₁.decide d rs gs = .ok d' → d' = d ∧ L.nothingLeft d = true)
    (hacc : Accepted L.thread fall 11) (hform : ∀ s, L.shape 12 s = true)
    (hrides : ∀ k s m E, ThrS L.thread Said 11 k s m E → L.thread.rides 12 m.st.input s)
    (hkeep : ∀ k s m E, ThrS L.thread Said 11 k s m E → L.thread.keeps 11 s s)
    (hE : ∀ k s m E s', ThrS L.thread Said 11 k s m E → L.thread.keeps 11 s s' → s' = s)
    (hfree : ∀ w (i : ItemS), i ≠ .pinT → i ≠ .nearU → ∀ s y y' v,
      ItemS.holdsSh L.N (L.Mg w) i s y v → ItemS.holdsSh L.N (L.Mg w) i s y' v) :
    FiveAtBorder L.thread Said fall 11 := by
  have hrow : L.thread.row 11 = SharedRows.rows true 11 := by
    show SharedRows.rows L.split 11 = _
    rw [hsp]
  have hown : (SharedRows.rows true 11).owes = [] := by decide
  refine ⟨playsS_of _ _ (AtPublicFiles.KeyThread.plays_sealed L.thread hb hr ho hn), ?_, ?_, ?_,
    acceptedS_of _ _ hacc⟩
  · intro blk hblk k s m E ds y cols s' u _ hS
    rw [hb] at hblk
    cases hblk
    obtain ⟨_, hdec, _⟩ := (VerifiableInference.Desc.step_iff _ b₁ s s' _ cols _).1 hS.2
    obtain ⟨rfl, hl⟩ := hd _ _ _ _ hdec
    have hM := hS.1
    unfold Thread.Moved at hM
    obtain ⟨⟨l, -, hp⟩, -⟩ := hM
    have hi : y.2.st.input = m.st.input := (play_mid _ _ _ _ _ hp).1
    refine ⟨⟨?_, u.1.2.2.1.2⟩, ?_, hkeep k s' m E u⟩
    · show (L.shape 12 s' && (!decide ((sharedPlaces L.split).length ≤ 12) ||
        L.nothingLeft s')) = true
      rw [hform, hl]
      simp
    · rw [hi]
      exact hrides k s' m E u
  · intro blk _ k s m E ds y cols s' _ _ _ ds' i hi
    rw [hrow, hown] at hi
    cases hi
  · intro k s m E s' ps i v u hk hi _ _ hu
    obtain rfl := hE k s m E s' u hk
    have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 11 := by
      have e : i ∈ fwdOpen SharedRows.start (SharedRows.rows L.split) 11 := hi
      rw [hsp] at e
      exact e
    obtain ⟨h1, h2⟩ := AtPublicFiles.KeySharedQuiet.open_seal i hi'
    exact hfree m.st.input i h1 h2 _ _ _ v hu

/-- **At a stand behind the last member the chain has ended.** -/
theorem ended_of_stand (hsp : L.split = true) (hn : ∀ d, L.nothingLeft d = (ended d).isSome)
    {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr L.thread 12 k s m E) : ∃ d, ended s = some d := by
  have hf : (L.shape 12 s && (!decide ((sharedPlaces L.split).length ≤ 12) ||
      L.nothingLeft s)) = true := u.2.2.1.1
  rw [hsp] at hf
  have hlen : (sharedPlaces true).length = 12 := rfl
  rw [hlen, hn] at hf
  simp only [Nat.le_refl, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hf
  exact Option.isSome_iff_exists.1 hf.2

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.ended_of_last
#print axioms ProofFile.Honest.K12.AtFile.five_eleven
#print axioms ProofFile.Honest.K12.AtFile.ended_of_stand
