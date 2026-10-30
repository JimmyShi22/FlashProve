-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/AtRecord.lean: the kind's three blocks at the first chain's carried record, as
steps of the fold: behind a yes every new sampled message is pinned at the record's statement, and
the record's field out is as it was.

Main names: step_ok (what a yes of any block's step holds); putLink_st, putFork_st and the like for
out; sendAtS_ok, commitAtS_ok, firstAtS_ok; pinned_sendAtS, pinned_commitAtS, pinned_firstAtS.

What is not claimed. The premises of the joined law stand: the tests on the plan, seeds that read as
joint seeds which are not bad. Nothing on the quiet steps that stand beside these blocks in a fold.
Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Travels

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- **What a yes of a block's step holds**: its rounds fit, and its decision has said yes at the
rounds without the sealed digest. -/
theorem step_ok {T : Type} (ft : Nat) (b : Block T Cl) (s s' : T) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (n : Nat) (h : Block.step ft b s rs cols = .ok (s', n)) :
    roundsFit b.rounds rs = true ∧ ∃ gs, b.decide s (rs.map noDigest) gs = .ok s' := by
  unfold Block.step at h
  obtain ⟨_, h1, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨t, h3, h⟩ := (bind_ok _ _ _).1 h
  have e : t = s' := (Prod.mk.inj (Except.ok.inj h)).1
  exact ⟨(need_ok _ _ _).1 h1, _, e ▸ h3⟩

theorem putLink_st (s : S) (L : LinkCtx) : (s.putLink L).st = s.st ∧ (s.putLink L).out = s.out := by
  unfold S.putLink
  split <;> (try split) <;> exact ⟨rfl, rfl⟩

theorem putFork_st (s : S) (F : Fork) : (s.putFork F).st = s.st ∧ (s.putFork F).out = s.out := by
  unfold S.putFork
  split <;> (try split) <;> exact ⟨rfl, rfl⟩

/-- **A yes of W's sending at the record.** -/
theorem sendAtS_ok (P : Par) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s rs gs = .ok s') :
    ∃ ids d', decideSend P (owedOf s) (stateOf s (#[] : Array Nat)) rs = .ok (ids, d') ∧
      s'.st = d'.st ∧ s'.out = s.out := by
  unfold sendAtS at h
  dsimp only at h
  split at h
  · split at h
    · obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
      obtain ⟨x, hx, rfl⟩ := (map_ok _ _ _).1 hy
      exact ⟨x.1, x.2, hx, rfl, rfl⟩
    · cases h
  · cases h

/-- **A yes of a later moment at the record.** -/
theorem commitAtS_ok (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    ∃ (t y : Owing (L3.St (DState Unit))), t.held.w = stateOf s () ∧
      (commitOwn P link moment arrays : Block _ Cl).decide t rs gs = .ok y ∧
      s'.st = y.held.w.st ∧ s'.out = s.out := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    refine ⟨_, y, rfl, hy, ?_, ?_⟩
    · rw [(putFork_st _ _).1, (putLink_st _ _).1]
      rfl
    · rw [(putFork_st _ _).2, (putLink_st _ _).2]
      rfl
  · cases h

/-- **A yes of the first segment's opening at the record.** -/
theorem firstAtS_ok (q : Params.First) (gp : GPar) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s rs gs = .ok s') :
    ∃ c d', firstOwn (firstPar q gp) (owedOf s) s.check (stateOf s ()) rs = .ok (c, d') ∧
      s'.st = d'.st ∧ s'.out = s.out := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  exact ⟨c, d', h2, rfl, rfl⟩

/-! ## Behind a yes of the three blocks' steps -/

/-- **Behind W's sending.** -/
theorem pinned_sendAtS (ft : Nat) (P : Par) (Lst : Nat → (Part → Nat → GE) → Prop) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (cols : List OpenedColumn) (n : Nat) (hB : planOkOwn P = true)
    (hstep : Block.step ft (sendAtS P : Block S Cl) s [r₁, r₂] cols = .ok (s', n)) (ρ : Seeds P)
    (hρ : ReadsAs P r₁ ρ) (hgood : ¬ Bad P Lst ρ) (k : Fin (shapesOf P).length)
    (hk : sampledAt P k) (hne : ∃ u, Lst k.val u) :
    Pinned (Lst k.val) (msgAt P k) s'.st (s.st.oracles.size + k.val) ∧ s'.out = s.out := by
  obtain ⟨hfit, gs, hd⟩ := step_ok ft _ s s' _ cols n hstep
  obtain ⟨ids, d', h1, e1, e2⟩ := sendAtS_ok P s s' _ gs hd
  refine ⟨?_, e2⟩
  rw [e1]
  exact pinned_behind P Lst _ (stateOf s (#[] : Array Nat)) d' (noDigest r₁) (noDigest r₂) ids hB
    hfit h1 ρ hρ hgood k hk hne

/-- **Behind a later moment.** -/
theorem pinned_commitAtS (ft : Nat) (P : Par) (Lst : Nat → (Part → Nat → GE) → Prop)
    (link moment : Nat) (arrays : Option (List Nat)) (s s' : S) (r₁ r₂ : Fmt.RoundView) (cols : List OpenedColumn)
    (n : Nat) (hB : planOkOwn P = true)
    (hstep : Block.step ft (commitAtS P link moment arrays : Block S Cl) s [r₁, r₂] cols =
      .ok (s', n)) (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ) (hgood : ¬ Bad P Lst ρ)
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) (hne : ∃ u, Lst k.val u) :
    Pinned (Lst k.val) (msgAt P k) s'.st (s.st.oracles.size + k.val) ∧ s'.out = s.out := by
  obtain ⟨hfit, gs, hd⟩ := step_ok ft _ s s' _ cols n hstep
  obtain ⟨t, y, e0, h1, e1, e2⟩ := commitAtS_ok P link moment arrays s s' _ gs hd
  refine ⟨?_, e2⟩
  have := pinned_commit (Cl := Cl) P Lst link moment arrays t y (noDigest r₁) (noDigest r₂) gs hB
    hfit h1 ρ hρ hgood k hk hne
  rw [e0] at this
  rw [e1]
  exact this

/-- **Behind the first segment's opening.** -/
theorem pinned_firstAtS (ft : Nat) (q : Params.First) (gp : GPar)
    (Lst : Nat → (Part → Nat → GE) → Prop) (s s' : S) (r₁ r₂ : Fmt.RoundView) (cols : List OpenedColumn) (n : Nat)
    (hB : planOkOwn (firstPar q gp) = true)
    (hstep : Block.step ft (firstSegmentOpening q gp : Block S Cl) s [r₁, r₂] cols = .ok (s', n))
    (ρ : Seeds (firstPar q gp)) (hρ : ReadsAs (firstPar q gp) r₁ ρ)
    (hgood : ¬ Bad (firstPar q gp) Lst ρ) (k : Fin (shapesOf (firstPar q gp)).length)
    (hk : sampledAt (firstPar q gp) k) (hne : ∃ u, Lst k.val u) :
    Pinned (Lst k.val) (msgAt (firstPar q gp) k) s'.st (s.st.oracles.size + k.val) ∧
      s'.out = s.out := by
  obtain ⟨hfit, gs, hd⟩ := step_ok ft _ s s' _ cols n hstep
  obtain ⟨c, d', h1, e1, e2⟩ := firstAtS_ok q gp s s' _ gs hd
  refine ⟨?_, e2⟩
  rw [e1]
  exact pinned_first (firstPar q gp) Lst _ s.check c (stateOf s ()) d' (noDigest r₁) (noDigest r₂)
    hB hfit h1 ρ hρ hgood k hk hne

end VerifiableInference.Desc.K1
