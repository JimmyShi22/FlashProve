-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SeedAtRecord.lean: the kind's three blocks at the first chain's carried record:
behind a yes of the block's step the record's sample rows of each new sampled message are the kind's
one row at the seed drawn; and the block never marks: the record's field failed is as it was.

Main names: joinP_msgs, joinAll_msgs, joinOwnP_msgs; seedIs_later, seedIs_commit, seedIs_first;
seedIs_sendAtS, seedIs_commitAtS, seedIs_firstAtS; sendAtS_failed, commitAtS_failed,
firstAtS_failed.

What is not claimed. One answer a message. That the seeds read is a premise. Nothing on soundness,
on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.SeedIs
import Johnson.Desc.K1.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.First (S)

variable {L Cl : Type}

theorem SameMsgs.trans {A B C : Statement} (h1 : SameMsgs A B) (h2 : SameMsgs B C) :
    SameMsgs A C := ⟨h2.1.trans h1.1, fun j => (h2.2 j).trans (h1.2 j)⟩

theorem joinP_msgs (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : Ground.joinP d g o kept = some d') : SameMsgs d.st d'.st := by
  unfold Ground.joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, fun j => Means.map_modify _ _ _ _ _ fun _ => rfl⟩
  · cases h

theorem joinAll_msgs (p : GPar) (g : Nat) : ∀ (l : List (ReqMessage × Nat)) (d d' : DState L),
    joinAll groundG p g l d = some d' → SameMsgs d.st d'.st
  | [], d, d', h => by
    obtain rfl : d = d' := Option.some.inj h
    exact ⟨rfl, fun _ => rfl⟩
  | _ :: l, d, d', h => by
    obtain ⟨d₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (joinP_msgs d d₁ _ _ _ h1).trans (joinAll_msgs p g l d₁ d' h2)

theorem joinOwnP_msgs (p : GPar) (d d' : DState L) (f f' : ReqFrame) (sent : List ReqMessage)
    (ids : Array Nat) (h : joinOwnP groundG p d f sent ids = some (f', d')) :
    SameMsgs d.st d'.st := by
  unfold joinOwnP at h
  split at h
  · obtain ⟨d₁, h1, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : d₁ = d' := (Prod.mk.inj e).2
    exact joinAll_msgs p _ _ d d₁ h1
  · cases h

/-! ## Behind the kind's decisions -/

theorem seedIs_later (P : Par) (rad : Nat → Nat) (owed : Option Nat) (c c' : ChainCheck)
    (w w' : DState Unit) (r₁ r₂ : Fmt.RoundView) (hC : condPort P rad = true)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : laterOwn P owed c w [r₁, r₂] = .ok (c', w')) (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ)
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    ∃ y, SeedIs P.codes (shapeAt P k) w'.st (w.st.oracles.size + k.val)
      (seedAt P (bitsZ P.codes (shapeAt P k)) ρ) y := by
  obtain ⟨ids, d₁, f', h1, h2, _⟩ := laterOwn_ok P owed c c' w w' _ hyes
  obtain ⟨y, hy⟩ := seedIs_behind P rad owed w d₁ r₁ r₂ ids hC hfit h1 ρ hρ k hk
  exact ⟨y, hy.travels (joinOwnP_msgs _ _ _ _ _ _ _ h2)⟩

theorem seedIs_commit (P : Par) (rad : Nat → Nat) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : Owing (L3.St (DState Unit))) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hC : condPort P rad = true)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : (commitOwn P link moment arrays : Block _ Cl).decide s [r₁, r₂] gs = .ok s')
    (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ) (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    ∃ y, SeedIs P.codes (shapeAt P k) s'.held.w.st (s.held.w.st.oracles.size + k.val)
      (seedAt P (bitsZ P.codes (shapeAt P k)) ρ) y := by
  obtain ⟨ids, d₁, f', h1, h2⟩ := commitOwn_ok P link moment arrays s s' _ gs hyes
  obtain ⟨y, hy⟩ := seedIs_behind P rad s.owed s.held.w d₁ r₁ r₂ ids hC hfit h1 ρ hρ k hk
  exact ⟨y, hy.travels (joinOwnP_msgs _ _ _ _ _ _ _ h2)⟩

theorem seedIs_first (P : Par) (rad : Nat → Nat) (owed : Option Nat) (c c' : ChainCheck)
    (d d' : DState Unit) (r₁ r₂ : Fmt.RoundView) (hC : condPort P rad = true)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : firstOwn P owed c d [r₁, r₂] = .ok (c', d')) (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ)
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    ∃ y, SeedIs P.codes (shapeAt P k) d'.st (d.st.oracles.size + k.val)
      (seedAt P (bitsZ P.codes (shapeAt P k)) ρ) y := by
  obtain ⟨g, d₁, ids, d₂, h0, h1, f₁, own, mine, f₂, h2⟩ := firstOwn_ok P owed c c' d d' _ hyes
  obtain ⟨y, hy⟩ := seedIs_behind P rad owed d₁ d₂ r₁ r₂ ids hC hfit h1 ρ hρ k hk
  rw [newGroupP_size d d₁ _ _ g h0] at hy
  exact ⟨y, hy.travels (joinOwnP_msgs _ _ _ _ _ _ _ h2)⟩

/-! ## Behind a yes of the three blocks' steps -/

theorem seedIs_sendAtS (ft : Nat) (P : Par) (rad : Nat → Nat) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (cols : List OpenedColumn) (n : Nat) (hC : condPort P rad = true)
    (hstep : Block.step ft (sendAtS P : Block S Cl) s [r₁, r₂] cols = .ok (s', n)) (ρ : Seeds P)
    (hρ : ReadsAs P r₁ ρ) (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    ∃ y, SeedIs P.codes (shapeAt P k) s'.st (s.st.oracles.size + k.val)
      (seedAt P (bitsZ P.codes (shapeAt P k)) ρ) y := by
  obtain ⟨hfit, gs, hd⟩ := step_ok ft _ s s' _ cols n hstep
  obtain ⟨ids, d', h1, e1, _⟩ := sendAtS_ok P s s' _ gs hd
  rw [e1]
  exact seedIs_behind P rad _ (stateOf s (#[] : Array Nat)) d' (noDigest r₁) (noDigest r₂) ids hC
    hfit h1 ρ hρ k hk

theorem seedIs_commitAtS (ft : Nat) (P : Par) (rad : Nat → Nat) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (r₁ r₂ : Fmt.RoundView) (cols : List OpenedColumn) (n : Nat)
    (hC : condPort P rad = true)
    (hstep : Block.step ft (commitAtS P link moment arrays : Block S Cl) s [r₁, r₂] cols =
      .ok (s', n)) (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ) (k : Fin (shapesOf P).length)
    (hk : sampledAt P k) :
    ∃ y, SeedIs P.codes (shapeAt P k) s'.st (s.st.oracles.size + k.val)
      (seedAt P (bitsZ P.codes (shapeAt P k)) ρ) y := by
  obtain ⟨hfit, gs, hd⟩ := step_ok ft _ s s' _ cols n hstep
  obtain ⟨t, y, e0, h1, e1, _⟩ := commitAtS_ok P link moment arrays s s' _ gs hd
  have := seedIs_commit (Cl := Cl) P rad link moment arrays t y (noDigest r₁) (noDigest r₂) gs hC
    hfit h1 ρ hρ k hk
  rw [e0] at this
  rw [e1]
  exact this

theorem seedIs_firstAtS (ft : Nat) (q : Params.First) (gp : GPar) (rad : Nat → Nat) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (cols : List OpenedColumn) (n : Nat) (hC : condPort (firstPar q gp) rad = true)
    (hstep : Block.step ft (firstSegmentOpening q gp : Block S Cl) s [r₁, r₂] cols = .ok (s', n))
    (ρ : Seeds (firstPar q gp)) (hρ : ReadsAs (firstPar q gp) r₁ ρ)
    (k : Fin (shapesOf (firstPar q gp)).length) (hk : sampledAt (firstPar q gp) k) :
    ∃ y, SeedIs (firstPar q gp).codes (shapeAt (firstPar q gp) k) s'.st
      (s.st.oracles.size + k.val)
      (seedAt (firstPar q gp) (bitsZ (firstPar q gp).codes (shapeAt (firstPar q gp) k)) ρ) y := by
  obtain ⟨hfit, gs, hd⟩ := step_ok ft _ s s' _ cols n hstep
  obtain ⟨c, d', h1, e1, _⟩ := firstAtS_ok q gp s s' _ gs hd
  rw [e1]
  exact seedIs_first (firstPar q gp) rad _ s.check c (stateOf s ()) d' (noDigest r₁) (noDigest r₂)
    hC hfit h1 ρ hρ k hk

/-! ## The blocks never mark -/

theorem putLink_failed (s : S) (Lk : LinkCtx) : (s.putLink Lk).failed = s.failed := by
  unfold S.putLink
  split <;> (try split) <;> rfl

theorem putFork_failed (s : S) (F : Fork) : (s.putFork F).failed = s.failed := by
  unfold S.putFork
  split <;> (try split) <;> rfl

theorem sendAtS_failed (P : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s rs gs = .ok s') : s'.failed = s.failed := by
  unfold sendAtS at h
  dsimp only at h
  split at h
  · split at h
    · obtain ⟨y, _, rfl⟩ := (map_ok _ _ _).1 h
      rfl
    · cases h
  · cases h

theorem commitAtS_failed (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    s'.failed = s.failed := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · obtain ⟨y, _, rfl⟩ := (map_ok _ _ _).1 h
    rw [putFork_failed, putLink_failed]
    rfl
  · cases h

theorem firstAtS_failed (q : Params.First) (gp : GPar) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s rs gs = .ok s') : s'.failed = s.failed := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, _, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  rfl

end VerifiableInference.Desc.K1
