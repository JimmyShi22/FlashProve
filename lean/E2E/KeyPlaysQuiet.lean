-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyPlaysQuiet.lean: THE FIRST OF THE FOUR DEBTS AT A MEMBER (`Plays`,
Johnson/Desc/ProofFile/Honest/Thread/Pays.lean) AT THE NINETEEN SUB-PROTOCOLS OF THE KEY FILE AT
WHICH NO PART OF A PROVER HAS ANYTHING TO SEND: the seventeen without a round, and the two sealing
rounds. In scope, at EVERY thread over the description's own flat lists. By calls. NOTHING IS SHOWN
OF ANY PROVER: no completeness, nothing on what a view shows.

  `quiet_of_rows`: GENERAL: a list of sub-protocols that pass the description's test on their shape,
      with its rows (place, number of rounds): where row number b counts no round, the sub-protocol
      number b has no round and states no oracle message
  **`plays_of_rows`**: so `Plays` holds there: one call of `plays_quiet`
      (Johnson/Desc/ProofFile/Honest/Thread/QuietLaw.lean)
  **`plays_sealed`**: GENERAL: the like at a sub-protocol whose one round is the sealing round, in
      which nothing is sent, and at whose place no part of a prover stands: the frame plays the
      round by itself; nothing is read; no tree is new
  `quiet_exact`: at the written rows of the full size the sub-protocols without a round are just
      these: eleven, three and three
  **`plays_quiet₁`**, **`plays_quiet₂`**, **`plays_quiet₃`**: IN SCOPE: `Plays` at these seventeen
  **`plays_seal₁`**, **`plays_seal₂`**: at the first and at the shared chain's last sub-protocol,
      where no part of a prover stands at its place
  `state₁`, `state₂`, `state₃`: the three chains' state types at the key file's description, by
      unfolding

Limits.
- `Plays` says that the prover's side goes through and that the new trees are the thread's tables.
  At these nineteen there is nothing to play but a round without a message, and no new tree: IT IS
  THE LIGHTEST OF THE DEBTS. The three others at these members (`Behind`, `Exchange`, `RidesPast`)
  and `Accepted` are not here.
- It holds at every thread over the lists, also at one whose sentence is false everywhere.
- The numbers are the full size's: in scope alone.

-/
import E2E.KeyThreads
import E2E.KeyPlacesNamed
import Johnson.Desc.ProofFile.Honest.Thread.QuietLaw

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block Place)
open Johnson.RunOne.Sound (rowsOf)
open ProofFile.Honest

/-! ## General -/

section General
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- Where a row counts no round, the sub-protocol has none and states no oracle message. -/
theorem quiet_of_rows (bs : List (Block S Cl)) (rows : List (Place × Nat)) (hr : rowsOf bs = rows)
    (hsh : ∀ x ∈ bs, x.shaped = true) {b : Nat} (hq : (rows[b]?).map (·.2) = some 0) :
    ∃ blk, bs[b]? = some blk ∧ blk.rounds = [] ∧ blk.oracles = [] := by
  rw [← hr] at hq
  unfold rowsOf at hq
  rw [List.getElem?_map, Option.map_map] at hq
  cases hb : bs[b]? with
  | none =>
    rw [hb] at hq
    cases hq
  | some blk =>
    rw [hb] at hq
    have h0 : blk.rounds.length = 0 := Option.some.inj hq
    have hs := hsh blk (List.mem_of_getElem? hb)
    unfold Block.shaped at hs
    rw [Bool.and_eq_true, beq_iff_eq] at hs
    exact ⟨blk, rfl, List.eq_nil_of_length_eq_zero h0,
      List.eq_nil_of_length_eq_zero (hs.1.trans h0)⟩

/-- **A sub-protocol whose row counts no round plays for nothing.** -/
theorem plays_of_rows (T : Thread Bk S Cl V W X Pb) (rows : List (Place × Nat))
    (hr : rowsOf T.bs = rows) (hsh : ∀ x ∈ T.bs, x.shaped = true) {b : Nat}
    (hq : (rows[b]?).map (·.2) = some 0) : Plays T b := by
  obtain ⟨blk, h1, h2, h3⟩ := quiet_of_rows T.bs rows hr hsh hq
  exact plays_quiet T h1 h2 h3

/-- **The sealing round plays by itself.** -/
theorem plays_sealed (T : Thread Bk S Cl V W X Pb) {b : Nat} {blk : Block S Cl}
    (hblk : T.bs[b]? = some blk)
    (hr : blk.rounds = [VerifiableInference.Desc.ChainEnd.sealRound]) (ho : blk.oracles = [[]])
    (hn : (T.hs.find? fun g => g.place == blk.place) = none) : Plays T b := by
  intro blk' hblk' k s m E ds l _ hd _ hl
  rw [hblk] at hblk'
  cases hblk'
  have el := steps_one_none hn hl
  have hlen := drawsFit_length _ _ hd
  rw [hr] at hlen
  obtain ⟨R, rfl⟩ : ∃ R, ds = [R] := by
    cases ds with
    | nil => cases hlen
    | cons R t =>
      cases t with
      | nil => exact ⟨R, rfl⟩
      | cons _ _ => cases hlen
  have eb : bareSteps (W := W) (Y := X) blk =
      [⟨blk.name, ⟨blk.place, 0⟩, VerifiableInference.Desc.ChainEnd.sealRound, [],
        fun _ _ => none, fun _ _ => none, 0, false, none⟩] := by
    simp [bareSteps, hr, ho]
  refine ⟨(⟨[⟨blk.name, blk.place, 0, false, [],
      List.replicate VerifiableInference.Desc.ChainEnd.sealRound.entry.roots none, R⟩],
      ⟨m.st.hears R, m.loc ++ [R], m.seen ++ [⟨[], R⟩], m.opened⟩⟩ : List Played × Mid W X), [],
    ⟨⟨l, hl, ?_⟩, ?_⟩, ?_⟩
  · rw [el, eb]
    rfl
  · rw [hr]
    rfl
  · intro σ hσ
    have e : T.hand (b + 1) = T.hand b := by
      unfold Thread.hand
      rw [treesTo_succ hblk, ho]
      rfl
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hσ
    rw [e] at h1
    simp [h1] at h2

end General

/-! ## In scope, at the key file's own description -/

section Scope
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription KeyInst flat_last)
open AtPublicFiles.KeyBook (places_named fullFirst fullShared fullSecond)
open VerifierAndGoals (PublicFiles InScope)

/-- At the written rows the sub-protocols without a round are just these. -/
theorem quiet_exact :
    (List.range 19).filter (fun b => (fullFirst[b]?).map (·.2) == some 0) =
        [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14] ∧
      (List.range 12).filter (fun b => (fullShared[b]?).map (·.2) == some 0) = [0, 3, 6] ∧
      (List.range 4).filter (fun b => (fullSecond[b]?).map (·.2) == some 0) = [0, 1, 3] := by
  decide

variable {Z : PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces} {W₀ Rc Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-- The three chains' state types, by unfolding. -/
theorem state₁ : (keyFileDescription Xs N P).S₁ = VerifiableInference.Desc.Key.FirstState := rfl
theorem state₂ : (keyFileDescription Xs N P).S₂ = _root_.Desc.K14.St := rfl
theorem state₃ : (keyFileDescription Xs N P).S₃ = VerifiableInference.Desc.Third.S₃ := rfl

/-- **The first chain's eleven.** -/
theorem plays_quiet₁ (scope : InScope Z = true) (h : KeyNamed Z Xs N P)
    (T : Thread Bk (keyFileDescription Xs N P).S₁ (keyFileDescription Xs N P).Cl (Local W₀ Rc KeyInst Tr)
      (Local W₀ Rc KeyInst Tr) X KeyInst) (hbs : T.bs = (keyFileDescription Xs N P).first.blocksInOrder) :
    ∀ b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14], Plays T b := fun b hb =>
  plays_of_rows T fullFirst (by rw [hbs]; exact (places_named scope h).1)
    (fun x hx => ((planOk_all h.plan).1 x (by rw [← hbs]; exact hx)).2)
    ((by decide : ∀ b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14],
      (fullFirst[b]?).map (·.2) = some 0) b hb)

/-- **The shared chain's three.** -/
theorem plays_quiet₂ (scope : InScope Z = true) (h : KeyNamed Z Xs N P)
    (T : Thread Bk (keyFileDescription Xs N P).S₂ (keyFileDescription Xs N P).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hbs : T.bs = (keyFileDescription Xs N P).shared.blocksInOrder) : ∀ b ∈ [0, 3, 6], Plays T b := fun b hb =>
  plays_of_rows T fullShared (by rw [hbs]; exact (places_named scope h).2.1)
    (fun x hx => ((planOk_all h.plan).2.1 x (by rw [← hbs]; exact hx)).2)
    ((by decide : ∀ b ∈ [0, 3, 6], (fullShared[b]?).map (·.2) = some 0) b hb)

/-- **The last chain's three.** -/
theorem plays_quiet₃ (scope : InScope Z = true) (h : KeyNamed Z Xs N P)
    (T : Thread Bk (keyFileDescription Xs N P).S₃ (keyFileDescription Xs N P).Cl (Local W₀ Rc KeyInst Tr)
      (Local W₀ Rc KeyInst Tr) X KeyInst) (hbs : T.bs = (keyFileDescription Xs N P).second.blocksInOrder) :
    ∀ b ∈ [0, 1, 3], Plays T b := fun b hb =>
  plays_of_rows T fullSecond (by rw [hbs]; exact (places_named scope h).2.2)
    (fun x hx => ((planOk_all h.plan).2.2 x (by rw [← hbs]; exact hx)).2)
    ((by decide : ∀ b ∈ [0, 1, 3], (fullSecond[b]?).map (·.2) = some 0) b hb)

/-- **The first chain's seal.** -/
theorem plays_seal₁
    (T : Thread Bk (keyFileDescription Xs N P).S₁ (keyFileDescription Xs N P).Cl (Local W₀ Rc KeyInst Tr)
      (Local W₀ Rc KeyInst Tr) X KeyInst) (hbs : T.bs = (keyFileDescription Xs N P).first.blocksInOrder)
    (hn : (T.hs.find? fun g => g.place == (keyFileDescription Xs N P).first.last.place) = none) :
    Plays T ((keyFileDescription Xs N P).first.blocksInOrder.length - 1) := by
  obtain ⟨blk, e, hr, ho, hp, -⟩ := flat_last (keyFileDescription Xs N P).first
  exact plays_sealed T (by rw [hbs]; exact e) (hr.trans rfl) (ho.trans rfl) (by rw [hp]; exact hn)

/-- **The shared chain's end.** -/
theorem plays_seal₂
    (T : Thread Bk (keyFileDescription Xs N P).S₂ (keyFileDescription Xs N P).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hbs : T.bs = (keyFileDescription Xs N P).shared.blocksInOrder)
    (hn : (T.hs.find? fun g => g.place == (keyFileDescription Xs N P).shared.last.place) = none) :
    Plays T ((keyFileDescription Xs N P).shared.blocksInOrder.length - 1) := by
  obtain ⟨blk, e, hr, ho, hp, -⟩ := flat_last (keyFileDescription Xs N P).shared
  exact plays_sealed T (by rw [hbs]; exact e) (hr.trans rfl) (ho.trans rfl) (by rw [hp]; exact hn)

end Scope

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.quiet_of_rows
#print axioms AtPublicFiles.KeyThread.plays_of_rows
#print axioms AtPublicFiles.KeyThread.plays_sealed
#print axioms AtPublicFiles.KeyThread.quiet_exact
#print axioms AtPublicFiles.KeyThread.state₁
#print axioms AtPublicFiles.KeyThread.state₂
#print axioms AtPublicFiles.KeyThread.state₃
#print axioms AtPublicFiles.KeyThread.plays_quiet₁
#print axioms AtPublicFiles.KeyThread.plays_quiet₂
#print axioms AtPublicFiles.KeyThread.plays_quiet₃
#print axioms AtPublicFiles.KeyThread.plays_seal₁
#print axioms AtPublicFiles.KeyThread.plays_seal₂
