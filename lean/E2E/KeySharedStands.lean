--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeySharedStands.lean: WHERE A RUN CAN BE MADE READY, THE KEY FILE's SHARED THREAD STANDS AT ITS
FIRST BORDER, AND BEHIND THE CHAIN's FRONT AT ITS SECOND: at the frame's own start of a run, at the
prover's own halves: `Enters₂` (Johnson/Desc/ProofFile/Honest/Thread/File.lean) at `laid₂`
(E2E/KeyRest.lean); that the front accepts; and the whole thread `Thr` at border 1. In scope, under
premises that are listed by name. By calls. NO PROPERTY OF A PROVER IS CLAIMED: nothing is sent at
these two borders.

WHY IT IS TYPED. Every other statement on these threads is an implication from "the thread stands".
Here that premise is traded for seven that name no thread: on the frame's own tests, on the prover,
on three letters and on the instance. IT IS AN IMPLICATION STILL: see the first limit.

  `Starts₂`: THE PREMISES, in one structure: on the run: the frame's own tests go through (`ready`)
      · on the prover: the key that it hands the shared chain is the instance's; no half of it
      stands at the front's place · on the letters: the stored table's columns are the prover's · on
      the instance: the key fits the shape's index; something is said of this input (`Rel`); THE
      CARRIED OOD SAMPLE IS THERE AND IS THE CELLS' OWN
  **`enters₂_laid`**: `Enters₂`: by the threads' own cut `enters₂_of` (Thread/Enters.lean): the
      clause on the state at the chain's start by the library's start of its side (`t₂_sourced`,
      E2E/KeyStateSide2.lean); ONE ITEM is open there: the pin on the stored table
  `steps_quiet_none`: GENERAL: for a sub-protocol without a round, at whose place no half stands,
      the frame lays no step
  **`accepted_front₂`**: the front accepts, at every fall: its decision returns the state as it is,
      by its text
  **`stands₁_at`**: AT ANY THREAD OVER THE SHARED CHAIN, from its start, what is owed at the front,
      its tests with code and that no half stands there. **`stands₁`**: THE THREAD AT BORDER 1: by `thr_behind` (Thread/PaysLaw.lean) from the
      row at the
      front (E2E/KeyBehind.lean, KeyRidesSame.lean, KeyExchangeEmpty.lean, KeyPlaysQuiet.lean) and
      `made_next` (Thread/MadeLaw.lean)

Limits.
- NO MEMBER OF `Starts₂` IS SHOWN: no prover, no book and no filling of the letters is typed at
  which its seven clauses hold together.
- THE FRONT HAS NO ROUND: nothing is played, nothing is sent, no challenge is heard up to border 1.
  The next sub-protocol is of a kind.
- The thread alone: what is said of the prover's run beside it (the pair) is not treated.
- "The carried OOD sample is the cells' own" is what the one open item says: it is a premise, not a
  result.

-/
import E2E.KeyBehind
import E2E.KeyRidesSame
import E2E.KeyPlaysQuiet
import E2E.KeyExchangeEmpty
import E2E.KeyThreadFits
import E2E.KeyFrontShared
import Johnson.Desc.ProofFile.Honest.Thread.Enters
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (Xi FirstState KItem Source LaterPlaces rows₂)
open Johnson.RunOne.KeyRows23 (St₂)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest

/-! ## 1 General: no step is laid for a sub-protocol without a round and without a half -/

section
variable {S Cl V W X : Type} {Bk : ProverCoinCounts} {rows : List (Addr × Due)}
  {look : Addr → (d : Due) × Cs d} {v : Option V} {b : Block S Cl} {hs : List (Placed V W X)}

theorem steps_quiet_none (hr : b.rounds = []) (ho : b.oracles = [])
    (hf : (hs.find? fun g => g.place == b.place) = none) :
    chainSteps Bk rows look v [b] hs = .ok [] := by
  simp only [chainSteps, hf, hr, ho]
  rfl

theorem stop_quiet_none (hf : (hs.find? fun g => g.place == b.place) = none)
    (loc ds : List Fmt.Drawn) : chainStopAt v [b] hs loc ds = none := by
  simp only [chainStopAt, hf]
  rfl

end

/-! ## 2 The premises -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X₀' X' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (H : Prover W₀ Rc Xi OnBytes.TableKey Unit X₀' X')
  (tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table)
  {Z : VerifierAndGoals.PublicFiles}

/-- **What is asked of the run, the prover, the letters and the instance.** It is a definition: a
premise's form. -/
structure Starts₂ (k : Coins Bk) (R : Ready W₀ Rc Xi OnBytes.TableKey Unit X₀' X') : Prop where
  ready : ready (D Xs N Pl) Bk H w₀ rc x k = .ok R
  key : H.key x = x.key
  bare : ∀ blk, (D Xs N Pl).shared.blocksInOrder[0]? = some blk →
    (H.shared.find? fun g => g.place == blk.place) = none
  stored : ∀ a c, L.stored a c = H.storedWords a c
  fits : KeyFits Xs x
  rel : L.Rel w₀ rc x
  own : ∃ r, L.base.recOf x = some r ∧ L.meetsT r (L.cells w₀ rc)

variable {k : Coins Bk} {R : Ready W₀ Rc Xi OnBytes.TableKey Unit X₀' X'}

theorem Starts₂.common (h : Starts₂ Xs N Pl L w₀ rc x H k R) : R.common = ⟨w₀, rc, x.key⟩ := by
  obtain ⟨-, tr, -, -, hc, -⟩ := ready_ok h.ready
  rw [hc, h.key]

/-! ## 3 The thread at its first border -/

/-- **The shared thread stands at the frame's own start.** -/
theorem enters₂_laid (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (h : Starts₂ Xs N Pl L w₀ rc x H k R) :
    Enters₂ (D Xs N Pl) H (laid₂ Xs N Pl L w₀ rc x H.shared tb₂) w₀ rc x k R := by
  have hc := h.common
  obtain ⟨r, hr, hm⟩ := h.own
  have hside : Side₂ Xs 0 x.key ((D Xs N Pl).start₂ x) := fun e₁ hg =>
    t₂_sourced Xs N Pl hs scope e₁ hg 0 0 (x, (D Xs N Pl).start₂ x) (Nat.zero_le _)
      (Reach.zero x) h.fits
  refine enters₂_of h.ready (fun v => h.stored v.w₀ v.rc) rfl rfl rfl ?_ ?_ trivial ⟨hc, h.rel⟩
  · refine ⟨rfl, ?_, r, ?_⟩
    · show Side₂ Xs 0 R.common.key ((D Xs N Pl).start₂ x)
      rw [hc]
      exact hside
    · show L.base.recOf ⟨R.common.key⟩ = some r
      rw [hc]
      exact hr
  · intro ds i hi
    have hi' : i ∈ ([.pinT] : List KItem) := shared_ends.1 ▸ hi
    obtain rfl := List.mem_singleton.1 hi'
    intro e₁
    refine ⟨r, ?_, ?_⟩
    · show L.base.recOf ⟨R.common.key⟩ = some r
      rw [hc]
      exact hr
    · show L.meetsT r (L.cells R.common.w₀ R.common.rc)
      rw [hc]
      exact hm

/-! ## 4 The front accepts -/

/-- **The shared chain's front accepts**, at every fall. -/
theorem accepted_front₂ {hs₂ : List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X₀')}
    (fall : Nat → St₂ → List Fmt.Drawn → Option String) :
    Accepted (laid₂ Xs N Pl L w₀ rc x hs₂ tb₂) fall 0 := by
  have hb : ∃ b₀, (laid₂ Xs N Pl L w₀ rc x hs₂ tb₂).bs[0]? = some b₀ ∧ b₀.rounds = [] ∧
      ∀ s rs gs, b₀.decide s rs gs = .ok s := ⟨_, rfl, rfl, fun _ _ _ => rfl⟩
  obtain ⟨b₀, e₀, hr, hd⟩ := hb
  exact AtPublicFiles.AtFiles.accepted_quiet _ e₀ hr fun _ s _ _ _ => ⟨s, hd s [] []⟩

/-! ## 5 The thread at its second border -/

/-- **A THREAD OVER THE SHARED CHAIN STANDS AT BORDER 1**, from its start and the debts at the
front. -/
theorem stands₁_at (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (U : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl Empty (Common W₀ Rc OnBytes.TableKey) X₀'
      OnBytes.TableKey)
    (hO : OverShared Xs N Pl U) (hB : Behind U 0) (ho : (U.row 0).owes = [])
    (hr : RidesPast U 0) (hfit : U.fits 12 = true)
    (hbare : ∀ blk, U.bs[0]? = some blk → (U.hs.find? fun g => g.place == blk.place) = none)
    (hE : Enters₂ (D Xs N Pl) H U w₀ rc x k R) :
    ∃ (s' : St₂) (y : List Played × Mid (Common W₀ Rc OnBytes.TableKey) X₀'),
      Thr U 1 k s' y.2 ((envOf (H.storedWords w₀ rc) (fun _ _ => none) []).add y.1) := by
  have hA : Thr U 0 k ((D Xs N Pl).start₂ x) (R.start₂ H)
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []) := hE
  have hb : ∃ b₀, U.bs[0]? = some b₀ ∧ b₀.rounds = [] ∧ b₀.oracles = [] := by
    rw [hO.bs]
    exact ⟨_, rfl, rfl, rfl⟩
  obtain ⟨b₀, e₀, hr₀, ho₀⟩ := hb
  have hf := hbare b₀ e₀
  have hd : drawsFit b₀.rounds [] = true := by
    rw [hr₀]
    rfl
  obtain ⟨y, cols, hMv, hTr⟩ := plays_quiet₂ scope hs.named U hO.bs 0 (by decide) b₀ e₀ k _ _ _
    [] [] hA hd (stop_quiet_none hf _ _) (steps_quiet_none hr₀ ho₀ hf)
  obtain ⟨s', hS⟩ := AtPublicFiles.AtFiles.accepted_front₂ Xs N Pl U (fall := fun _ _ _ => none) hO.bs b₀ e₀
    k _ _ _ [] y cols hA hd (stop_quiet_none hf _ _) rfl hMv
  exact ⟨s', y, thr_behind _ hfit (by decide) e₀ hA hd hS hTr hB (exchange_of_nil _ ho) hr
    (made_next _ hfit (by rw [hO.bs]; exact (planOk_all hs.named.plan).2.1) 0)⟩

/-- **THE SHARED THREAD STANDS AT BORDER 1.** -/
theorem stands₁ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (h : Starts₂ Xs N Pl L w₀ rc x H k R) :
    ∃ (s' : St₂) (y : List Played × Mid (Common W₀ Rc OnBytes.TableKey) X₀'),
      Thr (laid₂ Xs N Pl L w₀ rc x H.shared tb₂) 1 k s' y.2
        ((envOf (H.storedWords w₀ rc) (fun _ _ => none) []).add y.1) := by
  have hA : Thr (laid₂ Xs N Pl L w₀ rc x H.shared tb₂) 0 k ((D Xs N Pl).start₂ x) (R.start₂ H)
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []) :=
    enters₂_laid Xs N Pl L w₀ rc x H tb₂ hs scope h
  have hb : ∃ b₀, (laid₂ Xs N Pl L w₀ rc x H.shared tb₂).bs[0]? = some b₀ ∧ b₀.rounds = [] ∧
      b₀.oracles = [] := ⟨_, rfl, rfl, rfl⟩
  obtain ⟨b₀, e₀, hr, ho⟩ := hb
  have hf := h.bare b₀ e₀
  have hd : drawsFit b₀.rounds [] = true := by
    rw [hr]
    rfl
  have hfit : (laid₂ Xs N Pl L w₀ rc x H.shared tb₂).fits 12 = true := by
    have e := fits₂ H scope hs.named (rest₂ Xs N Pl L w₀ rc x)
    rw [(lengths scope hs.named).2.1] at e
    exact e
  obtain ⟨y, cols, hMv, hTr⟩ := plays_quiet₂ scope hs.named
    (laid₂ Xs N Pl L w₀ rc x H.shared tb₂) rfl 0 (by decide) b₀ e₀ k _ _ _ [] [] hA hd
    (stop_quiet_none hf _ _) (steps_quiet_none hr ho hf)
  obtain ⟨s', hS⟩ := accepted_front₂ Xs N Pl L w₀ rc x tb₂ (fun _ _ _ => none) b₀ e₀ k _ _ _ [] y
    cols hA hd (stop_quiet_none hf _ _) rfl hMv
  exact ⟨s', y, thr_behind _ hfit (by decide) e₀ hA hd hS hTr
    (behind_laid₂ Xs N Pl L w₀ rc x hs scope 0 (by decide))
    (exchange_of_nil _ (by decide : (rowsAt (rows₂.map sharedRow) 0).owes = []))
    (ridesPast₂ Xs N Pl L w₀ rc x 0 (by decide))
    (made_next _ hfit (planOk_all hs.named.plan).2.1 0)⟩

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.steps_quiet_none
#print axioms AtPublicFiles.KeyThread.stop_quiet_none
#print axioms AtPublicFiles.KeyThread.Starts₂.common
#print axioms AtPublicFiles.KeyThread.enters₂_laid
#print axioms AtPublicFiles.KeyThread.accepted_front₂
#print axioms AtPublicFiles.KeyThread.stands₁_at
#print axioms AtPublicFiles.KeyThread.stands₁
