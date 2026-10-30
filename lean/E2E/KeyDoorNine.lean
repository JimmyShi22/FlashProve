-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyDoorNine.lean: member 9 of the key's shared chain: its block is a seat of the job of the test on
G_u, and at a thread that stands at border 9 the seat's way in is that job's state on entry.

Why. The job's state on entry is a fold that falls back silently on a state of the shape alone
(`doorOf`, K12/JobShared.lean). A sentence at that state would say nothing of the run where the fold
failed. `enters_nine` says that at this stand the seat's way in IS the job's state: and the seat's way
in takes the thread's own state. So there the fold of the door returned what the thread folded. Four
texts written apart meet: the thread's list, its first state and stored table; the frame's `Made`; the
job of the test; the seat.

Main names.
  `jobNine`: the job: `jobLocU` at the chain's own numbers of the place, with the key's readers.
  `seat_nine`: member 9 of the chain is that job's seat.
  `enters_nine`: the field `enters` of `K12At`, from `Thr` at 9.

What stays open. Nothing says that any thread stands at 9 at this job's half. At the table's letter set to `oldArm`, `Plays` at 9 is
false wherever playable (E2E/KeyFreshTreePlace.lean): a test's own trees are not its tables. Nothing here plays the member.

NOT IN FRONT OF A LAW OVER COINS: `enters_nine` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: it stands at a run's coins `k`, and `u` ties the
thread's letters, of the first kind. None of these is the term that the committer makes. None: the
bar is flat.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeySharedQuiet
import Johnson.Desc.ProofFile.Honest.K12.JobsLocU
import Johnson.Desc.ProofFile.Honest.K12.DoorAnyRun
import Johnson.Desc.ProofFile.Honest.K12.PlayedTerm
import Johnson.Desc.ProofFile.Honest.K12.SaysYesSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyDoorNine
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K12 (frontOf)
open ProofFile.Honest.K12.Light (jobLocU door_of_called)
open OnBytes (TableKey OracleNotice TreeLay)
open VerifiableInference.Desc (Place Block foldBlocks)
open VerifiableInference.Desc.K12 (Seat.enter)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Claim sharedTests keyAsProof descriptionFromSource)
open _root_.Desc.K14 (St first frontBlock)
open _root_.Desc.K14.Honest (Eight Like flatOf_carried)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (parKey sentKey randKey threadKey)

theorem get_at {α : Type} (p : List α) (g : α) (t : List α) (n : Nat) (h : p.length = n) :
    (p ++ g :: t)[n]? = some g := by
  subst h
  simp

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- **The job of the test on G_u at the key's chain.** -/
abbrev jobNine (B : Eight (parKey Xs Pl)) :=
  (jobLocU (X := X₀) ⟨parKey Xs Pl, 0⟩ (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Pl.U) (sentKey Xs Pl)
    [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] (keyProver K).storedWords
    (fun c => K.weights c.w₀) (fun c => randKey K c.rc) none).toRun.toTest

/-- **Member 9 is the seat of that test.** -/
theorem seat_nine (B : Eight (parKey Xs Pl)) :
    (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).bs[9]? = some (H2K.JointK.keyGu Pl) ∧
      ProofFile.Honest.K12.SeatOf (H2K.JointK.keyGu Pl) (jobNine (X₀ := X₀) Xs Pl K B)
        (Seat.enter (·.gU) (·.firstMask)) VerifiableInference.Desc.K12.Seat.leave := by
  constructor
  · have hO := AtPublicFiles.KeySharedQuiet.over_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w
    rw [hO.bs]
    show (AtPublicFiles.AtFiles.flat₂ Xs.chains Pl)[9]? = _
    rw [AtPublicFiles.AtFiles.flat₂_cut]
    have hl : (H2K.JointK.keySharedPre Xs.chains Pl).length = 9 := by
      unfold H2K.JointK.keySharedPre
      rw [List.length_cons, List.length_map, AtPublicFiles.AtFiles.Full.blocksOr_eight B]
      rfl
    exact get_at _ _ _ 9 hl
  · have h := ProofFile.Honest.K12.seatOf_inside (Cl := Unit) (jobNine (X₀ := X₀) Xs Pl K B)
      (Seat.enter (·.gU) (·.firstMask)) VerifiableInference.Desc.K12.Seat.leave
    exact ⟨h.place, h.rounds, h.oracles, h.decide⟩

/-- **At a thread that stands at border 9 the seat's way in is the job's state on entry.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem enters_nine {layO : TreeLay} (hQ : Plan2 (parKey Xs Pl) (sentKey Xs Pl) layO)
    (B : Eight (parKey Xs Pl)) {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) 9 k s m E) :
    Seat.enter (·.gU) (·.firstMask) s =
      .ok ((jobNine Xs Pl K B).rec₀ m.st.input (frontOf m)) := by
  obtain ⟨hand, hfit, -, -, made, -, -⟩ := u
  obtain ⟨hsm, -, -, -, s₀, cols, hbeg, hcols, hfold⟩ := made
  have e₀ : s₀ = first (parKey Xs Pl).codes m.st.input.key := hbeg
  subst e₀
  have F := flatOf_carried (Cl := Claim) (keyAsProof Xs.chains) (parKey Xs Pl) B.b1 B.b2 B.b3 B.b4 B.b5
    B.b6 B.b7 B.b8 (sharedTests Pl) VerifiableInference.Desc.K12.Seat.last B.made
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, hxs, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have hbs : (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).bs = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := hxs
  have htake : (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).bs.take 9 = [x0, x1, x2, x3, x4, x5, x6, x7, x8] := by
    rw [hbs]
    rfl
  have hpre : List.Forall₂ Like [x0, x1, x2, x3, x4, x5, x6, x7, x8]
      [frontBlock (keyAsProof Xs.chains), B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] :=
    .cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7
      (.cons l8 .nil))))))))
  have hd : (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).ahead ++ declsTo (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).bs 9 =
      [x0, x1, x2, x3, x4, x5, x6, x7, x8].flatMap (·.rounds) := by
    have hf := congrArg (fun l : List (Block St Claim) =>
      (l.flatMap (fun x : Block St Claim => x.rounds) : List Fmt.DeclaredRound)) htake
    exact hf
  have hlen : m.seen.length = ([x0, x1, x2, x3, x4, x5, x6, x7, x8].flatMap (·.rounds)).length := by
    have e := drawsFit_length _ _ hfit
    have e2 := congrArg List.length hsm
    rw [List.length_map] at e2
    exact e2.trans (e.trans (congrArg List.length hd))
  have htk : m.seen.take ([x0, x1, x2, x3, x4, x5, x6, x7, x8].flatMap (·.rounds)).length = m.seen := by
    rw [← hlen]
    exact List.take_length
  have hst : E.stored = (keyProver K).storedWords m.st.input.w₀ m.st.input.rc :=
    funext fun i => funext fun p => hand.1 i p
  have hfold' : foldBlocks 0 [x0, x1, x2, x3, x4, x5, x6, x7, x8]
      (first (parKey Xs Pl).codes m.st.input.key)
      (m.seen.take ([x0, x1, x2, x3, x4, x5, x6, x7, x8].flatMap (·.rounds)).length) cols =
      .ok (s, [], []) := by
    rw [htk]
    exact (congrArg (fun l : List (Block St Claim) =>
      foldBlocks 0 l (first (parKey Xs Pl).codes m.st.input.key) m.seen cols) htake).symm.trans hfold
  have hfill : fillCols (readsOf 1 0 E.stored E.tree
      ([x0, x1, x2, x3, x4, x5, x6, x7, x8].flatMap (·.rounds))
      ((m.seen.take ([x0, x1, x2, x3, x4, x5, x6, x7, x8].flatMap (·.rounds)).length).map (·.drawn)))
      [] = .ok cols := by
    rw [htk, hsm]
    exact (congrArg (fun d => fillCols (readsOf 1 0 E.stored E.tree d m.st.heard) []) hd).symm.trans
      hcols
  obtain ⟨-, -, hdoor⟩ := door_of_called (V := Common W₀ Rc TableKey) (X := X₀) (keyAsProof Xs.chains)
    (parKey Xs Pl) (sentKey Xs Pl) B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hQ.facts.goes
    [x0, x1, x2, x3, x4, x5, x6, x7, x8] hpre E.stored E.tree m.st.input.key m.seen [] m.seen cols []
    cols s (List.append_nil _).symm (List.append_nil _).symm hfold' hfill
  exact hdoor (fun v => v.key) (fun v => (keyProver K).storedWords v.w₀ v.rc) m.st.input (frontOf m)
    rfl hst.symm htk.symm

end

end AtPublicFiles.KeyDoorNine

#print axioms AtPublicFiles.KeyDoorNine.get_at
#print axioms AtPublicFiles.KeyDoorNine.seat_nine
#print axioms AtPublicFiles.KeyDoorNine.enters_nine
