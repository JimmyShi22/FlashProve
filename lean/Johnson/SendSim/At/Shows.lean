-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Shows.lean: at a Seated side, for challenges that its rounds can sample, what the
honest sender discloses is shownR at the data that the job reads, and what its simulator outputs is
shownR at no data, each as a function of the coins. Both are the error value if the job does not fit
its place. The proofs of Spec.showsAt and Spec.tellsAt.
Terms: Johnson/SendSim/At/Sim.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves, by unfolding the framework's function play. Both statements hold for each
value of the coins; no distribution is named.
  showsAt, tellsAt   Spec.showsAt, on the sender, and Spec.tellsAt, on the simulator. Both are
              written out in Johnson/SendSim/At/Member.lean.
  play_send   Let r₁ and r₂ be two rounds that agree with K1's two rounds in what play reads of them
              (shapeOf). If the job fits its place (sendFits) and the first challenge consists of
              exactly the seeds (seedsFit), play of the sender's two rounds succeeds, and what it
              discloses is shownR.
  play_misfit   If the job does not fit its place, play of the sender's two rounds fails.

Limits. The statements say that what is disclosed is the function shownR of the coins. They say
nothing about the values of shownR.

How it fits. Johnson/SendSim/At/Joins.lean uses showsAt and tellsAt for sendExactAt
(Johnson/SendSim/At/ExactAt.lean). Johnson/SendSim/At/JoinFresh.lean and
Johnson/SendSim/At/FreshWide.lean use showsAt for the field fresh at a Seated side, on the way to
sendFreshAtWide (Johnson/SendSim/Seat/HandedWideProofs.lean). The proofs rest on fits_seed,
fits_answer and length_answers (Johnson/SendSim/At/Shapes.lean) and play_two
(Johnson/Desc/ProofFile/Honest/Law/ToyPlay.lean).

The other names.
  rows_zero, rows_one   the rows that the sender makes in its first and in its second round are
              rowsR at the data that J reads at the state before the sender's rounds.
  tell_err    a round whose Move.say returns an error makes Step.tell fail.
  drawsFit_two   challenges that two rounds can sample are a list of two.
  seated_two  what Seated gives: σ's member has two rounds that agree with K1's in shapeOf, and ds
              has two challenges. Of the field fits it uses only the lengths.
-/
import Johnson.SendSim.At.Member
import Johnson.SendSim.At.Shapes
import Johnson.Desc.ProofFile.Honest.Law.ToyPlay

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt answers held)

variable {S Cl V W X Pb : Type}

/-- The rows that the sender makes in its first round, at the state m, are rowsR at the data that J
reads at m. -/
theorem rows_zero (J : SendJob W X) (c : Cs (dueR J.P J.ride)) (m : Mid W X) :
    J.rows c m.shown m.st 0 = rowsR J.P J.ride (J.data m.st.input (frontOf m)) c := by
  simp [SendJob.rows, frontOf, Seen.front, Mid.shown]

/-- The rows that the sender makes in its second round, after one more round x and challenge d, are
the same: rowsR at the data that J reads at m. -/
theorem rows_one (J : SendJob W X) (c : Cs (dueR J.P J.ride)) (m : Mid W X) (x : Fmt.RoundView)
    (d : Fmt.Drawn) :
    J.rows c ⟨m.seen ++ [x], m.opened⟩ ⟨m.st.input, m.st.heard ++ [d], m.st.own⟩ 1 =
      rowsR J.P J.ride (J.data m.st.input (frontOf m)) c := by
  simp [SendJob.rows, frontOf, Seen.front, Mid.shown]

/-- If r₁ and r₂ agree with K1's two rounds in shapeOf, the job fits its place (sendFits) and the
first challenge consists of exactly the seeds (seedsFit), then play of the sender's two rounds at
r₁, r₂ succeeds, and what it discloses at the positions asks is shownR at the data that J reads at
m. -/
theorem play_send (J : SendJob W X) (name : String) (a : Addr)
    (r₁ r₂ : Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle) (v : Option V)
    (c : Cs (dueR J.P J.ride)) (m : Mid W X) (d₀ d₁ : Fmt.Drawn) (asks : List (List (List Nat)))
    (h₁ : shapeOf r₁ = shapeOf ({ entry := K1.seedEntry J.P }, (K1.oracles J.P).headD []))
    (h₂ : shapeOf r₂ = shapeOf ({ entry := K1.answerEntry J.P }, []))
    (hf : sendFits J.P J.ride = true) (hd : seedsFit J.P [d₀, d₁] = true) :
    (play ((sendPart (V := V) J).steps name a [r₁, r₂] v (c, (), ())) [d₀, d₁] [] m).toOption.map
        (fun y => ProofFile.Honest.shownOf y.1 asks) =
      some (shownR J.P J.first J.ride (J.data m.st.input (frontOf m)) [d₀, d₁] asks c) := by
  have hp := play_two (W := W) (X := X)
    (s₀ := ((sendPart (V := V) J).steps name a [r₁, r₂] v (c, (), ()))[0]'(Nat.zero_lt_succ 1))
    (s₁ := ((sendPart (V := V) J).steps name a [r₁, r₂] v (c, (), ()))[1]'(Nat.lt_succ_self 1))
    (d₀ := d₀) (d₁ := d₁) (m := m)
    (mv₀ := ⟨fun _ s t =>
      if !sendFits J.P J.ride then .error "K1: the job does not fit its place" else
      .ok ⟨[], treeTables J.P (J.rows c s t 0)⟩, fun t => t.own⟩)
    (mv₁ := ⟨fun _ s t =>
      if !sendFits J.P J.ride then .error "K1: the job does not fit its place" else
      if !seedsFit J.P (t.lately 1) then .error "K1: the challenge does not hold the seeds" else
      .ok ⟨(answers J.P (stAt J.P J.first) J.first
          (held (fun _ _ _ => 0) J.first J.P (J.rows c s t 1))
          (seedsAt J.P (t.lately 1))).map fun a => .answer (toE a), []⟩, fun t => t.own⟩)
    (z₀ := ⟨[], treeTables J.P (rowsR J.P J.ride (J.data m.st.input (frontOf m)) c)⟩)
    (z₁ := ⟨(answers J.P (stAt J.P J.first) J.first
          (held (fun _ _ _ => 0) J.first J.P (rowsR J.P J.ride (J.data m.st.input (frontOf m)) c))
          (seedsAt J.P [d₀, d₁])).map fun a => .answer (toE a), []⟩)
    (fun _ _ => rfl) (fun _ _ => by cases v <;> rfl) rfl
    (by simp only [hf, Bool.not_true, Bool.false_eq_true, if_false, rows_zero])
    (fits_seed J.P _ r₁ h₁)
    (fun _ _ => rfl) (fun _ _ => by cases v <;> rfl) rfl
    (by
      have hd' : seedsFit J.P [d₀] = true := hd
      have hs' : seedsAt J.P [d₀] = seedsAt J.P [d₀, d₁] := rfl
      simp [Mid.after, State.hears, State.lately, SendJob.rows, frontOf, Seen.front, Mid.shown, hf,
        hd', hs'])
    (fits_answer J.P _ (length_answers _ _ _ _ _) r₂ h₂)
  have hs : (sendPart (V := V) J).steps name a [r₁, r₂] v (c, (), ()) =
      [((sendPart (V := V) J).steps name a [r₁, r₂] v (c, (), ()))[0]'(Nat.zero_lt_succ 1),
       ((sendPart (V := V) J).steps name a [r₁, r₂] v (c, (), ()))[1]'(Nat.lt_succ_self 1)] := rfl
  rw [hs, hp]
  simp [Except.toOption, ProofFile.Honest.shownOf, shownR, playedOf, asked, List.zipIdx_map,
    Function.comp_def]

/-- If a round's part does not abort and its Move.say returns the error e, Step.tell fails with that
error. -/
theorem tell_err {s : Step W X} {b : Option Fmt.RoundView} {m : Mid W X} {mv : Move Unit W X} {e : String}
    (hst : s.stop m.loc s.nth = none) (hmv : s.move = some mv)
    (hz : mv.say () m.shown m.st = .error e) :
    s.tell b m = .error ⟨.unfit, s.name ++ ": " ++ e⟩ := by
  simp [Step.tell, hst, hmv, hz]

/-- A list of challenges that two rounds can sample (drawsFit) has exactly two members. -/
theorem drawsFit_two {a₁ a₂ : Fmt.DeclaredRound} {ds : List Fmt.Drawn}
    (hd : drawsFit [a₁, a₂] ds = true) : ∃ d₀ d₁, ds = [d₀, d₁] := by
  cases ds with
  | nil => simp [drawsFit] at hd
  | cons d₀ t =>
    cases t with
    | nil => simp [drawsFit] at hd
    | cons d₁ t' =>
      cases t' with
      | nil => exact ⟨d₀, d₁, rfl⟩
      | cons _ _ => simp [drawsFit] at hd

/-- If the job does not fit its place, play of the sender's two rounds fails, so its result as an
Option is none. -/
theorem play_misfit (J : SendJob W X) (name : String) (a : Addr)
    (r₁ r₂ : Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle) (v : Option V)
    (c : Cs (dueR J.P J.ride)) (m : Mid W X) (d₀ d₁ : Fmt.Drawn)
    (hf : sendFits J.P J.ride = false) :
    (play ((sendPart (V := V) J).steps name a [r₁, r₂] v (c, (), ())) [d₀, d₁] [] m).toOption =
      none := by
  have hs : (sendPart (V := V) J).steps name a [r₁, r₂] v (c, (), ()) =
      [((sendPart (V := V) J).steps name a [r₁, r₂] v (c, (), ()))[0]'(Nat.zero_lt_succ 1),
       ((sendPart (V := V) J).steps name a [r₁, r₂] v (c, (), ()))[1]'(Nat.lt_succ_self 1)] := rfl
  have ht := tell_err (b := ([] : List Fmt.RoundView).head?) (m := m)
    (s := ((sendPart (V := V) J).steps name a [r₁, r₂] v (c, (), ()))[0]'(Nat.zero_lt_succ 1))
    (mv := ⟨fun _ s t =>
      if !sendFits J.P J.ride then .error "K1: the job does not fit its place" else
      .ok ⟨[], treeTables J.P (J.rows c s t 0)⟩, fun t => t.own⟩)
    (e := "K1: the job does not fit its place")
    (stop_none (fun _ _ => rfl) (fun _ _ => by cases v <;> rfl) _ _) rfl (by simp [hf])
  rw [hs, play, ht]
  rfl

/-- If σ is Seated at J and its rounds can sample ds, then memberAt σ J has two rounds, which agree
with K1's two rounds in shapeOf, and ds has two challenges. -/
theorem seated_two {σ : Side S Cl V W X Pb} {J : SendJob W X} (h : Seated σ J)
    {ds : List Fmt.Drawn} (hd : drawsFit σ.block.rounds ds = true) :
    ∃ r₁ r₂ d₀ d₁, (memberAt σ J).rounds = [r₁, r₂] ∧ ds = [d₀, d₁] ∧
      shapeOf r₁ = shapeOf ({ entry := K1.seedEntry J.P }, (K1.oracles J.P).headD []) ∧
      shapeOf r₂ = shapeOf ({ entry := K1.answerEntry J.P }, []) := by
  have hfit := h.fits
  simp only [Side.fits, Side.half, Placed.rounds, h.row, Bool.and_eq_true, beq_iff_eq] at hfit
  have hr : σ.block.rounds.length = 2 := hfit.1.2.symm
  have ho : σ.block.oracles.length = 2 := hfit.2.trans hr
  obtain ⟨a₁, a₂, ha⟩ : ∃ a₁ a₂, σ.block.rounds = [a₁, a₂] := by
    match σ.block.rounds, hr with
    | [a₁, a₂], _ => exact ⟨a₁, a₂, rfl⟩
  obtain ⟨o₁, o₂, hoo⟩ : ∃ o₁ o₂, σ.block.oracles = [o₁, o₂] := by
    match σ.block.oracles, ho with
    | [o₁, o₂], _ => exact ⟨o₁, o₂, rfl⟩
  have hsh := h.shape
  rw [ha, hoo, roundsOf_eq] at hsh
  rw [ha] at hd
  obtain ⟨d₀, d₁, hds⟩ := drawsFit_two hd
  refine ⟨(a₁, o₁), (a₂, o₂), d₀, d₁, ?_, hds, ?_, ?_⟩
  · show (σ.block.rounds.zip σ.block.oracles).take 2 = _
    rw [ha, hoo]
    rfl
  · exact List.head_eq_of_cons_eq hsh
  · exact List.head_eq_of_cons_eq (List.tail_eq_of_cons_eq hsh)

/-- Proof of Spec.showsAt, from play_send and play_misfit. -/
theorem showsAt : Spec.showsAt := by
  intro S Cl V W X Pb φ σ J h m ds asks c hd
  obtain ⟨r₁, r₂, d₀, d₁, hr, hds, h₁, h₂⟩ := seated_two h hd
  subst hds
  show (play ((sendPart (V := V) J).steps σ.block.name ⟨σ.block.place, 0⟩ (memberAt σ J).rounds
    (φ.sees m.st.input) (c, (), ())) [d₀, d₁] [] m).toOption.map
      (fun y => ProofFile.Honest.shownOf y.1 asks) = _
  rw [hr]
  by_cases hf : sendFits J.P J.ride = true
  · rw [if_pos hf]
    exact play_send J _ _ r₁ r₂ _ c m d₀ d₁ asks h₁ h₂ hf (h.draws _ hd).1
  · rw [if_neg hf, play_misfit J _ _ r₁ r₂ _ c m d₀ d₁ (by simpa using hf)]
    rfl

/-- Proof of Spec.tellsAt, from play_send and play_misfit at the job without data (bare). -/
theorem tellsAt : Spec.tellsAt := by
  intro S Cl V W X Pb φ σ J h w front ds asks c hd
  obtain ⟨r₁, r₂, d₀, d₁, _, hds, _, _⟩ := seated_two h hd
  subst hds
  show (play ((sendPart (V := Empty) (bare J.P J.first J.ride)).steps "" ⟨σ.block.place, 0⟩
    (roundsOf J.P) none (c, (), ())) [d₀, d₁] [] standIn).toOption.map
      (fun y => ProofFile.Honest.shownOf y.1 asks) = _
  rw [roundsOf_eq]
  by_cases hf : sendFits J.P J.ride = true
  · rw [if_pos hf]
    exact play_send (bare J.P J.first J.ride) _ _ _ _ _ c standIn d₀ d₁ asks rfl rfl hf
      (h.draws _ hd).1
  · rw [if_neg hf, play_misfit (bare J.P J.first J.ride) _ _ _ _ _ c standIn d₀ d₁
      (by simpa using hf)]
    rfl

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.play_send
#print axioms OnBytes.SendSim.At.play_misfit
#print axioms OnBytes.SendSim.At.seated_two
#print axioms OnBytes.SendSim.At.showsAt
#print axioms OnBytes.SendSim.At.tellsAt
#print axioms OnBytes.SendSim.At.rows_zero
#print axioms OnBytes.SendSim.At.rows_one
#print axioms OnBytes.SendSim.At.tell_err
#print axioms OnBytes.SendSim.At.drawsFit_two
