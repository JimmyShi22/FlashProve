-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/RadiiSays.lean: where the maker of the seven lists of the planner's calls returns
(`callsFrom`, Johnson/Desc/First/Link/RowsRun.lean), the samples in the first proof chain's list ARE
an explicit function of the sizes of a proof file (`samplesP0`,
Johnson/HB/LLHARD/RadiiWritten.lean). A definition and statements with their proofs; nothing is
evaluated.

Why. The radii of the sampled oracle messages are computed from these samples. The maker plans every
chain twice, which Lean's kernel does not bear; the function is small.

It stands on the tools of Johnson/Desc/First/Link/Law/RowsNoArms.lean: `trace`,
`Quiet`, `run_bind_ok`, `note_run`, `trace_push` and, above all, `nArm_quiet`: a link's own routine
notes no call with a sample. That file walks two runs side by side; here one run is held against a
list.

  `Says x F`: wherever x returns, what the list of calls says of samples has grown by F.
  `says_quiet`, `says_bind`, `says_quiet_bind`, `says_bind_quiet`, `says_ite`, `says_note`,
    `says_noteV`: tools.
  `nReqSend_says`, `nStages_says`, `nIopp_says`, `nMomentsA_says`, `nFrameA_says`, `nLinFirst_says`:
    each routine of the first proof chain says its share.
  `noted_says`; `calls_say`: **the statement**: the setting is the sizes' own; there are seven
    lists; the fifth is the first proof chain's, and its samples are `samplesP0 c.sized.proof`: at
    every table of arms, every list of open rows and every number of pending rows.

Can the premise be met? Whether the maker returns is asked by no test of the verifier and given by
no theorem. Limits. The first proof chain alone. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.RowsNoArms
import Johnson.HB.LLHARD.RadiiWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open VerifiableInference.Number (sendsFrom)

/-- A noting routine says F: wherever it returns, what the list of calls says of samples has grown
by F. -/
def Says {α : Type} (x : N α) (F : List (List SampleSize)) : Prop :=
  ∀ cs p a cs' p', (x.run cs).run p = .ok ((a, cs'), p') → trace cs' = trace cs ++ F

section
variable {α β : Type}

theorem says_quiet {x : N α} (h : Quiet x) : Says x [] := fun cs p a cs' p' hr => by
  rw [h cs p a cs' p' hr, List.append_nil]

theorem says_bind {x : N α} {f : α → N β} {F G H : List (List SampleSize)} (hx : Says x F)
    (hf : ∀ a, Says (f a) G) (e : F ++ G = H) : Says (x >>= f) H := by
  intro cs p b cs' p' h
  obtain ⟨a, cs1, p1, h1, h2⟩ := run_bind_ok h
  rw [hf a cs1 p1 b cs' p' h2, hx cs p a cs1 p1 h1, List.append_assoc, e]

theorem says_quiet_bind {x : N α} {f : α → N β} {G : List (List SampleSize)} (hx : Quiet x)
    (hf : ∀ a, Says (f a) G) : Says (x >>= f) G := says_bind (says_quiet hx) hf rfl

theorem says_bind_quiet {x : N α} {f : α → N β} {F : List (List SampleSize)} (hx : Says x F)
    (hf : ∀ a, Quiet (f a)) : Says (x >>= f) F :=
  says_bind hx (fun a => says_quiet (hf a)) (List.append_nil F)

theorem says_ite {c : Prop} [Decidable c] {x y : N α} {F : List (List SampleSize)} (hx : Says x F)
    (hy : Says y F) : Says (if c then x else y) F := by
  split
  · exact hx
  · exact hy

theorem says_note (c : Call) : Says (note c) c.sendSamples := fun cs p a cs' p' hr => by
  rw [note_run hr, trace_push]

theorem says_noteV (c : Call) (y : Planning α) : Says (noteV c y) c.sendSamples :=
  fun cs p a cs' p' hr => by rw [noteV_run hr, trace_push]

end

theorem nReqSend_says (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) (ownRound : Bool) :
    Says (nReqSend codes sent group atStart riders ownRound)
      [reqSamples codes sent group atStart riders] := by
  unfold nReqSend
  dsimp only
  exact says_quiet_bind (quiet_lift _) fun _ => says_note _

theorem nStages_says (f : Nat) (m : Bool) :
    ∀ (first : Bool) (st : List StageSize), Says (nStages f m first st) (stageSamples st)
  | first, x :: y :: rest => by
    unfold nStages
    dsimp only
    refine says_quiet_bind (quiet_note rfl) fun _ => ?_
    refine says_bind (says_noteV _ _) (fun _ => ?_) (G := stageSamples (y :: rest)) ?_
    · exact says_quiet_bind (quiet_lift _) fun _ => nStages_says f m false (y :: rest)
    · rw [stageSamples]
      rfl
  | _, [x] => by
    unfold nStages
    dsimp only
    exact says_quiet (quiet_bind (quiet_noteV _ rfl) fun _ => quiet_lift _)
  | _, [] => by
    unfold nStages
    exact says_quiet (quiet_lift _)

theorem nIopp_says (st : List StageSize) (rows f : Nat) (m : Bool) :
    Says (nIopp st rows f m) (stageSamples st) := by
  unfold nIopp
  exact says_quiet_bind (quiet_lift _) fun _ =>
    says_quiet_bind (quiet_note rfl) fun _ => nStages_says f m true st

theorem nMomentsA_says (A : Nat → Arm) (z : ProofSized) (l : Nat) (msgs : List ReqMessage) :
    ∀ fuel moment, Says (nMomentsA A z l msgs fuel moment) (momentSamples z msgs fuel moment)
  | 0, _ => says_quiet (quiet_pure _)
  | fuel + 1, moment => by
    unfold nMomentsA
    dsimp only
    refine says_bind (nReqSend_says _ _ _ _ _ _) (fun _ => ?_)
      (G := momentSamples z msgs fuel (moment + 1)) ?_
    · refine says_quiet_bind (nArm_quiet _ _) fun _ => ?_
      refine says_quiet_bind (quiet_note rfl) fun _ => ?_
      exact says_bind_quiet (nMomentsA_says A z l msgs fuel (moment + 1)) fun _ => quiet_pure _
    · rw [momentSamples]
      rfl

/-- **The frame says the samples off the sizes**, at every table of arms. -/
theorem nFrameA_says (A : Nat → Arm) (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink) (open_ : List Nat)
      (before : GroupSize),
    Says (nFrameA A z l gs links open_ before) (frameSamples z l gs links)
  | [], _, _, _, _ => by
    unfold nFrameA
    exact says_quiet (quiet_pure _)
  | g :: gs, l, links, open_, before => by
    have ih := fun c => nFrameA_says A z gs (l + 1) (links.drop 1) (open_.drop 1) c
    unfold nFrameA
    rw [frameSamples]
    cases links.head? with
    | none =>
      dsimp only
      refine says_quiet_bind ?_ fun _ => ?_
      · quiet
      refine says_bind (nReqSend_says _ _ _ _ _ _) (fun _ => ?_) rfl
      refine says_ite ?_ ?_
      · refine says_quiet_bind (quiet_noteV _ rfl) fun _ => ?_
        refine says_quiet_bind (quiet_pure _) fun _ => ?_
        exact nIopp_says _ _ _ _
      · refine says_quiet_bind (quiet_pure _) fun _ => ?_
        exact nIopp_says _ _ _ _
    | some lk =>
      dsimp only
      refine says_ite ?_ ?_
      · refine says_quiet_bind (quiet_note rfl) fun _ => ?_
        refine says_quiet_bind (quiet_note rfl) fun _ => ?_
        refine says_bind (nReqSend_says _ _ _ _ _ _) (fun _ => ?_) rfl
        refine says_ite ?_ ?_
        · refine says_quiet_bind (quiet_noteV _ rfl) fun _ => ?_
          refine says_quiet_bind (quiet_pure _) fun _ => ?_
          refine says_quiet_bind (nArm_quiet _ _) fun _ => ?_
          refine says_quiet_bind (quiet_note rfl) fun _ => ?_
          refine says_bind (nMomentsA_says A z l _ _ _) (fun _ => ?_) rfl
          refine says_quiet_bind (quiet_note rfl) fun _ => ?_
          refine says_quiet_bind (quiet_note rfl) fun _ => ?_
          exact ih _
        · refine says_quiet_bind (quiet_pure _) fun _ => ?_
          refine says_quiet_bind (nArm_quiet _ _) fun _ => ?_
          refine says_quiet_bind (quiet_note rfl) fun _ => ?_
          refine says_bind (nMomentsA_says A z l _ _ _) (fun _ => ?_) rfl
          refine says_quiet_bind (quiet_note rfl) fun _ => ?_
          refine says_quiet_bind (quiet_note rfl) fun _ => ?_
          exact ih _
      · refine says_quiet_bind (quiet_pure _) fun _ => ?_
        refine says_bind (nReqSend_says _ _ _ _ _ _) (fun _ => ?_) rfl
        refine says_ite ?_ ?_
        · refine says_quiet_bind (quiet_noteV _ rfl) fun _ => ?_
          refine says_quiet_bind (quiet_pure _) fun _ => ?_
          refine says_quiet_bind (nArm_quiet _ _) fun _ => ?_
          refine says_quiet_bind (quiet_note rfl) fun _ => ?_
          refine says_bind (nMomentsA_says A z l _ _ _) (fun _ => ?_) rfl
          refine says_quiet_bind (quiet_note rfl) fun _ => ?_
          refine says_quiet_bind (quiet_note rfl) fun _ => ?_
          exact ih _
        · refine says_quiet_bind (quiet_pure _) fun _ => ?_
          refine says_quiet_bind (nArm_quiet _ _) fun _ => ?_
          refine says_quiet_bind (quiet_note rfl) fun _ => ?_
          refine says_bind (nMomentsA_says A z l _ _ _) (fun _ => ?_) rfl
          refine says_quiet_bind (quiet_note rfl) fun _ => ?_
          refine says_quiet_bind (quiet_note rfl) fun _ => ?_
          exact ih _

theorem nLinFirst_says (codes : Codes) (x : LinSized) :
    Says (nLinFirst codes x) (((linSizeOf codes x).map fun v => [v.w :: v.besideW]).getD []) := by
  unfold nLinFirst
  intro cs p a cs' p' h
  obtain ⟨v, c1, p1, h1, h2⟩ := run_bind_ok h
  generalize linSizeOf codes x = o at h1 ⊢
  cases o with
  | none => cases h1
  | some w =>
    cases h1
    rw [note_run h2, trace_push]
    rfl

/-- What `noted` returns at a routine that says F has the samples F. -/
theorem noted_says {s : Setting} {scope : Scope} {x : N Unit} {F : List (List SampleSize)}
    (hs : Says x F) {calls : List Call} {P : Planned} (h : noted s scope x = .ok (calls, P)) :
    calls.flatMap Call.sendSamples = F := by
  unfold noted at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨⟨a, cs⟩, p⟩, hr, h⟩ := exc_bind h
  cases h
  exact hs _ _ _ _ _ hr

/-- **Where the seven lists of calls are made, the first proof chain's list has the samples off
the sizes of a proof file**, at every table of arms. -/
theorem calls_say {c : Configured} {o : List Nat} {n : Nat} {A : Nat → Arm} {s : Setting}
    {ch : List Johnson.G.Chain} (h : callsFrom c o n A = .ok (s, ch)) :
    s = c.sized.set ∧ ∃ a0 a1 a2 a3 a4 a5 a6, ch = [a0, a1, a2, a3, a4, a5, a6] ∧
      a4.file = "proof" ∧ a4.chain = 0 ∧
      a4.calls.flatMap Call.sendSamples = samplesP0 c.sized.proof := by
  unfold callsFrom at h
  dsimp only at h
  generalize c.key = K at h
  generalize c.proof = P at h
  split at h
  · obtain ⟨l, hl, h⟩ := exc_bind h
    cases h
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, rfl⟩ := mapM_id7 hl
    refine ⟨rfl, a0, a1, a2, a3, a4, a5, a6, rfl, ?_⟩
    obtain ⟨⟨calls, Q⟩, hn, h4⟩ := exc_bind h4
    dsimp only at h4
    split at h4
    swap
    · obtain ⟨_, e, _⟩ := exc_bind h4
      cases e
    obtain ⟨_, _, h4⟩ := exc_bind h4
    obtain ⟨_, _, h4⟩ := exc_bind h4
    split at h4
    swap
    · obtain ⟨_, e, _⟩ := exc_bind h4
      cases e
    obtain ⟨_, _, h4⟩ := exc_bind h4
    cases h4
    refine ⟨rfl, rfl, noted_says ?_ hn⟩
    unfold samplesP0
    refine says_bind (nFrameA_says A c.sized.proof _ _ _ _ _) (fun _ => ?_) rfl
    refine says_quiet_bind (quiet_note rfl) fun _ => ?_
    refine says_ite ?_ ?_
    · refine says_quiet_bind (quiet_note rfl) fun _ => ?_
      exact says_bind_quiet (nLinFirst_says _ _) fun _ => quiet_note rfl
    · refine says_quiet_bind (quiet_pure _) fun _ => ?_
      exact says_bind_quiet (nLinFirst_says _ _) fun _ => quiet_note rfl
  · cases h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.says_quiet
#print axioms VerifiableInference.Desc.LinkJoin.says_bind
#print axioms VerifiableInference.Desc.LinkJoin.says_quiet_bind
#print axioms VerifiableInference.Desc.LinkJoin.says_bind_quiet
#print axioms VerifiableInference.Desc.LinkJoin.says_ite
#print axioms VerifiableInference.Desc.LinkJoin.says_note
#print axioms VerifiableInference.Desc.LinkJoin.says_noteV
#print axioms VerifiableInference.Desc.LinkJoin.nReqSend_says
#print axioms VerifiableInference.Desc.LinkJoin.nStages_says
#print axioms VerifiableInference.Desc.LinkJoin.nIopp_says
#print axioms VerifiableInference.Desc.LinkJoin.nMomentsA_says
#print axioms VerifiableInference.Desc.LinkJoin.nFrameA_says
#print axioms VerifiableInference.Desc.LinkJoin.nLinFirst_says
#print axioms VerifiableInference.Desc.LinkJoin.noted_says
#print axioms VerifiableInference.Desc.LinkJoin.calls_say
