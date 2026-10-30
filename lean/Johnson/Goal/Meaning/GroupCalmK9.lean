-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/GroupCalmK9.lean: "CALM" (GS, Johnson/Goal/Meaning/GroupCalm.lean: as many
groups, each with the same members and flags) AT KIND K9's MAKERS, AS THE PROOF FILE's SEATS NAME
THEM, at the level of a sub-protocol's decision.
  gs_of_groups, gs_modify: two ways to be calm.
  admitP_gs, addRowP_gs, takeMaskP_gs, closeLedgerP_gs, spendAsMaskP_gs, elsewhereP_gs, recvP_gs:
    the ground's calls that neither make a group nor join a message to one.
  takeN_gs, asRow_gs, door_gs: K9's door. Calm s t := GS s.st t.st.
  oneEquation_calm: the one equation. batch_calm: the batching, given that the gathered claims are
    calm.
(RunsKeep and what stands on it: Johnson/Goal/Meaning/RunsKeep.lean, which this file imports.)
BESIDE IT: Johnson/Desc/First/Link/Law/GsAt.lean says GS at the level of a step: at the one equation
and the shutting outright, at the batching and behind it under its own premise on the link;
Johnson/Desc/First/Close/Law/GroupsStay.lean has the closing. THIS FILE IS A SECOND WRITING of what
GsAt.lean proves at the step.
No soundness.
-/
import Johnson.Goal.Meaning.GroupCalm
import Johnson.Goal.Meaning.RunsKeep
import Johnson.Goal.Meaning.SizeSeated
import Johnson.Desc.BlockLaws
import Johnson.Desc.Ground.Begin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K9

variable {Cl L : Type}

/-! ## Two ways to be calm -/

theorem gs_of_groups {S S' : Statement} (h : S'.groups = S.groups) : GS S S' :=
  ⟨by rw [h], fun g => by rw [h]⟩

/-- One group is written, its members and flags are not. -/
theorem gs_modify {S S' : Statement} {g : Nat} {f : Group → Group}
    (h : S'.groups = S.groups.modify g f)
    (hf : ∀ G, (f G).members = G.members ∧ (f G).kept = G.kept) : GS S S' := by
  refine ⟨by rw [h, Array.size_modify], fun i => ?_⟩
  rw [h, Array.getElem?_modify]
  split
  · cases S.groups[i]? with
    | none => rfl
    | some G => simp [(hf G).1, (hf G).2]
  · rfl

/-! ## The ground's calls that neither make a group nor join a message to one -/

theorem admitP_gs (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row)
    (h : admitP d o rows = some d') : GS d.st d'.st := by
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, -, places, -, rfl⟩ := h
    exact gs_of_groups rfl
  · cases h

theorem addRowP_gs (d d' : DState L) (g : Nat) (row : OnBytes.Row)
    (h : addRowP d g row = some d') : GS d.st d'.st := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact gs_modify (g := g) (f := fun G => { G with rows := G.rows.push row }) rfl
      fun _ => ⟨rfl, rfl⟩
  · cases h

theorem takeMaskP_gs (d d' : DState L) (o n : Nat)
    (h : takeMaskP d o = some (n, d')) : GS d.st d'.st := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, -, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact gs_of_groups rfl
  · cases h

theorem closeLedgerP_gs (d d' : DState L) (o : Nat)
    (h : closeLedgerP d o = some d') : GS d.st d'.st := by
  unfold closeLedgerP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact gs_of_groups (Ground.closeLedgers_groups _ _)
  · cases h

theorem spendAsMaskP_gs (d d' : DState L) (o : Nat)
    (h : spendAsMaskP d o = some d') : GS d.st d'.st := by
  unfold spendAsMaskP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact gs_of_groups rfl
  · cases h

theorem elsewhereP_gs (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') : GS d.st d'.st := by
  unfold elsewhereP at h
  split at h
  · obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact gs_of_groups rfl
  · cases h

theorem recvP_gs (ft : Nat) (d d' : DState L) (sent : Array OracleNotice) (ids : Array Nat)
    (h : recvP ft d sent = some (ids, d')) : GS d.st d'.st := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, -, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact gs_of_groups rfl
  · cases h

/-! ## K9's door -/

theorem takeN_gs {X : Type} (o : Nat) : ∀ (n : Nat) (d : St X) (acc : List Nat)
    (y : List Nat × St X), takeN o n d acc = .ok y → GS d.st y.2.st
  | 0, d, acc, y, h => by
    cases h
    exact gs_refl _
  | n + 1, d, acc, y, h => by
    unfold takeN at h
    obtain ⟨x, hx, h⟩ := bindE h
    exact gs_trans (takeMaskP_gs d x.2 o x.1 (there_some hx)) (takeN_gs o n x.2 _ y h)

theorem asRow_gs {X : Type} {Rw : ReqRows} {f : ReqFrame} {q : Equation} {d : St X}
    {y : Row × St X} (h : asRow Rw f q d = .ok y) : GS d.st y.2.st := by
  unfold asRow at h
  obtain ⟨row, _, h⟩ := bindE h
  dsimp only at h
  split at h
  · cases h
    exact gs_refl _
  · obtain ⟨m, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨o, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    cases h
    exact takeN_gs o _ d [] x hx

theorem door_gs {X : Type} {owed : RowsOwed} {laid : Option Nat} {Lk : LinkCtx} {F : Fork}
    {d : St X} {o : Out X} (h : door owed laid Lk F d = .ok o) : GS d.st o.d.st := by
  unfold door at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨x, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨y, hy, h⟩ := bindE h
  obtain ⟨d', hd, h⟩ := bindE h
  cases h
  exact gs_trans (asRow_gs hy) (addRowP_gs y.2 d' _ y.1 (there_some hd))

/-- The relation on the verifier's states: the statement's groups stay calm. -/
def Calm (s t : S) : Prop := GS s.st t.st

theorem calm_refl (s : S) : Calm s s := gs_refl _

theorem calm_trans (a b c : S) (h : Calm a b) (k : Calm b c) : Calm a c := gs_trans h k

theorem calm_of_st {s t : S} (h : t.st = s.st) : Calm s t := by
  unfold Calm
  rw [h]
  exact gs_refl _

theorem calm_of_enters {s t : S} (q : Enters s t) : Calm s t := calm_of_st q.1

theorem calm_of_quiet {s t : S} (q : Quiet s t) : Calm s t := calm_of_st q.1.1

/-- **The one equation.** -/
theorem oneEquation_calm (p : Where) : Decides Calm (oneEquation (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  have k := door_gs ho
  rw [(atS_get (there_some hq)).2] at k
  exact k

/-- **The batching**, where the gatherer's run of claims is calm. -/
theorem batch_calm (p : K9.Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl Calm claims) : Whole Calm (K9.batch K9.atS p claims) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have a1 : Calm s t₁ := by
    simp only [drawAlone] at h1
    split at h1
    · obtain ⟨q, hq, h1⟩ := bindE h1
      obtain ⟨chi, _, h1⟩ := bindE h1
      obtain ⟨o, ho, h1⟩ := bindE h1
      cases h1
      show GS s.st q.d.st
      rw [(atS_get (there_some hq)).2]
      exact gs_refl _
    · cases h1
  have a2 : Calm t₁ s' := by
    simp only [adds] at h
    obtain ⟨s₀, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨F, _, h⟩ := bindE h
    cases h
    refine calm_trans _ _ _ (hcl t₁ x hx) ?_
    show GS x.2.st q.d.st
    rw [(atS_get (there_some hq)).2]
    exact gs_refl _
  exact calm_trans _ _ _ a1 a2

#print axioms gs_modify
#print axioms recvP_gs
#print axioms door_gs
#print axioms oneEquation_calm
#print axioms batch_calm

end Meaning.K2
