-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/CrK6.lean: K6, THE OUTPUT HEAD's OWN ROUNDS: an accepting decision is `KeepsCr`.

One of nine files (Honest/K9/CrAre.lean, CrFl, CrWalk, CrK4, CrK5, CrK6, CrSeated, CrVia, CrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves what the batching's draw will test of the
ledger (`cr`) and of the segment's book-keeping (`lnk`). The walk through each sub-protocol's text is the library's own walk for
the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files Slots*.lean beside it), carried over by program
to the reading `cr`, name by name, and righted by hand where the ground fact is another.

Limits. One direction: from an accepting decision. Nothing on the runs of claims unless it is said. This file proves no property
of a prover or a protocol.
-/
import Johnson.Desc.Kinds.Law.KeepsTrees
import Johnson.Desc.ProofFile.Honest.K9.CrWalk
import Johnson.Desc.First.Link.Law.LooksK6
import Johnson.Desc.First.Link.Law.LooksWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (cr cr_core)

theorem hideRun_cr {F G : Fork} {first : Nat} {v : Array E} {k : E}
    (h : F.hideRun first v k = some G) : cr G = cr F :=
  cr_core (OnBytes.Desc.First.K4.hideRun_core h)

/-- Wherever the hearing returns, its ledger has the reading of the ledger in front. -/
def KeepsCrH {α : Type} (x : Hear α) : Prop :=
  ∀ F rs a G left, x F rs = some (a, G, left) → cr G = cr F

theorem keepsCr_bind {α β : Type} {x : Hear α} {f : α → Hear β} (hx : KeepsCrH x)
    (hf : ∀ a, KeepsCrH (f a)) : KeepsCrH (x >>= f) := by
  intro F rs b G left h
  obtain ⟨a, G1, l1, h1, h2⟩ := bind_some h
  exact (hf a _ _ _ _ _ h2).trans (hx _ _ _ _ _ h1)

theorem keepsCr_pure {α : Type} (a : α) : KeepsCrH (pure a : Hear α) := by
  intro F rs b G left h
  obtain ⟨_, rfl, _⟩ := pure_some h
  rfl

theorem keepsCr_need {α : Type} (x : Option α) : KeepsCrH (Hear.need x) := by
  intro F rs b G left h
  obtain ⟨_, rfl, _⟩ := need_some h
  rfl

theorem keepsCr_round (n k : Nat) : KeepsCrH (Hear.round n k) := by
  intro F rs b G left h
  unfold Hear.round at h
  cases rs with
  | nil => cases h
  | cons r l =>
    dsimp only at h
    cases hr : Part.MaskedSum.roundOf n k r with
    | none => rw [hr] at h; cases h
    | some v =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]

theorem keepsCr_hide (v : List E) : KeepsCrH (hide v) := by
  intro F rs b G left h
  unfold hide at h
  cases hr : ({ F with next := F.next + v.length } : Fork).hideRun F.next v.toArray
      OnBytes.oneE with
  | none => rw [hr] at h; cases h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
    have e := hideRun_cr hr
    exact e

theorem keepsCr_drawPoint (n : Nat) : KeepsCrH (drawPoint n) :=
  keepsCr_bind (keepsCr_round 0 n) fun _ => keepsCr_pure _

theorem keepsCr_sendThenBatch (n rows : Nat) : KeepsCrH (sendThenBatch n rows) := by
  unfold sendThenBatch
  refine keepsCr_bind (keepsCr_round n 1) fun x => ?_
  obtain ⟨v, g⟩ := x
  exact keepsCr_bind (keepsCr_hide v) fun _ => keepsCr_bind (keepsCr_need _) fun _ => keepsCr_pure _

/-- The part's hearing of a sumcheck. -/
theorem keepsCr_heardBy (lead : Nat) (C : Array Hid → Form) (z : Point) (ends : Nat) :
    KeepsCrH (heardBy lead C z ends) := by
  intro F0 t b F1 left h
  unfold heardBy at h
  obtain ⟨rs, Fx, l0, h1, k1⟩ := bind_some h
  have hFx : F0 = Fx := by
    unfold Hear.stretch at h1
    split at h1
    · cases h1
    · simp only [Option.some.injEq, Prod.mk.injEq] at h1
      exact h1.2.1
  subst hFx
  obtain ⟨ld, Fy, l1, h2, k2⟩ := bind_some k1
  obtain ⟨_, rfl, rfl⟩ := need_some h2
  obtain ⟨c', Fa, l2, h3, k3⟩ := bind_some k2
  have L1 : cr Fa = cr F0 := keepsCr_hide ld _ _ _ _ _ h3
  obtain ⟨Fl, Fz, l3, h4, k4⟩ := bind_some k3
  obtain ⟨rfl, rfl, rfl⟩ := ledger_some h4
  obtain ⟨hG, Fw, l4, h5, k5⟩ := bind_some k4
  obtain ⟨e5, rfl, rfl⟩ := need_some h5
  obtain ⟨hd, G⟩ := hG
  dsimp only at k5
  obtain ⟨_, Tt, R, _, _, _, hrun2⟩ := Part.MaskedSum.hear_spec e5
  have L2 : cr G = cr Fa := by
    have e := hideRun_cr hrun2
    exact e
  obtain ⟨Fr, Fv, l5, h6, k6⟩ := bind_some k5
  obtain ⟨e6, rfl, rfl⟩ := need_some h6
  have L3 : cr Fr = cr G := hideRun_cr e6
  obtain ⟨u, Fu, l6, h7, k7⟩ := bind_some k6
  obtain ⟨rfl, rfl⟩ := lay_some h7
  obtain ⟨es, Ft, l7, h8, k8⟩ := bind_some k7
  obtain ⟨rfl, rfl, _⟩ := hiddenFrom_some h8
  obtain ⟨_, rfl, _⟩ := pure_some k8
  exact (L3.trans L2).trans L1

theorem keepsCr_sumcheck (z : Point) (ends : Nat) : KeepsCrH (sumcheck z ends) := by
  unfold sumcheck
  refine keepsCr_bind (keepsCr_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  exact keepsCr_pure _

theorem keepsCr_level (z : Point) (start : Form) : KeepsCrH (level z start) := by
  unfold level
  refine keepsCr_bind (keepsCr_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  refine keepsCr_bind (keepsCr_round 0 1) fun y => ?_
  obtain ⟨a, g⟩ := y
  exact keepsCr_bind (keepsCr_need _) fun _ => keepsCr_pure _

section Classes
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

theorem keepsCr_normRest (pV : Point) : KeepsCrH (Norm.hearRest pV) := by
  unfold Norm.hearRest
  refine keepsCr_bind (keepsCr_sendThenBatch _ _) fun x => ?_
  obtain ⟨W, gam⟩ := x
  refine keepsCr_bind ?_ fun rhoI => ?_
  · exact keepsCr_pure _
  refine keepsCr_bind (keepsCr_level _ _) fun sq => ?_
  refine keepsCr_bind (keepsCr_sendThenBatch _ _) fun y => ?_
  obtain ⟨P, om⟩ := y
  exact keepsCr_bind (keepsCr_sumcheck _ _) fun _ => keepsCr_pure _

theorem keepsCr_norm : KeepsCrH Norm.hear :=
  keepsCr_bind (keepsCr_drawPoint _) fun pV => keepsCr_normRest pV

theorem keepsCr_final : KeepsCrH FinalNorm.hear :=
  keepsCr_bind (keepsCr_sumcheck _ _) fun _ => keepsCr_pure _

/-- **The head's whole hearing.** -/
theorem keepsCr_hear : KeepsCrH hear :=
  keepsCr_bind keepsCr_norm fun _ => keepsCr_bind keepsCr_final fun _ =>
    keepsCr_bind (keepsCr_sumcheck _ _) fun _ => keepsCr_pure _

end Classes

/-- **The decision of K6's block at S leaves the ledger's reading.** -/
theorem blockAt_cr (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    cr ((seatAt h iU3).ledger s') = cr ((seatAt h iU3).ledger s) := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
      (seatAt h iU3) s rs = .ok s' := hd
  obtain ⟨g, H, F, left, w, s1, s2, _, hh, e1, e2, hs⟩ := decideBy_spec hd'
  rw [hs, seatAt_fit h iU3 s F H w s1 s2 e1 e2]
  exact keepsCr_hear _ _ _ _ _ hh

end VerifiableInference.Desc.Kinds.Head.Law

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head VerifiableInference.Desc.Kinds.Head.Law

/-- **K6: the output head's own rounds.** -/
theorem k6_stepsC (h : OnBytes.Model.Head.Shape) (iU3 work l : ℕ) :
    (blockAt h iU3 work l).Steps (KeepsCr) := by
  intro s rs gs s' hd
  obtain ⟨F0, F', L, a1, a2, a3, a4⟩ := k6_reads h iU3 work l s s' rs gs hd
  have ht : cr (s'.fork?.getD {}) = cr (s.fork?.getD {}) :=
    blockAt_cr h iU3 work l s s' rs gs hd
  rw [a1, a3] at ht
  refine keeps_of_casesC fun G' L' hG hL' => ⟨F0, L, a1, a2, ?_, ?_⟩
  · rw [Option.some.inj (a4.symm.trans hL')]
  · rw [← Option.some.inj (a3.symm.trans hG)]
    exact id ht

/-- **So of the sub-protocol as a lot seats it.** -/
theorem k6_steps_seatedC {W : OnBytes.Model.Verify.Public} {l : ℕ}
    {ms : List (ℕ × ℕ)} {b : Block S Claim} (h : seatedClaims W l ms = some b) :
    b.Steps (KeepsCr) := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  intro s rs gs s' hd
  exact k6_stepsC W.hS i _ l s rs gs s' ((tested_decide _ _ _ _ _ _ _ _).1 hd).1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.Kinds.Head.Law.hideRun_cr
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_bind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_pure
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_need
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_round
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_hide
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_drawPoint
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_sendThenBatch
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_heardBy
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_sumcheck
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_level
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_normRest
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_norm
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_final
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsCr_hear
#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockAt_cr
#print axioms VerifiableInference.Desc.LinkJoin.k6_stepsC
#print axioms VerifiableInference.Desc.LinkJoin.k6_steps_seatedC
