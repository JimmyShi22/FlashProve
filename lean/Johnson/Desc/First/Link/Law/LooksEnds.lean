-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LooksEnds.lean: THE LAST MAKERS OF THE PROOF FILE's SEAT IN FRONT OF
WHAT STANDS BEHIND THE LAST LINK, EACH IN `KeepsLooks` (Johnson/Desc/First/Link/Law/LooksWalk.lean):
K1's
first sending · K7 as the seat lays it · K2, whole, and its four steps without a round · the step
behind the reads' sending as the lots make it. Theorems. No text already in the library turns.

  `k1First_whole`: the first segment's opening stands between two links and leaves that.
  `k7Of_whole`: `Kinds.Reply.blockOf W l`: the reply is laid beside the links' own parts.
  `k2_whole` · `headFront_keeps` («H.0.front»: the head's link is entered, NOT opened: no ledger is
    open behind) · `headOpen_makes` (**«H.1.quiet»: THE HEAD's LINK's MAKER, at the step itself**:
    `headOpenQ_fork`, K2C/HeadLedger.lean; the link's number by `front_ok`; UNDER ONE PREMISE ON THE
    PLAN: `shOf P.l` is the looks of P.X.Fp's arrays) · `finFront_keeps`, `finBehind_keeps` (the
    finish: no link is open).
  `readsBlockAt_whole`, `readsQuietAt_whole`: `ProofFile.readsQuietAt`'s value.
Limits. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.LooksClose
import Johnson.Desc.K1.First
import Johnson.Stored.ReplySeatAt
import Johnson.Top.H0.Tw.K2C.Finish
import Johnson.Desc.ProofFile.Lots.Makers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9L (ok_bind)
open VerifiableInference.Desc.First.K2

section
variable (shOf : ℕ → List Look)

/-- K1's first sending. -/
theorem k1First_whole {Cl : Type} (q : Params.First) (gp : _) :
    Whole (KeepsLooks shOf) (K1.firstSegmentOpening (Cl := Cl) q gp) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [K1.firstSegmentOpening] at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨⟨c, d⟩, _, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  exact keeps_same shOf rfl rfl

/-- K7 as the seat lays it. -/
theorem k7Of_whole (W : Verify.Public) (l : ℕ) :
    Whole (KeepsLooks shOf) (Kinds.Reply.blockOf W l) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have h' := h
  unfold Kinds.Reply.blockOf Kinds.Reply.blockAt Kinds.Reply.entered at h'
  dsimp only at h'
  split at h'
  · split at h'
    · exact nomatch h'
    · exact k7_steps shOf Kinds.Reply.seatAt (fun _ _ => ⟨rfl, rfl⟩) l 1 W.hS.V s rs gs s' h'
  · exact nomatch h'

theorem k2_whole (p : P2) : Whole (KeepsLooks shOf) (codeSwitchKind p : Block S Unit) :=
  ⟨k2_steps shOf p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- «H.0.front»: the head's link is entered, not opened. -/
theorem headFront_keeps (tl : HTailF2) : Fn (KeepsLooks shOf) (headFrontQ tl) := by
  intro s s' h
  unfold headFrontQ at h
  split at h
  · exact nomatch h
  · rename_i hb
    split at h
    · exact nomatch h
    · obtain ⟨x, _, h⟩ := Keeps.ebind_ok h
      obtain ⟨s₁, h1, h⟩ := Keeps.ebind_ok h
      have hB : s.atBetween = true := by simpa using hb
      have e1 : s.enterHead tl = s₁ := ((S.unmarked_ok _ _).1 h1).1
      unfold S.enterHead at e1
      rw [if_pos hB] at e1
      rw [← e1] at h
      dsimp only at h
      rw [← Except.ok.inj h]
      exact keeps_none shOf rfl

/-- **«H.1.quiet»: THE HEAD's LINK's MAKER.** -/
theorem headOpen_makes (P : HeadPar) (hsh : shOf P.l = P.X.Fp.trees.toList.map look) :
    Fn (KeepsLooks shOf) (headOpenQ P) := by
  intro s s' h
  obtain ⟨a2, st, f, mine, L, out, y, cov, s₁, b, q⟩ := (headOpenQ_iff P s s').1 h
  obtain ⟨_, ⟨b', hb', ho⟩, _⟩ := headOpenOpens P s s' h
  obtain ⟨_, _, hL, _⟩ := Johnson.Desc.First.Walk.Law.front_ok q.front
  have hb2 : b' = { b with
      L := L
      F := Johnson.Desc.First.Walk.emptySlots
        (Johnson.Desc.First.Walk.weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns } := by
    have e := hb'
    rw [q.out'] at e
    injection e with e
    exact e.symm
  have hlink : s'.link? = some L := by
    unfold S.link?
    rw [hb']
    simp only [ho, if_true]
    rw [hb2]
  exact keeps_laid shOf { trees := P.X.Fp.trees } P.hp.ns L (headOpenQ_fork h) hlink
    (by rw [hL]; exact hsh)

/-- The finish's front: no link is open behind. -/
theorem finFront_keeps : Fn (KeepsLooks shOf) finishFrontQ := by
  intro s s' h
  unfold finishFrontQ at h
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · split at h
      · obtain ⟨s₁, _, h⟩ := Keeps.ebind_ok h
        split at h
        · rw [← Except.ok.inj h]
          exact keeps_none shOf rfl
        · exact nomatch h
      · exact nomatch h
      · exact nomatch h

theorem finBehind_keeps : Fn (KeepsLooks shOf) finishBehindQ := by
  intro s s' h
  unfold finishBehindQ at h
  split at h
  · obtain ⟨m, _, rfl⟩ := Keeps.emap_ok h
    exact keeps_none shOf rfl
  · exact nomatch h

theorem readsBlockAt_whole {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {Hp : Head.HPlanH2} {kinds : List (ℕ × ℕ)} {l : ℕ} {b : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b) : Whole (KeepsLooks shOf) b := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact readsLay_whole shOf _
  · split at h
    · cases h
      exact readsHead_whole shOf _
    · cases h

/-- The step behind the reads' sending, as the lots make it. -/
theorem readsQuietAt_whole {G : ProofFile.Ground} {l : ℕ} {X : Stages.LinkH} {piece : ℕ}
    {b : Block S Unit} (h : ProofFile.readsQuietAt G l X piece = some b) :
    Whole (KeepsLooks shOf) b := by
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact readsAtt_whole shOf h
    | exact readsBlockAt_whole shOf h
    | cases h

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k1First_whole
#print axioms VerifiableInference.Desc.LinkJoin.k7Of_whole
#print axioms VerifiableInference.Desc.LinkJoin.k2_whole
#print axioms VerifiableInference.Desc.LinkJoin.headFront_keeps
#print axioms VerifiableInference.Desc.LinkJoin.headOpen_makes
#print axioms VerifiableInference.Desc.LinkJoin.finFront_keeps
#print axioms VerifiableInference.Desc.LinkJoin.finBehind_keeps
#print axioms VerifiableInference.Desc.LinkJoin.readsQuietAt_whole
