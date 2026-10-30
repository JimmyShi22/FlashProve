-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SlotsEnds.lean: THE ENDS.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
WHOSE: THE WALK COMES FROM LooksEnds.lean, beside this file: that file's
theorems on the arrays' looks, CARRIED OVER BY PROGRAM to the two numbers, name by name (…looks… ↦
…slots…; else a letter S behind the name), and righted by hand where the ground fact is another.
That file is imported for what it holds that does not speak of looks.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LooksEnds
import Johnson.Desc.First.Link.Law.LooksClose
import Johnson.Desc.First.Link.Law.SlotsClose
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
variable (nsOf : ℕ → ℕ × ℕ)

/-- K1's first sending. -/
theorem k1First_wholeS {Cl : Type} (q : Params.First) (gp : _) :
    Whole (KeepsSlots nsOf) (K1.firstSegmentOpening (Cl := Cl) q gp) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [K1.firstSegmentOpening] at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨⟨c, d⟩, _, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  exact keeps_sameS nsOf rfl rfl

/-- K7 as the seat lays it. -/
theorem k7Of_wholeS (W : Verify.Public) (l : ℕ) :
    Whole (KeepsSlots nsOf) (Kinds.Reply.blockOf W l) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have h' := h
  unfold Kinds.Reply.blockOf Kinds.Reply.blockAt Kinds.Reply.entered at h'
  dsimp only at h'
  split at h'
  · split at h'
    · exact nomatch h'
    · exact k7_stepsS nsOf Kinds.Reply.seatAt (fun _ _ => ⟨rfl, rfl⟩) l 1 W.hS.V s rs gs s' h'
  · exact nomatch h'

theorem k2_wholeS (p : P2) : Whole (KeepsSlots nsOf) (codeSwitchKind p : Block S Unit) :=
  ⟨k2_stepsS nsOf p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- «H.0.front»: the head's link is entered, not opened. -/
theorem headFront_keepsS (tl : HTailF2) : Fn (KeepsSlots nsOf) (headFrontQ tl) := by
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
      exact keeps_noneS nsOf rfl

/-- **«H.1.quiet»: THE HEAD's LINK's MAKER.** -/
theorem headOpen_makesS (P : HeadPar) (hsh : nsOf P.l = (P.hp.ns, P.hp.ns)) :
    Fn (KeepsSlots nsOf) (headOpenQ P) := by
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
  exact keeps_laidS nsOf { trees := P.X.Fp.trees } P.hp.ns L (headOpenQ_fork h) hlink
    (by rw [hL]; exact hsh)

/-- The finish's front: no link is open behind. -/
theorem finFront_keepsS : Fn (KeepsSlots nsOf) finishFrontQ := by
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
          exact keeps_noneS nsOf rfl
        · exact nomatch h
      · exact nomatch h
      · exact nomatch h

theorem finBehind_keepsS : Fn (KeepsSlots nsOf) finishBehindQ := by
  intro s s' h
  unfold finishBehindQ at h
  split at h
  · obtain ⟨m, _, rfl⟩ := Keeps.emap_ok h
    exact keeps_noneS nsOf rfl
  · exact nomatch h

theorem readsBlockAt_wholeS {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {Hp : Head.HPlanH2} {kinds : List (ℕ × ℕ)} {l : ℕ} {b : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b) : Whole (KeepsSlots nsOf) b := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact readsLay_wholeS nsOf _
  · split at h
    · cases h
      exact readsHead_wholeS nsOf _
    · cases h

/-- The step behind the reads' sending, as the lots make it. -/
theorem readsQuietAt_wholeS {G : ProofFile.Ground} {l : ℕ} {X : Stages.LinkH} {piece : ℕ}
    {b : Block S Unit} (h : ProofFile.readsQuietAt G l X piece = some b) :
    Whole (KeepsSlots nsOf) b := by
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact readsAtt_wholeS nsOf h
    | exact readsBlockAt_wholeS nsOf h
    | cases h

end

end VerifiableInference.Desc.LinkJoin
