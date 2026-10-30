-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroEnds.lean: THE REMAINING MAKERS OF THE SEAT STAND IN `KeepsZero`: K1's FIRST
SENDING, K7, K2, THE HEAD's LINK's FRONT AND MAKER, THE FINISH, THE STEPS BEHIND THE READS' SENDING.
MADE BY PROGRAM FROM THE LIBRARY's Johnson/Desc/First/Link/Law/LooksEnds.lean, WITH THE ROWS' FIRST
COLUMNS (`l0s`, Johnson/P1K8R/ZeroFrame.lean) IN THE PLACE OF THE ARRAYS' LOOKS AND `KeepsZero` IN
THE PLACE OF KeepsLooks: every declaration of that file that names the looks, or leans on one that
does, under a new name; the others are called where they lie. None of the library's goals. No prover
stands in it; nothing on completeness, soundness or hiding.

  `k1First_wholeZ`, `k7Of_wholeZ`, `k2_wholeZ`, `headFront_kz`, **`headOpen_makesZ`** (BY HAND:
      under `AllZero` of the plan's ledger)
  `finFront_kz`, `finBehind_kz`, `readsBlockAt_wholeZ`, `readsQuietAt_wholeZ`
Limits. The head's link's maker's premise, `AllZero` of the plan's ledger, is shown of no plan here.
Nothing on any reached state.

-/
import Johnson.P1K8R.ZeroClose
import Johnson.Desc.First.Link.Law.LooksEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9L (ok_bind)
open VerifiableInference.Desc.First.K2
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

section

/-- K1's first sending. -/
theorem k1First_wholeZ {Cl : Type} (q : Params.First) (gp : _) :
    Whole KeepsZero (K1.firstSegmentOpening (Cl := Cl) q gp) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [K1.firstSegmentOpening] at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨⟨c, d⟩, _, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  exact kzL_same rfl rfl

/-- K7 as the seat lays it. -/
theorem k7Of_wholeZ (W : Verify.Public) (l : ℕ) :
    Whole KeepsZero (Kinds.Reply.blockOf W l) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have h' := h
  unfold Kinds.Reply.blockOf Kinds.Reply.blockAt Kinds.Reply.entered at h'
  dsimp only at h'
  split at h'
  · split at h'
    · exact nomatch h'
    · exact k7_kz Kinds.Reply.seatAt (fun _ _ => ⟨rfl, rfl⟩) l 1 W.hS.V s rs gs s' h'
  · exact nomatch h'

theorem k2_wholeZ (p : P2) : Whole KeepsZero (codeSwitchKind p : Block S Unit) :=
  ⟨k2_kz p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- «H.0.front»: the head's link is entered, not opened. -/
theorem headFront_kz (tl : HTailF2) : Fn KeepsZero (headFrontQ tl) := by
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
      exact kz_none rfl

/-- **«H.1.quiet»: THE HEAD's LINK's MAKER.** -/
theorem headOpen_makesZ (P : HeadPar) (hz : AllZero P.X.Fp) :
    Fn KeepsZero (headOpenQ P) := by
  intro s s' h
  exact kz_laid { trees := P.X.Fp.trees } P.hp.ns (headOpenQ_fork h)
    (allZero_trees (F := P.X.Fp) rfl hz)

/-- The finish's front: no link is open behind. -/
theorem finFront_kz : Fn KeepsZero finishFrontQ := by
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
          exact kz_none rfl
        · exact nomatch h
      · exact nomatch h
      · exact nomatch h

theorem finBehind_kz : Fn KeepsZero finishBehindQ := by
  intro s s' h
  unfold finishBehindQ at h
  split at h
  · obtain ⟨m, _, rfl⟩ := Keeps.emap_ok h
    exact kz_none rfl
  · exact nomatch h

theorem readsBlockAt_wholeZ {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {Hp : Head.HPlanH2} {kinds : List (ℕ × ℕ)} {l : ℕ} {b : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b) : Whole KeepsZero b := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact readsLay_wholeZ _
  · split at h
    · cases h
      exact readsHead_wholeZ _
    · cases h

/-- The step behind the reads' sending, as the lots make it. -/
theorem readsQuietAt_wholeZ {G : ProofFile.Ground} {l : ℕ} {X : Stages.LinkH} {piece : ℕ}
    {b : Block S Unit} (h : ProofFile.readsQuietAt G l X piece = some b) :
    Whole KeepsZero b := by
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact readsAtt_wholeZ h
    | exact readsBlockAt_wholeZ h
    | cases h

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k1First_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.k7Of_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.k2_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.headFront_kz
#print axioms VerifiableInference.Desc.LinkJoin.headOpen_makesZ
#print axioms VerifiableInference.Desc.LinkJoin.finFront_kz
#print axioms VerifiableInference.Desc.LinkJoin.finBehind_kz
#print axioms VerifiableInference.Desc.LinkJoin.readsBlockAt_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.readsQuietAt_wholeZ
