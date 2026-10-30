-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/LookupCOutD.lean: what the lookup's block that a typed composition holds at a caller
puts out: the written function of the record of end values, with the signature's samples and all
oracle strings handed on.

Statements and proofs. No "variable" stands in the file. [*]: a file that is not in this library.

Why. lookOutD_run, lookOutD_view and lookEnds_view (OnBytes/Tie/Pv/Lookup/Forest/FoOutD.lean) speak
of the bare typed lookup Cb.Fo.forB. A typed composition holds a KIND's block at a caller. What that
block is, read at the texts:
 * the four kinds' base reduction IS bare forB, by definition: kLookupC's field R := fun c => (forB
   Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R (Johnson/Top/H/LookupC.lean); kLookupCN is kLookupC with
   another joint behind (LookupCRows.lean); kLookupCR has the same term at r.c (LookupCRide.lean;
   lookupCR_R: rfl); kLookupCRN is kLookupCR with another joint behind (LookupCRideRows.lean;
   lookupCRN_R: rfl). NO MAP OF STATEMENTS STANDS IN A KIND. The caller's own joint R0, the entries
   msg₀ and the riders stand in the relations A and B alone: the reduction does not see them;
 * the composition's block is the kind lifted over its signature: BaseKind.toKind
   (Johnson/Top/Kind.lean), BK.ofSig (Johnson/E/KObj/Arrows.lean): R := (the base reduction).keep
   Sg.Smp Sg.ext; IOR.keep (Ior/Frame.lean) is keepX, then keepE: THE SAME SHAPE BY DEFINITION: no
   round more; the samples and the signature's oracles are handed on unchanged.
So the maps from a file's written rounds are FoOutD's own (mapsT ds _ (specF h) (rkFor h L Ex).R _),
typed at the block's shape (as lookCarryK has the carry: Johnson/Top/H/LookupPlace.lean:
"The two shapes are one by definition"), and the law goes through one step that the library has.

What the file states.
 * lookKeep_run, lookKeep_view: at ANY further state Z and further oracles F: ((forB GE h L V₀
   V₀C).R.keep Z F).red.out a τ = some ((the bare law's out-statement at a.1.1, a.1.2), a.2): at
   every typed transcript (lookOutD at forFl); at the image of a file's written rounds (lookOutE at
   endsOf of the view's rounds read in the field). Premises: the bare laws', to the letter.
 * lookKind_isKeep: the four kinds' blocks' reductions are that kept forB, at the caller's
   signature.
 * lookKind_view, lookKindR_view: lookKeep_view said at ((kLookupCN L).toKind.block c).R and at
   ((kLookupCRN L).toKind.block r).R (at kLookupC and kLookupCR the same, by lookKind_isKeep): a :
   (St₀ × Sg.Smp) × (Ex.prod Sg.ext).Str; b = ((lookOutE c.h lm jLK (placeOf mk pl) a.1.1 En,
   a.1.2), a.2), En := endsOf c.h lm jLK (the view's rounds read): SO THE RECORD STILL DETERMINES b,
   GIVEN a. It is the clause "there is a b with K.out a (M.view σ) = some b" of a block's law in the
   form that other files (on the proof file's links) offer, with b named.
 * lookRider_at: what a rider's target reads of the out-statement is the caller's state and the
   record's point: r.tgt m (lookOutE … st En, y) is AtCoords r.g r.sel r.f st (fun t => (En.zx ++
   En.zy).getD t 0) m.

The proofs. lookKeep_run, lookKeep_view: VerifiableInference.OnPublicFiles.keep_out (LookupPlace.lean),
written in full (a second law of that name stands in namespace Iop, Cb/Ent/SentOutProofs.lean[*]: an
equation with a map; it is not beneath this file's imports), at the bare law at (a.1.1, a.2.1); the
pairs' eta, by definition: the very step of look_place_top. lookKind_isKeep: rfl, four
times: toKind, BK.ofSig, keep and the four kinds are reducible. lookKind_view, lookKindR_view:
lookKeep_view at Z := Sg.Smp, F := Sg.ext. lookRider_at: Iff.rfl.

Kin, by what the conclusions say.
 * keep_out, two laws: Johnson/Top/H/LookupPlace.lean (from "the verifier beneath puts
   out"), Cb/Ent/SentOutProofs.lean[*] (an equation, with a map); keep_red_out
   (Cb/Ld/LdSigLiftProofs.lean), keepX_red_out, keepE_red_out (Ior/FrameProofsBasic.lean): the way
   back. SPENT, not typed again.
 * look_place_top, look_place_topC (LookupPlace.lean), and LookupTied.lean[*]'s like: "the block's
   verifier puts out ((x, a.1.2), a.2)" at the kind's block: under a run of the verifier program's
   Forest.pad, at the partial carry, x a letter under a premise on bare forB's out. Here: no
   program, the total image, x named.
 * look_out_tot (Johnson/Top/H/LookUnderRule.lean[*]: a file of this project that is not in this
   library): there is an
   f with ((kLookupCN [c]).toKind.block c).R.red.out a τ = some ((f a.1.1 τ, a.1.2), a.2) at every a
   and τ: THE NEAREST KIN: lookKeep_run IS ITS SHARPENING: f WRITTEN, under FoNums.ok and the
   layout's two laws.
 * look_leaves (Johnson/Top/H/LookNoTree.lean[*]: not in the build that the nets below went over, nor in this library):
   from "puts out a'": the samples and the signature's oracles are left. lookupC_total
   (LookupCFmt.lean[*]): the base reduction's out is some. FirstMet.atSigma
   (ClauseOfPlacesLookupPinnedMet.lean[*]) and LookStationsAtTau.lean[*]'s like: the
   right side's shape at the image of a passing transcript, over the verifier program's contexts.
 * kLookupC_R (LookupCFmt.lean[*]), lookupCR_R, lookupCRN_R: "the kind's base reduction is forB's", by
   rfl. keepE_out (Course/RulesKeepE.lean[*]), a second keepE_red_out
   (OnBytes/TypedOracleCompiler/Joined/KnowBKeepE.lean[*]), red_seq_eq, red_post_out, red_pre_out
   (Cb/Pv/Lookup/Alg/TwSeq.lean): general laws of outputs; none is spent.
 The nets. One: "kLookupC…" or "toKind.block" on one line with "red.out", and "keep_out":
 over 12,290 files of one form of the library and two further sets of this project's files. A second: 38,162
 Lean files (that form of the library, other forms of it, and further sets of this project's files):
 shapes within six lines of "theorem": FIVE STATEMENTS NAME A KIND's
 REDUCTION's out, AND NO SIXTH; none gives it as a written function of the rounds. A third,
 over seven roots: no twin. None of the three is held against the library that ships.

Limits. AT LETTERS: no caller's value. MAPS OF STATEMENTS DO STAND BEHIND THE BLOCK, AS SEAMS
(stepSame … (ledAll c kp g more), LookupCRows.lean; the callers' own): they take the TX apart: they
are the taker's side: nothing here speaks of them. That a caller's layout meets the two laws (hmk,
hbc) and FoNums.ok c.h: premises (LookPubOK's masks and cells, by report).
lookOutD and lookOutE are the law's bridge: not to be built at a real size (FoOutD.lean's head). No
entry's value is read: the out-statement holds forms on entries; nothing here says that a mask entry
is read, or spent once. No test of work and no test of fit stands in a statement. No law here is
said to carry to verify().
What of the claim it touches. The public files, through c.h, c.L, lm, jLK, mk, pl, ds: letters.
a.1.1, a.1.2 and a.2 are handed through. No commitment ID, no prompt, no output token.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.LookupCRideRows
import Johnson.Top.H.LookupPlace
import OnBytes.Tie.Pv.Lookup.Forest.FoOutD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel

/-- **The kept lookup at a typed transcript.** -/
theorem lookKeep_run :
  ∀ (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh), FoNums.ok h = true →
  ∀ (L : Lay GE St₀ J₀) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀),
    (∀ s, L.mkS s = mk (jLK + s)) →
    (∀ t c j, c < h.NC →
      L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2) →
  ∀ (Ex : ExtSpec) (Z : Type) (F : ExtSpec) (a : (St₀ × Z) × (Ex.prod F).Str)
    (τ : Tr (forB GE h L V₀ V₀C (Ex := Ex)).R.shape),
    ((forB GE h L V₀ V₀C (Ex := Ex)).R.keep Z F).red.out a τ =
      some ((lookOutD h lm jLK (placeOf mk pl) (forFl h L Ex τ) a.1.1, a.1.2), a.2) :=
  fun St₀ J₀ _ _ h H L lm jLK mk pl hmk hbc Ex _ _ a τ =>
    VerifiableInference.OnPublicFiles.keep_out _ a.1.1 a.2.1 a.1.2 a.2.2 τ _ a.2.1
      (lookOutD_run GE St₀ J₀ h H L lm jLK mk pl hmk hbc Ex (a.1.1, a.2.1) τ)

/-- **The kept lookup at the image of a file's written rounds.** -/
theorem lookKeep_view :
  ∀ (St₀ J₀ : Type) [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh), FoNums.ok h = true →
  ∀ (L : Lay GE St₀ J₀) (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀),
    (∀ s, L.mkS s = mk (jLK + s)) →
    (∀ t c j, c < h.NC →
      L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2) →
  ∀ (Ex : ExtSpec) (ds : List RDT) (hM : List.Forall₂ MeetsT ds (specF h)),
    (∀ d ∈ ds, NoAns d.items) →
  ∀ (Z : Type) (F : ExtSpec) (a : (St₀ × Z) × (Ex.prod F).Str) (τ : Tr (uLT (ckP .two) ds)),
    ((forB GE h L V₀ V₀C (Ex := Ex)).R.keep Z F).red.out a
        ((mapsT ds _ (specF h) (rkFor h L Ex).R hM.length_eq).view τ) =
      some ((lookOutE h lm jLK (placeOf mk pl) a.1.1
        (endsOf h lm jLK ((rvT (ckP .two) ds τ).map (rdRV Reading.gl))), a.1.2), a.2) :=
  fun _ _ _ _ h H L lm jLK mk pl hmk hbc Ex ds hM hA _ _ a τ =>
    VerifiableInference.OnPublicFiles.keep_out _ a.1.1 a.2.1 a.1.2 a.2.2 _ _ a.2.1
      (lookEnds_view h H L lm jLK mk pl hmk hbc Ex ds hM hA (a.1.1, a.2.1) τ)

/-- The four kinds' blocks hold the kept lookup. -/
theorem lookKind_isKeep :
  (∀ (L : List LookupCCaller) (c : LookupCCaller),
    ((kLookupC L).toKind.block c).R =
        (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.keep c.Sg.Smp c.Sg.ext ∧
      ((kLookupCN L).toKind.block c).R =
        (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.keep c.Sg.Smp c.Sg.ext) ∧
  ∀ (L : List LookupCRCaller) (r : LookupCRCaller),
    ((kLookupCR L).toKind.block r).R =
        (forB Cb.Gl.E r.c.h r.c.L V₀ V₀C (Ex := r.c.Ex)).R.keep r.c.Sg.Smp r.c.Sg.ext ∧
      ((kLookupCRN L).toKind.block r).R =
        (forB Cb.Gl.E r.c.h r.c.L V₀ V₀C (Ex := r.c.Ex)).R.keep r.c.Sg.Smp r.c.Sg.ext :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩

/-- **The law at the kind's block**, at a caller. -/
theorem lookKind_view :
  ∀ (L : List LookupCCaller) (c : LookupCCaller), FoNums.ok c.h = true →
  ∀ (lm jLK : ℕ) (mk : ℕ → c.J₀) (pl : ℕ → ℕ → c.J₀),
    (∀ s, c.L.mkS s = mk (jLK + s)) →
    (∀ t k j, k < c.h.NC →
      c.L.bc t k j = pl (FoNums.cellRC c.h lm (t, k, j)).1 (FoNums.cellRC c.h lm (t, k, j)).2) →
  ∀ (ds : List RDT) (hM : List.Forall₂ MeetsT ds (specF c.h)), (∀ d ∈ ds, NoAns d.items) →
  ∀ (a : (c.St₀ × c.Sg.Smp) × (c.Ex.prod c.Sg.ext).Str) (τ : Tr (uLT (ckP .two) ds)),
    ((kLookupCN L).toKind.block c).R.red.out a
        ((mapsT ds _ (specF c.h) (rkFor c.h c.L c.Ex).R hM.length_eq).view τ) =
      some ((lookOutE c.h lm jLK (placeOf mk pl) a.1.1
        (endsOf c.h lm jLK ((rvT (ckP .two) ds τ).map (rdRV Reading.gl))), a.1.2), a.2) :=
  fun _ c H lm jLK mk pl hmk hbc ds hM hA a τ =>
    lookKeep_view c.St₀ c.J₀ c.h H c.L lm jLK mk pl hmk hbc c.Ex ds hM hA c.Sg.Smp c.Sg.ext a τ

/-- **The same at the kind with riders.** -/
theorem lookKindR_view :
  ∀ (L : List LookupCRCaller) (r : LookupCRCaller), FoNums.ok r.c.h = true →
  ∀ (lm jLK : ℕ) (mk : ℕ → r.c.J₀) (pl : ℕ → ℕ → r.c.J₀),
    (∀ s, r.c.L.mkS s = mk (jLK + s)) →
    (∀ t k j, k < r.c.h.NC →
      r.c.L.bc t k j =
        pl (FoNums.cellRC r.c.h lm (t, k, j)).1 (FoNums.cellRC r.c.h lm (t, k, j)).2) →
  ∀ (ds : List RDT) (hM : List.Forall₂ MeetsT ds (specF r.c.h)), (∀ d ∈ ds, NoAns d.items) →
  ∀ (a : (r.c.St₀ × r.c.Sg.Smp) × (r.c.Ex.prod r.c.Sg.ext).Str) (τ : Tr (uLT (ckP .two) ds)),
    ((kLookupCRN L).toKind.block r).R.red.out a
        ((mapsT ds _ (specF r.c.h) (rkFor r.c.h r.c.L r.c.Ex).R hM.length_eq).view τ) =
      some ((lookOutE r.c.h lm jLK (placeOf mk pl) a.1.1
        (endsOf r.c.h lm jLK ((rvT (ckP .two) ds τ).map (rdRV Reading.gl))), a.1.2), a.2) :=
  fun _ r H lm jLK mk pl hmk hbc ds hM hA a τ =>
    lookKeep_view r.c.St₀ r.c.J₀ r.c.h H r.c.L lm jLK mk pl hmk hbc r.c.Ex ds hM hA r.c.Sg.Smp
      r.c.Sg.ext a τ

/-- What a rider's target reads of the out-statement: the caller's state and the record's point. -/
theorem lookRider_at :
  ∀ (r : LookupCRCaller) (lm jLK : ℕ) (ι : Fo.Pl → Option r.c.J₀) (st : r.c.St₀)
    (En : Ends Cb.Gl.E)
    (y : r.c.Ex.Str) (m : r.c.Sg.Msg),
    r.tgt m (lookOutE r.c.h lm jLK ι st En, y) ↔
      AtCoords r.g r.sel r.f st (fun t => (En.zx ++ En.zy).getD t 0) m :=
  fun _ _ _ _ _ _ _ _ => Iff.rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.lookKeep_run
#print axioms VerifiableInference.OnPublicFiles.lookKeep_view
#print axioms VerifiableInference.OnPublicFiles.lookKind_isKeep
#print axioms VerifiableInference.OnPublicFiles.lookKind_view
#print axioms VerifiableInference.OnPublicFiles.lookKindR_view
#print axioms VerifiableInference.OnPublicFiles.lookRider_at
