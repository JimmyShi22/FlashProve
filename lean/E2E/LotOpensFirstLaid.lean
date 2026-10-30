-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotOpensFirstLaid.lean: for what the key file's first chain opens: the part that is
general in the letters of laid₁ (E2E/KeyRest.lean), and the depths of two senders' texts at the key file's
book. No file E2E/FirstH… is named here.

  laid_cut, pre_opens_none, laid_trees16   the thread's list, cut at the ranges' test; nothing in front of it
                  opens (IOP's pre_dry); in scope five trees are sent up to and with it
  opens_laid, declared_laid   GENERAL IN THE FILLING, THE HALVES AND THE TABLE: in scope, opensAvailable at
                  every border; DepthsDeclared at every border, where the table has the depths 22, 19, 17,
                  20 at own 1, 2, 3, 4
  depth_msg       the multiplicities' sender's text (treeTbl at multiplicitiesSending) has depth 22 at all k, w, h
  depth_rngJob    the ranges' test's text (testTbl at rangesTestJob, ok the constant yes) has the depths 19, 17, 20 at
                  all k, w, h
  depths_need     A CONTROL: IT CAN SAY NO: in scope, at a table whose depth at own 2 is not 19 as the
                  invariant reads it, DepthsAt at border 16 is false

By what. One member alone declares openings: number 15, the ranges' test; what it opens, by the kernel at the
written place (rng_opens, E2E/LotOpensFirstGround.lean). That a text answers with a table at EVERY family of
coins is the book's: at own 1 msgJob_stated (the book has just the part's count), at own 2 to 4 full_lays
(laysB at the key file's book) with IOP's members_ranges (E2E/KeyRangesLends.lean).

Limits. In scope, at the written sizes. On declared openings and on logLength alone: nothing on a table's
contents, nothing on a run. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotOpensFirstGround
import E2E.KeyRangesTrees
import E2E.KeyRangesLends
import E2E.KeyFirstSends

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

/-! ## 1 General in the letters of laid₁ -/

section
open VerifiableInference.Desc (Place)
open AtPublicFiles.KeyThread (KeyFill laid₁ pre_dry pre_length trees15)
open AtPublicFiles.AtFiles (keyFileDescription)
open AtPublicFiles.AtFiles.Full (nums_sourced)
open H2K.JointK (keyFirstPre keyFirstPost rngEntry keyFirst_cut)
open H2K.Member (nKRFull)

variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} {Z : PublicFiles}
  (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec)
  (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tb : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- The thread's list, cut at the ranges' test. -/
theorem laid_cut : (laid₁ Xs N Pl L w₀ rc x hs tb).bs =
    keyFirstPre Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N ++
      rngEntry Xs.Y.k.oneTime N :: keyFirstPost Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N :=
  keyFirst_cut _ _ _ _ _

theorem pre_opens_none :
    ∀ d ∈ (keyFirstPre Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N).flatMap (·.rounds),
      d.opens = [] :=
  fun d hd => (pre_dry _ _ _ _ _ d hd).2

/-- **In scope five trees are sent up to and with the ranges' test.** -/
theorem laid_trees16 (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    treesTo (laid₁ Xs N Pl L w₀ rc x hs tb).bs
      ((keyFirstPre Xs.Y.k.oneTime Xs.Y.D.1 Xs.Y.told.1 Xs.set N).length + 1) = 5 := by
  have e := treesTo_at_cut (laid_cut Xs N Pl L w₀ rc x hs tb) (pre_length scope hsrc.named)
    (trees15 hsrc scope)
  obtain rfl := nums_sourced hsrc scope
  exact e.trans (congrArg (2 + ·) (rngEntry_trees _))

/-- **opensAvailable at every border.** -/
theorem opens_laid (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) (n : Nat) :
    (laid₁ Xs N Pl L w₀ rc x hs tb).opensAvailable n = true := by
  have ht := laid_trees16 Xs N Pl L w₀ rc x hs tb hsrc scope
  obtain rfl := nums_sourced hsrc scope
  exact opens_of_cut _ (laid_cut Xs nKRFull Pl L w₀ rc x hs tb) rfl (pre_opens_none Xs nKRFull)
    (post_shut _ _ _ _ _) (rngEntry_opens _)
    (fun p hp => by
      obtain ⟨j, hj, hlt⟩ := openedFirst_own p hp
      exact ⟨j, hj, Nat.lt_of_lt_of_eq hlt ht.symm⟩) n

/-- **DepthsDeclared at every border**, where the table has the four depths. -/
theorem declared_laid (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hdp : ∀ p ∈ openedFirst, ∀ k w h, (tb p.1 k w h).2.logLength = p.2) (n : Nat) :
    DepthsDeclared (laid₁ Xs N Pl L w₀ rc x hs tb) n := by
  obtain rfl := nums_sourced hsrc scope
  exact declared_of_cut _ (laid_cut Xs nKRFull Pl L w₀ rc x hs tb) (pre_opens_none Xs nKRFull)
    (post_shut _ _ _ _ _) (rngEntry_opens _) hdp n

/-- **A control: it can say no.** In scope, where the table's depth at own 2, as the invariant reads it at
this state of the run, is not 19, DepthsAt at border 16 is false. -/
theorem depths_need (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) (k : Coins Bk)
    (m : Mid (Local W₀ Rc Xi Unit) X')
    (hno : ((laid₁ Xs N Pl L w₀ rc x hs tb).tableAt (.own 2) k m).2.logLength ≠ 19) :
    ¬ DepthsAt (laid₁ Xs N Pl L w₀ rc x hs tb) 16 k m := by
  have hl := pre_length scope hsrc.named
  obtain rfl := nums_sourced hsrc scope
  refine depthsAt_needs _ (laid_cut Xs nKRFull Pl L w₀ rc x hs tb)
    (Nat.lt_of_le_of_lt (Nat.le_of_eq hl) (by decide)) ?_ k m hno
  have e : ((rngEntry Xs.Y.k.oneTime nKRFull).rounds.flatMap (·.opens)).map
      (fun o => (o.2, o.1.a)) = _ := rng_opens
  rw [e]
  decide

end

/-! ## 2 The depths of T₁'s own tables -/

section
open VerifiableInference.Desc.Key (sendingPar pieces)
open AtPublicFiles.AtFiles.Full (six_sourced nums_sourced)
open AtPublicFiles.KeyBook (msgJob_stated rides_full rideMsg sendingPar_sent)
open AtPublicFiles.KeyValues (multiplicitiesSending matrixEntryOf multiplicitiesGroups oneOf)
open AtPublicFiles.KeyThread (rangesTestJob members_ranges)
open ProofFile.Honest.K1 (treeTbl)
open Lk6.AtPlan (keyFull)

variable {W₀ Rc X' : Type} {Z : PublicFiles} (K₀ : KeyPub) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights)

/-- **Own 1: depth 22, at all k, w, h.** -/
theorem depth_msg (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hK₀ : fullPub = some K₀) (own₀ : X') (k : Coins (keyBook K₀)) (w : In1 W₀ Rc)
    (h : List Fmt.Drawn) :
    (treeTbl 0 id (multiplicitiesSending (X := X') f Xs) own₀ 0 k w h).2.logLength = 22 := by
  have h6 := six_sourced hsrc scope
  have hr : (oneOf Xs).ranges = keyFull.ranges.x := h6.ranges
  have hcodes : (multiplicitiesSending (Rc := Rc) (X := X') f Xs).P.codes = keyFull.codes := h6.codes
  have hsent : (multiplicitiesSending (Rc := Rc) (X := X') f Xs).P.sent = Wf.messageOf keyFull.ranges.x := by
    show (sendingPar (oneOf Xs) pieces.msg "the lookups' own message and what rides with it"
      (Wf.messageOf (oneOf Xs).ranges) (multiplicitiesGroups Xs)).sent = _
    rw [sendingPar_sent, hr]
  rw [treeTbl_depth id (multiplicitiesSending (X := X') f Xs) own₀ 0
      (covers_of_stated (V := Unit) (keyBook K₀) (multiplicitiesSending (X := X') f Xs)
        (msgJob_stated K₀ hK₀ (oneOf Xs) ⟨h6.codes, h6.indexMasks, h6.ranges, h6.lin⟩ pieces
          (multiplicitiesGroups Xs) 1 (matrixEntryOf f) rideMsg rides_full.2.1)) k w h,
    trees_eq _ _ _ hcodes hsent, msg_logN]
  rfl

/-- **The ranges' test's text at the job rangesTestJob: the depths 19, 17, 20, at all k, w, h**: general in
the job's letters entry, groups and first, in own₀ and in n₀. -/
theorem depth_rngJob (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hK₀ : fullPub = some K₀) (entry : In1 W₀ Rc → Nat → Nat → OnBytes.Slice.GF)
    (groups : List (List Nat)) (first : Nat) (own₀ : X') (n₀ : Nat) {τ : Nat} (hτ : τ < 3)
    (k : Coins (keyBook K₀)) (w : In1 W₀ Rc) (h : List Fmt.Drawn) :
    (ProofFile.Honest.K12.testTbl 0 (rangesTestJob (X' := X') Xs N Pl entry groups first) own₀ n₀
      (fun _ _ _ => true) τ k w h).2.logLength = [19, 17, 20].getD τ 0 := by
  have hm := members_ranges (X' := X') Xs N Pl entry groups first hsrc scope
  obtain rfl := nums_sourced hsrc scope
  exact depth_rng K₀ hK₀ _ rfl hm rfl own₀ n₀ hτ k w h

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.laid_trees16
#print axioms AtPublicFiles.FirstH.Lots.opens_laid
#print axioms AtPublicFiles.FirstH.Lots.declared_laid
#print axioms AtPublicFiles.FirstH.Lots.depths_need
#print axioms AtPublicFiles.FirstH.Lots.depth_msg
#print axioms AtPublicFiles.FirstH.Lots.depth_rngJob
