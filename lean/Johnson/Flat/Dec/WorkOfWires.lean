-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/Dec/WorkOfWires.lean: HOW MANY BITS OF PROOF OF WORK THE WIRES OF THE THREE FILES DECLARE: in
a written round, the number in that round's data (d.entry.work); in the rounds that send a plain part
alone, none. So where no round's data has more than n bits, no wire has.

  mostWork_app_le              two lists of rounds in a row.
  work_of_none                 a wire without a record of a test: 0 bits.
  work_wireS, work_wireSh      a written round, local or shared: d.entry.work.
  mostWork_wiresSL | Lo | Sh   a list of written rounds.
  mostWork_wqWhole             a whole file: six parts.
  mostWork_wqW                 the copy's file.
  le_mostWork_wiresSL | wqW | linkWires   the copy's file from below: every round's number is reached.
  mostWork_offlineWires | linkWires | onlineWires      at the three wire records of wireOfFullD (Johnson/Flat/Dec/WiresAtSizes.lean),
                               at any data of rounds.

Limits. Numbers that the wires declare (WireRB.work, Hiop/SoundAsIOPClearing.lean). Nothing on what a
verifier does with them.
-/
import Hiop.SoundAsIOPClearing
import Johnson.Prover.Law.FirstBlockAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover
open _root_.Run _root_.Run.PQ Compile.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms TypedOracleCompiler.Joined
open OnBytes.Maker
open _root_.Iop (Shape Round RAnn RoundSplits RoundSplits.app Dig)

/-! ## Tools -/

theorem mostWork_app_le {lam K n : ℕ} : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    {W : RoundsQueryLayout lam K s A} {V : RoundsQueryLayout lam K u B}, RoundsQueryLayout.mostWork s A W ≤ n →
      RoundsQueryLayout.mostWork u B V ≤ n → RoundsQueryLayout.mostWork (s ++ u) (RoundSplits.app A B) (WireSB.app W V) ≤ n
  | [], _, _, _, _, _, _, hV => hV
  | _ :: _, _, (_, _), _, (_, _), _, hW, hV =>
      max_le ((le_max_left _ _).trans hW) (mostWork_app_le ((le_max_right _ _).trans hW) hV)

theorem work_of_none {lam K : ℕ} {r : Round} {a : RAnn r} (w : WireRB lam K r a)
    (hJ : w.grJ = none) (h0 : w.gr0 = none) : w.work = 0 := by
  unfold WireRB.work
  rw [hJ, h0]
  cases a.kind <;> rfl

theorem work_of_local {lam K : ℕ} {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hk : a.kind = .lo) :
    w.work = (w.grJ.map (·.b)).getD 0 := by
  unfold WireRB.work
  rw [hk]
  cases w.grJ <;> rfl

theorem work_of_shared {lam K : ℕ} {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hk : a.kind = .sh) :
    w.work = (w.gr0.map (·.b)).getD 0 := by
  unfold WireRB.work
  rw [hk]
  cases w.gr0 <;> rfl

/-- The library's record for b bits of work has b test bits. -/
theorem bits_grOf {Wn : Type} [Inhabited Wn] (D : _root_.Iop.GrData Wn) (C P : Type) : ∀ b : ℕ,
    (((_root_.Iop.grOf D C P b).map TypedOracleCompiler.Tagged.ofGr).map (·.b)).getD 0 = b
  | 0 => rfl
  | _ + 1 => rfl

/-! ## Written rounds -/

section Rounds
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem work_wireS (d : TypedOracleCompiler.Run.PQ.RD) :
    (TypedOracleCompiler.Run.PQ.wireS C K chal d).work = d.entry.work :=
  (work_of_local _ rfl).trans (bits_grOf _ _ _ d.entry.work)

theorem work_wireSh (d : TypedOracleCompiler.Run.PQ.RD) :
    (TypedOracleCompiler.Slice.wireSh C K chal d).work = d.entry.work :=
  (work_of_shared _ rfl).trans (bits_grOf _ _ _ d.entry.work)

theorem mostWork_wiresSL {n : ℕ} : ∀ ds : List TypedOracleCompiler.Run.PQ.RD,
    (∀ d ∈ ds, d.entry.work ≤ n) →
    RoundsQueryLayout.mostWork _ _ (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds) ≤ n
  | [], _ => Nat.zero_le _
  | d :: ds, h =>
      max_le ((work_wireS C K chal d).le.trans (h d (List.mem_cons_self ..)))
        (mostWork_wiresSL ds fun e he => h e (List.mem_cons_of_mem _ he))

theorem mostWork_wiresLo {n : ℕ} : ∀ ds : List RDT, (∀ d ∈ ds, d.entry.work ≤ n) →
    RoundsQueryLayout.mostWork _ _ (wiresLo C K chal ds) ≤ n
  | [], _ => Nat.zero_le _
  | d :: ds, h =>
      max_le ((work_wireS C K chal d.toRD).le.trans (h d (List.mem_cons_self ..)))
        (mostWork_wiresLo ds fun e he => h e (List.mem_cons_of_mem _ he))

theorem mostWork_wiresSh {n : ℕ} : ∀ ds : List RDT, (∀ d ∈ ds, d.entry.work ≤ n) →
    RoundsQueryLayout.mostWork _ _ (wiresSh C K chal ds) ≤ n
  | [], _ => Nat.zero_le _
  | d :: ds, h =>
      max_le ((work_wireSh C K chal d.toRD).le.trans (h d (List.mem_cons_self ..)))
        (mostWork_wiresSh ds fun e he => h e (List.mem_cons_of_mem _ he))

/-- From below: every written round's bits are among the wires'. -/
theorem le_mostWork_wiresSL : ∀ ds : List TypedOracleCompiler.Run.PQ.RD, ∀ d ∈ ds,
    d.entry.work ≤ RoundsQueryLayout.mostWork _ _ (TypedOracleCompiler.Run.PQ.wiresSL C K chal ds)
  | e :: ds, d, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact (work_wireS C K chal d).ge.trans (le_max_left _ _)
      · exact (le_mostWork_wiresSL ds d h).trans (le_max_right _ _)

/-! ## The files -/

/-- **The copy's file.** -/
theorem mostWork_wqW {n : ℕ} (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List XO) {Y : Type}
    (dec : Y → View → Bool) (h : ∀ d ∈ ds, d.entry.work ≤ n) :
    RoundsQueryLayout.mostWork (OnBytes.Flat.linkSkeletonOfRoundData C ds a xs dec).up.loc.shape
      (OnBytes.Flat.linkSkeletonOfRoundData C ds a xs dec).up.ann
      (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh ≤ n :=
  max_le ((work_of_none (TypedOracleCompiler.Run.PQ.wire0S C K chal) rfl rfl).le.trans (Nat.zero_le _))
    (mostWork_wiresSL C K chal ds h)

/-- The copy's file, from below. -/
theorem le_mostWork_wqW (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List XO) {Y : Type}
    (dec : Y → View → Bool) (d : TypedOracleCompiler.Run.PQ.RD) (h : d ∈ ds) :
    d.entry.work ≤ RoundsQueryLayout.mostWork (OnBytes.Flat.linkSkeletonOfRoundData C ds a xs dec).up.loc.shape
      (OnBytes.Flat.linkSkeletonOfRoundData C ds a xs dec).up.ann
      (Johnson.RunOne.StrictW.wqW C ds a xs dec K chal).sh :=
  (le_mostWork_wiresSL C K chal ds d h).trans (le_max_right _ _)

variable (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **A whole file.** -/
theorem mostWork_wqWhole {n : ℕ} (h : ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), d.entry.work ≤ n) :
    RoundsQueryLayout.mostWork (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wqWhole C K chal D tF tJ t3 silent run).sh ≤ n :=
  max_le ((work_of_none (wireSilent (K + 1) TF tF _) rfl rfl).le.trans (Nat.zero_le _))
    (mostWork_app_le (u := (chainsOf C D tF tJ t3).shJ) (B := (chainsOf C D tF tJ t3).annJ)
      (V := (wiresOf C K chal D tF tJ t3).shJ)
      (mostWork_wiresLo C K chal D.ds₁ fun d hd => h d (List.mem_append_left _ hd))
      (max_le ((work_of_none (wireSilent (K + 1) TJ tJ _) rfl rfl).le.trans (Nat.zero_le _))
        (mostWork_app_le (u := (chainsOf C D tF tJ t3).sh₃) (B := (chainsOf C D tF tJ t3).ann₃)
          (V := (wiresOf C K chal D tF tJ t3).sh₃)
          (mostWork_wiresSh C K chal D.ds₂ fun d hd =>
            h d (List.mem_append_right _ (List.mem_append_left _ hd)))
          (max_le ((work_of_none (wireSilent (K + 1) T3 t3 _) rfl rfl).le.trans (Nat.zero_le _))
            (mostWork_wiresLo C K chal D.ds₃ fun d hd =>
              h d (List.mem_append_right _ (List.mem_append_right _ hd)))))))

end Rounds

/-! ## The wiring of the three files at the full size -/

section Frame
open VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice

variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)
  (K depthReqT : ℕ)

local notation "WW" =>
  wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P K depthReqT

/-- **The key file's wire record** (the offline part). -/
theorem mostWork_offlineWires {n : ℕ} (h : ∀ d ∈ DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃), d.entry.work ≤ n) :
    RoundsQueryLayout.mostWork _ _ (wTC WW).sh ≤ n :=
  mostWork_wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
    ByteArray.empty silK runK h

/-- **The copy's file's** (the link). -/
theorem mostWork_linkWires {n : ℕ} (h : ∀ d ∈ ds, d.entry.work ≤ n) :
    RoundsQueryLayout.mostWork _ _ (wLC WW).sh ≤ n :=
  mostWork_wqW (ckP .two) K (chalP .two K) ds frS.P.T.a xs dec h

/-- The copy's file's, from below. -/
theorem le_mostWork_linkWires (d : TypedOracleCompiler.Run.PQ.RD) (h : d ∈ ds) :
    d.entry.work ≤ RoundsQueryLayout.mostWork _ _ (wLC WW).sh :=
  le_mostWork_wqW (ckP .two) K (chalP .two K) ds frS.P.T.a xs dec d h

/-- **The proof file's** (the online part). -/
theorem mostWork_onlineWires {n : ℕ} (h : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), d.entry.work ≤ n) :
    RoundsQueryLayout.mostWork _ _ (wBC WW).sh ≤ n :=
  mostWork_wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty silP runP h

end Frame

end OnBytes.Prover

#print axioms OnBytes.Prover.mostWork_app_le
#print axioms OnBytes.Prover.work_wireS
#print axioms OnBytes.Prover.work_wireSh
#print axioms OnBytes.Prover.mostWork_wqW
#print axioms OnBytes.Prover.mostWork_wqWhole
#print axioms OnBytes.Prover.mostWork_offlineWires
#print axioms OnBytes.Prover.mostWork_linkWires
#print axioms OnBytes.Prover.mostWork_onlineWires
#print axioms OnBytes.Prover.le_mostWork_linkWires
