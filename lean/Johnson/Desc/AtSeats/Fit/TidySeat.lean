-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/TidySeat.lean: AT THE PROOF FILE's SEAT, GENERAL IN THE
RELATION: NEW, typed by hand.
  seatKeepsF_of · seatBackF_of   the two structures at ByS R, from StQuiet R and K1.AdmitOn R;
  ASKED: hK2 (K2's sub-protocol with rounds: Fits) · hK12 (the first chain's last proximity test:
  Decides)
  descPure_fits   so every sub-protocol of the first chain's flat list: Fits (ByS R) b
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.AtSeats.Fit.TidyRow
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Means (Tidy)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl WholeF Fits andThen_fits)
open VerifiableInference.Desc.Ground (GroundQuiet By TidyStay groundQuiet_tidy admitOn_tidy
  tidyStay_begun groundKeeps_grows)
open VerifiableInference.Desc.K13.Law (StQuiet row_of_quiet)
open ProofFile (Pub)

variable {R : Statement → Statement → Prop}

/-- **The seat's makers in front of the sub-protocols behind the last link**, at a relation on the
statement that the plain functions keep, and the admitting of a sample where the rows are on the
message. Kind K2's sub-protocol with rounds is asked (hK2). -/
theorem seatKeepsF_of (K : StQuiet R) (hA : K1.AdmitOn R)
    (hK2 : ∀ p : K2.P2, p.firstTree = 0 → Fits (ByS R) (K2.codeSwitchKind p : Block S Unit)) :
    SeatKeepsF (ByS R) where
  refl := by_reflQ K
  trans := by_transQ K
  frames := fun _ h => framesOf_byQ K h
  k1First := fun q gp _ => ⟨K1.firstAtS_fits K.quiet hA q gp, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩
  k1Later := fun q gp l p m a _ => ⟨K1.commitAtS_fits K.quiet hA _ l m a, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩
  reads := fun h => whole_byQ K (readsQuietAt_quiet h)
  k3 := fun c r X cs' sh' a _ h => whole_byQ K (theStated_quiet c r X cs' sh' a h)
  k4 := fun p => whole_byQ K (blockAtC_quiet p)
  k5 := fun W l g bf _ h => whole_byQ K (k5AtN_quiet W l g bf h)
  k6 := fun h => whole_byQ K (seatedClaims_quiet h)
  k7 := fun W l => whole_byQ K (k7Of_quiet W l)
  k8 := fun p => whole_byQ K (k8Whole_quiet p)
  k11 := fun P => whole_byQ K (headMerge11_quiet P)
  closeOf := closeOf_byQ K
  batch := fun p _ hf => batchW_byQ K p hf
  k2 := fun p h0 => ⟨hK2 p h0, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  front := headFrontQ_byQ K
  openQ := fun P _ => headOpenQ_byQ K P
  finFront := finishFrontQ_byQ K
  finBehind := finishBehindQ_byQ K

/-- **The makers behind the last link.** The first chain's last proximity test is asked (hK12). -/
theorem seatBackF_of (K : StQuiet R) (hA : K1.AdmitOn R)
    (hK12 : ∀ p : K12.P12, Decides (ByS R) (K12.atFinish p)) : SeatBackF (ByS R) where
  k12 := fun _ _ => ⟨hK12 _, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M3 := fun p => ⟨K13.atM3_keeps K.quiet p, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩
  k13M4 := fun p P _ => ⟨andThen_fits (ByS R) (by_transQ K) _ _ _ rfl
      (K1.sendAtS_fits K.quiet hA P) (K13.rowsB_keeps K.quiet K13.atS _ K13.atS_lensSt p),
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- **AT THE PROOF FILE's SEAT, THE WHOLE FIRST CHAIN.** -/
theorem descPure_fits (K : StQuiet R) (hA : K1.AdmitOn R)
    (hK2 : ∀ p : K2.P2, p.firstTree = 0 → Fits (ByS R) (K2.codeSwitchKind p : Block S Unit))
    (hK12 : ∀ p : K12.P12, Decides (ByS R) (K12.atFinish p))
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ b ∈ c.blocksInOrder, b.planOk = true → Fits (ByS R) b :=
  descPure_flatF (seatKeepsF_of K hA hK2) (seatBackF_of K hA hK12) (fun _ _ => trivial) h

end Meaning.K2
