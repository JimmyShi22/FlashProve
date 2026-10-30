-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/L0/PlanAtHead.lean: THE LAST TABLE's TESTS ON THE LIST OF ROUNDS (`LLT25.PlanOk₃`, 33
fields) AT THE ONE HEAD `P5J.AtMg`, AT THE JOIN's LETTERS. Theorems with their proofs; one structure
of letters; five abbreviations.

  `PlanJ`: `PlanOk₃` at the join's letters; r := `rWFull` (the field closed is had there
    alone). `ShSeven`, `ms2J`, `nsJ`: the shared table's members and numbers in their own general
    form; that `Sh.ms A` is that form: ShSevenIs.lean. `LeftJ`, `CoreJ`: `PlanLeft₃`, `PlanCore₃` there.
  **`closed_at_head`**: `closed_in_scope` (Johnson/LLT25R/LastEnd.lean) at the head: NO PREMISE IS LEFT: its pin
    is the first of the door's rows (`LPFD.asks_written` off the head's field laid.asks).
  `stretch_at_head`: ∃ dB dt, the field stretch (`LLT25.hds_of_planOk`): dB :: dt IS OPENED.
  **`planPaid₃_at_head`**: TEN OF THE 33 FROM THE HEAD ALONE: closed, stretch, someO, free0, dataIs,
    planOk, ownMask, twoStages, places, planTreeO.
  **`planOk₃_at_head`**: ∃ dB dt, `PlanJ`, from the head and `LeftJ` (23 fields), asked only at the
    dB :: dt that the stretch is.
  **`planOk₃_of_core`**: the same from `CoreJ` (14 fields and one clause) and three ends of other
    files, in their own texts (elderBelow; sampled ∧ wIn ∧ iIn; 1 < t₂).
CALLED, NOT TYPED ANEW: `closed_in_scope`, `planOk_tie`, `hds_of_planOk` (Johnson/LLT25R/);
`ownMask_in_scope_W`, `free_at_seat_W`, `place_W_of_full`, `plan_at_seat_W`,
`nums_of_planOk`; `planTreeO_of_same` (Johnson/P2LawR/; its three equations: rfl at F0T);
`LaidAt.atDepth`, `LaidAt.heads`; `hsit_sh`; `LPFD.asks_written`.
Limits. `AtMg` alone is asked (`AtMgA` gives it). A member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/); `LeftJ` | `CoreJ` are shown at no
letters: IF THEY CANNOT BE MET THE THEOREMS SAY NOTHING. Ld stays a letter. The full size alone.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.L0.PlanCore
import Johnson.P5J.MgAtAll
import Johnson.P5J.FourAtMg
import Johnson.LLT25R.LastEnd
import Johnson.LLT25R.LastStretch
import Johnson.P2LawR.PlanTreeOAtSame
import Johnson.Desc.Sound.SharedMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J.L0
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.K13 (Where)
open _root_.Desc.K14 (St)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open _root_.Desc.K14.Law.Fence (CoreFacts MemberFacts)
open H2K.Pin (NTuple)
open _root_.Desc.K14.Law.Fence (msSh numbersSh hsit_sh)
open LLT25
open H2K.JointK (descN)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-! ## The join's own letters -/

/-- **The shared table's seven letters**: its shape, three radii, its first tree's number and two
layouts. THE JOIN's: S := A.Q.S · rU := A.rad2 0 · rO := A.rad5 0 · rSp := A.rad5 1 · lo := Sh.t₁ A ·
layU := Sh.layU A · layO := Sh.layO A at A := Sh.planAt Zp Np (F0T o Zp Np cF): there `ms2J` IS
`Sh.ms A` by that definition's own text (Johnson/Desc/K14/Law/SharedConst.lean). (That file is not
imported here: its cone holds the library's twins of the Johnson/Loose/ files beneath `PlanOk₃`.) -/
structure ShSeven where
  S : OnBytes.Params.LinShape
  rU : ℕ
  rO : ℕ
  rSp : ℕ
  lo : ℕ
  layU : OnBytes.TreeLay
  layO : OnBytes.TreeLay

/-- The shared table's members. -/
abbrev ms2J (J : ShSeven) : List Mem := msSh J.S J.rU J.rO J.rSp J.lo J.layU J.layO

/-- The shared table's numbers, with (0, 0) (0, 0) as at the join. -/
abbrev nsJ (J : ShSeven) : NumbersS := numbersSh J.lo J.layU J.layO (0, 0) (0, 0)

/-- **`PlanOk₃` at the join's own letters**; r is `rWFull`. -/
abbrev PlanJ (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (J : ShSeven) (dB : RDT) (dt : List RDT)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) : Prop :=
  PlanOk₃ o ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a) (F0T o Zp Np cF) (At.arr Zp) dB dt
    (At.ms Zp Z.lay) (ms2J J) (At.N Zp cF) (nsJ J) fullLinks
    (First.flatPlaces true fullLinks true) H2K.Member.rWFull ((At.N Zp cF).treesAt none) 0 1
    (vAt Zp (At.N Zp cF)) Ld

/-- **What is left of it, by name**, at the same letters. -/
abbrev LeftJ (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (J : ShSeven) (dB : RDT) (dt : List RDT)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) : Prop :=
  PlanLeft₃ o ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a) (F0T o Zp Np cF) (At.arr Zp) dB dt
    (At.ms Zp Z.lay) (ms2J J) (At.N Zp cF) (nsJ J) fullLinks
    (First.flatPlaces true fullLinks true) H2K.Member.rWFull ((At.N Zp cF).treesAt none) 0 1
    (vAt Zp (At.N Zp cF)) Ld

/-- The field stretch's sentence at these letters: the third piece's stretch of the written rounds is
dB :: dt. -/
abbrev StretchJ (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (dB : RDT) (dt : List RDT) : Prop :=
  ds₂ (D.at frS.P.T.a).ds₃
      (held (P := (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).XiPub ×
        (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).S₁ × _root_.Desc.K14.St) (c0 Zp))
      (held (P := (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).XiPub ×
        (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).S₁ × _root_.Desc.K14.St) (c1 Np))
      (held (P := (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).XiPub ×
        (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).S₁ × _root_.Desc.K14.St) (c2 Np)) =
      dB :: dt

/-! ## From the head -/

/-- The seated term is K12's files' name of the IOP as written in Lean. -/
theorem f0t_is_descN (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) :
    F0T o Zp Np cF = descN o ProofFile.pureRoad.links guardedProximityTestParts Zp Np cF := rfl

/-- That name's test on the list of rounds, at the head. -/
theorem _root_.P5J.AtMg.planN (h : AtMg o Z D r Zp Np cF) :
    (descN o ProofFile.pureRoad.links guardedProximityTestParts Zp Np cF).planOk = true :=
  f0t_is_descN o Zp Np cF ▸ h.laid.planOk

/-- The ledger's name's test, at the head. -/
theorem _root_.P5J.AtMg.planL (h : AtMg o Z D r Zp Np cF) :
    (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).planOk = true :=
  (planOk_tie o ProofFile.pureRoad.links Zp Np cF).trans h.planN

/-- The door's first row, at the head: the declared rounds are the written ones. -/
theorem _root_.P5J.AtMg.pin (h : AtMg o Z D r Zp Np cF) :
    VerifiableInference.PlanWritten.seatPinnedProof Z.pol
      (descN o ProofFile.pureRoad.links guardedProximityTestParts Zp Np cF) = true :=
  f0t_is_descN o Zp Np cF ▸ LPFD.asks_written h.laid.asks

/-- **(1) THE CALL OF `closed_in_scope` AT THE HEAD**: no premise is left. -/
theorem closed_at_head (h : AtMg o Z D r Zp Np cF) :
    ∃ ch b₁ b₂ T, ClosedL (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W) H2K.Member.rWFull ch b₁ b₂ T :=
  closed_in_scope h.scope Zp h.laid.pub ProofFile.pureRoad.links Np cF h.laid.places h.planL h.pin

/-- The place's numbers are the places' own. -/
theorem _root_.P5J.AtMg.numsW (h : AtMg o Z D r Zp Np cF) :
    (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W).nums = Np.W.nums :=
  H2K.Made.nums_of_planOk ⟨3, none, 2, .K12⟩ Np.W
    (H2K.JointK.plan_at_seat_W o Zp ProofFile.pureRoad.links Np cF h.planN)

/-- The data of the ledger's name, at the head. -/
theorem _root_.P5J.AtMg.dataL (h : AtMg o Z D r Zp Np cF) :
    (FL o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
  rw [LaidAt.atDepth h.scope h.laid]
  exact h.laid.data

/-- **The third piece's stretch of the written rounds has a first round**: dB :: dt is opened. -/
theorem stretch_at_head (h : AtMg o Z D r Zp Np cF) :
    ∃ dB dt, StretchJ o D Zp Np cF dB dt := by
  obtain ⟨⟨a₁, k₁, q₁⟩, ⟨a₂, k₂, q₂⟩, -⟩ := LaidAt.heads o Zp Np cF
  exact hds_of_planOk o ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF (D.at frS.P.T.a) a₁ k₁ a₂ k₂
    "proof file" h.dataL h.planL q₁ q₂

/-- **TEN OF THE 33, AT THE HEAD**, at whichever dB :: dt the stretch is. -/
theorem planPaid₃_at_head (h : AtMg o Z D r Zp Np cF) (J : ShSeven) (dB : RDT) (dt : List RDT)
    (hs : StretchJ o D Zp Np cF dB dt) :
    PlanPaid₃ o ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a) (F0T o Zp Np cF) dB dt
      (ms2J J) (nsJ J) H2K.Member.rWFull 1 where
  closed := closed_at_head h
  stretch := hs
  someO := hsit_sh J.S J.rU J.rO J.rSp J.lo J.layU J.layO .oOmega
  free0 := by
    rw [h.numsW, H2K.JointK.free_at_seat_W o Z.pol Z.lay Z.KL Zp h.laid.pub ProofFile.pureRoad.links Np cF
      h.laid.places h.planN]
    decide
  dataIs := ⟨_, h.dataL⟩
  planOk := h.planL
  ownMask := H2K.JointK.ownMask_in_scope_W h.scope Zp h.laid.pub ProofFile.pureRoad.links Np cF
    h.laid.places h.planN
  twoStages := by
    rw [h.numsW, (H2K.Sizes.place_W_of_full (H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub)
      h.laid.places).1]
    decide
  places := h.laid.places
  planTreeO := P2Law.planTreeO_of_same (F0T o Zp Np cF) o ProofFile.pureRoad.links Zp Np cF
    (D.at frS.P.T.a) ⟨_, h.dataL⟩ h.planL rfl rfl rfl

/-- **(2) `PlanOk₃` AT THE HEAD, AT THE JOIN's OWN LETTERS**: dB :: dt is opened; what is left is
asked ONLY AT THE dB :: dt THAT THE STRETCH IS (the guard `StretchJ`: without it the premise would ask
the field placeB at every list of rounds). -/
theorem planOk₃_at_head (h : AtMg o Z D r Zp Np cF) (J : ShSeven)
    (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (L : ∀ dB dt, StretchJ o D Zp Np cF dB dt → LeftJ o Z D Zp Np cF J dB dt Ld) :
    ∃ dB dt, PlanJ o Z D Zp Np cF J dB dt Ld := by
  obtain ⟨dB, dt, hs⟩ := stretch_at_head h
  exact ⟨dB, dt, PlanOk₃.of_parts (planPaid₃_at_head h J dB dt hs) (L dB dt hs)⟩

/-- **What stays, by name**, at the same letters: fourteen of the 33 and seatsApart's first clause. -/
abbrev CoreJ (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (J : ShSeven) (dB : RDT) (dt : List RDT)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) : Prop :=
  PlanCore₃ o ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a) (F0T o Zp Np cF) (At.arr Zp) dB dt
    (At.ms Zp Z.lay) (ms2J J) (At.N Zp cF) (nsJ J) H2K.Member.rWFull ((At.N Zp cF).treesAt none) 0 1
    (vAt Zp (At.N Zp cF)) Ld

/-- **(2), THE SHORTER FORM: `PlanOk₃` AT THE HEAD FROM WHAT STAYS.** hE, hT, hn: the ends that other
files have at the head (`AtMg.elderBelow_at`, `AtMg.endTests_at`, `AtMg.trees_at`), in their own
texts (Johnson/HB/LLHARD/PlanOk3AtHead.lean, HeadFacts.lean): premises here, since this file
does not import those two. -/
theorem planOk₃_of_core (h : AtMg o Z D r Zp Np cF) (J : ShSeven)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) (hn : 1 < (D.at frS.P.T.a).t₂)
    (hE : (At.N Zp cF).index.1 < (D.at frS.P.T.a).t₁ ∧ (At.N Zp cF).w.1 < (D.at frS.P.T.a).t₁)
    (hT : sampledBelow ((D.at frS.P.T.a).t₁ + (D.at frS.P.T.a).t₂) (At.N Zp cF)
        ((openSets fullLinks (First.flatPlaces true fullLinks true)
        (start fullLinks))[(First.flatPlaces true fullLinks true).length]?.getD []) = true ∧
      (At.N Zp cF).w ∈ sampledIn (At.N Zp cF)
        ((openSets fullLinks (First.flatPlaces true fullLinks true)
        (start fullLinks))[(First.flatPlaces true fullLinks true).length]?.getD []) ∧
      (At.N Zp cF).index ∈ sampledIn (At.N Zp cF)
        ((openSets fullLinks (First.flatPlaces true fullLinks true)
        (start fullLinks))[(First.flatPlaces true fullLinks true).length]?.getD []))
    (C : ∀ dB dt, StretchJ o D Zp Np cF dB dt → CoreJ o Z D Zp Np cF J dB dt Ld) :
    ∃ dB dt, PlanJ o Z D Zp Np cF J dB dt Ld :=
  planOk₃_at_head h J Ld fun dB dt hs =>
    PlanLeft₃.of_core (C dB dt hs) rfl rfl hn hE hT.1 hT.2.1 hT.2.2

end P5J.L0

#print axioms P5J.L0.planOk₃_of_core
#print axioms P5J.L0.closed_at_head
#print axioms P5J.L0.stretch_at_head
#print axioms P5J.L0.planPaid₃_at_head
#print axioms P5J.L0.planOk₃_at_head
