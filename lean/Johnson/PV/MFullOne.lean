-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/MFullOne.lean: AT THE FULL SIZE, AT THE OWN LETTERS OF THE ONE FILE OF EVALUATIONS
  (carrierV of LvOf … at lk := lkF, aL := aLF): **A VALUE FOR m (mFLaid) WITH NO STAND-IN AMONG ITS
  LETTERS, WHICH IS THE WRITING SIDE OF A CODING THAT IS ONE TO ONE AND ONTO.** mFLaid AS A WHOLE
  HAS NOT RUN: what ran so far had okS := always; the real bk ran at hollow carriers; the entry's
  strings ran under the stub.
  okOwnF (Johnson/PV/OkOwn.lean): THE FRONT SET's OWN TEST, AS A VALUE WITH CODE. IN okS := always's
    PLACE.
  apartF: on its yeses the request's two strings (PV.RunArgsF.spF pol KL) are one to one: by the
    second string alone (early_of_requestBytes) · hreqF: so are the typed instance's, on
    what passes the written test
  lkFOne: linkAt at mPubTopFull's letters, at this carrier · linkF_is: W4M.linkFF … IS
    its put (linkPutC_eq with its one premise paid: W4M.hun)

  **mFOne … : OracleCoding (typedOracleFamily 256 (K + 1) ‹the carrier›) 256** := W4M.mAny (Johnson/PV/LawsAny.lean) at
    mF's own letters, back := backFV: BIJECTIVE BY ITS TYPE. PREMISES THAT STAY, ALL ON DATA: kindsAndWorkBelow256
    of both data · K + 2 < 2 ^ 49 · c has 32 bytes.
  **mF_blocks | mF_rng := rfl · mF_code**: mF … okOwnF … W4M.linkFF … bkFV IS mFOne's writing side
    AT EVERY ORACLE BUT OracleName.other.
AT OracleName.other THE TWO PART (the bijective coding moves a spare string aside by a parser that is
  taken by choice): what joins them there is (Tm): «VRAV asks nothing at OracleName.other». Nothing on
  soundness.


-/
import Johnson.PV.MFullQ
import Johnson.PV.LawsAny
import Johnson.PV.MvAtAny
import Johnson.PV.LinkFull
import Johnson.PV.Hun
import Johnson.PV.RunArgsFull
import Johnson.PV.OkOwn

set_option autoImplicit false
set_option maxRecDepth 40000

namespace PV.MFull
open Rom Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
    OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Run TypedOracleCompiler.Run.SerArm OnBytes.K.Arm.Pub OnBytes.Tie TypedOracleCompiler.Slice
    VerifiableInference.OnPublicFiles
open OnBytes.K.Arm
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open VerifiableInference.OnPublicFiles.SlotsBehindCutD
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

open PV.OkOwn (okOwnF)

/-- On its yeses the request's two strings are one to one. -/
theorem apartF (pol KL : ByteArray) (x y : ReqAt Inst.Model.ppref) (hx : okOwnF x = true) (hy :
    okOwnF y = true)
    (e : PV.RunArgsF.spF pol KL x = PV.RunArgsF.spF pol KL y) : x = y := by
  unfold PV.RunArgsF.spF at e
  exact PV.OkOwn.ownF_apart x y hx hy (Prod.mk.inj e).2

/-- So are the typed instance's two strings, on what passes the written test. -/
theorem hreqF (pol KL : ByteArray) (r₀ : RecFull) (z z' : Option (ReqAt Inst.Model.ppref) × RecFull
    × RecFull)
    (h : ((match z.1 with
      | some x => okOwnF x
      | none => false) && isAt serRecFull r₀ z.2.1 && isAt serRecFull r₀ z.2.2) = true)
    (h' : ((match z'.1 with
      | some x => okOwnF x
      | none => false) && isAt serRecFull r₀ z'.2.1 && isAt serRecFull r₀ z'.2.2) = true)
    (e : (z.1.map (PV.RunArgsF.spF pol KL)).getD default = (z'.1.map (PV.RunArgsF.spF pol KL)).getD
        default) : z = z' := by
  obtain ⟨a, r1, r2⟩ := z
  obtain ⟨a', r1', r2'⟩ := z'
  cases a with
  | none => simp at h
  | some x =>
    cases a' with
    | none => simp at h'
    | some x' =>
      simp only [Bool.and_eq_true] at h h'
      obtain rfl := apartF pol KL x x' h.1.1 h'.1.1 e
      rw [(isAt_iff serRecFull r₀ r1).1 h.1.2, (isAt_iff serRecFull r₀ r2).1 h.2,
        (isAt_iff serRecFull r₀ r1').1 h'.1.2, (isAt_iff serRecFull r₀ r2').1 h'.2]

variable (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : (ReqAt Inst.Model.ppref) × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull)
      (depthReq : ℕ)
  (early : (ReqAt Inst.Model.ppref) → (ReqAt Inst.Model.ppref)) (salt : ℕ) (K : ℕ)
  (h₀ : HId) (k : OnBytes.Params.KeyChains) (c' : OnBytes.Params.ProofChains) (pol KL : ByteArray)
      (r₀ : RecFull)
  (c : ByteArray) (hc : c.size = 32) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)

/-- The entry file's code: linkAt (OnBytes/TypedOracleCompiler/Slice/ArmLinkCode.lean), at this carrier. -/
noncomputable def lkFOne : LinkCode (carF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF
    PV.EntryFive.aLF) (K + 1) :=
  TypedOracleCompiler.Slice.ArmLinkCode.linkAt (entryXD recordGround c) topD1Full c hc pdL (pubRestTopFull
              c) (carF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) ((Equiv.refl
              _).trans (W4M.pbFu c))
    (isPLAt (entryXD recordGround c) topD1Full (carF DK DP runK runP rK rP depthReq early
        PV.EntryFive.lkF PV.EntryFive.aLF) ((Equiv.refl _).trans (W4M.pbFu c)))
    (hpLAt (entryXD recordGround c) topD1Full (carF DK DP runK runP rK rP depthReq early
        PV.EntryFive.lkF PV.EntryFive.aLF) ((Equiv.refl _).trans (W4M.pbFu c)))
    (codeA (v := frS.P.v) (s := 1)) OnBytes.Flat.trAns codeA_inj (fun a a' => (codeA_length a).trans
        (codeA_length a').symm)
    trAns_sib_inj (K + 1)

/-- **The strings with code ARE its put.** -/
theorem linkF_is : W4M.linkFF (carF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF
    PV.EntryFive.aLF) (Equiv.refl _) K c hc pdL = (lkFOne DK DP runK runP rK rP depthReq early K c
    hc pdL).pL.put :=
  W4M.linkPutC_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W4M.hun

/-- **THE CODING, ONE TO ONE AND ONTO, AT THE OWN LETTERS OF THE ONE FILE OF EVALUATIONS.** -/
noncomputable def mFOne (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) =
                  true)
    (hK : K + 1 + 1 < 2 ^ 49) : OracleCoding (typedOracleFamily 256 (K + 1) (carF DK DP runK runP rK rP depthReq early
                             PV.EntryFive.lkF PV.EntryFive.aLF)) 256 :=
  W4M.mAny (L := (carF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF)) (K
      := K) (ckP .two) (DK.at frS.P.T.a) (DP.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
    (front₀ rP) (join₀ rP) ByteArray.empty (fun z => some z) (fun z => some z) h₀ k c'
    (fun z => (z.1.map (PV.RunArgsF.spF pol KL)).getD default)
    (fun z => (match z.1 with
      | some x => okOwnF x
      | none => false) && isAt serRecFull r₀ z.2.1 && isAt serRecFull r₀ z.2.2)
    (fun _ l => OnBytes.K.cAL frS.P.v 1 l) OnBytes.Flat.tlAns c sR (Equiv.refl (List Bool)) (plF DK
        DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) (plF DK DP runK runP rK
        rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF)
    (isAt (serKF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) (plF DK DP
        runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF)) (isAt (serKF DK DP runK
        runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) (plF DK DP runK runP rK rP
        depthReq early PV.EntryFive.lkF PV.EntryFive.aLF)) (TypedOracleCompiler.Run.SeedVals.cfgL c)
        pubShapeTopFull
    (isAt_iff (serKF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) (plF DK
        DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF)) (isAt_iff (serKF DK DP
        runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) (plF DK DP runK runP rK rP
        depthReq early PV.EntryFive.lkF PV.EntryFive.aLF)) (pubRestTopFull c)
    (lkFOne DK DP runK runP rK rP depthReq early K c hc pdL) (OnBytes.Maker.Page.leavesJ W4M.L0 (8 *
        salt) c (Equiv.refl (List Bool))) dK dP
    (fun _ _ _ h h' => Option.some.inj (h.trans h'.symm)) (fun _ _ _ h h' => Option.some.inj
        (h.trans h'.symm)) hDK hDP hK hc
    (hreqF pol KL r₀) (by rw [show (lkFOne DK DP runK runP rK rP depthReq early K c hc pdL).l =
        OnBytes.Params.labelLink from rfl]; decide)
    (backFV DK DP runK runP rK rP depthReq early K)

/-- The value that is laid for m: at the front set's own test, the entry's strings with code, and
  the real bk. -/
abbrev mFLaid : ImplV (typedOracleFamily 256 (K + 1) (carF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF
                 PV.EntryFive.aLF)) 256 :=
  mF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF salt K h₀ k c'
      (PV.RunArgsF.spF pol KL) okOwnF r₀ c sR (W4M.linkFF (carF DK DP runK runP rK rP depthReq early
      PV.EntryFive.lkF PV.EntryFive.aLF) (Equiv.refl _) K c hc pdL) dK dP (bkFV DK DP runK runP rK
      rP depthReq early K)

variable (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : K + 1
                                + 1 < 2 ^ 49)

theorem mF_blocks : (mFLaid DK DP runK runP rK rP depthReq early salt K h₀ k c' pol KL r₀ c hc sR
    pdL dK dP).blocks =
    (mFOne DK DP runK runP rK rP depthReq early salt K h₀ k c' pol KL r₀ c hc sR pdL dK dP hDK hDP
        hK).blocks := rfl

theorem mF_rng : (mFLaid DK DP runK runP rK rP depthReq early salt K h₀ k c' pol KL r₀ c hc sR pdL
    dK dP).rng =
    (mFOne DK DP runK runP rK rP depthReq early salt K h₀ k c' pol KL r₀ c hc sR pdL dK dP hDK hDP
        hK).rng := rfl

/-- **AT EVERY ORACLE BUT THE SPARE ONE THE STRING THAT IS LAID IS THE BIJECTIVE CODING's.** -/
theorem mF_code (o : TypedOracleCompiler.Compile.Batch.OracleName) (ho : o ≠ .other) (q : domOf 256 (carF DK DP runK
                    runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) o) (j : Fin (blk (K + 1) o)) :
    (mFLaid DK DP runK runP rK rP depthReq early salt K h₀ k c' pol KL r₀ c hc sR pdL dK dP).code o
        q j =
      (mFOne DK DP runK runP rK rP depthReq early salt K h₀ k c' pol KL r₀ c hc sR pdL dK dP hDK hDP
          hK).code o q j := by
  have e := W4M.mAny_code (L := (carF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF
      PV.EntryFive.aLF)) (K := K) (ckP .two) (DK.at frS.P.T.a) (DP.at frS.P.T.a) (front₀ rK) (join₀
      rK) ByteArray.empty
    (front₀ rP) (join₀ rP) ByteArray.empty (fun z => some z) (fun z => some z) h₀ k c'
    (fun z => (z.1.map (PV.RunArgsF.spF pol KL)).getD default)
    (fun z => (match z.1 with
      | some x => okOwnF x
      | none => false) && isAt serRecFull r₀ z.2.1 && isAt serRecFull r₀ z.2.2)
    (fun _ l => OnBytes.K.cAL frS.P.v 1 l) OnBytes.Flat.tlAns c sR (Equiv.refl (List Bool)) (plF DK
        DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) (plF DK DP runK runP rK
        rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF)
    (isAt (serKF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) (plF DK DP
        runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF)) (isAt (serKF DK DP runK
        runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) (plF DK DP runK runP rK rP
        depthReq early PV.EntryFive.lkF PV.EntryFive.aLF)) (TypedOracleCompiler.Run.SeedVals.cfgL c)
        pubShapeTopFull
    (isAt_iff (serKF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) (plF DK
        DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF)) (isAt_iff (serKF DK DP
        runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) (plF DK DP runK runP rK rP
        depthReq early PV.EntryFive.lkF PV.EntryFive.aLF)) (pubRestTopFull c)
    (lkFOne DK DP runK runP rK rP depthReq early K c hc pdL) (OnBytes.Maker.Page.leavesJ W4M.L0 (8 *
        salt) c (Equiv.refl (List Bool))) dK dP
    (fun _ _ _ h h' => Option.some.inj (h.trans h'.symm)) (fun _ _ _ h h' => Option.some.inj
        (h.trans h'.symm)) hDK hDP hK hc
    (hreqF pol KL r₀) (by rw [show (lkFOne DK DP runK runP rK rP depthReq early K c hc pdL).l =
        OnBytes.Params.labelLink from rfl]; decide)
    (backFV DK DP runK runP rK rP depthReq early K) o ho q j
  refine Eq.trans ?_ e
  show (W4M.mAt (L := (carF DK DP runK runP rK rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF))
      (K := K) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (W4M.linkFF (carF DK DP runK runP rK
      rP depthReq early PV.EntryFive.lkF PV.EntryFive.aLF) (Equiv.refl _) K c hc pdL) _ _ _ _).code
      o q j = _
  rw [linkF_is]
  refine (W4M.mAt_code_okX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun z => (match z.1 with
      | some x => okOwnF x
      | none => false) && isAt serRecFull r₀ z.2.1 && isAt serRecFull r₀ z.2.2)
    (by funext z; obtain ⟨a, r1, r2⟩ := z; cases a <;> rfl) _ o q j).trans ?_
  exact W4M.mAt_code_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ o q j

end PV.MFull

#print axioms PV.MFull.apartF
#print axioms PV.MFull.linkF_is
#print axioms PV.MFull.mFOne
#print axioms PV.MFull.mF_code
