-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Dec/MOneD.lean: at the full size: A TWIN OF THE VALUES FOR THE CODING OF TYPED QUERIES
(Johnson/PV/MFullQ.lean's tail: `backFV`, `bkFV`; Johnson/PV/MFullOne.lean: `lkFOne`, `linkF_is`, `mFOne`, `mFLaid`, `mF_blocks`, `mF_rng`,
`mF_code`), WITH THE ENTRY FILE's DECISION A LETTER: dec, behind runP.

THE REQUEST's ITEM IS A LETTER `it : ReqAt Inst.Model.ppref → ByteArray`, where that file has the two letters pol | KL and makes the item of them inside, at the format's second
hash, a fixed function. `spI it x` := (it x, the request's own bytes) · `apartI` | `hreqI`: what the coding asks of the two strings (on requests that pass `okOwnF` they tell them apart) reads the
second string alone: so it holds AT EVERY ITEM, with no premise. `itF pol KL`: that file's item, for callers that have no letter of their own to hand: IT ALONE of this file's definitions names `spF`, and none of the others reaches it (the two controls and `spI_spF`, theorems, do).

Why. These values are typed over the interface of the three files' typed oracles, in which the entry file's protocol stands, and in it its
decision. At another decision they are other terms of other types. No line of them reads the decision.
How it differs. Each of the ten names has a D behind it; for `PV.EntryFive.lkF`: `lkD dec` := `linkProtocolOfRoundData (ckP .two) dsF aF xsF dec`; for `aLF`: `aLD`. All
else is that file's text, docstrings too. The rounds' data and the stored openings stay `dsF`, `xsF`: the entry's strings with code (`W4M.linkFF`) take
an equivalence to the link's shape at these data.
Controls: `lkD_decF`, `mFOneD_decF`, `mFLaidD_decF`: at dec := `decF` and at the item that pol | KL make they are that file's own, by unfolding; `spI_spF`.
Limits: those of the two files' heads. Nothing on soundness.

-/
import Johnson.PV.MFullOne

set_option autoImplicit false
set_option maxRecDepth 40000

namespace PV.MFull
open Rom Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Run TypedOracleCompiler.Run.SerArm OnBytes.K.Arm.Pub OnBytes.Tie TypedOracleCompiler.Slice VerifiableInference.OnPublicFiles
open OnBytes.K.Arm
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open VerifiableInference.OnPublicFiles.SlotsBehindCutD
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

open PV.OkOwn (okOwnF)

/-- The entry file's protocol at the written data and openings, its decision a letter. -/
abbrev lkD (dec : RecFull × RecFull → PQ.View → Bool) : InteractiveOracleProof (RecFull × RecFull) (twoExternalStrings (2 ^ frS.P.T.a) _root_.Run.PQ.SgX) :=
  linkProtocolOfRoundData (ckP .two) PV.EntryFive.dsF frS.P.T.a PV.EntryFive.xsF dec

/-- Its marks. -/
abbrev aLD : RoundSplits (_root_.Run.Twin.up (TypedOracleCompiler.Run.PQ.SOf (ckP .two) PV.EntryFive.dsF)) :=
  _root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) PV.EntryFive.dsF)

theorem lkD_decF : lkD PV.EntryFive.decF = PV.EntryFive.lkF := rfl

/-- **The request's two strings, THE ITEM A LETTER**: the item as it is handed in, and the request's own bytes. -/
def spI (it : ReqAt Inst.Model.ppref → ByteArray) (x : ReqAt Inst.Model.ppref) : ByteArray × ByteArray :=
  (it x, requestBytesOf x.val)

/-- The item that `PV.RunArgsF.spF` makes of the two strings pol | KL, at the second hash function: for callers that have no letter of their own to hand. -/
abbrev itF (pol KL : ByteArray) : ReqAt Inst.Model.ppref → ByteArray := fun x => (PV.RunArgsF.spF pol KL x).1

/-- At that item `spI` is `spF`. -/
theorem spI_spF (pol KL : ByteArray) : spI (itF pol KL) = PV.RunArgsF.spF pol KL := rfl

/-- On its yeses the request's two strings are one to one, AT EVERY ITEM: the second string alone is read. -/
theorem apartI (it : ReqAt Inst.Model.ppref → ByteArray) (x y : ReqAt Inst.Model.ppref) (hx : okOwnF x = true) (hy : okOwnF y = true)
    (e : spI it x = spI it y) : x = y := by
  unfold spI at e
  exact PV.OkOwn.ownF_apart x y hx hy (Prod.mk.inj e).2

/-- So are the typed instance's two strings, on what passes the written test. -/
theorem hreqI (it : ReqAt Inst.Model.ppref → ByteArray) (r₀ : RecFull) (z z' : Option (ReqAt Inst.Model.ppref) × RecFull × RecFull)
    (h : ((match z.1 with
      | some x => okOwnF x
      | none => false) && isAt serRecFull r₀ z.2.1 && isAt serRecFull r₀ z.2.2) = true)
    (h' : ((match z'.1 with
      | some x => okOwnF x
      | none => false) && isAt serRecFull r₀ z'.2.1 && isAt serRecFull r₀ z'.2.2) = true)
    (e : (z.1.map (spI it)).getD default = (z'.1.map (spI it)).getD default) : z = z' := by
  obtain ⟨a, r1, r2⟩ := z
  obtain ⟨a', r1', r2'⟩ := z'
  cases a with
  | none => simp at h
  | some x =>
    cases a' with
    | none => simp at h'
    | some x' =>
      simp only [Bool.and_eq_true] at h h'
      obtain rfl := apartI it x x' h.1.1 h'.1.1 e
      rw [(isAt_iff serRecFull r₀ r1).1 h.1.2, (isAt_iff serRecFull r₀ r2).1 h.2,
        (isAt_iff serRecFull r₀ r1').1 h'.1.2, (isAt_iff serRecFull r₀ r2').1 h'.2]

section Back
variable (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : (ReqAt Inst.Model.ppref) × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : (ReqAt Inst.Model.ppref) → (ReqAt Inst.Model.ppref)) (K : ℕ)

/-- **THE TOTAL CODE BEHIND THE ESCAPE, AS A VALUE.** -/
def backFVD : StrCode (AllPts 256 (K + 1) (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) :=
  TypedOracleCompiler.Run.ArmBack.backL2 (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (Ser.prod (Ser.option PV.SerReq.sXF) (Ser.prod serRecFull serRecFull))
    _root_.Compile.serBits
    (fun t => match t with
      | .link => serLF
      | .test => serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD
      | .onl => serPF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (K + 1)

/-- **bk AS A VALUE.** -/
def bkFVD : AllPts 256 (K + 1) (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) → List Bool := (backFVD DK DP runK runP dec rK rP depthReq early K).put

/-- It is bkF at the two serialisers. -/
theorem bkFV_isD : bkFVD DK DP runK runP dec rK rP depthReq early K = bkF DK DP runK runP rK rP depthReq early (lkD dec) aLD K PV.SerReq.sXF serLF := rfl


end Back

variable (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : (ReqAt Inst.Model.ppref) × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : (ReqAt Inst.Model.ppref) → (ReqAt Inst.Model.ppref)) (salt : ℕ) (K : ℕ)
  (h₀ : HId) (k : OnBytes.Params.KeyChains) (c' : OnBytes.Params.ProofChains) (it : ReqAt Inst.Model.ppref → ByteArray) (r₀ : RecFull)
  (c : ByteArray) (hc : c.size = 32) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)

/-- The entry file's code: the linkAt, at this carrier. -/
noncomputable def lkFOneD : LinkCode (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (K + 1) :=
  TypedOracleCompiler.Slice.ArmLinkCode.linkAt (entryXD recordGround c) topD1Full c hc pdL (pubRestTopFull c) (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) ((Equiv.refl _).trans (W4M.pbFu c))
    (isPLAt (entryXD recordGround c) topD1Full (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) ((Equiv.refl _).trans (W4M.pbFu c)))
    (hpLAt (entryXD recordGround c) topD1Full (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) ((Equiv.refl _).trans (W4M.pbFu c)))
    (codeA (v := frS.P.v) (s := 1)) OnBytes.Flat.trAns codeA_inj (fun a a' => (codeA_length a).trans (codeA_length a').symm)
    trAns_sib_inj (K + 1)

/-- **The strings with code ARE its put.** -/
theorem linkF_isD : W4M.linkFF (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (Equiv.refl _) K c hc pdL = (lkFOneD DK DP runK runP dec rK rP depthReq early K c hc pdL).pL.put :=
  W4M.linkPutC_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W4M.hun

/-- **THE CODING, ONE TO ONE AND ONTO, AT THE ONE SHEET's OWN LETTERS.** -/
noncomputable def mFOneD (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true)
    (hK : K + 1 + 1 < 2 ^ 49) : OracleCoding (typedOracleFamily 256 (K + 1) (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) 256 :=
  W4M.mAny (L := (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) (K := K) (ckP .two) (DK.at frS.P.T.a) (DP.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
    (front₀ rP) (join₀ rP) ByteArray.empty (fun z => some z) (fun z => some z) h₀ k c'
    (fun z => (z.1.map (spI it)).getD default)
    (fun z => (match z.1 with
      | some x => okOwnF x
      | none => false) && isAt serRecFull r₀ z.2.1 && isAt serRecFull r₀ z.2.2)
    (fun _ l => OnBytes.K.cAL frS.P.v 1 l) OnBytes.Flat.tlAns c sR (Equiv.refl (List Bool)) (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
    (isAt (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) (isAt (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) (TypedOracleCompiler.Run.SeedVals.cfgL c) pubShapeTopFull
    (isAt_iff (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) (isAt_iff (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) (pubRestTopFull c)
    (lkFOneD DK DP runK runP dec rK rP depthReq early K c hc pdL) (OnBytes.Maker.Page.leavesJ W4M.L0 (8 * salt) c (Equiv.refl (List Bool))) dK dP
    (fun _ _ _ h h' => Option.some.inj (h.trans h'.symm)) (fun _ _ _ h h' => Option.some.inj (h.trans h'.symm)) hDK hDP hK hc
    (hreqI it r₀) (by rw [show (lkFOneD DK DP runK runP dec rK rP depthReq early K c hc pdL).l = OnBytes.Params.labelLink from rfl]; decide)
    (backFVD DK DP runK runP dec rK rP depthReq early K)

/-- The value that is laid for m: at the front set's own test, the entry's strings with code, and the real bk. -/
abbrev mFLaidD : ImplV (typedOracleFamily 256 (K + 1) (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) 256 :=
  mF DK DP runK runP rK rP depthReq early (lkD dec) aLD salt K h₀ k c' (spI it) okOwnF r₀ c sR (W4M.linkFF (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (Equiv.refl _) K c hc pdL) dK dP (bkFVD DK DP runK runP dec rK rP depthReq early K)

variable (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : K + 1 + 1 < 2 ^ 49)

theorem mF_blocksD : (mFLaidD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP).blocks =
    (mFOneD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK hDP hK).blocks := rfl

theorem mF_rngD : (mFLaidD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP).rng =
    (mFOneD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK hDP hK).rng := rfl

/-- **AT EVERY ORACLE BUT THE SPARE ONE THE STRING THAT IS LAID IS THE BIJECTIVE CODING's.** -/
theorem mF_codeD (o : TypedOracleCompiler.Compile.Batch.OracleName) (ho : o ≠ .other) (q : domOf 256 (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) o) (j : Fin (blk (K + 1) o)) :
    (mFLaidD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP).code o q j =
      (mFOneD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK hDP hK).code o q j := by
  have e := W4M.mAny_code (L := (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) (K := K) (ckP .two) (DK.at frS.P.T.a) (DP.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
    (front₀ rP) (join₀ rP) ByteArray.empty (fun z => some z) (fun z => some z) h₀ k c'
    (fun z => (z.1.map (spI it)).getD default)
    (fun z => (match z.1 with
      | some x => okOwnF x
      | none => false) && isAt serRecFull r₀ z.2.1 && isAt serRecFull r₀ z.2.2)
    (fun _ l => OnBytes.K.cAL frS.P.v 1 l) OnBytes.Flat.tlAns c sR (Equiv.refl (List Bool)) (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)
    (isAt (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) (isAt (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) (TypedOracleCompiler.Run.SeedVals.cfgL c) pubShapeTopFull
    (isAt_iff (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) (isAt_iff (serKF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (plF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) (pubRestTopFull c)
    (lkFOneD DK DP runK runP dec rK rP depthReq early K c hc pdL) (OnBytes.Maker.Page.leavesJ W4M.L0 (8 * salt) c (Equiv.refl (List Bool))) dK dP
    (fun _ _ _ h h' => Option.some.inj (h.trans h'.symm)) (fun _ _ _ h h' => Option.some.inj (h.trans h'.symm)) hDK hDP hK hc
    (hreqI it r₀) (by rw [show (lkFOneD DK DP runK runP dec rK rP depthReq early K c hc pdL).l = OnBytes.Params.labelLink from rfl]; decide)
    (backFVD DK DP runK runP dec rK rP depthReq early K) o ho q j
  refine Eq.trans ?_ e
  show (W4M.mAt (L := (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD)) (K := K) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (W4M.linkFF (carF DK DP runK runP rK rP depthReq early (lkD dec) aLD) (Equiv.refl _) K c hc pdL) _ _ _ _).code o q j = _
  rw [linkF_isD]
  refine (W4M.mAt_code_okX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun z => (match z.1 with
      | some x => okOwnF x
      | none => false) && isAt serRecFull r₀ z.2.1 && isAt serRecFull r₀ z.2.2)
    (by funext z; obtain ⟨a, r1, r2⟩ := z; cases a <;> rfl) _ o q j).trans ?_
  exact W4M.mAt_code_any _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ o q j

/-- At the decision `decF` and at the item that pol | KL make the coding is that file's own. -/
theorem mFOneD_decF (pol KL : ByteArray) : mFOneD DK DP runK runP PV.EntryFive.decF rK rP depthReq early salt K h₀ k c' (itF pol KL) r₀ c hc sR pdL dK dP hDK hDP hK =
    mFOne DK DP runK runP rK rP depthReq early salt K h₀ k c' pol KL r₀ c hc sR pdL dK dP hDK hDP hK := rfl

theorem mFLaidD_decF (pol KL : ByteArray) : mFLaidD DK DP runK runP PV.EntryFive.decF rK rP depthReq early salt K h₀ k c' (itF pol KL) r₀ c hc sR pdL dK dP =
    mFLaid DK DP runK runP rK rP depthReq early salt K h₀ k c' pol KL r₀ c hc sR pdL dK dP := rfl

end PV.MFull

#print axioms PV.MFull.bkFV_isD
#print axioms PV.MFull.linkF_isD
#print axioms PV.MFull.mFOneD
#print axioms PV.MFull.mF_blocksD
#print axioms PV.MFull.mF_rngD
#print axioms PV.MFull.mF_codeD
#print axioms PV.MFull.mFOneD_decF
#print axioms PV.MFull.mFLaidD_decF
