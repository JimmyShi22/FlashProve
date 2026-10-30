-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/Sits.lean: THE ROW K10_sits, ITS PROOF-FILE HALF AT THE FULL SIZE: IN THE PROOF FILE's
DESCRIPTION, IN SCOPE, THE ENTRY OF THE FIRST CHAIN's LIST OF BLOCKS AT K10's PLACE IN EVERY LINK IS THE CONSTANT OF WHICH K10's LAW SPEAKS, AT THE
PLAN's NUMBERS, UNDER THE SEAT's WRAPPERS ALONE; ITS YES GIVES THE LAW's PREMISE; AND THE LAW AT THAT ENTRY ITSELF. Statements and proofs.
THE LIST's SENTENCE (in a file not in this library: K10_sits): "the entry of the description's list of blocks at each place of the kind is the constant of which
K10_law speaks, at the plan's numbers, under the seat's wrappers alone (another name and place; the mark's guard), or its yes gives that law's premise".
  k10_sits     under three premises (VerifierAndGoals.InScope P · VerifierAndGoals.readFiles P = ok pp · Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B:
               what ProofFile.onlineDescription's yes opens into: Johnson/IMR/SeatOpen.lean): at every l < 25: the chain's link l has, as the SECOND of its closing's blocks, a block b with
               LaidAlone ProofFile.sameReply b (K9.closing Q).retype b.name (the driver's address): b IS ((guardMark ((K9.closing Q).retype) with the spot's name) at the driver's
               address).guarded sameReply hearsReply (Johnson/IMR/SeatForm.lean: seatedAs): nothing is joined behind; Q := ProofFile.k10Par Z (ProofFile.k9Stretches Z) p, p := ProofFile.k9Where .. l:
               THE PLAN's NUMBERS AS K9's LOT READS THEM. It is Johnson/IMR/CloseSeat.lean's close_of at j = 1, with x read out: (K9.closeOf p Q)[1] is K9.closing Q by make.
               K9.closing Q IS THE LAW's CONSTANT: pieceAt_closing (Johnson/Desc/First/Close/Law/AtBlock.lean): the piece of k10_block | k10_block_self has the block below (K9.closing Pr).
  seated_yes   THE SENTENCE's SECOND ARM TOO: a yes of such a b, from s to t, is a yes of closeFrame on what recOf reads, at Q's entries, and t is putRec s of "nothing owed", the
               frame and the statement; t bears no mark; the reply stands. By IM.yes_alone and lift_decide_iff.
  k10_seated   SO THE LAW HOLDS AT THE SEATED BLOCK ITSELF: k10_any_self (Johnson/Desc/First/Close/Law/AtAny.lean) at b: the piece pieceOn b .. has the block below b: the very
               entry of the chain under the proof's device: no wrapper stands between the law and what the description calls.
THE WRAPPERS ARE MORE THAN THE LIST's BRACKET NAMES ("another name and place; the mark's guard"): seatedAs lays FOUR: the name · the place · guardMark · THE REPLY's GUARD (Block.guarded sameReply
hearsReply); and beneath them Block.retype carries the block to the fold's claims (its test on the plan then also asks that the block states no claims). So the sentence's FIRST arm is met for the
seat's wrappers, not to the bracket's letter; ITS SECOND ARM (seated_yes) IS MET OUTRIGHT.
A GIFT OF yes_alone: what a yes returns bears no mark, and K10's writing turns no mark: so THE SEATED BLOCK HAS NO YES AT A MARKED RECORD: typed in SitsAll.lean, beside this file: seated_unmarked.
LIMITS. (0) k10_sits runs over l < 25: "at each place of the kind" is SitsAll.lean's, for the first chain. (1) It stands on the seat files of Johnson/IMR/ (fourteen files, CloseSeat.lean and SeatForm.lean among them):
compiled for this file. (2) THE THREE PREMISES ARE PREMISES: that onlineDescription returns in scope is shown by nobody in Lean (by report, an evaluation ran over another
set of files). (3) THE FULL SIZE's PLAN ALONE (InScope; 25 links). The key file's description: whether it seats this kind has not been looked at. (4) Written over an
earlier set of this project's files, with ProofFile's files laid over them. (5) That Lk.close has no fourth block, and
where the block stands in the blocksInOrder list, is FlatScope.lean's. (6) k10_seated's rounds' data dB, dE, dR and their number are letters: that they are the data of b's declared rounds
(alone_rounds: b.rounds = the kind's) is not laid in. (7) All bounds of the law stand (AtBlockSelf.lean's Limits). Nothing on soundness of the protocol.

-/
import Johnson.IMR.CloseSeat
import Johnson.Desc.First.Close.Law.AtAny

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S closeKinds)
open VerifiableInference.Desc.First.Close (Par closeFrame entries lift_decide_iff)
open VerifiableInference.Desc.K9 (recOf putRec)
open ProofFile (Cl)
open IM

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z :
                                      ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **K10_sits.** -/
theorem k10_sits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (p : VerifiableInference.Desc.K9.Where) (Q : Par) (b : Block S Cl),
      c.links[l]? = some Lk ∧ k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
      Lk.close[1]? = some b ∧
      LaidAlone ProofFile.sameReply b
        (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype b.name
        (cAt l (subAt l) 1 KindName.K10) := by
  intro l hl
  obtain ⟨Lk, p, Q, h1, h2, h3, h4⟩ := close_of hS hR O l hl
  obtain ⟨b, x, hb, hx, hL⟩ := h4 1 KindName.K10 rfl
  have ex : x = (VerifiableInference.Desc.K9.closing Q : Block S Unit) := (Option.some.inj hx).symm
  subst ex
  exact ⟨Lk, p, Q, b, h1, h2, h3, hb, hL⟩

/-- **A yes of the seated block is a yes of `closeFrame`**, read and written as K10's law reads and
writes; and what is written bears no mark and has the reply that stood. -/
theorem seated_yes {same : S → S → Bool} {b : Block S Cl} {Q : Par} {name : String} {a : Place}
    (h : LaidAlone same b (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype name a)
    (hk : a.kind ≠ KindName.K7) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hy : b.decide s rs gs = .ok t) :
    (∃ x, closeFrame (recOf s).owed (recOf s).frame (recOf s).st (entries Q) rs = .ok x ∧
      t = putRec s ⟨none, x.1, x.2⟩) ∧ t.failed = none ∧ same s t = true := by
  obtain ⟨h1, h2, h3⟩ := (yes_alone h hk s t rs gs).1 hy
  exact ⟨(lift_decide_iff (Cl := Unit) Q recOf putRec s t rs gs).1 h1, h2, h3⟩

end LPFK10

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)
open VerifiableInference.Desc (Place KindName)
open IM (LaidAlone)
open LPFK10 (seated_yes)

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : S.Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

/-- **K10's LAW AT THE SEATED BLOCK ITSELF.** -/
theorem k10_seated
    (L : List (BatFoldCaller GE))
    (dB dE dR : RDT)
    (ρ : Rd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) (wT dB) (wT
      dE) (wT dR))
    (hρ : ρ = realRd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) dB dE
      dR (oneOf id) (oneOf id))
    (hst : StepOK (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).n fx (rd2
      (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC
      bZ w₀ w₁)).n).mon fx.1 = 1)
    (hFi : R.G.Fits)
    (hg : R.Good)
    (hj : InJ R.s R.e)
    (hc : CountsAt R.s R.e bC bZ)
    (he : R.G.e < R.s.d)
    (hv : ∀ a, (R.view a).Fix R.G.e)
    (hP : Pulls R pull)
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    {W : Type}
    {F : Frame}
    {same : VerifiableInference.Desc.First.S → VerifiableInference.Desc.First.S → Bool}
    {b : Block VerifiableInference.Desc.First.S ProofFile.Cl}
    {Q : Par}
    {name : String}
    {a₀ : Place}
    (hL : LaidAlone same b (VerifiableInference.Desc.K9.closing Q : Block
      VerifiableInference.Desc.First.S Unit).retype name a₀)
    (hk7 : a₀.kind ≠ KindName.K7)
    (base : ℕ)
    (ext : VerifiableInference.Desc.First.S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE ::
      List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
      w₁)).k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R
      pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k dR)))
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str)
    (x : Johnson.Bridge.FoldedPlace)
    (hx : x.Paid)
    (hxs : x.s = R.s)
    (hxe : x.e = R.e)
    (hxC : bC ≤ x.bC)
    (hxZ : bZ ≤ x.bZ)
    {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na))
    (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (y : Johnson.Bridge.BatPlace)
    (hy : y.Paid)
    (hys : y.s = R.s)
    (hye : y.e = R.e)
    (hyz : (ZV R n num).err ≤ y.rows - 1)
    (iB : IsRd (toRD dB) (Fmt.M2.rBatN y.rows)) :
    (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n
      num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.red.Leads (K10OnS R N keep pull n num fx A₀ bC bZ w₀
      w₁ L pS Q fa) (fun a a' => (∃ τ, a'.2 = (pieceOn (W := W) (F := F) b base dB dE dR (Yc
      (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.imp
      a.2 τ ∧ sTests (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep
      (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).stage a.2 τ = true ∧
      closeFrame (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 (entries Q) ((sView (ckP .two) (pieceOn (W
      := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx
      A₀ bC bZ w₀ w₁)).k ext err).stage a.2 τ).rounds.map noDigest) = .ok (rdBK a'.1)) ∧ a'.1 = wrK
      a.1 (rdBK a'.1).1 (rdBK a'.1).2 ∧ ((rdK a.1).1 = none ∧ ∃ lk, (rdK a.1).2.1.shape.link[(rdK
      a.1).2.1.link]? = some lk ∧ (rdK a.1).2.1.next = .laterOrClose ∧ (rdK a.1).2.1.moment =
      reqMoments lk) ∧ (rdBK a'.1).1 = {
          (rdK a.1).2.1 with
          rows := (rdBK a'.1).1.rows, mask := none, link := (rdK a.1).2.1.link + 1, next := .first }
      ∧ (CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a) (rdBK
        a'.1).1.rows → (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧ ∀ m :
        S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) → ∀ G lay, (rdK
        a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → (begun (rdK a.1).2.2 (rdK a.1).2.1.group
        G).layout (rdK a.1).2.1.group = some lay → ∀ (r : R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows
        (rdK a.1).2.2 G).toList.length), ∑ j, rowVec N (begun (rdK a.1).2.2 (rdK a.1).2.1.group G)
        lay (runRows (rdK a.1).2.2 G).toList[i] j * (R.Sh.rho.up (R.G.msg m, r)).1 j = readE
        (runRows (rdK a.1).2.2 G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep
          (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ds)) :=
  k10_any_self R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc he hv hP
    pS Q b (fun s rs gs s' h => (seated_yes hL hk7 s s' rs gs h).1) base ext err fa x hx hxs hxe hxC
    hxZ iE iR y hy hys hye hyz iB

end VerifiableInference.Desc.First.Close

#print axioms LPFK10.k10_sits
#print axioms LPFK10.seated_yes
#print axioms VerifiableInference.Desc.First.Close.k10_seated
