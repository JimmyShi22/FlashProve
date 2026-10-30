-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/SitsLaw.lean: THE ROW K10_sits AND K10's LAW IN ONE TERM, FOR THE FIRST CHAIN OF THE PROOF FILE's DESCRIPTION AT THE FULL SIZE. A definition, statements and proofs.
  K10LawAt b Q    k10_seated's statement (Sits.lean, beside this file) with all its letters bound: a proposition on a block b of the first chain's record and the place's numbers Q: for every typed
                  group R, names, pull, rounds' data .. that meet the law's premises, the piece pieceOn b .. leads from K10OnS .. Q .. to the law's end, at the cap of 128 bits a round.
  k10LawAt_of     it holds of every b that is LaidAlone .. (K9.closing Q).retype .. at an address that is not K7's: k10_seated.
  first_is        F is the term that Open.desc names, and that term's first chain is c, by make.
  k10_law_sits    in scope: at EVERY block b of c.blocksInOrder whose place is of the kind K10: there are l < 25, p, Q with ProofFile.k9Where .. l = some p, ProofFile.k10Par Z .. p = some Q, c.blocksInOrder[14 l + n + 5]? = some b, and
                  K10LawAt b Q. (k10_sits_each, SitsAll.lean; the address's kind is K10: by evaluation.)
LIMITS. K10LawAt IS A "FOR ALL" OVER LETTERS WITH PREMISES: that any letters meet them at the seated place is not shown here (at the written groups the premises on numbers are paid: K10FullLay.lean,
K10SmallLay.lean for the bare block; not laid at pieceOn b). pieceOn b .. is not yet the piece that the rule above the pieces cuts of the flat list (its rounds' data, ext, err, base are letters).
All limits of SitsAll.lean (the shared and the last chain are not treated) and of Sits.lean. Nothing on soundness of the protocol.

-/
import Johnson.LPFK10R.SitsAll

set_option autoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)
open VerifiableInference.Desc (Place KindName FileDescription Chain Link)
open IM (LaidAlone)

/-- **K10's law at a block b on the first chain's record, at the place's numbers Q**: `k10_seated`'s
statement, all its letters bound. -/
def K10LawAt (b : Block VerifiableInference.Desc.First.S ProofFile.Cl) (Q : Par) : Prop :=
  ∀ {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep] {B : Type}
    [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ) (num : R.G.Row B ≃ Fin n) (fx :
    Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type} {E₀ :
    ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg
    × Wp)) (bC bZ : ℕ) (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R
    n num)).kp Wp) (L : List (BatFoldCaller GE)) (dB dE dR : RDT) (ρ : Rd (R.foldCaller keep (SbV R
    B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) (wT dB) (wT dE) (wT dR)) (hρ : ρ = realRd
    (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) dB dE dR (oneOf id)
    (oneOf id)) (hst : StepOK (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ
    w₀ w₁)).val (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).n fx
    (rd2 (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁))) (hfx : fx.2 *
    (HVar.plain GE (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
    w₁)).n).mon fx.1 = 1) (hFi : R.G.Fits) (hg : R.Good) (hj : InJ R.s R.e) (hc : CountsAt R.s R.e
    bC bZ) (he : R.G.e < R.s.d) (hv : ∀ a, (R.view a).Fix R.G.e) (hP : Pulls R pull) (pS : ∀ as : (Σ
    a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE) {W : Type} {F : Frame} (base :
    ℕ) (ext : VerifiableInference.Desc.First.S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE ::
    List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k
    dR)) → W → W) (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (R.foldCaller keep (SbV
    R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k dR))) (fa :
    VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV R B)
    (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller keep (SbV
    R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str) (x : Johnson.Bridge.FoldedPlace) (hx :
    x.Paid) (hxs : x.s = R.s) (hxe : x.e = R.e) (hxC : bC ≤ x.bC) (hxZ : bZ ≤ x.bZ) {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na)) (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb)) (y :
    Johnson.Bridge.BatPlace) (hy : y.Paid) (hys : y.s = R.s) (hye : y.e = R.e) (hyz : (ZV R n
    num).err ≤ y.rows - 1) (iB : IsRd (toRD dB) (Fmt.M2.rBatN y.rows)),
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
      (Err.cap 128 (uLT (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ds))

theorem k10LawAt_of {same : VerifiableInference.Desc.First.S → VerifiableInference.Desc.First.S → Bool}
    {b : Block VerifiableInference.Desc.First.S ProofFile.Cl} {Q : Par} {name : String} {a₀ : Place}
    (hL : LaidAlone same b
      (VerifiableInference.Desc.K9.closing Q : Block VerifiableInference.Desc.First.S Unit).retype name a₀)
    (hk7 : a₀.kind ≠ KindName.K7) : K10LawAt b Q := by
  intro S R N keep _ B _ pull n num fx Kc St₀ Wp E₀ A₀ bC bZ w₀ w₁
    L dB dE dR ρ hρ hst hfx hFi hg hj hc he hv hP pS W F base ext err fa x hx hxs hxe hxC hxZ na nb
      iE iR y hy hys hye hyz iB
  exact
    k10_seated R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc he hv hP
      pS hL hk7 base ext err fa x hx hxs hxe hxC hxZ iE iR y hy hys hye hyz iB

end VerifiableInference.Desc.First.Close

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par K10LawAt k10LawAt_of)
open ProofFile (Cl)
open IM

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {o : ProofFile.SecondHashFunctionArgument} {pol KL : ByteArray}

/-- **c is the description's first chain**: F is the term that `Open.desc` names, and that term's first
chain is c, by make. (F's own field has F's own types: so the second half is said of the term.) -/
theorem first_is (O : Open o pol lay KL F Z Bs base c A B) :
    F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      (ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c).first = c :=
  ⟨O.desc, rfl⟩

/-- **THE ROW AND THE LAW IN ONE TERM**: in scope, at every block of the flat list of c, the description's
first chain (`first_is`, `Open.desc`), whose place is of the kind K10: it stands at a named number of that list, the plan's
numbers Q are the lot's own, and K10's law holds at the piece of that very block. -/
theorem k10_law_sits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ b ∈ c.blocksInOrder, b.place.kind = KindName.K10 →
      ∃ l < 25, ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par),
        k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
        c.blocksInOrder[ixK10 l]? = some b ∧ K10LawAt b Q := by
  intro b hb hk
  obtain ⟨l, hl, Lk, p, Q, -, h2, h3, -, h5, h6⟩ := k10_sits_each hS hR O b hb hk
  exact ⟨l, hl, p, Q, h2, h3, h5, k10LawAt_of h6 (by simp)⟩

end LPFK10

#print axioms VerifiableInference.Desc.First.Close.k10LawAt_of
#print axioms LPFK10.first_is
#print axioms LPFK10.k10_law_sits
