-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/GoodOf.lean: K10's LAW IN THE FORM THAT THE RULE ABOVE THE PIECES ASKS
OF A PIECE (`Piece.GoodIn`), WITH THE TWO TIES TO A TABLE AS ONE PREMISE. A definition, statements
and proofs.

Why. K10's law is typed in the form `Leads` (Johnson/Desc/Plain/Leads.lean): from every statement
with the promise the prover has lost towards "whatever the verifier puts out stands in Q to the
statement in front". The rule above the pieces asks `Piece.GoodIn` (Johnson/Desc/Sound/GoodIn.lean;
`Piece.Own`, Johnson/Desc/Sound/Spine.lean, is that at two sets of items): .. towards "the statement
behind has the promise behind, and every witness of it gives, by the piece's extractor at this
transcript, a witness of the statement in front". The two have one shape.
  `Piece.goodIn_of_leads` (general in the piece): a law in the form `Leads`, at the piece's own
    error, with hQ: at every transcript at which the piece says yes, the law's end gives the promise
    behind and carries a witness back: gives `GoodIn`. By `Doomed.mono`.
  `K10EndS`: the end of `k10_any_self` (AtAny.lean, beside this file) as a named relation between
    the statement in front and the statement behind. `k10_any_end`: that law with its end under the
    name.
  `k10_goodIn`: at `pieceOn b ..` with the error := the cap of 128 bits a round: `GoodIn K10OnS on'
    Rf Rb` for every on', Rf, Rb with hQ.
Limits. THE LAW's BOUND "`Leads`, not `GoodIn`" IS NOT CLOSED BY THIS FILE: IT IS MOVED INTO hQ, AND
NAMED. hQ is the whole of what ties K10's law to a table: (1) the promise behind (on' a') from
`K10EndS`; (2) from a witness of the relation behind to a witness in front THROUGH THE PIECE's
EXTRACTOR ext, which is a letter here. `K10EndS` speaks of no witness: its last conjunct is an
implication from `CarriedAt` (a sentence on the statement behind) to "every word decodes and every
row holds of the decoded messages": so (2) needs: the relation behind gives `CarriedAt`; the
extractor lays the decoded messages; the rows' sums are what the table's item "row" says
(EndSays.lean, FillRow.lean, under `LaidOn`); the pins. None of these is shown here. That hQ can be
met at any on', Rf, Rb but trivial ones is not shown. All other bounds of the law stand. Nothing on
soundness of the protocol.

-/
import Johnson.Desc.First.Close.Law.AtAny
import Johnson.Desc.Sound.Spine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

/-- **From a law in the form `Leads` to what the rule above the pieces asks of a piece**
(`Piece.GoodIn`): both say "from every statement with the promise the prover has lost towards ..":
so it is enough that, at every transcript at which the piece says yes, the law's end gives the
promise behind and carries a witness back through the piece's own extractor. -/
theorem Piece.goodIn_of_leads {S Cl W : Type} {C : CK} {F : Frame} (p : Piece C F S Cl W)
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (Q : S × F.E.Str → S × F.E.Str → Prop) (h : p.ior.red.Leads on Q p.err)
    (hQ : ∀ a τ b, on a → p.ior.red.out a τ = some b → Q a b →
      on' b ∧ ∀ w, R' b w → R a (p.ext a τ w)) : p.GoodIn on on' R R' :=
  fun a ha => Doomed.mono _ _ (fun τ hτ b hb => hQ a τ b ha hb (hτ b hb)) (h a ha)

end VerifiableInference.Desc.Sound

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : S.Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

/-- **K10's law's end**, as a relation between the statement in front and the statement behind:
`k10_any_self`'s, under a name. -/
def K10EndS
    (L : List (BatFoldCaller GE))
    (dB dE dR : RDT)
    {Cl W : Type}
    {F : Frame}
    (Pr : Par)
    (b : Block VerifiableInference.Desc.First.S Cl)
    (base : ℕ)
    (ext : VerifiableInference.Desc.First.S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE ::
      List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
      w₁)).k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R
      pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k dR)))
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str)
    (a a' : VerifiableInference.Desc.First.S × F.E.Str) : Prop :=
  (∃ τ, a'.2 = (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R
    pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.imp a.2 τ ∧ sTests (ckP .two) (pieceOn (W
    := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀
    bC bZ w₀ w₁)).k ext err).stage a.2 τ = true ∧ closeFrame (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2
    (entries Pr) ((sView (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller
    keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).stage a.2 τ).rounds.map
    noDigest) = .ok (rdBK a'.1)) ∧ a'.1 = wrK a.1 (rdBK a'.1).1 (rdBK a'.1).2 ∧ ((rdK a.1).1 = none
    ∧ ∃ lk, (rdK a.1).2.1.shape.link[(rdK a.1).2.1.link]? = some lk ∧ (rdK a.1).2.1.next =
    .laterOrClose ∧ (rdK a.1).2.1.moment = reqMoments lk) ∧ (rdBK a'.1).1 = {
        (rdK a.1).2.1 with
        rows := (rdBK a'.1).1.rows, mask := none, link := (rdK a.1).2.1.link + 1, next := .first }
    ∧ (CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a) (rdBK
      a'.1).1.rows → (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧ ∀ m :
      S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) → ∀ G lay, (rdK
      a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → (begun (rdK a.1).2.2 (rdK a.1).2.1.group
      G).layout (rdK a.1).2.1.group = some lay → ∀ (r : R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows
      (rdK a.1).2.2 G).toList.length), ∑ j, rowVec N (begun (rdK a.1).2.2 (rdK a.1).2.1.group G) lay
      (runRows (rdK a.1).2.2 G).toList[i] j * (R.Sh.rho.up (R.G.msg m, r)).1 j = readE (runRows (rdK
      a.1).2.2 G).toList[i].target)

/-- `k10_any_self`, with its end under that name. -/
theorem k10_any_end
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
    {Cl W : Type}
    {F : Frame}
    (Pr : Par)
    (b : Block VerifiableInference.Desc.First.S Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2
      (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
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
      w₁ L pS Pr fa) (K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base ext err fa)
      (Err.cap 128 (uLT (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep
          (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ds)) :=
  k10_any_self R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc he hv hP
    pS Pr b H base ext err fa x hx hxs hxe hxC hxZ iE iR y hy hys hye hyz iB

/-- **K10's LAW IN THE FORM THAT THE RULE ABOVE THE PIECES ASKS** (`Piece.GoodIn`), at the piece
    whose
error is the cap of 128 bits a round: between the promise `K10OnS` and any promise on' behind, any
relations Rf in front and Rb behind, FOR WHICH THE LAW's END PAYS THE TWO TIES (hQ): at every
transcript at which the piece says yes: the promise behind; and a witness behind, carried through
the piece's own extractor, is a witness in front. -/
theorem k10_goodIn
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
    {Cl W : Type}
    {F : Frame}
    (Pr : Par)
    (b : Block VerifiableInference.Desc.First.S Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2
      (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (base : ℕ)
    (ext : VerifiableInference.Desc.First.S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE ::
      List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
      w₁)).k dR)) → W → W)
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
    (iB : IsRd (toRD dB) (Fmt.M2.rBatN y.rows))
    (on' : VerifiableInference.Desc.First.S × F.E.Str → Prop) (Rf Rb :
        VerifiableInference.Desc.First.S × F.E.Str → W → Prop)
    (hQ : ∀ a τ a', K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr fa a → (pieceOn (W := W) (F
      := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ
      w₀ w₁)).k ext (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (R.foldCaller keep
      (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k dR)))).ior.red.out a τ = some a' →
      K10EndS R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR Pr b base ext (Err.cap 128 (uLT (ckP
      .two) (dB :: dE :: List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num)
      fx A₀ bC bZ w₀ w₁)).k dR))) fa a a' → on' a' ∧ ∀ w, Rb a' w → Rf a (ext a τ w)) :
    (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n
      num) fx A₀ bC bZ w₀ w₁)).k ext (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc
      (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k dR)))).GoodIn
      (K10OnS R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS Pr fa) on' Rf Rb :=
  Piece.goodIn_of_leads _ _ _ _ _ _
    (k10_any_end R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc he hv hP
      pS Pr b H base ext (Err.cap 128 (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k dR))) fa x hx hxs hxe hxC hxZ
      iE iR y hy hys hye hyz iB) hQ

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.Sound.Piece.goodIn_of_leads
#print axioms VerifiableInference.Desc.First.Close.k10_any_end
#print axioms VerifiableInference.Desc.First.Close.k10_goodIn
