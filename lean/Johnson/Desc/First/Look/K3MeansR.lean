-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3MeansR.lean: the kind "lookup" (K3): ALL THAT THE KIND's FIFTY PLACES ASK
OF THE MEANING, IN THE SECOND FORM ("reached" in hand): one structure.

Main names:
  `HeadMeanR`: at the output head's calls: the premises of `k3_head_seatLawsR`
    (Johnson/Desc/First/Look/K3HeadAtTableR.lean) that speak of the meaning or of the readers.
  `K3MeanR`: the four sorts together: dig (`DigMeanR`), att (`AttMeanR`), lay (`LayMeanR`): the
    lookups' authors' structures (K3MeansDigR.lean, K3CallsMeanR.lean), taken as they typed them;
    head (`HeadMeanR`).

Limits: structures over letters (N, Mg, Rch, the readers, the guard gd); shown at no term; not tried
for emptiness. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3Base
import Johnson.Desc.First.Look.K3MeansDigR
import Johnson.Desc.First.Look.K3CallsMeanR
import Johnson.Desc.First.Look.K3HeadAtTableR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn shift pubFit)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr)

variable [Desc.Kinds.Head.Sizes] [Desc.Kinds.Head.Policy]

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) (X : Verify.Public)
  (Dn : Desc.First.Look.Sent) (L : K3Letters Cells Tok) (N : Numbers)
  (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Cl)

local notation "WT" => Desc.Wit Cells Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
set_option quotPrecheck false in
local notation "PieceT" => Piece (ckP .two) Fr (P × Desc.First.S) Cl WT

/-- **At the head's calls, second form.** rq: the kind's letter "the request", of the public
part. -/
structure HeadMeanR (a : Desc.Place) (k l : ℕ) (adr : HeadAdr)
    (rq : P → Desc.Kinds.Head.Request) (Q : Fork → Prop)
    (gd : Desc.Wit Cells Tok MsgT → Prop) (x : Desc.First.Look.Place)
    (smp : Desc.First.S → (i : Fin (sigListCalls Dn L.rad x.link).length) →
      Option ((attSg x Dn L.rad).om i).Smp)
    (smpW : Desc.First.S → Option L.oW.Smp) (strW : P → Fr.E.Str → L.oW.Str)
    (q : PieceT) (b' : Desc.Block Desc.First.S Cl) : Prop where
  hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).planOk =
        true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).decide s rs
        cols = .ok s' → smp s' = smp s
  hsmpW : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).planOk =
        true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).decide s rs
        cols = .ok s' → smpW s' = smpW s
  hstrW : ∀ (z : P) y (τ : Tr (uLT (ckP .two) q.ds)),
    strW z (behind (ckP .two) Fr q.base q.ds y τ) = strW z y
  hseat : ∀ i : Fin (sigListCalls Dn L.rad x.link).length, (L.seat x.link false i.1).1 < q.base
  smp0 : Nonempty (attSg x Dn L.rad).Smp
  smpW0 : Nonempty L.oW.Smp
  table : ∀ B', SeatOf b' B' → ∀ z : P, letI := rq z
    HeadAtTableR (Fr := Fr) G adr x X.H.tl Dn L.rad L.oW L.wOf L.nr L.nc SET
      (fun j => L.seat x.link false j.1) L.arr smp smpW (strW z) L.msgW Q gd
      (fun a => Rch k ((z, a.1), a.2)) claim N Mg linksFull PS z k l
      (fun a c => ∃ τ, (strictAt B' q).ior.red.out a τ = some c)
  rides : RidesAtR N Mg Rch k q b'

end

section
variable {P Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) (X : Verify.Public)
  (codes : Codes) (shape : Params.ReqShape)
  (Dn : Desc.First.Look.Sent) (L : K3Letters Cells Tok) (N : Numbers)
  (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
  (pieces : List (Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl (Desc.Wit Cells Tok MsgT)))
  (smpC : (x : Desc.First.Look.Place) → Desc.First.S →
    (i : Fin (sigListCalls Dn L.rad x.link).length) → Option ((attSg x Dn L.rad).om i).Smp)
  (smpD : (x : Desc.First.Look.Place) → Desc.First.S →
    (i : Fin (digList x Dn L.rad).length) → Option ((digSg x Dn L.rad).om i).Smp)
  (smpW : Desc.First.S → Option L.oW.Smp) (strW : P → Fr.E.Str → L.oW.Str)
  (adr : HeadAdr) (rq : P → Desc.Kinds.Head.Request) (Q : Fork → Prop)
  (gd : Desc.Wit Cells Tok MsgT → Prop)

/-- **ALL THAT THE KIND's FIFTY PLACES ASK OF THE MEANING, SECOND FORM.** pieces: the maker's first
row. -/
structure K3MeanR : Prop where
  dig : ∀ l < 25, ∀ sub, linksFull[l]? = some sub → ∀ x tl, digAt X l = some (x, tl) →
    ∀ q, pieces[k3K l true]? = some q → ∀ b', k3Const X codes shape l true = some b' →
      DigMeanR G X Dn L N Mg Rch K3Lot.ofForm (IM.k3Place l true) (k3K l true) l sub x tl (smpD x)
        q b'
  att : ∀ l < 25, ∀ x A tl, attAt X l = some (x, A, tl) →
    ∀ q, pieces[k3K l false]? = some q → ∀ b', k3Const X codes shape l false = some b' →
      AttMeanR G X Dn L N Mg K3Lot.ofForm Rch (IM.k3Place l false) (k3K l false) l x A tl (smpC x)
        q b'
  lay : ∀ l < 25, ∀ x tl, layAt X l = some x → tlAt X l = some tl →
    ∀ q, pieces[k3K l false]? = some q → ∀ b', k3Const X codes shape l false = some b' →
      LayMeanR G X Dn L N Mg K3Lot.ofForm Rch (IM.k3Place l false) (k3K l false) l x tl (smpC x)
        smpW strW q b'
  head : ∀ x, Desc.Kinds.Head.Law.headAt X = some x →
    ∀ q, pieces[k3K 24 false]? = some q → ∀ b', k3Const X codes shape 24 false = some b' →
      HeadMeanR G X Dn L N Mg Rch K3Lot.ofForm (IM.k3Place 24 false) (k3K 24 false) 24 adr rq Q gd
        x (smpC x) smpW strW q b'

end

end VerifiableInference.OnPublicFiles
