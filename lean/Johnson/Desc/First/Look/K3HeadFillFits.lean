-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3HeadFillFits.lean: the kind "lookup" (K3), the lookup argument on the
calls at the output head's link: LEAN's WORD THAT THE LAYERS' THREE LEMMAS ON worth HAVE THE TYPES OF
`HeadAtTable`'s THREE FIELDS (Johnson/Desc/First/Look/K3HeadAtTable.lean).

Main names: `head_fill_fits` (the layer `fillK3Head`, at the guard that always holds) ·
`head_fillG_fits` (the layer `fillK3HeadG`, at its own guard): each field of any member IS the
lemma (two proofs of one sentence).

Why a file of its own: the composed meaning imports K3HeadFill.lean and K3HeadFillG.lean,
whose layers stand over the definitions alone. The two checks need the kind's LAW files,
so they stand here, apart from the meaning's text. Their text is taken from those two files.

Limits: two checks of types. Nothing on soundness; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3HeadFillG
import Johnson.Desc.First.Look.K3HeadAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr headLay headRider)

variable [Desc.Kinds.Head.Sizes] [Desc.Kinds.Head.Policy]

section
variable {P Cells Tok : Type} (X : Verify.Public) (D : Desc.First.Look.Sent)
  (L : K3Letters Cells Tok) (adr : HeadAdr) (rq : P → Desc.Kinds.Head.Request)
  (gd : Desc.Wit Cells Tok MsgT → Prop) (Mg : Meaning P (Desc.Wit Cells Tok MsgT))

/-- **Lean's word that the three lemmas have the types of `HeadAtTable`'s three fields** at the
layer's term and letters, at the guard that always holds: each field of any member IS the lemma
(two proofs of one sentence). -/
theorem head_fill_fits {Cl Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) (set : Params.Setting)
    {x : Desc.First.Look.Place} (hx : Desc.Kinds.Head.Law.headAt X = some x)
    (smp : Desc.First.S → (i : Fin (sigListCalls D L.rad x.link).length) →
      Option ((attSg x D L.rad).om i).Smp)
    (smpW : Desc.First.S → Option L.oW.Smp) (strW : Fr.E.Str → L.oW.Str) (Q : Fork → Prop)
    (claim : Aff → Cl) (N : Desc.First.Numbers) (links : List Desc.First.ModelPart)
    (ps : List Desc.Place) (z : P) (k : ℕ)
    (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop) :
    letI := rq z
    ∀ T : HeadAtTable (Fr := Fr) G adr x X.H.tl D L.rad L.oW L.wOf L.nr L.nc set
      (fun j => L.seat x.link false j.1) L.arr smp smpW strW L.msgW Q (fun _ => True) claim N
      (fillK3Head X D L adr rq Mg) links ps z k (headLink X) Yes,
      T.worthP = (fun s y w h _ => headP_fill X D L adr rq Mg claim hx z s y w h) ∧
        T.worthK = (fun s y w h _ => headK_fill X D L adr rq Mg claim hx z s y w h) ∧
        T.worthR = (fun s y w h _ => headR_fill X D L adr rq Mg claim hx z s y w h) :=
  fun _ => ⟨rfl, rfl, rfl⟩

/-- **Lean's word that the three lemmas have the types of `HeadAtTable`'s three fields** at the
layer's term and letters. -/
theorem head_fillG_fits {Cl Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) (set : Params.Setting)
    {x : Desc.First.Look.Place} (hx : Desc.Kinds.Head.Law.headAt X = some x)
    (smp : Desc.First.S → (i : Fin (sigListCalls D L.rad x.link).length) →
      Option ((attSg x D L.rad).om i).Smp)
    (smpW : Desc.First.S → Option L.oW.Smp) (strW : Fr.E.Str → L.oW.Str) (Q : Fork → Prop)
    (claim : Aff → Cl) (N : Desc.First.Numbers) (links : List Desc.First.ModelPart)
    (ps : List Desc.Place) (z : P) (k : ℕ)
    (Yes : Desc.First.S × Fr.E.Str → Desc.First.S × Fr.E.Str → Prop) :
    letI := rq z
    ∀ T : HeadAtTable (Fr := Fr) G adr x X.H.tl D L.rad L.oW L.wOf L.nr L.nc set
      (fun j => L.seat x.link false j.1) L.arr smp smpW strW L.msgW Q gd claim N
      (fillK3HeadG X D L adr rq gd Mg) links ps z k (headLink X) Yes,
      T.worthP = (fun s y w h hg => headP_fillG X D L adr rq gd Mg claim hx z s y w h hg) ∧
        T.worthK = (fun s y w h hg => headK_fillG X D L adr rq gd Mg claim hx z s y w h hg) ∧
        T.worthR = (fun s y w h hg => headR_fillG X D L adr rq gd Mg claim hx z s y w h hg) :=
  fun _ => ⟨rfl, rfl, rfl⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.head_fill_fits
#print axioms VerifiableInference.OnPublicFiles.head_fillG_fits
