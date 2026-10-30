-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3HeadMean.lean: the kind "lookup" (K3), the lookup argument on the calls at
the output head's link: `HeadMeanR` (Johnson/Desc/First/Look/K3MeansR.lean: what the kind's law asks
of the meaning and of the readers there, second form) AT THE COMPOSED MEANING `mgAll 𝔇 Mg`,
at the named readers.

Main name:
  `headMeanR_mgAll`: all eight fields of `HeadMeanR`, at smp := `smpCalls`, smpW := `Stored.smpWc`,
    strW z := `Stored.strWc 𝔇.decT s₀ z`, Q := `k3QAny`, gd := "the cells are in range".
    PAID HERE: hsmp, hsmpW (`calls_hsmp`: the readers read the state's statement alone) · hstrW,
    smpW0 (`stored_paid`) · hseat (each seat is among what segment 24 sends at moment 0, and that
    was sent before the piece) · smp0 · table (`headGotR_named` with `HeadLeftR`).
    LEFT AS PREMISES: the facts on the constant and the piece (h, hOk, hl, hpcX, e, hback, hs) · the
    plain ones of `headGotR_named` · `K3Fold` · `BehindPartsR` at the piece 3 · `HeadLeftR`
    (objects, model, smallBack) · rides (`RidesAtR`).

Limits: these are premises: shown together at no 𝔇. Rch is a letter. The
full size's written lists alone. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.Sound.MgAt.K3HeadNamed
import Johnson.Desc.First.Look.K3MeansR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc (Wit)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **`HeadMeanR` at the term.** -/
theorem headMeanR_mgAll {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    {Fr : Frame} {Cl : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (x : Desc.First.Look.Place)
    (seats : List (ℕ × ℕ)) (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
    (a : Desc.Place) (b' : Desc.Block Desc.First.S Cl)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (s₀ : Desc.First.S)
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hl : a.link = some 24) (hpcX : a.piece = Desc.K3.pieceAt X 24 false)
    (e : placeAt X 24 false =
      some (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x))
    (hback : q.back = [])
    (hs : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x).shape = some x.fs)
    (hx : Desc.Kinds.Head.Law.headAt X = some x) (h24 : headLink X = 24)
    (hM : Mg.more = {}) (hS : Stored.NoRec 𝔇.decT) (es : 𝔇.smp = smpNamed 𝔇.cs seats)
    (hbase : ∀ t ∈ 𝔇.N.sent 24 0, t.1 < q.base)
    (hsome : ∀ i, ∃ y ∈ 𝔇.ms, Alike y
      ⟨callsSending x 𝔇.sent 𝔇.l3.rad (fun j => 𝔇.l3.seat x.link false j.1), i⟩)
    (hsent : ∀ i : Fin (sigListCalls 𝔇.sent 𝔇.l3.rad x.link).length,
      𝔇.l3.seat x.link false i.1 ∈ 𝔇.N.sent 24 0)
    (hfits : Desc.Sound.SeatFits 𝔇.G 𝔇.sent.codes (sigListCalls 𝔇.sent 𝔇.l3.rad x.link)
      fun j => 𝔇.l3.seat x.link false j.1)
    (F : K3Fold Rch 𝔇.sent)
    {arrs : Array (Nat × String)} {pl pl' : Desc.Place} {told : List (List Desc.Oracle)}
    (Bp : ∀ B', SeatOf b' B' → ∀ z : P,
      BehindPartsR (Fr := Fr) x (Params.settingOf X.P.frame) 𝔇.N (mgAll 𝔇 Mg) linksFull PS z
        (k3K 24 false) 24 3 arrs pl pl' told
        (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
        (fun u => Rch (k3K 24 false) ((z, u.1), u.2)))
    (Left : ∀ B', SeatOf b' B' → ∀ z : P,
      letI := k3SizesAt X
      letI := k3PolicyAt X
      letI := 𝔇.rq z
      HeadLeftR (Fr := Fr) 𝔇.G (k3AdrAt X) x X.H.tl 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr
        𝔇.l3.nc (Params.settingOf X.P.frame) (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr
        (smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x)
        (Stored.smpWc (rows := rows) (cols := cols)) (Stored.strWc 𝔇.decT s₀ z) 𝔇.l3.msgW k3QAny
        (fun w => Flat.InRange w.cells) (fun u => Rch (k3K 24 false) ((z, u.1), u.2)) claim 𝔇.N
        (mgAll 𝔇 Mg) linksFull PS z (k3K 24 false) 24
        (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v))
    (rides : RidesAtR 𝔇.N (mgAll 𝔇 Mg) Rch (k3K 24 false) q b') :
    letI := k3SizesAt X
    letI := k3PolicyAt X
    HeadMeanR 𝔇.G X 𝔇.sent 𝔇.l3 𝔇.N (mgAll 𝔇 Mg) Rch claim a (k3K 24 false) 24 (k3AdrAt X) 𝔇.rq
      k3QAny (fun w => Flat.InRange w.cells) x (smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x)
      (Stored.smpWc (rows := rows) (cols := cols)) (fun z => Stored.strWc 𝔇.decT s₀ z) q b' := by
  letI := k3SizesAt X
  letI := k3PolicyAt X
  have SP := stored_paid (Fr := Fr) (Mg := mgAll 𝔇 Mg) (decT := 𝔇.decT) s₀ (mgAll_decodes 𝔇 Mg)
    (mgAll_pinW 𝔇 Mg) hS
  exact
    { hsmp := calls_hsmp claim a.piece _ _
        (fun s s' hst _ => smpCalls_same seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x s s' hst)
      hsmpW := calls_hsmp claim a.piece _ (Stored.smpWc (rows := rows) (cols := cols))
        (fun _ _ _ _ => rfl)
      hstrW := fun z y τ => SP.hstrW (ckP .two) q.base q.ds z y τ
      hseat := fun i => hbase _ (hsent i)
      smp0 := smp_nonempty _
      smpW0 := SP.smpW0
      table := fun B' hB z =>
        headAtTableR_mgAll 𝔇 Mg claim x _ z Rch (strictAt B' q) s₀
          (headGotR_named 𝔇 Mg claim x seats z Rch (strictAt B' q) s₀ hx h24 hM hS es hbase hsome
            hsent hfits F hs
            (seat_yes claim readers codes shape h hOk hl hpcX e hback B' hB) (Bp B' hB z))
          (Left B' hB z)
      rides := rides }

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.headMeanR_mgAll
