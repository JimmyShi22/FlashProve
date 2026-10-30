-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3HeadNamed.lean: the kind "lookup" (K3), the lookup argument on the calls
at the output head's link: THE TWENTY-THREE FIELDS OF `HeadGotR` AT THE COMPOSED MEANING
(Johnson/Desc/Sound/MgAt/K3HeadR.lean) WHERE THE TABLE's READER OF OOD
SAMPLES IS THE NAMED ONE.

Main name:
  `headGotR_named`: `headGotR_mgAll` at smp := `smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x`, under
    𝔇.smp = `smpNamed 𝔇.cs seats`: the premise "the reader reads the state's statement alone" falls
    (`smpNamed_same`), and of `ListSits` three fields are left (`listSits_named`).
    WHAT IS LEFT IN FRONT OF THE TWENTY-THREE: the public parameters have the head's place · the
    head's link is 24 · the meaning beneath adds nothing to the door · the decoder does not read
    the first chain's state · that equation on 𝔇.smp · what segment 24 sends at moment 0 was sent
    before the piece · some · sent · fits · `K3Fold` (the tight list of facts along the fold) ·
    `BehindPartsR` at the piece 3 with hs and hY.

Limits: these are premises: shown together at no 𝔇. Nothing on
soundness by itself; nothing on hiding.


-/
import Johnson.Desc.Sound.MgAt.K3HeadR
import Johnson.Desc.First.Look.K3ListSitsOf

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

/-- **The twenty-three, at the named reader.** -/
theorem headGotR_named {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
    {Fr : Frame} {Cl : Type} (claim : Aff → Cl) (x : Desc.First.Look.Place)
    (seats : List (ℕ × ℕ)) (z : P) (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Wit (CellsQ rows cols) Tok MsgT))
    (s₀ : Desc.First.S) (hx : Desc.Kinds.Head.Law.headAt X = some x) (h24 : headLink X = 24)
    (hM : Mg.more = {}) (hS : Stored.NoRec 𝔇.decT) (e : 𝔇.smp = smpNamed 𝔇.cs seats)
    (hbase : ∀ t ∈ 𝔇.N.sent 24 0, t.1 < p.base)
    (hsome : ∀ i, ∃ y ∈ 𝔇.ms, Alike y
      ⟨callsSending x 𝔇.sent 𝔇.l3.rad (fun j => 𝔇.l3.seat x.link false j.1), i⟩)
    (hsent : ∀ i : Fin (sigListCalls 𝔇.sent 𝔇.l3.rad x.link).length,
      𝔇.l3.seat x.link false i.1 ∈ 𝔇.N.sent 24 0)
    (hfits : Desc.Sound.SeatFits 𝔇.G 𝔇.sent.codes (sigListCalls 𝔇.sent 𝔇.l3.rad x.link)
      fun j => 𝔇.l3.seat x.link false j.1)
    (F : K3Fold Rch 𝔇.sent)
    {arrs : Array (Nat × String)} {pl pl' : Desc.Place} {told : List (List Desc.Oracle)}
    (hs : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x).shape = some x.fs)
    (hY : ∀ a c, (∃ τ, p.ior.red.out a τ = some c) →
      ∃ (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
        (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (rs : List Fmt.RoundView)
        (cols : List (List (ℕ × List UInt64))), okRoundsE rs = true ∧
        (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
          (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) guests).decide a.1 rs
          cols = .ok c.1)
    (parts : BehindPartsR (Fr := Fr) x (Params.settingOf X.P.frame) 𝔇.N (mgAll 𝔇 Mg) linksFull PS z
      (k3K 24 false) 24 3 arrs pl pl' told (fun a c => ∃ τ, p.ior.red.out a τ = some c)
      (fun a => Rch (k3K 24 false) ((z, a.1), a.2))) :
    letI := k3SizesAt X
    letI := k3PolicyAt X
    letI := 𝔇.rq z
    HeadGotR (Fr := Fr) 𝔇.G (k3AdrAt X) x X.H.tl 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr
      𝔇.l3.nc (Params.settingOf X.P.frame) (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr
      (smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x)
      (Stored.smpWc (rows := rows) (cols := cols)) (Stored.strWc 𝔇.decT s₀ z) 𝔇.l3.msgW k3QAny
      (fun w => Flat.InRange w.cells) (fun a => Rch (k3K 24 false) ((z, a.1), a.2)) claim 𝔇.N
      (mgAll 𝔇 Mg) linksFull PS z (k3K 24 false) 24
      (fun a c => ∃ τ, p.ior.red.out a τ = some c) :=
  headGotR_mgAll 𝔇 Mg claim x (smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x) z Rch p s₀ hx h24 hM hS
    (fun z s s' h => by
      rw [e]
      funext t i
      exact smpNamed_same 𝔇.cs seats (z, s) (z, s') h t i)
    hbase (e ▸ listSits_named 𝔇.G x 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat seats 𝔇.ms 𝔇.N 24 hsome hsent hfits)
    F hs hY parts

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.headGotR_named
