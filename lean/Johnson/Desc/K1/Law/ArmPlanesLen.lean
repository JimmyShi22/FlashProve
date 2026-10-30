-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmPlanesLen.lean: THE OUTPUT HEAD's HALF OF THE BINDER hArm AT THE RUN "planes": THE CLAUSE
hlen (what the lookup on the calls heard is no longer than the planes' matrix has room) READ OFF THE PROMISE
IN FRONT OF THE READS' PLACE: the lookups' sentence at the public item leftOn 24 (leftOn_at342,
Johnson/Desc/K1/Law/ArmHeadBare.lean) says that what was heard has THE PLAN's OWN SHAPE (K3Left.shape): so the
clause falls to a sentence on the public parameters alone (hLen). A PAYER OF THE FIELD hPl' (PlanesLeft4) FROM
ITS LAST CLAUSE, hHostC. A definition, and statements with their proofs: calls.

Main names:
  shape_at342         what the lookup heard has the shape of the plan's place.
  hlen_at342          **the clause.**
  PlanesLeft5         PlanesLeft4 less hlen: hHostC alone.
  planesLeft4_of      **PlanesLeft4 inside the fence, from hLen and PlanesLeft5.**
What is not claimed. hLen; hHostC. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.ArmHeadBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgBase)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (p8K6)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)

/-- What the lookup on the calls heard has the shape of the plan's place. -/
theorem shape_at342 {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) :
    ∃ p h, First.Look.placeAt XV 24 false = some p ∧ p.shape = some h ∧
      ∀ gk, x.2.lookHeard? = some gk → gk.shape = h := by
  obtain ⟨p, hp, ⟨h, hsh, F, F', G, g, rs, _, _, hK, hh, _⟩, _⟩ := leftOn_at342 Dm dk hIn
  refine ⟨p, h, hp, hsh, fun gk hg => ?_⟩
  obtain rfl : g = gk := Option.some.inj (hh.symm.trans hg)
  exact hK.shape

/-- **The clause hlen**, from a sentence on the public parameters. -/
theorem hlen_at342
    (hLen : ∀ p h, First.Look.placeAt XV 24 false = some p → p.shape = some h →
      h.NC * 2 ^ (h.kT + 5 - (p8K6 XV 24).h.lmbH) ≤
        ((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).k *
          (((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).m /
            2 ^ (p8K6 XV 24).h.lmbH))
    {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) :
    ∀ gk, x.2.lookHeard? = some gk →
      gk.shape.NC * 2 ^ (gk.shape.kT + 5 - (p8K6 XV 24).h.lmbH) ≤
        ((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).k *
          (((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).m /
            2 ^ (p8K6 XV 24).h.lmbH) := by
  obtain ⟨p, h, hp, hsh, hg⟩ := shape_at342 Dm dk hIn
  intro gk hk
  rw [hg gk hk]
  exact hLen p h hp hsh

end

section
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head
  VerifiableInference.Desc.Kinds
open OnBytes (E zeroE)
open OnBytes.Model (World Reading HFun HTailF2 Fork)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K9 (Readers RunOf)
open VerifiableInference.Desc.Sound (dataQ Mem MsgT cellsAt seatTab worldOwn ArmCellIn)
open VerifiableInference.Desc.Kinds.Head.Law.Planes

/-- **PlanesLeft4 less hlen.** -/
structure PlanesLeft5 (X : OnBytes.Model.Verify.Public) (own own' : List (Nat × Nat))
    (s : S) (a b : K9.Part) (rdW : Nat × Nat → Sound.MsgQ) : Prop where
  hHostC : ∀ e r gk, withTables (p8K6 X 24) s = some e →
      callerReaders (planesAt (readsOf X)) e = some r → e.lookHeard? = some gk →
      Meaning.Planes.K3HostPlanes gk.shape (p8K6 X 24).h.lmbH (_root_.Fo.rdL Reading.gl gk.zb0)
        (_root_.Fo.rdL Reading.gl gk.zb1) (nuK6 X s (Sound.dataQ own a rdW))
        (fun f => f.value Reading.gl (worldOwn b [] (Sound.dataQ own' b rdW)))
        (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {})

end

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}

/-- **PlanesLeft4 at a state inside the promise in front of the reads' place.** -/
theorem planesLeft4_of (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
    (hLen : ∀ p h, First.Look.placeAt XV 24 false = some p → p.shape = some h →
      h.NC * 2 ^ (h.kT + 5 - (p8K6 XV 24).h.lmbH) ≤
        ((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).k *
          (((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).m /
            2 ^ (p8K6 XV 24).h.lmbH))
    {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) {own own' : List (ℕ × ℕ)} {a b : K9.Part}
    {rdW : ℕ × ℕ → Sound.MsgQ} (L : PlanesLeft5 XV own own' x.2 a b rdW) :
    PlanesLeft4 XV own own' x.2 a b rdW :=
  ⟨hlen_at342 Dm dk hLen hIn, L.hHostC⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.shape_at342
#print axioms VerifiableInference.Desc.K1.hlen_at342
#print axioms VerifiableInference.Desc.K1.planesLeft4_of
