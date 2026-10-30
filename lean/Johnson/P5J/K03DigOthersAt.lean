-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03DigOthersAt.lean: THE KIND "LOOKUP" (K3): THE FIELD othersPub ("the other kinds' public tests that are open behind hold behind") OF WHAT IS LEFT AT A SEGMENT's DIGITS (DigShortR, Johnson/P5J/K03DigAt.lean), AT THE CONSTANT, AT ALL 25 SEGMENTS: by one call of the lookup's files' othersPub_dig_mgAll (Johnson/Desc/Sound/MgAt/K3DigitsOthers.lean). Two abbreviations, two theorems. THE FENCE: the ledger's text othersPub at the digits has two premises behind the promise in front: "reached" (Rch (k3K l true) ((z, u.1), u.2)) and "no mark" (u.1.failed = none); the lookups' theorem, its debt hForms and DigShortR's field have them too: both abbreviations take Rch. A joining: by calls alone.
  DigFormsR Dm Mg Rch l sub q b' : Prop: THE ONE DEBT THAT IS LEFT, in that theorem's own text (its binder hForms, lifted by program): across an accept of the digits' piece every item "formsIn l pc nm" among keptDigits l sub ++ newDigits l sub holds behind.
  DigOthersR Dm Mg Rch l q b' : Prop: the field's sentence, as that theorem ends (lifted by program).
  k03_othersPub_dig: UNDER h : AtMgA OnBytes.secondHashFunction …, 𝔏 : Free … with the three equations q₁ q₂ q₃, l < 25, the written sort, digAt X l = some (x, tl), the row's piece q, the kind's constant b' AND DigFormsR: DigOthersR at 𝔇 := h.toAtMg.𝔇 h.𝔇 · mgBase · h.toAtMg.rch.
  PAID: hM (k03_hM) · hlinks (𝔇.links = linksFull: rfl) · hBase (mgBase's public tests read no state: rfl) · hOk | hback (k03_pieces_at).
  k03_digShort_others: A TRIPWIRE: laid as the field othersPub into a value of DigShortR, it types.
Limits. DigFormsR is a premise: no member is shown. The head is a premise. At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03DigAt
import Johnson.Desc.Sound.MgAt.K3DigitsOthers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open VerifiableInference.Desc.First (ModelPart Pub Meaning shift pubFit pubSets pubStep pubRowM pubOfItems
  stepOpen openSets start pubAll_ledger pubAll_freeAbove)


section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
  (l : ℕ) (sub : ModelPart)
  (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (b' : Desc.Block Desc.First.S ProofFile.Cl)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- The one debt that is left. -/
abbrev DigFormsR : Prop :=
  ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        ∀ r ∈ keptDigits l sub ++ newDigits l sub, (∃ pc nm, r = .formsIn l pc nm) →
        (mgAll Dm Mg).pub r (z, v.1) = true

/-- The field's sentence. -/
abbrev DigOthersR : Prop :=
    ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
      ∀ r ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[(k3K l true)]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull (IM.k3Place l true)) ++
        pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[(k3K l true)]?.getD [])
          (Desc.First.rowOf linksFull (IM.k3Place l true))),
      k3Like r = false → (mgAll Dm Mg).pub r (z, v.1) = true

end

end VerifiableInference.OnPublicFiles

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
  (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

/-- **THE FIELD othersPub AT THE CONSTANT, AT ALL 25 LOOKUPS ON THE DIGITS.** -/
theorem k03_othersPub_dig (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {l : ℕ} (hl : l < 25) {sub : VerifiableInference.Desc.First.ModelPart} (hsub : linksFull[l]? = some sub)
    {x : Place} {tl : HTailF2} (hx : digAt (At.X Zp) l = some (x, tl))
    (q) (hq : (h.toAtMg.row 𝔏)[k3K l true]? = some q)
    (b') (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b')
    (hF : DigFormsR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l sub q b') :
    DigOthersR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l q b' := by
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  exact othersPub_dig_mgAll (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch Zp.first.codes Zp.first.shape k03_hM
    rfl (fun _ _ _ _ => rfl) hl hsub hx q b' hb (Pc.planOk l hl true b' hb)
    (Pc.back l hl true q hq) hF

/-- **A TRIPWIRE: the sentence is DigShortR's field othersPub to the letter.** -/
theorem k03_digShort_others (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {l : ℕ} (hl : l < 25) {sub : VerifiableInference.Desc.First.ModelPart} (hsub : linksFull[l]? = some sub)
    {x : Place} {tl : HTailF2} (hx : digAt (At.X Zp) l = some (x, tl))
    (q) (hq : (h.toAtMg.row 𝔏)[k3K l true]? = some q)
    (b') (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b')
    (hF : DigFormsR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l sub q b')
    (nos : Array ℕ) (n : ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid) (M : List OracleShape)
    (S : DigShortR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l x q b' nos n Ld M) :
    DigShortR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l x q b' nos n Ld M :=
  { S with othersPub := k03_othersPub_dig h 𝔏 q₁ q₂ q₃ hl hsub hx q hq b' hb hF }

end P5J

#print axioms P5J.k03_othersPub_dig
#print axioms P5J.k03_digShort_others
