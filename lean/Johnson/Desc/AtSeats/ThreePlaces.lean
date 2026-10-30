-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.AtSeats.Road
/-
THE THREE PLACES BEHIND THE FIRST CHAIN's OWN PROXIMITY TEST, EACH AS ONE CALL: «whoever has a tie at every block that is UnderR the law's
block, at every value z of the public part, at a family pc of pieces whose letters the description's piece has, has the tie of the
description's own piece». The tie of the kind's own files comes in WHOLE, as one premise H: its own premises stay with these files.
  tied355_of   at «M:3»: the law's block atM3 (whereOf Z)                    (k13_tied_seat's conclusion is H at pc := (pieceM3 …).seat)
  tied356_of   at «M:4»: atM4 (whereOf Z) (K1.sendAtS (K1.parW Z.first … 4 msg))   (w_tied_seat's at pc := K1.sendPiece · base d₁ d₂ … e)
  tied357_of   at the seal: First.firstEnd 5 front, at any front             (firstEnd_tied_seat's at pc := (pieceSeal …).seat)
In scope. NO SOUNDNESS.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf endAsks)
open ProofFile (Cl)


theorem tied355_of {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[355]? = some q)
    (links : List ModelPart) (ps : List Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w)
    (pc : Block S Cl → Piece C (frameAt D all D.key₁ T.ft₁) S Cl W)
    (hQ : ∀ c' : Block S Cl, (⟨c', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece C (frameAt D all D.key₁ T.ft₁) S Cl W) = pc c')
    (H : ∀ c' : Block S Cl, c'.UnderR (atM3 (whereOf Z)) → ∀ z : ProofFile.InstPub,
      TiedAt N Mg links ps (fun s : S => (z, s)) 355 (pc c')) :
    TiedAt N Mg links ps (fun a => a) 355 (q.withMap E) := by
  obtain ⟨⟨e, hflat, _, hu⟩, _⟩ := k13_sits_flat hS hR O
  exact tiedAt_of_seatTie hT hflat hq links ps N Mg E hE pc hQ (H _ (below_underR hu))

theorem tied356_of {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[356]? = some q)
    (links : List ModelPart) (ps : List Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w)
    (pc : Block S Cl → Piece C (frameAt D all D.key₁ T.ft₁) S Cl W)
    (hQ : ∀ c' : Block S Cl, (⟨c', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece C (frameAt D all D.key₁ T.ft₁) S Cl W) = pc c')
    (H : ∀ msg, linMessageW Z.first.lin = some msg → ∀ c' : Block S Cl,
      c'.UnderR (atM4 (whereOf Z) (K1.sendAtS
        (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg))) →
      ∀ z : ProofFile.InstPub, TiedAt N Mg links ps (fun s : S => (z, s)) 356 (pc c')) :
    TiedAt N Mg links ps (fun a => a) 356 (q.withMap E) := by
  obtain ⟨_, e, msg, hflat, _, hm, hu⟩ := k13_sits_flat hS hR O
  exact tiedAt_of_seatTie hT hflat hq links ps N Mg E hE pc hQ (H msg hm _ (below_underR hu))

theorem tied357_of {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[357]? = some q)
    (links : List ModelPart) (ps : List Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w)
    (pc : Block S Cl → Piece C (frameAt D all D.key₁ T.ft₁) S Cl W)
    (hQ : ∀ c' : Block S Cl, (⟨c', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece C (frameAt D all D.key₁ T.ft₁) S Cl W) = pc c') (front : List (Block S Cl))
    (H : ∀ c' : Block S Cl, c'.UnderR (First.firstEnd 5 front) → ∀ z : ProofFile.InstPub,
      TiedAt N Mg links ps (fun s : S => (z, s)) 357 (pc c')) :
    TiedAt N Mg links ps (fun a => a) 357 (q.withMap E) := by
  obtain ⟨e, hflat, _, hu⟩ := k13_sits_flat357 hS hR O
  exact tiedAt_of_seatTie hT hflat hq links ps N Mg E hE pc hQ
    (H _ (below_underR (hu.trans ⟨rfl, fun _ _ _ _ h => h⟩)))

end VerifiableInference.Desc.K13.Law
