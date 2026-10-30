-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameKindR.lean:
the end of frame_tiedR_ours (FrameSitsR.lean) IS KindTiedR at the kind "frame"
(Johnson/Desc/Sound/TiedR.lean): so it is one of the "for every kind" that eachTiedR_of_kinds takes.

  frame_kindTiedR   KindTiedR N Mg linksFull (the written list) Rch E (T.p₁ :: T.l₁) KindName.frame,
                    under frame_tiedR_ours' premises
  frame_kindTiedR9  the same at the composed meaning mgAll Dm mgBase, N := Dm.N, from
                    FrameParams9 (FrameRows9.lean), the two premises on E and Dm.N, GivesIn, and the
                    two shares that are other files' to show
  givesIn_of_kn     GivesIn's first half is the promise itself: what is owed is Kn k of every
                    reached statement that bears no mark

Limits. FrameSitsR.lean's and FrameRows9.lean's: no premise is shown at a filling. No soundness
statement.

-/
import Johnson.P1L20R.FrameRows9
import Johnson.Desc.Sound.TiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers flatPlacesOf)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {C : CK} {D : WholeD} {all : List LeftT}
  {X₁ X₂ W : Type}
  {T : ThreeAt C D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
    X₁ X₂ W}
  {Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop}
  {In : ℕ → ProofFile.InstPub × S → Strs → Prop}

/-- **The kind "frame"'s share of the chain of promises, under the name KindTiedR.** -/
theorem frame_kindTiedR (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : OfDesc _ T)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (Hold : ProofFile.InstPub × S → W → OnBytes.TensorRow → Prop)
    (H : FrameOwesR (T := T) N Mg Z E Hold In) (hI : ∀ k, GivesIn (T := T) N Mg Rch In k)
    (hSeal : ∀ q, (T.p₁ :: T.l₁)[357]? = some q →
      TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch 357
        (q.withMap (E 357)))
    (hBehind : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[behindIx l]? = some q →
      TiedAtR N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) Rch (behindIx l)
        (q.withMap (E (behindIx l)))) :
    KindTiedR N Mg linksFull (flatPlacesOf linksFull true) Rch E (T.p₁ :: T.l₁) KindName.frame :=
  frame_tiedR_ours hS hR O hT hp N Mg E Hold H hI hSeal hBehind

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {C : CK} {D : WholeD} {all : List LeftT}
  {X₁ X₂ Xi Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  {T : ThreeAt C D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
    X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}
  {Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop}
  {Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X} {Kn : ℕ → ProofFile.InstPub × S → Strs → Prop}

/-- **The same at the composed meaning**, from FrameParams9. -/
theorem frame_kindTiedR9 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : OfDesc _ T)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (H : FrameParams9 Dm Z T Kn)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Wit (CellsQ rows cols) Tok MsgT →
      Wit (CellsQ rows cols) Tok MsgT)
    (hE : (∀ a b w, E 0 a b w = w) ∧ (∀ l, l < 25 → ∀ a b w, E (14 * l + 1) a b w = w) ∧
      ∀ l, l < 25 → ∀ a b w, E (clearIx l) a b w = w)
    (hN : NoneBetween Dm.N (flatPlacesOf linksFull true) 0 ∧
      (∀ l, l < 25 → NoneBetween Dm.N (flatPlacesOf linksFull true) (14 * l + 1)) ∧
      ∀ l, l < 25 → NoneBetween Dm.N (flatPlacesOf linksFull true) (clearIx l))
    (hI : ∀ k, GivesIn (T := T) Dm.N (mgAll Dm mgBase) Rch (InK Dm.N (mgAll Dm mgBase) Kn) k)
    (hSeal : ∀ q, (T.p₁ :: T.l₁)[357]? = some q →
      TiedAtR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) Rch 357
        (q.withMap (E 357)))
    (hBehind : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[behindIx l]? = some q →
      TiedAtR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) Rch
        (behindIx l) (q.withMap (E (behindIx l)))) :
    KindTiedR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) Rch E (T.p₁ :: T.l₁)
      KindName.frame :=
  frame_kindTiedR hS hR O hT hp Dm.N (mgAll Dm mgBase) E (holdAt Dm) (frameOwes9_of H E hE hN) hI
    hSeal hBehind

/-- What GivesIn asks beyond the promise: Kn k of every reached statement that bears no mark. -/
theorem givesIn_of_kn
    (h : ∀ k a, Rch k a → a.1.2.failed = none →
      Kn k (a.1.1, a.1.2) (strsOf (frameAt D all D.key₁ T.ft₁) a.2)) :
    ∀ k, GivesIn (T := T) Dm.N (mgAll Dm mgBase) Rch (InK Dm.N (mgAll Dm mgBase) Kn) k :=
  fun k a ha hr hu => ⟨ha, h k a hr hu⟩

end

end P1L20

#print axioms P1L20.frame_kindTiedR
#print axioms P1L20.frame_kindTiedR9
#print axioms P1L20.givesIn_of_kn
