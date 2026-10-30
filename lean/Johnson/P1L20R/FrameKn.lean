-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameKn.lean:
GivesIn, a premise of frame_tiedR_ours (FrameSitsR.lean): WHAT IS
KNOWN IN FRONT OF THE FRAME'S 51 STEPS BESIDE THE PROMISE IS NAMED, AS THE TIGHT LIST, AND PAID FROM
THREE FIELDS OF FoldFacts (Johnson/Desc/First/FoldFacts.lean).

  KnTight ft k a y  the tight list: at the frame's 51 numbers: the book is in order from the tree
                    number ft on; every place of the book names a tree and a part that the book
                    holds; the rows that the last closing has returned name oracle messages for
                    which the book has a place. All three at the verifier's state a.2, in FoldFacts'
                    own letters; nothing on the strings y; off the 51 numbers: nothing
  kn_of_foldFacts   the premise of givesIn_of_kn (FrameKindR.lean) from the three fields
  givesIn_of_foldFacts   GivesIn at In := InK ... (KnTight d.ft), at every number
  kn_at9            what InAt9 hands to whoever spends the list
  fence9_of         THE FENCE (FrameOwed9.fence, FramePaid9.lean), TO THE LETTER, at KnTight ft: by
                    fence_of_in_data (Johnson/Top/H0/Walk/FrameCarryKey.lean),
                    from four named premises: three on the public side (the whole data of the files;
                    every piece's base is at most its count of the first chain's trees; the code
                    switch's first tree's number is ft) and one on the states at which the promise
                    and the list hold (the book's trees are at most the piece's base)
  frame_kindTiedR9_ff   frame_kindTiedR9 (FrameKindR.lean) with FoldFacts in the place of GivesIn

Limits. FoldFacts is a structure of statements: it is shown at nothing here; at a condition
"reached" that never holds every field is free. The fence's four premises are shown at nothing here.
No soundness statement.

-/
import Johnson.P1L20R.FrameKindR
import Johnson.P1L20R.FramePaid9
import Johnson.Desc.First.FoldFacts
import Johnson.Top.H0.Walk.FrameCarryKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf FoldData FoldFacts)
open VerifiableInference.Desc.First.K2Caller (rest)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- **THE TIGHT LIST**: what is known in front of the frame's 51 steps beside the promise. -/
def KnTight (ft : ℕ) (k : ℕ) (a : ProofFile.InstPub × S) (_y : Strs) : Prop :=
  k ∈ our51 →
    VerifiableInference.Desc.K12.Door.atFirstBook ft a.2 = true ∧
    VerifiableInference.Desc.K12.Door.atFirstFits a.2 = true ∧
    ∀ o ∈ OnBytes.singleRowsOracles a.2.live.frame.rows, o < a.2.book.place.size

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {C : CK} {D : WholeD} {all : List LeftT}
  {X₁ X₂ Xi Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  {T : ThreeAt C D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
    X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}
  {Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop}
  {Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X}
  {d : FoldData} {reqW : ProofFile.InstPub → Array UInt32} {links : List ModelPart} {ps : List Place}

/-- **The tight list, of every reached statement that bears no mark: from three fields.** -/
theorem kn_of_foldFacts (H : FoldFacts Rch (fun a => a.1) d reqW links ps) :
    ∀ k a, Rch k a → a.1.2.failed = none →
      KnTight d.ft k (a.1.1, a.1.2) (strsOf (frameAt D all D.key₁ T.ft₁) a.2) :=
  fun k a hr hu _ => ⟨H.bookInOrder k a hr hu, H.bookFits k a hr hu, H.rowsSent k a hr hu⟩

/-- **GivesIn, paid from FoldFacts.** -/
theorem givesIn_of_foldFacts (H : FoldFacts Rch (fun a => a.1) d reqW links ps) :
    ∀ k, GivesIn (T := T) Dm.N (mgAll Dm mgBase) Rch
      (InK Dm.N (mgAll Dm mgBase) (KnTight d.ft)) k :=
  givesIn_of_kn (kn_of_foldFacts H)

/-- What InAt9 hands to whoever spends the list. -/
theorem kn_at9 {ft k : ℕ} {p : ProofFile.InstPub} {s : S} {y : Strs}
    (h : InAt9 Dm (KnTight ft) k (p, s) y) (hk : k ∈ our51) :
    VerifiableInference.Desc.K12.Door.atFirstBook ft s = true ∧
    VerifiableInference.Desc.K12.Door.atFirstFits s = true ∧
    ∀ o ∈ OnBytes.singleRowsOracles s.live.frame.rows, o < s.book.place.size :=
  h.2.2 hk

/-- **THE FENCE, TO THE LETTER OF FrameOwed9.fence, at the tight list.** Dw: the whole data of the
files. -/
theorem fence9_of {ft : ℕ} (Dw : WholeD) (hW : ProofFile.wholeAt Z = some Dw)
    (hBase : ∀ k, k ∈ our51 → ∀ q, (T.p₁ :: T.l₁)[k]? = some q → q.base ≤ Dw.t₁)
    (hSize : ∀ k, k ∈ our51 → ∀ q, (T.p₁ :: T.l₁)[k]? = some q → ∀ p s y,
      InAt9 Dm (KnTight ft) k (p, s) y → s.book.trees.size ≤ q.base)
    (hFt : ∀ k, k ∈ our51 → ∀ m, openP9 (k + 1) (.carry m) → (ProofFile.pAtK2 Z m).stands = .link →
      (VerifiableInference.Desc.First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree = ft) :
    ∀ k, k ∈ our51 → ∀ q, (T.p₁ :: T.l₁)[k]? = some q → ∀ m, openP9 (k + 1) (.carry m) →
      (ProofFile.pAtK2 Z m).stands = .link → ∀ p s y, InAt9 Dm (KnTight ft) k (p, s) y →
      CarryFence Z m q.base (rest s) :=
  fun k hk q hq m hm hs =>
    fence_of_in_data Z Dw hW m q.base (hBase k hk q hq) hs (InAt9 Dm (KnTight ft) k)
      fun p s y h => by
        obtain ⟨a, b, c'⟩ := kn_at9 h hk
        exact ⟨by rw [hFt k hk m hm hs]; exact a, b, c', hSize k hk q hq p s y h⟩

/-- **The kind "frame"'s share of the chain of promises, with FoldFacts in GivesIn's place.** -/
theorem frame_kindTiedR9_ff (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : OfDesc _ T)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (H : FrameParams9 Dm Z T (KnTight d.ft))
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Wit (CellsQ rows cols) Tok MsgT →
      Wit (CellsQ rows cols) Tok MsgT)
    (hE : (∀ a b w, E 0 a b w = w) ∧ (∀ l, l < 25 → ∀ a b w, E (14 * l + 1) a b w = w) ∧
      ∀ l, l < 25 → ∀ a b w, E (clearIx l) a b w = w)
    (hN : NoneBetween Dm.N (flatPlacesOf linksFull true) 0 ∧
      (∀ l, l < 25 → NoneBetween Dm.N (flatPlacesOf linksFull true) (14 * l + 1)) ∧
      ∀ l, l < 25 → NoneBetween Dm.N (flatPlacesOf linksFull true) (clearIx l))
    (hF : FoldFacts Rch (fun a => a.1) d reqW links ps)
    (hSeal : ∀ q, (T.p₁ :: T.l₁)[357]? = some q →
      TiedAtR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) Rch 357
        (q.withMap (E 357)))
    (hBehind : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[behindIx l]? = some q →
      TiedAtR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) Rch
        (behindIx l) (q.withMap (E (behindIx l)))) :
    KindTiedR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) Rch E (T.p₁ :: T.l₁)
      KindName.frame :=
  frame_kindTiedR9 hS hR O hT hp H E hE hN (givesIn_of_foldFacts hF) hSeal hBehind

end

end P1L20

#print axioms P1L20.kn_of_foldFacts
#print axioms P1L20.givesIn_of_foldFacts
#print axioms P1L20.kn_at9
#print axioms P1L20.fence9_of
#print axioms P1L20.frame_kindTiedR9_ff
