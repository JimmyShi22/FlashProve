-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReExt.lean: THE PLAIN FORM'S PREMISE ON A CHAIN READS NO PIECE'S EXTRACTOR: SO A
ROW'S LAWS MAY BE OWED AT THE SAME PIECES WITH THE TABLE'S EXTRACTOR LAID IN. Three definitions and
eight lemmas. No protocol's soundness is said.

Why. The plain form's premise on a chain (`EachLeads`, Johnson/Desc/Plain/FoldChain.lean) reads of a
piece its reduction and its errors, never its extractor. What a kind owes at a table of joints
(`Piece.Own`, `Piece.Frames`) names the piece's extractor, which is handed the stretch's transcript;
the table's extractor is a map E of a block's two statements.
  `Piece.withMap p E`: the same piece (block, base, data, rounds put back, errors) with the
    extractor "where the block says yes and puts out b: E a b w; else w".
  `withMap_ext`: so at every yes its extractor IS E: by the make: no reader of a transcript is
    wanted.
  `withMap_id`: where E lays nothing it is the identity, at every transcript.
  `goodIn_withMap`, `own_withMap`, `frames_withMap`: a law that was proved at the piece's OWN
    extractor counts at the piece so turned, where that extractor is E at every yes.
  `reExt E k l`: along a row, from block number k on.
  `eachLeads_of_reExt`: the plain form's premise at the row so turned gives the premise at the row
    itself.
  `eachE_reExt`: the row so turned has `EachE` at E, given the sure facts at the row itself.
  `eachLeads_of_goodIn_reExt`: **`EachGoodIn` at the row so turned, and the sure facts, give
    `EachLeads` at THE ROW ITSELF**, at the relation "one witness carried by E; the sure facts".

Limits. On the road with extractors (knowledge soundness) the pieces' own extractors are read: there
the pieces themselves must be made so (a maker whose extractors are "where the block says yes and
puts out b: E a b w; else w"): not typed. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.LeadsE
import Johnson.Desc.Sound.Spine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Plain
open _root_.Iop (Doomed)

variable {S Cl W ι : Type} {C : CK} {F : Frame}

/-- **The same piece with the map E as its extractor.** -/
def Piece.withMap (p : Piece C F S Cl W) (E : S × F.E.Str → S × F.E.Str → W → W) :
    Piece C F S Cl W :=
  { p with
    ext := fun a τ w => match p.ior.red.out a τ with
      | some b => E a b w
      | none => w }

/-- At every yes its extractor is E. -/
theorem withMap_ext (p : Piece C F S Cl W) (E : S × F.E.Str → S × F.E.Str → W → W)
    (a : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (b : S × F.E.Str) (w : W)
    (h : (p.withMap E).ior.red.out a τ = some b) : (p.withMap E).ext a τ w = E a b w := by
  have h' : p.ior.red.out a τ = some b := h
  show (match p.ior.red.out a τ with
    | some b => E a b w
    | none => w) = E a b w
  rw [h']

/-- Where E lays nothing, its extractor is the identity, at every transcript. -/
theorem withMap_id (p : Piece C F S Cl W) (E : S × F.E.Str → S × F.E.Str → W → W)
    (hE : ∀ a b w, E a b w = w) (a : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (w : W) :
    (p.withMap E).ext a τ w = w := by
  show (match p.ior.red.out a τ with
    | some b => E a b w
    | none => w) = w
  cases p.ior.red.out a τ with
  | none => rfl
  | some b => exact hE a b w

/-- **A law at the piece's own extractor counts at the piece so turned**, where that extractor is E
at every yes. -/
theorem goodIn_withMap (p : Piece C F S Cl W) (E : S × F.E.Str → S × F.E.Str → W → W)
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (h : p.GoodIn on on' R R')
    (hx : ∀ a τ b w, p.ior.red.out a τ = some b → p.ext a τ w = E a b w) :
    (p.withMap E).GoodIn on on' R R' := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb =>
    ⟨(hτ b hb).1, fun w hw => by
      rw [withMap_ext p E a τ b w hb, ← hx a τ b w hb]
      exact (hτ b hb).2 w hw⟩) (h a ha)

/-- The same for what a kind owes at its row. -/
theorem own_withMap (p : Piece C F S Cl W) (E : S × F.E.Str → S × F.E.Str → W → W)
    (on on' : S × F.E.Str → Prop) (means : ι → S × F.E.Str → W → Prop) (In Out : ι → Prop)
    (h : p.Own on on' means In Out)
    (hx : ∀ a τ b w, p.ior.red.out a τ = some b → p.ext a τ w = E a b w) :
    (p.withMap E).Own on on' means In Out :=
  goodIn_withMap p E on on' (relAt means In) (relAt means Out) h hx

/-- The same for the items that ride past. -/
theorem frames_withMap (p : Piece C F S Cl W) (E : S × F.E.Str → S × F.E.Str → W → W)
    (on on' : S × F.E.Str → Prop) (means : ι → S × F.E.Str → W → Prop) (O In : ι → Prop)
    (h : p.Frames on on' means O In)
    (hx : ∀ a τ b w, p.ior.red.out a τ = some b → p.ext a τ w = E a b w) :
    (p.withMap E).Frames on on' means O In := fun a τ b w i ha hb hb' hO hI hm => by
  rw [withMap_ext p E a τ b w hb, ← hx a τ b w hb]
  exact h a τ b w i ha hb hb' hO hI hm

/-- Along a row. -/
def reExt (E : ℕ → S × F.E.Str → S × F.E.Str → W → W) :
    ℕ → List (Piece C F S Cl W) → List (Piece C F S Cl W)
  | _, [] => []
  | k, p :: l => p.withMap (E k) :: reExt E (k + 1) l

/-- The plain form's premise reads no extractor. -/
theorem eachLeads_of_reExt (E : ℕ → S × F.E.Str → S × F.E.Str → W → W)
    (on : ℕ → S × F.E.Str → Prop) (Q : ℕ → S × F.E.Str → S × F.E.Str → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (k : ℕ), EachLeads on Q k (reExt E k l) → EachLeads on Q k l
  | [], _, _ => trivial
  | _ :: l, k, h => ⟨h.1, h.2.1, eachLeads_of_reExt E on Q l (k + 1) h.2.2⟩

/-- What is sure of a block's two statements at every yes inside the promise, along a row. -/
def EachSure (on : ℕ → S × F.E.Str → Prop) (Sure : ℕ → S × F.E.Str → S × F.E.Str → Prop) :
    ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | k, p :: l =>
    (∀ a τ b, on k a → p.ior.red.out a τ = some b → Sure k a b) ∧ EachSure on Sure (k + 1) l

/-- The row so turned has `EachE` at E. -/
theorem eachE_reExt (E : ℕ → S × F.E.Str → S × F.E.Str → W → W) (on : ℕ → S × F.E.Str → Prop)
    (Sure : ℕ → S × F.E.Str → S × F.E.Str → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (k : ℕ), EachSure on Sure k l →
      EachE on E Sure k (reExt E k l)
  | [], _, _ => trivial
  | p :: l, k, h =>
    ⟨fun a τ b w hb => withMap_ext p (E k) a τ b w hb, fun a τ b ha hb => h.1 a τ b ha hb,
      eachE_reExt E on Sure l (k + 1) h.2⟩

/-- **The row's laws at the pieces with E laid in, and the sure facts, give the plain form's premise
at the row itself.** -/
theorem eachLeads_of_goodIn_reExt (E : ℕ → S × F.E.Str → S × F.E.Str → W → W)
    (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (Sure : ℕ → S × F.E.Str → S × F.E.Str → Prop) (l : List (Piece C F S Cl W)) (k : ℕ)
    (g : EachGoodIn on R k (reExt E k l)) (s : EachSure on Sure k l) :
    EachLeads on (QE on R E Sure) k l :=
  eachLeads_of_reExt E on _ l k (eachLeadsE on R E Sure _ k g (eachE_reExt E on Sure l k s))

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.withMap_ext
#print axioms VerifiableInference.Desc.Sound.withMap_id
#print axioms VerifiableInference.Desc.Sound.goodIn_withMap
#print axioms VerifiableInference.Desc.Sound.own_withMap
#print axioms VerifiableInference.Desc.Sound.frames_withMap
#print axioms VerifiableInference.Desc.Sound.eachLeads_of_reExt
#print axioms VerifiableInference.Desc.Sound.eachE_reExt
#print axioms VerifiableInference.Desc.Sound.eachLeads_of_goodIn_reExt
