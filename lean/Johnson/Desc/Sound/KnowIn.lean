-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/KnowIn.lean: from a proved typed reduction that pays for leaving a promise to
`Piece.GoodIn` (Johnson/Desc/Sound/GoodIn.lean) of a block of the description. A SHEET OF
STATEMENTS: one definition, propositions written as `def … : Prop`, and controls of form. NOTHING IS
PROVED IN THIS FILE.

The setting. GoodIn.lean says what a block with a promise owes. ChainRule.lean has the road from a
proved typed reduction of the library to a block's knowledge soundness (`PieceOfProved`,
`PieceGood`): a reading of the block's written rounds as the typed reduction's rounds (`CarryS`,
OnBytes/Flat/CarrySkip.lean), and "where the block says yes the typed reduction says yes at the same
transcript". `PieceGood` asks that the block carries its condition at every transcript. This file
has the same road for a typed reduction that can leave its promise.

What is said. `KnowIn`: `Piece.GoodIn` for any reduction: at the errors the prover has lost towards
one property: where the verifier puts out, the output is inside the promise, and a witness of it
gives, by the extractor, a witness in front. `KnowInOfBadFam`: the three premises of the library's
`knowInto_of_badFam` (Ior/KnowColl.lean) give it. `KnowInOfCarry`: so do `Know` and a condition that
is carried at every transcript. `KnowIntoOfKnowIn`: it gives the library's `KnowInto`. `KnowInSeq`:
TWO IN A ROW: the promise of the first is the condition of the second; the errors in a row; the
extractors composed: so a composite that holds a reduction with a promise (a proximity test that
holds sendings) keeps the notion, where the library's `knowInto_seq` forgets it. `PieceGoodIn`: THE
CARRIAGE: from `KnowIn` of a typed reduction, a reading of the block's rounds, and "where the block
says yes the typed reduction puts out at the same transcript; if its output is inside its promise,
the block's is inside the block's; and a witness behind the block gives one behind the typed
reduction, from whose witness in front comes the block's": `Piece.GoodIn` at the block's own errors.
`RowKnowIn`, `ChainKnowIn`: A ROW OF BLOCKS, AND THE CHAIN's OWN DECISION: from `EachGoodIn` (and
`Tiled`): `KnowIn` from the first boundary to the last: what a claim that is carried past a whole
chain with a promise at its end will want.

Controls of form. `Piece.GoodIn` is `KnowIn` at the block's own reduction, by definition. The
library's three lemmas on a sending with a sample outside the domain (`ldSend_within`,
`ldSend_out_on`, `ldSend_back`, Cb/Ld/LdSendProofs.lean), AS THEY LIE, fill the three premises of
`KnowInOfBadFam`.

Limits. (1) Rules at parameters: no block of the description and no typed reduction but `ldSend`
occurs. (2) `PieceGoodIn`'s premise on the block's yes is owed block by block, as `PieceOfProved`'s.
IT ASKS MORE THAN `PieceGood`'s IN TWO PLACES: the clause on the two promises; and the image τ' and
the typed reduction's output are asked WHEREVER THE BLOCK SAYS YES, whether a witness stands behind
or none (`PieceGood` asks them only where a witness stands behind): the promise is owed whatever is
claimed behind. So whoever has `PieceGood`'s premise has not yet this one. (3) The degenerate cases
of ChainRule.lean, Limits (2). (4) Nothing on acceptance. (5) For a batch: SharedRule.lean takes
`Piece.GoodIn` from here on (`LostOfGoodIn`); no statement says that a link with keys keeps the
promise at a chain's end.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.GoodIn
import OnBytes.Flat.CarrySkip
import Ior.KnowColl
import Cb.Ld.LdSendProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed BadFam Tr)

/-- **Knowledge sound, and keeps the promise, at one list of errors.** From every statement with
`on` the prover has lost (`Doomed`, Iop/Rbr.lean) towards: where the verifier puts out, the output
has `on'`, and every witness of it gives, by the extractor, a witness of the statement in front. -/
def KnowIn {A B WA WB : Type} (K : Reduction A B) (on : A → Prop) (on' : B → Prop)
    (RA : A → WA → Prop) (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA)
    (ε : Err K.shape) : Prop :=
  ∀ a, on a → Doomed K.shape ε fun τ =>
    ∀ b, K.out a τ = some b → on' b ∧ ∀ w, RB b w → RA a (ext a τ w)

/-- From sets of bad challenges: the three premises of the library's `knowInto_of_badFam`. -/
def KnowInOfBadFam : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (on : A → Prop) (on' : B → Prop)
    (RA : A → WA → Prop) (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape)
    (bad : A → BadFam K.shape),
    (∀ a, on a → (bad a).Within ε) →
    (∀ a τ b, on a → (bad a).Clean τ → K.out a τ = some b → on' b) →
    (∀ a τ b w, on a → (bad a).Clean τ → K.out a τ = some b → RB b w → RA a (ext a τ w)) →
    KnowIn K on on' RA RB ext ε

/-- From knowledge soundness and a condition that is carried at every transcript. -/
def KnowInOfCarry : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (on : A → Prop) (on' : B → Prop)
    (RA : A → WA → Prop) (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape),
    (∀ a τ b, on a → K.out a τ = some b → on' b) → K.Know on RA RB ext ε →
    KnowIn K on on' RA RB ext ε

/-- It gives the library's `KnowInto`. -/
def KnowIntoOfKnowIn : Prop :=
  ∀ (A B WA WB : Type) (K : Reduction A B) (on : A → Prop) (on' : B → Prop)
    (RA : A → WA → Prop) (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape),
    KnowIn K on on' RA RB ext ε → K.KnowInto on on' RA RB ext ε

/-- **Two in a row.** The promise of the first is the condition of the second; the errors in a row;
the extractors composed (d: the value where the first verifier refuses). -/
def KnowInSeq : Prop :=
  ∀ (A B C WA WB WC : Type) (K₁ : Reduction A B) (K₂ : Reduction B C) (on₁ : A → Prop)
    (on₂ : B → Prop) (on₃ : C → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop)
    (RC : C → WC → Prop) (e₁ : A → Tr K₁.shape → WB → WA) (e₂ : B → Tr K₂.shape → WC → WB)
    (ε₁ : Err K₁.shape) (ε₂ : Err K₂.shape) (d : WA),
    KnowIn K₁ on₁ on₂ RA RB e₁ ε₁ → KnowIn K₂ on₂ on₃ RB RC e₂ ε₂ →
    KnowIn (K₁.seq K₂) on₁ on₃ RA RC (Reduction.extSeq K₁ K₂ e₁ e₂ d) (Err.app ε₁ ε₂)

/-- **The carriage to a block of the description.** Kp: a typed reduction with `KnowIn`. G: the
reading of the block's written rounds as the rounds of Kp, which may hang on the statement; `Fits`:
the block's errors bear those of Kp. rd: the statement of Kp that is read off the block's. The
premise on the block's yes: from a statement with `on`, where the block says yes at τ, the reading
has an image τ' and Kp puts out y there; if y is inside the promise of Kp, the statement behind the
block is inside the block's promise; and every witness behind the block gives a witness w' of y such
that a witness in front of Kp, had by its extractor from w', gives the block's extractor's value as
a witness in front of the block. -/
def PieceGoodIn : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (Xp Yp Wp Wq : Type)
    (Kp : Reduction Xp Yp) (G : S × F.E.Str → CarryS (uLT C p.ds) Kp.shape) (δ : Err Kp.shape)
    (rd : S × F.E.Str → Xp) (on on' : S × F.E.Str → Prop) (onp : Xp → Prop) (onp' : Yp → Prop)
    (RA RB : S × F.E.Str → W → Prop) (RAp : Xp → Wp → Prop) (RBp : Yp → Wq → Prop)
    (ep : Xp → Tr Kp.shape → Wq → Wp),
    (∀ a, (G a).Fits δ p.err) → (∀ a, on a → onp (rd a)) →
    (∀ a τ a', on a → p.ior.red.out a τ = some a' →
      ∃ τ' y, (G a).tr τ = some τ' ∧ Kp.out (rd a) τ' = some y ∧ (onp' y → on' a') ∧
        ∀ w, RB a' w → ∃ w', RBp y w' ∧
          (RAp (rd a) (ep (rd a) τ' w') → RA a (p.ext a τ w))) →
    KnowIn Kp onp onp' RAp RBp ep δ →
    p.GoodIn on on' RA RB

/-- **A row of blocks.** If every block of a row has `GoodIn` between its two boundaries, the blocks
one after the other have `KnowIn` from the first boundary to the last, at the errors in a row, with
the extractors composed. -/
def RowKnowIn : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (i : ℕ) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)),
    EachGoodIn on R i (p :: l) →
    KnowIn (rowIOR p l).red (on i) (on (i + 1 + l.length)) (R i) (R (i + 1 + l.length))
      (rowExt d p l) (rowErr p l)

/-- **The chain's own decision.** If moreover the stretches tile the chain, the chain's decision
(the fold) has `KnowIn`: it is knowledge sound AND KEEPS THE PROMISE AT THE CHAIN's END, at the
blocks' errors in a row. (`ChainRule` ends in `KnowInto`, which forgets that.) -/
def ChainKnowIn : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (name : String) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (d : W) (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (h : (rowIOR p l).shape = uLT C (rowData p l)),
    Tiled p l → EachGoodIn on R 0 (p :: l) →
    KnowIn (foldRed name ((p :: l).map (·.b)) p l h) (on 0) (on (1 + l.length)) (R 0)
      (R (1 + l.length)) (rowExt d p l) (rowErr p l)


-- what a block with a promise owes is this notion at the block's own reduction, by definition
example (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W)
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) :
    p.GoodIn on on' R R' = KnowIn p.ior.red on on' R R' p.ext p.err := rfl

-- THE LIBRARY's THREE LEMMAS ON A SENDING WITH A SAMPLE, AS THEY LIE, fill the three premises
example (h : KnowInOfBadFam) (E : Type) [Field E] (o : Cb.OMsg E) (Kc X W W' : Type)
    (E₀ : ExtSpec) (A : IOR.Rels Kc X E₀ W) (back : o.Msg → W' → W) (L : ℕ) (hL : o.ListLE L)
    (hE : o.Evades) :
    KnowIn (Cb.ldSend o X E₀).red A.on (o.sent A back).on A.relR (o.sent A back).relR
      (fun _ _ w => back w.1.1 w.2) (L.choose 2 * o.Z.err, (0, ())) :=
  h _ _ _ _ (Cb.ldSend o X E₀).red A.on (o.sent A back).on A.relR (o.sent A back).relR _ _
    (fun _ => Cb.ldSendBad o) (fun _ _ => Cb.ldSend_within E o L hL hE)
    (fun a τ b ha hc hb => Cb.ldSend_out_on E o Kc X W W' E₀ A back a τ b ha hc hb)
    fun a τ b w _ _ hb hw => Cb.ldSend_back E o Kc X W W' E₀ A back a τ b w hb hw

end VerifiableInference.Desc.Sound
