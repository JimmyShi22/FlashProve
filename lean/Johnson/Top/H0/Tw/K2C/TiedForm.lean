-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/TiedForm.lean: FROM A KIND's LAW AT A SEATED BLOCK, AT ITS OWN WORDS, ITS
OWN EXTRACTOR AND ITS OWN ERRORS, TO THE TIE AT THE DESCRIPTION's PIECE WITH THE TABLE's
EXTRACTOR: for a row that lays, as the code switch's does. A rule over letters; typed for the code
switch; nothing in it names the kind. NO BLOCK IMPORTS THIS FILE. NO RESULT ON THE PROTOCOL. Why.
The tie that the chain of promises asks at a place (TiedBy, Johnson/Desc/Sound/TiedBy.lean) stands
at the description's piece q with the table's extractor E laid in. The law of the code switch at a
seated block (k2_goodIn_seated) stands at a piece over the carried record alone, with the law's
own extractor and the law's own errors.
  TiesAt          ALL A KIND's FILES OWE AT ONE PLACE, IN ONE STRUCTURE, over the letters N, Mg,
                  links, ps, E: the law (good) · its errors are no more than the piece's (errLe) ·
                  at every yes its extractor is the table's (lays) · the five ties t1 … t5 ·
                  «decodes» rides (dec). The words o o' R R' and the extractor may name the public
                  part z.
  goodIn_err      a law at smaller errors counts at larger ones
  tiedBy_of_ties  TiesAt, the piece's form (q.b is «below B» lifted; no round behind) and NO YES
                  AT A MARKED RECORD give TiedBy at q.withMap E. By tiedBy_of_partE
                  (Johnson/Desc/Sound/TiedLays.lean) and goodIn_withMap (ReExt.lean).
LIMITS. A carriage. TiesAt is met by no block here. «For every z»: also at public parts that no
run reaches. No soundness is claimed.
-/
import Johnson.Desc.Sound.TiedLays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Err Doomed)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

variable {P Cl W : Type} {C : CK} {F : Frame}

/-- The piece over the carried record that holds «below B», over q's stretch, with an extractor and
errors of the kind's own. -/
abbrev ownPiece (q : Piece C F (P × First.S) Cl W) (B : Block First.S Cl)
    (ext : First.S × F.E.Str → Iop.Tr (uLT C q.ds) → W → W) (err : Err (uLT C q.ds)) :
    Piece C F First.S Cl W :=
  ⟨below B, q.base, q.ds, q.back, ext, err⟩

/-- **All that a kind's files owe at one place.** -/
structure TiesAt (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece C F (P × First.S) Cl W) (B : Block First.S Cl)
    (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W)
    (ext : P → First.S × F.E.Str → Iop.Tr (uLT C q.ds) → W → W) (err : Err (uLT C q.ds))
    (o o' : P → First.S × F.E.Str → Prop) (R R' : P → First.S × F.E.Str → W → Prop) : Prop where
  good : ∀ z, (ownPiece q B (ext z) err).GoodIn (o z) (o' z) (R z) (R' z)
  errLe : Err.le err q.err
  lays : ∀ z a τ b w, (ownPiece q B (ext z) err).ior.red.out a τ = some b →
    ext z a τ w = atPub E z a b w
  t1 : ∀ z a, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none → o z a
  t2 : ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
    (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
    onQ N Mg links ps (fun s => (z, s)) (k + 1) b
  t3 : ∀ z a τ b w, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
    (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
    relAt (meansQ N Mg fun s => (z, s)) (outsQ links ps k) b w → R' z b w
  t4 : ∀ z a τ b w, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
    (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
    relAt (meansQ N Mg fun s => (z, s)) (outsQ links ps k) b w → R z a (atPub E z a b w) →
    relAt (meansQ N Mg fun s => (z, s)) (insQ links ps k) a (atPub E z a b w)
  t5 : ∀ z a τ b w i, onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
    (ownPiece q B (ext z) err).ior.red.out a τ = some b →
    onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
    relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    meansQ N Mg (fun s => (z, s)) i a (atPub E z a b w)
  dec : ∀ z a τ b, (ownPiece q B (ext z) err).ior.red.out a τ = some b →
    Mg.decodes (z, a.1) (strsOf F a.2) → Mg.decodes (z, b.1) (strsOf F b.2)

/-- A law at smaller errors counts at larger ones. -/
theorem goodIn_err {S : Type} (b : Block S Cl) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (ext : S × F.E.Str → Iop.Tr (uLT C ds) → W → W) {e e' : Err (uLT C ds)} (he : Err.le e e')
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (h : (⟨b, base, ds, back, ext, e⟩ : Piece C F S Cl W).GoodIn on on' R R') :
    (⟨b, base, ds, back, ext, e'⟩ : Piece C F S Cl W).GoodIn on on' R R' :=
  fun a ha => Doomed.mono_err _ he (h a ha)

/-- **From the kind's own words to the tie at the description's piece.** -/
theorem tiedBy_of_ties (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)
    (k : ℕ) (q : Piece C F (P × First.S) Cl W) (B : Block First.S Cl)
    (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s))
    (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W)
    (ext : P → First.S × F.E.Str → Iop.Tr (uLT C q.ds) → W → W) (err : Err (uLT C q.ds))
    (o o' : P → First.S × F.E.Str → Prop) (R R' : P → First.S × F.E.Str → W → Prop)
    (hM : ∀ a τ b, (ownPiece q B (fun _ _ w => w) q.err).ior.red.out a τ = some b →
      a.1.failed = none)
    (H : TiesAt N Mg links ps k q B E ext err o o' R R') :
    TiedBy N Mg links ps (fun a => a) k (q.withMap E) (fun a => o a.1.1 (a.1.2, a.2))
      (fun a => o' a.1.1 (a.1.2, a.2)) (fun a w => R a.1.1 (a.1.2, a.2) w)
      (fun a w => R' a.1.1 (a.1.2, a.2) w) := by
  refine tiedBy_of_partE N Mg links ps k q (below B) hq E o o' R R' fun z => ?_
  have g : ((ownPiece q B (ext z) q.err).withMap (atPub E z)).GoodIn (o z) (o' z) (R z) (R' z) :=
    goodIn_withMap _ _ _ _ _ _
      (goodIn_err (below B) q.base q.ds q.back (ext z) H.errLe _ _ _ _ (H.good z))
      (fun a τ b w hb => H.lays z a τ b w hb)
  refine ⟨g, H.t1 z, fun a τ b ha hm hb ho => H.t2 z a τ b ha hm hb ho,
    fun a τ b w ha hm hb ho hw => H.t3 z a τ b w ha hm hb ho hw, ?_, ?_, ?_,
    fun a τ b hb hd => H.dec z a τ b hb hd⟩
  · intro a τ b w ha hm hb ho hw hr
    rw [withMap_ext (ownPiece q B (fun _ _ w => w) q.err) (atPub E z) a τ b w hb] at hr ⊢
    exact H.t4 z a τ b w ha hm hb ho hw hr
  · intro a τ b w i ha hm hb hon hall hi hin
    rw [withMap_ext (ownPiece q B (fun _ _ w => w) q.err) (atPub E z) a τ b w hb]
    exact H.t5 z a τ b w i ha hm hb hon hall hi hin
  · intro a τ b hb hm
    exact absurd (hM a τ b hb) hm

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.goodIn_err
#print axioms VerifiableInference.Desc.First.K2.tiedBy_of_ties
