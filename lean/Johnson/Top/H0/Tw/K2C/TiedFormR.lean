-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/TiedFormR.lean: ALL THAT IS OWED AT ONE PLACE OF A SUB-PROTOCOL WHOSE ROW
LAYS, WITH
"REACHED" IN HAND IN EACH TIE: the second form of Johnson/Top/H0/Tw/K2C/TiedForm.lean. One structure
of Prop, two theorems. A rule over parameters; typed for the code switch; nothing in it names the
kind.
A law file: no sub-protocol imports it.

Why. The chain of promises has a second form (`TiedAtR`, Johnson/Desc/Sound/ChainOfPromisesR.lean):
beside
the table's promise at a border stands a condition Rch k that every accepting step hands on, and
each
of the five ties may take it as a premise. Since the table asks no public test that only
says
a fact on every reached state, some ties CAN BE HAD IN THAT FORM ALONE: at the code switch the fifth
(Johnson/Top/H0/K2Ties/T5.lean: the pending claims on the committed table are read through the
state's
own book).

What is said.
  `TiesAtR`: the fields of `TiesAt`; t1 … t5 each with ONE PREMISE MORE: Rch k at the statement in
    front, the public part z laid back in. good, errLe, lays and dec do not turn.
  `tiesAtR_of_tiesAt`: every member of the first form is one of the second, for nothing.
  `tiedAtR_of_ties`: `TiesAtR`, the piece's form (q.b is "below B" lifted over the public part) and
    NO ACCEPT AT A MARKED STATE give `TiedAtR` at q.withMap E.

Limits. A carriage: `TiesAtR` is met by no sub-protocol here. At Rch := never every tie is free and
nothing is said. "For every z": also at public parts that no run reaches. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Top.H0.Tw.K2C.TiedForm
import Johnson.Desc.Sound.ChainOfPromisesR

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

/-- **All that is owed at one place, with "reached" in hand in each tie.** -/
structure TiesAtR (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)
    (Rch : ℕ → (P × First.S) × F.E.Str → Prop) (k : ℕ) (q : Piece C F (P × First.S) Cl W)
    (B : Block First.S Cl) (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W)
    (ext : P → First.S × F.E.Str → Iop.Tr (uLT C q.ds) → W → W) (err : Err (uLT C q.ds))
    (o o' : P → First.S × F.E.Str → Prop) (R R' : P → First.S × F.E.Str → W → Prop) : Prop where
  good : ∀ z, (ownPiece q B (ext z) err).GoodIn (o z) (o' z) (R z) (R' z)
  errLe : Err.le err q.err
  lays : ∀ z a τ b w, (ownPiece q B (ext z) err).ior.red.out a τ = some b →
    ext z a τ w = atPub E z a b w
  t1 : ∀ z a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
    ¬ a.1.failed ≠ none → o z a
  t2 : ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
    ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
    onQ N Mg links ps (fun s => (z, s)) (k + 1) b
  t3 : ∀ z a τ b w, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
    ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
    relAt (meansQ N Mg fun s => (z, s)) (outsQ links ps k) b w → R' z b w
  t4 : ∀ z a τ b w, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
    ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
    relAt (meansQ N Mg fun s => (z, s)) (outsQ links ps k) b w → R z a (atPub E z a b w) →
    relAt (meansQ N Mg fun s => (z, s)) (insQ links ps k) a (atPub E z a b w)
  t5 : ∀ z a τ b w i, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
    ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b →
    onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
    relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    meansQ N Mg (fun s => (z, s)) i a (atPub E z a b w)
  dec : ∀ z a τ b, (ownPiece q B (ext z) err).ior.red.out a τ = some b →
    Mg.decodes (z, a.1) (strsOf F a.2) → Mg.decodes (z, b.1) (strsOf F b.2)

/-- **Every member of the first form is one of the second.** -/
theorem tiesAtR_of_tiesAt (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)
    (Rch : ℕ → (P × First.S) × F.E.Str → Prop) (k : ℕ) (q : Piece C F (P × First.S) Cl W)
    (B : Block First.S Cl) (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W)
    (ext : P → First.S × F.E.Str → Iop.Tr (uLT C q.ds) → W → W) (err : Err (uLT C q.ds))
    (o o' : P → First.S × F.E.Str → Prop) (R R' : P → First.S × F.E.Str → W → Prop)
    (H : TiesAt N Mg links ps k q B E ext err o o' R R') :
    TiesAtR N Mg links ps Rch k q B E ext err o o' R R' :=
  ⟨H.good, H.errLe, H.lays, fun z a ha _ => H.t1 z a ha, fun z a τ b ha _ => H.t2 z a τ b ha,
    fun z a τ b w ha _ => H.t3 z a τ b w ha, fun z a τ b w ha _ => H.t4 z a τ b w ha,
    fun z a τ b w i ha _ => H.t5 z a τ b w i ha, H.dec⟩

/-- **From the second form to the tie at the description's piece, with "reached".** -/
theorem tiedAtR_of_ties (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)
    (Rch : ℕ → (P × First.S) × F.E.Str → Prop) (k : ℕ) (q : Piece C F (P × First.S) Cl W)
    (B : Block First.S Cl) (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s))
    (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W)
    (ext : P → First.S × F.E.Str → Iop.Tr (uLT C q.ds) → W → W) (err : Err (uLT C q.ds))
    (o o' : P → First.S × F.E.Str → Prop) (R R' : P → First.S × F.E.Str → W → Prop)
    (hM : ∀ a τ b, (ownPiece q B (fun _ _ w => w) q.err).ior.red.out a τ = some b →
      a.1.failed = none)
    (H : TiesAtR N Mg links ps Rch k q B E ext err o o' R R') :
    TiedAtR N Mg links ps (fun a => a) Rch k (q.withMap E) := by
  have g : ∀ z, ((ownPiece q B (ext z) q.err).withMap (atPub E z)).GoodIn (o z) (o' z) (R z)
      (R' z) := fun z =>
    goodIn_withMap _ _ _ _ _ _
      (goodIn_err (below B) q.base q.ds q.back (ext z) H.errLe _ _ _ _ (H.good z))
      (fun a τ b w hb => H.lays z a τ b w hb)
  rw [withMap_is_liftAtE q (below B) hq E]
  refine ⟨fun a => o a.1.1 (a.1.2, a.2), fun a => o' a.1.1 (a.1.2, a.2),
    fun a w => R a.1.1 (a.1.2, a.2) w, fun a w => R' a.1.1 (a.1.2, a.2) w,
    liftGoodInExt (P × First.S) First.S P Cl W C F Prod.snd (fun t s => (t.1, s)) Prod.fst
      (ownPiece q B (fun _ _ w => w) q.err) _ o o' R R' (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ => rfl) g,
    fun a ha hr hm => H.t1 a.1.1 (a.1.2, a.2) ha hr hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a τ b ha hr hm hb ho
    obtain ⟨x, hx, rfl⟩ := out_liftAtE (ownPiece q B (fun _ _ w => w) q.err) _ a b τ hb
    exact H.t2 a.1.1 (a.1.2, a.2) τ x ha hr hm hx ho
  · intro a τ b w ha hr hm hb ho hw
    obtain ⟨x, hx, rfl⟩ := out_liftAtE (ownPiece q B (fun _ _ w => w) q.err) _ a b τ hb
    exact H.t3 a.1.1 (a.1.2, a.2) τ x w ha hr hm hx ho hw
  · intro a τ b w ha hr hm hb ho hw hR
    obtain ⟨x, hx, rfl⟩ := out_liftAtE (ownPiece q B (fun _ _ w => w) q.err) _ a b τ hb
    have e := withMap_ext (ownPiece q B (fun _ _ w => w) q.err) (atPub E a.1.1) (a.1.2, a.2) τ x w
      hx
    have hR' : R a.1.1 (a.1.2, a.2) (atPub E a.1.1 (a.1.2, a.2) x w) := e ▸ hR
    exact e ▸ H.t4 a.1.1 (a.1.2, a.2) τ x w ha hr hm hx ho hw hR'
  · intro a τ b w i ha hr hm hb hon hall hi hin
    obtain ⟨x, hx, rfl⟩ := out_liftAtE (ownPiece q B (fun _ _ w => w) q.err) _ a b τ hb
    have e := withMap_ext (ownPiece q B (fun _ _ w => w) q.err) (atPub E a.1.1) (a.1.2, a.2) τ x w
      hx
    exact e ▸ H.t5 a.1.1 (a.1.2, a.2) τ x w i ha hr hm hx hon hall hi hin
  · intro a τ b hb hm
    obtain ⟨x, hx, rfl⟩ := out_liftAtE (ownPiece q B (fun _ _ w => w) q.err) _ a b τ hb
    exact absurd (hM (a.1.2, a.2) τ x hx) hm
  · intro a τ b hb hd
    obtain ⟨x, hx, rfl⟩ := out_liftAtE (ownPiece q B (fun _ _ w => w) q.err) _ a b τ hb
    exact H.dec a.1.1 (a.1.2, a.2) τ x hx hd

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.tiesAtR_of_tiesAt
#print axioms VerifiableInference.Desc.First.K2.tiedAtR_of_ties
