-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/TieTwoAt.lean (over TieTwo.lean, K2C/TiedForm.lean and
Johnson/Desc/Kinds/Law/K6Frame.lean): THE TIE t2,
IN THE VERY LETTERS OF THE FIELD t2 OF «all that is owed at one place, with "reached" in hand»
(TiesAtR, K2C/TiedFormR.lean; the same clause with Rch struck is TiesAt.t2, K2C/TiedForm.lean):
from HandsR and the strings' side. Free of the kind. NO BLOCK IMPORTS THIS FILE.
  yes_of_out     an accept of the piece that holds «below B» is an accept of B's own step, at the
                 frame's first tree (out_step and below_step, called)
  t2R_of_handsR  for every public part z: HandsR (Fk z) N links ps (EQ Mg links ps z) F.ft k B ·
                 «reached» gives the fence · the field dec · and, at every accept with the promise
                 in front, «reached», no mark in front, the law's condition behind and no mark
                 behind: the OOD samples held · «shown» and «no collision» at every tenant whose
                 pin is open behind · what the open public items say beside their tests ⟹ the
                 clause t2
LIMITS. A rule over letters; its premises are the work. At Rch := never it says nothing. No
soundness is claimed.
-/
import Johnson.P1K2R.TieTwo
import Johnson.Top.H0.Tw.K2C.TiedForm
import Johnson.Desc.Kinds.Law.K6Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Err)
open VerifiableInference.Desc (Block Place Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Numbers Item Pub Meaning onAt samplesHeld sampledIn)
open VerifiableInference.Desc.First.K2 (ownPiece)
open ProofFile (Cl)
open IM (HandsR Yes openAt)

variable {P W : Type} {C : CK} {F : Frame}

theorem yes_of_out {q : Piece C F (P × S) Cl W} {B : Block S Cl}
    {ext : S × F.E.Str → Iop.Tr (uLT C q.ds) → W → W} {err : Err (uLT C q.ds)}
    {a b : S × F.E.Str} {τ : Iop.Tr (uLT C q.ds)}
    (h : (ownPiece q B ext err).ior.red.out a τ = some b) : Yes F.ft B a.1 b.1 := by
  obtain ⟨cols, n, e⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.out_step (ownPiece q B ext err) a b τ h
  exact ⟨_, cols, n,
    (VerifiableInference.Desc.Kinds.Head.Law.Came.below_step F.ft B a.1 _ cols b.1 n e).2⟩

theorem t2R_of_handsR {N : Numbers} {Mg : Meaning P W} {links : List ModelPart} {ps : List Place}
    {Rch : ℕ → (P × S) × F.E.Str → Prop} {k : ℕ} {q : Piece C F (P × S) Cl W} {B : Block S Cl}
    {ext : P → S × F.E.Str → Iop.Tr (uLT C q.ds) → W → W} {err : Err (uLT C q.ds)}
    {o' : P → S × F.E.Str → Prop} {Fk : P → Nat → S → Prop}
    (H : ∀ z, HandsR (Fk z) N links ps (EQ Mg links ps z) F.ft k B)
    (hF : ∀ z (a : S × F.E.Str), Rch k ((z, a.1), a.2) → Fk z k a.1)
    (dec : ∀ z a τ b, (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      Mg.decodes (z, a.1) (strsOf F a.2) → Mg.decodes (z, b.1) (strsOf F b.2))
    (hHeld : ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
      b.1.failed = none → samplesHeld N Mg (openAt links ps (k + 1)) (z, b.1) = true)
    (hSN : ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
      b.1.failed = none → ∀ x ∈ sampledIn N (openAt links ps (k + 1)),
        Mg.shown x.1 x.2 (strsOf F b.2) ∧ Mg.noColl x.1 x.2 (z, b.1) (strsOf F b.2))
    (hPP : ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
      b.1.failed = none → ∀ x ∈ pubAt Mg links ps (k + 1), Mg.pubP x (z, b.1)) :
    ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b → o' z b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b := by
  intro z a τ b ha hr hm hb ho
  have hu : a.1.failed = none := Classical.byContradiction hm
  have ha' : onAt N Mg links ps[k]? (openAt links ps k) (pubAt Mg links ps k) (z, a.1)
      (strsOf F a.2) := ha
  exact on_of_handsR (H z) (hF z a hr) (yes_of_out hb) hu ha' (dec z a τ b hb ha'.1)
    (hHeld z a τ b ha hr hm hb ho) (hSN z a τ b ha hr hm hb ho) (hPP z a τ b ha hr hm hb ho)

end P1K2

#print axioms P1K2.yes_of_out
#print axioms P1K2.t2R_of_handsR
