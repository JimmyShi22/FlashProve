-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/T2AtPiece.lean: K10's SECOND TIE TO THE TABLE OF JOINTS, OVER THE
PIECE's OWN OUT. Statements and proofs. A file BESIDE the table: it turns nothing of it.

Why. The table's second tie runs over a piece's reduction: "where the piece puts out b from
a, and the promise in front holds of a, the promise behind holds of b". PromiseOfEnd.lean and
AsksOfMg.lean (beside this file) run over the law's end and over letters for the strings.
  `pieceOn_step`: let b be a block whose yes is a yes of `closeFrame`, read and written as K10 reads
    and writes (H: the premise of K10's law on its block; `seated_yes` pays it at a seated block).
    Where the piece of b (`pieceOn`, AtAny.lean) puts out a' from a: `K10Step a.1 a'.1`
    (AsksOfMg.lean), AND THE STRINGS BEHIND ARE WHAT THE LIBRARY's STAGE LEAVES: a'.2 = `behind` ..
    a.2 τ (Johnson/Desc/Sound/StringsStay.lean: past it the stored table, and every tree with a
    number below the piece's base, ride unturned: `cellStays`, `colStays`, `wordStays`,
    `nearStays`).
  `Behind F base y y'`: y and y' are the readings (`strsOf F`) of strings of which the second are
    `behind` .. of the first, at some rounds' data and transcript, at that base.
  `k10_t2_piece`: so, under `K10Asks` at St := `Behind F base`: for all a, τ, a': the table's
    promise at ps[k]? and the k-th open set at (z, a.1) and `strsOf F a.2`; the piece's out: the
    promise at ps[k + 1]? and the (k + 1)-th open set at (z, a'.1) and `strsOf F a'.2`. NO WORD OF
    THE LAW's END IS SPENT: in the tie the kind's own promise behind may be "true".
Limits. `K10Asks`, "what is kept lies in its group" and the plan's two numbers are premises still.
The table's `onQ` is not named in code: the two sides are its unfolding at get := fun s =>
(z, s) [by reading]. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.AsksOfMg
import Johnson.Desc.Sound.StringsStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (Numbers Item Pub Meaning ModelPart onAt openSets start closersFit
  closersNext k10_promise_at)

section
variable {Cl W : Type} {F : Frame} (Pr : Par) (b : Block VerifiableInference.Desc.First.S Cl)
  (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2
    (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
  (base : ℕ) (dB dE dR : RDT) (k₀ : ℕ)
  (ext : VerifiableInference.Desc.First.S × F.E.Str →
    Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate k₀ dR)) → W → W)
  (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate k₀ dR)))

include H in
/-- **What the piece's out holds**: the step on the record; the strings that the stage leaves. -/
theorem pieceOn_step (a a' : VerifiableInference.Desc.First.S × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR k₀ ext err).ds))
    (h : (pieceOn (W := W) (F := F) b base dB dE dR k₀ ext err).ior.red.out a τ = some a') :
    K10Step a.1 a'.1 ∧
      a'.2 = behind (ckP .two) F base (dB :: dE :: List.replicate k₀ dR) a.2 τ := by
  obtain ⟨-, -, ⟨gs, hd⟩, hi⟩ := Piece.out_decide _ a a' τ h
  obtain ⟨x, hx, hw⟩ := H _ _ _ _ (below_yes _ _ _ _ _ hd)
  exact ⟨⟨_, _, x, hx, hw⟩, hi⟩

/-- The readings of strings in front of and behind a stage at that base. -/
def Behind (F : Frame) (base : ℕ) (y y' : Strs) : Prop :=
  ∃ (ds : List RDT) (u : F.E.Str) (τ : Iop.Tr (uLT (ckP .two) ds)),
    y = strsOf F u ∧ y' = strsOf F (behind (ckP .two) F base ds u τ)

include H in
/-- **K10's SECOND TIE, OVER THE PIECE's OWN OUT.** -/
theorem k10_t2_piece {Pz Wt : Type} (Nu : Numbers) (Mg : Meaning Pz Wt) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (p : Place) (hF : closersFit links ps (start links) = true)
    (hX : closersNext links ps = true) (hk : ps[k]? = some p) (hK : p.kind = .K10)
    (hKept : ∀ t ∈ Nu.keptOf (p.link.getD 0), t ∈ Nu.group (p.link.getD 0))
    (ht : Nu.treesAt ps[k + 1]? = Nu.treesAt ps[k]?)
    (hm : Nu.msgsAt ps[k + 1]? = Nu.msgsAt ps[k]?) (Q Q' : List Pub)
    (A : K10Asks Nu Mg ((openSets links ps (start links))[k]?.getD [])
      ((openSets links ps (start links))[k + 1]?.getD []) Q Q' (Behind F base)) (z : Pz)
    (a a' : VerifiableInference.Desc.First.S × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR k₀ ext err).ds))
    (ha : onAt Nu Mg links ps[k]? ((openSets links ps (start links))[k]?.getD []) Q (z, a.1)
      (strsOf F a.2))
    (h : (pieceOn (W := W) (F := F) b base dB dE dR k₀ ext err).ior.red.out a τ = some a') :
    onAt Nu Mg links ps[k + 1]? ((openSets links ps (start links))[k + 1]?.getD []) Q' (z, a'.1)
      (strsOf F a'.2) := by
  obtain ⟨hs, hy⟩ := pieceOn_step Pr b H base dB dE dR k₀ ext err a a' τ h
  have hB : Behind F base (strsOf F a.2) (strsOf F a'.2) := ⟨_, a.2, τ, rfl, by rw [hy]; rfl⟩
  obtain ⟨es, rs, x, hx, hw⟩ := hs
  have hs' : K10Step a.1 a'.1 := ⟨es, rs, x, hx, hw⟩
  have e := k10_promise_at Nu Mg links ps k p hF hX hk hK hKept ht hm Q Q' (z, a.1) z
    (strsOf F a.2) (strsOf F a'.2) es rs x hx ha
  rw [← hw] at e
  exact e (A.dec z _ _ _ _ hs' hB) (A.inOrder z _ _ hs') (A.pub z _ _ hs') (A.pubP z _ _ hs')
    (A.held z _ _ hs') (A.shown z _ _ _ _ hs' hB)

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.pieceOn_step
#print axioms VerifiableInference.Desc.First.Close.k10_t2_piece
