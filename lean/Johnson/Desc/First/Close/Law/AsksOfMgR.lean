-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/AsksOfMgR.lean (kind K10): WHAT K10's SECOND TIE TO THE TABLE OF JOINTS
ASKS OF A MEANING, UNDER A FENCE ON THE STATE IN FRONT; AND THE TIE OVER THE PIECE's OWN OUT FROM
IT. A definition, statements and proofs. A file BESIDE the table: it turns nothing of it.

Why. `K10Asks` (AsksOfMg.lean, beside this file) runs over ALL states s with `K10Step s s'`. At the
composed meaning its field pub is then the promise's public test handed on at every such state: and
that fails, by reading, at a state whose index masks' message is a member of the link's group
(EPubAtK10.lean's head says why). So `k10_t2_piece` (T2AtPiece.lean) stands there on a premise that
cannot be met. The table's second tie, in its second form, has "reached" in hand at the state in
front: so a fact that holds at reached states may enter.
  `K10AsksR Fn Nu Mg O O' Q Q' St`: `K10Asks`' six sentences, each with ONE PREMISE MORE: Fn s, Fn :
    S → Prop a letter, at the state in front.
  `K10Asks.fenced`: whoever has `K10Asks` has `K10AsksR` at every Fn. `K10AsksR.weaker`: a stronger
    fence is easier to pay under.
  `k10_t2_pieceR`: `k10_t2_piece` under `K10AsksR Fn` and Fn a.1: the table's promise at ps[k]? and
    the k-th open set at (z, a.1); the piece's out: the promise at ps[k + 1]? and the (k + 1)-th
    open set at (z, a'.1).
Limits. `K10AsksR` is shown of no meaning here; Fn of no state. "What is kept lies in its group" and
the plan's two numbers are premises still. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.T2AtPiece

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9 (recOf putRec)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (Numbers Item Pub Meaning ModelPart onAt openSets start closersFit
  closersNext k10_promise_at pubHeld sampledIn)

/-- **What K10's second tie asks of a meaning, at the fenced states.** -/
structure K10AsksR {Pz Wt : Type} (Fn : VerifiableInference.Desc.First.S → Prop) (Nu : Numbers)
    (Mg : Meaning Pz Wt) (O O' : List Item) (Q Q' : List Pub) (St : Strs → Strs → Prop) :
    Prop where
  dec : ∀ z s s' y y', Fn s → K10Step s s' → St y y' → Mg.decodes (z, s) y →
    Mg.decodes (z, s') y'
  inOrder : ∀ z s s', Fn s → K10Step s s' → s.failed = none → Mg.inOrder (z, s) = true →
    Mg.inOrder (z, s') = true
  pub : ∀ z s s', Fn s → K10Step s s' → s.failed = none → pubHeld Mg O Q (z, s) = true →
    pubHeld Mg O' Q' (z, s') = true
  pubP : ∀ z s s', Fn s → K10Step s s' → s.failed = none → (∀ q ∈ Q, Mg.pubP q (z, s)) →
    ∀ q ∈ Q', Mg.pubP q (z, s')
  held : ∀ z s s', Fn s → K10Step s s' → s.failed = none → ∀ t ∈ sampledIn Nu O,
    Mg.held t.1 t.2 (z, s) = true → Mg.held t.1 t.2 (z, s') = true
  shown : ∀ z s s' y y', Fn s → K10Step s s' → St y y' → s.failed = none → ∀ t ∈ sampledIn Nu O,
    Mg.shown t.1 t.2 y ∧ Mg.noColl t.1 t.2 (z, s) y →
      Mg.shown t.1 t.2 y' ∧ Mg.noColl t.1 t.2 (z, s') y'

section
variable {Pz Wt : Type} {Fn Fn' : VerifiableInference.Desc.First.S → Prop} {Nu : Numbers}
  {Mg : Meaning Pz Wt} {O O' : List Item} {Q Q' : List Pub} {St : Strs → Strs → Prop}

/-- Whoever has the first form has the fenced one for nothing. -/
theorem K10Asks.fenced (A : K10Asks Nu Mg O O' Q Q' St) : K10AsksR Fn Nu Mg O O' Q Q' St :=
  ⟨fun z s s' y y' _ => A.dec z s s' y y', fun z s s' _ => A.inOrder z s s',
    fun z s s' _ => A.pub z s s', fun z s s' _ => A.pubP z s s', fun z s s' _ => A.held z s s',
    fun z s s' y y' _ => A.shown z s s' y y'⟩

/-- A stronger fence is easier to pay under. -/
theorem K10AsksR.weaker (h : ∀ s, Fn' s → Fn s) (A : K10AsksR Fn Nu Mg O O' Q Q' St) :
    K10AsksR Fn' Nu Mg O O' Q Q' St :=
  ⟨fun z s s' y y' f => A.dec z s s' y y' (h s f), fun z s s' f => A.inOrder z s s' (h s f),
    fun z s s' f => A.pub z s s' (h s f), fun z s s' f => A.pubP z s s' (h s f),
    fun z s s' f => A.held z s s' (h s f), fun z s s' y y' f => A.shown z s s' y y' (h s f)⟩

end

section
variable {Cl W : Type} {F : Frame} (Pr : Par) (b : Block VerifiableInference.Desc.First.S Cl)
  (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2
    (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
  (base : ℕ) (dB dE dR : RDT) (k₀ : ℕ)
  (ext : VerifiableInference.Desc.First.S × F.E.Str →
    Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate k₀ dR)) → W → W)
  (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate k₀ dR)))

include H in
/-- **K10's SECOND TIE, OVER THE PIECE's OWN OUT, FROM A FENCED STATE.** -/
theorem k10_t2_pieceR {Pz Wt : Type} (Fn : VerifiableInference.Desc.First.S → Prop)
    (Nu : Numbers) (Mg : Meaning Pz Wt) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (p : Place) (hF : closersFit links ps (start links) = true)
    (hX : closersNext links ps = true) (hk : ps[k]? = some p) (hK : p.kind = .K10)
    (hKept : ∀ t ∈ Nu.keptOf (p.link.getD 0), t ∈ Nu.group (p.link.getD 0))
    (ht : Nu.treesAt ps[k + 1]? = Nu.treesAt ps[k]?)
    (hm : Nu.msgsAt ps[k + 1]? = Nu.msgsAt ps[k]?) (Q Q' : List Pub)
    (A : K10AsksR Fn Nu Mg ((openSets links ps (start links))[k]?.getD [])
      ((openSets links ps (start links))[k + 1]?.getD []) Q Q' (Behind F base)) (z : Pz)
    (a a' : VerifiableInference.Desc.First.S × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR k₀ ext err).ds))
    (hf : Fn a.1)
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
  exact e (A.dec z _ _ _ _ hf hs' hB) (A.inOrder z _ _ hf hs') (A.pub z _ _ hf hs')
    (A.pubP z _ _ hf hs') (A.held z _ _ hf hs') (A.shown z _ _ _ _ hf hs' hB)

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.K10Asks.fenced
#print axioms VerifiableInference.Desc.First.Close.K10AsksR.weaker
#print axioms VerifiableInference.Desc.First.Close.k10_t2_pieceR
