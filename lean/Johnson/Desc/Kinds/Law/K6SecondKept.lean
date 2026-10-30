-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6SecondKept.lean: THE SECOND TIE OF THE SUB-PROTOCOL AT THE OUTPUT HEAD TO
THE TABLE OF JOINTS, AT ONE ACCEPTING STEP: the table's promise behind it, from the promise in front
and what is asked AT THAT STEP ALONE.

ON THE PATTERN, AND WITH THE PROOF, OF Johnson/Desc/Sound/K6Second.lean
(k6_t2_quiet). Two things part. (1) That rule takes "every public item that is open behind holds" as
sentences over ALL statements in the promise, though it spends them at one: so a condition that
stands beside the promise (Johnson/Desc/Sound/ChainOfPromisesR.lean: Rch) could not reach them. Here
they are asked at the step. (2) That rule asks that "in order" does not read where the chain stands,
at EVERY value of that field (BlindOrder). Here less is asked: "in order" is kept across the step.
(In another version of the composed meaning both hold.)


Main name (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  k6_t2_kept.

Every letter under "there is": none.
What it does not say. That its premises can be met. Nothing on soundness.
-/
import Johnson.Desc.Sound.K6Second

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning Pub sampledIn pubOfItems bookAt)
open VerifiableInference.Desc.Sound (Piece Frame MsgT onQ strsOf openQ pubQ onParts_of_on
  shape_behind quiet_K6 onQ_step_quiet)

variable {P Cells Tok : Type} {Wp : OnBytes.Model.Verify.Public} {fld : Fmt.Fld} {Fr : Frame}
  {q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)} {l : ℕ}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

/-- **The second tie, at one accepting step.** -/
theorem k6_t2_kept (H : Seated Wp fld Fr q l bef B bS) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (p p' : Place) (m : ℕ) (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p')
    (hl : p.link = some m) (hl' : p'.link = some m) (hs : links[m]? = some .head)
    (hpc : p.piece = 4) (hpc' : p'.piece = 5)
    (hNum : N.treesAt ps[k + 1]? = N.treesAt ps[k]? ∧ N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?)
    (a : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (b : (P × S) × Fr.E.Str) (ha : onQ (Fr := Fr) N Mg links ps (fun a => a) k a)
    (hm : a.1.2.failed = none) (hb : q.ior.red.out a τ = some b)
    (hOrd : Mg.inOrder a.1 = true → Mg.inOrder b.1 = true)
    (hHeld : ∀ x : ℕ × ℕ, Mg.held x.1 x.2 a.1 = true → Mg.held x.1 x.2 b.1 = true)
    (hDec : Mg.decodes a.1 (strsOf Fr a.2) → Mg.decodes b.1 (strsOf Fr b.2))
    (hSh : ∀ x ∈ sampledIn N (openQ links ps k),
      Mg.shown x.1 x.2 (strsOf Fr a.2) → Mg.shown x.1 x.2 (strsOf Fr b.2))
    (hNc : ∀ x ∈ sampledIn N (openQ links ps k),
      Mg.noColl x.1 x.2 a.1 (strsOf Fr a.2) → Mg.noColl x.1 x.2 b.1 (strsOf Fr b.2))
    (hPub : ∀ x ∈ pubQ Mg.more links ps (k + 1) ++ pubOfItems (openQ links ps (k + 1)),
      Mg.pub x b.1 = true)
    (hPP : ∀ x ∈ pubQ Mg.more links ps (k + 1), Mg.pubP x b.1) :
    onQ (Fr := Fr) N Mg links ps (fun a => a) (k + 1) b := by
  have A := onParts_of_on N Mg links ps (fun a => a) k a ha hm
  obtain ⟨o, F1, X, Q, h1, h2, _, e⟩ := k6_behind H a b τ hb
  refine onQ_step_quiet N Mg links ps (fun a => a) k p hp (quiet_K6 links p m hl hs hpc) a b ha
    (fun h => absurd hm h) hDec (fun _ => ?_) ?_ ?_ (fun h => hOrd h) (fun _ _ => ?_)
    (fun _ h => ?_) (fun _ _ => ?_) (fun x _ h => hHeld x h) hSh hNc
  · have hs0 : First.shapeAt links (some p) a.1.2 = true := by
      have := A.shape
      rw [hp] at this
      exact this
    show First.shapeAt links ps[k + 1]? b.1.2 = true
    rw [hp', e]
    exact shape_behind links p p' m hl hl' hs hpc hpc' a.1.2 o _ h1 h2 h2 rfl hs0
  · show b.1.2.st.groups = a.1.2.st.groups
    rw [e]
  · show b.1.2.book.place = a.1.2.book.place
    rw [e]
  · rw [← First.openSets_succ links ps (First.start links) k p hp,
      ← First.pubSets_succ Mg.more links ps k p hp]
    unfold First.pubHeld
    exact List.all_eq_true.2 hPub
  · show bookAt N ps[k + 1]? b.1.2 = true
    have h' : bookAt N ps[k]? a.1.2 = true := h
    unfold bookAt at h' ⊢
    rw [hNum.1, hNum.2, e]
    exact h'
  · rw [← First.pubSets_succ Mg.more links ps k p hp]
    exact hPP

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_t2_kept
