-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/LawF.lean
(kind K9's soundness lemma): THEOREMS: THE LAW OF A SEGMENT's BATCHING OVER ANY
FUNCTION OF CLAIMS. Johnson/Desc/LinkLaw2.lean and LinkLaw3.lean state it of a segment's record
(Link): the batching block is handed claimsInBy L.each L.hear L.order, the runs that the hearing
blocks state, all called in a row in front of the adding, with the link's test behind each. A
description may lay the batching otherwise: the draw, and then several steps of adding, each of
which calls some runs and adds their claims, so that a later run is called at a record into which
earlier claims are added already. No segment's gatherer is that function. Here the law is stated of
a block b and ANY function f of claims.
  PremisesF   the premises, by name:
     later     "later" is a preorder;
     termsOk   the exponents of the terms differ from each other and are at most d;
     fixedF    FIXED BEFORE THE DRAW, of f as a whole: where f returns at a good state, the sum of
               its claims with their weights, numbered from 0, is the polynomial in the challenge
               whose terms see the fixed part and the prover's data alone (the conclusion of
               LinkLaw2's claimsIn_fixed, as a premise);
     batch     LinkLaw2's BatchAdds, of b and f;
     full      behind the block all that a claim's value reads has been laid.
  ValueF      WHAT THE LAW NEEDS OF THE BLOCK, AS ONE SENTENCE: at a yes of b's step, from a ready
              state: just one element was drawn; the state behind meets "behind"; the one
              equation's left-hand side there is the polynomial with these terms, at that element.
  PremisesF.value   PremisesF gives ValueF. (Law/Moves.lean gives it of a draw with steps of adding
              behind it.)
  badF, badF_card_le   the bad challenges; at most d.
  goodInF     **the piece that holds b is good** (the form that the rule of composition takes),
              from ValueF and the test on the exponents: FROM
              "every coefficient of the terms is 0 at the data to which the prover is bound" TO
              "the one equation in the state behind holds at these data".
  goodInF_real   the same at the format's own kit of challenges, from the degree alone.
  premisesF_of_link   LinkLaw2's premises at a segment without runs behind the batching give these.
The block's own type of claims (Cb) is free: a description may state no claim by type (Unit) and add
K9's claims inside its blocks. The letters are LinkLaw2's (LinkSem): a hollow filling gives a hollow
law.

-/
import Johnson.Desc.LinkLaw9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)
open _root_.Run (ckP EV toU3)
open _root_.Iop (Err)

variable {S Cl Cb W P Y K : Type} {C : CK} {F : Frame}
variable [Field K] [Fintype K] [DecidableEq K]

/-- The premises of the law over a function f of claims. -/
structure PremisesF (X : LinkSem K S Cl P Y) (b : Block S Cl)
    (f : S → Except String (List Cl × S)) (terms : P → Y → List (ℕ × K)) (ft d : ℕ) : Prop where
  later : X.LaterOk
  termsOk : ∀ s y, X.ready s → Desc.TermsOk K (terms (X.fixed s) y) d
  fixedF : ∀ s cls s', X.good s → f s = .ok (cls, s') → X.good s' ∧ X.chi s' = X.chi s ∧
    ∀ t y, X.later s' t → X.full t →
      X.wsum t y (X.chi s) 0 cls = termsAt K (terms (X.fixed s) y) (X.chi s)
  batch : X.BatchAdds ft b f
  full : ∀ s, X.behind s → X.full s

/-- What the law needs of the block. -/
def ValueF (X : LinkSem K S Cl P Y) (b : Block S Cb) (terms : P → Y → List (ℕ × K)) (ft : ℕ) :
    Prop :=
  ∀ s rs cols s' k, X.ready s → viewWordsBelowPrime ⟨rs, cols⟩ = true → b.step ft s rs cols = .ok (s', k) →
    ∃ x, rs.flatMap (·.drawn.elems) = [x] ∧ X.behind s' ∧
      ∀ y, X.one s' s' y = termsAt K (terms (X.fixed s) y) (X.rd x)

omit [Fintype K] [DecidableEq K] in
/-- At one yes of the block's step. -/
theorem PremisesF.value {X : LinkSem K S Cl P Y} {b : Block S Cl}
    {f : S → Except String (List Cl × S)} {terms : P → Y → List (ℕ × K)} {ft d : ℕ}
    (H : PremisesF X b f terms ft d) : ValueF X b terms ft := by
  intro s rs cols s' k hr hw hs
  obtain ⟨x, s₁, cls, s₂, hx, hg, hf, hc, hcl, hone⟩ := H.batch s rs cols s' k hr hw hs
  obtain ⟨hg₂, hc₂, hsum⟩ := H.fixedF _ _ _ hg hcl
  obtain ⟨hb, hl₂, hv⟩ := hone hg₂ (hc₂.trans hc)
  exact ⟨x, hx, hb, fun y => by
    rw [hv s' y (H.later.1 s'), ← hc, hsum s' y hl₂ (H.full s' hb), hf]⟩

open Classical in
/-- The bad challenges at a list of terms: none if all coefficients are 0; else the roots. -/
noncomputable def badF (t : List (ℕ × K)) : Finset K :=
  if ∃ x ∈ t, x.2 ≠ 0 then Finset.univ.filter fun c => termsAt K t c = 0 else ∅

theorem badF_card_le (t : List (ℕ × K)) (d : ℕ) (h : Desc.TermsOk K t d) :
    (badF t).card ≤ d := by
  unfold badF
  split
  · next hx => exact termsAt_roots_le K _ d h hx
  · simp

/-- A root that is not bad: all coefficients are 0. -/
theorem zero_of_root (t : List (ℕ × K)) (c : K) (hroot : termsAt K t c = 0) (hbad : c ∉ badF t) :
    ∀ x ∈ t, x.2 = 0 := by
  intro x hx
  by_contra hne
  apply hbad
  unfold badF
  rw [if_pos ⟨x, hx, hne⟩, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hroot⟩

open Classical in
/-- The bad field elements at a statement. -/
noncomputable def badAtF (X : LinkSem K S Cl P Y) (terms : P → Y → List (ℕ × K))
    (on : S × F.E.Str → Prop) (Bnd : S × F.E.Str → W → Y → Prop) (a : S × F.E.Str) : Finset K :=
  if h : on a ∧ ∃ y, ∃ w, Bnd a w y then badF (terms (X.fixed a.1) (Classical.choose h.2)) else ∅

/-- **The piece that holds the block is good.** -/
theorem goodInF (X : LinkSem K S Cl P Y) (b : Block S Cb) (terms : P → Y → List (ℕ × K)) (d : ℕ)
    (hok : ∀ s y, X.ready s → Desc.TermsOk K (terms (X.fixed s) y) d)
    (hval : ValueF X b terms F.ft) (p : Piece C F S Cb W) (hb : p.b = below b)
    (hext : ∀ a τ w, p.ext a τ w = w)
    (on on' : S × F.E.Str → Prop) (Bnd : S × F.E.Str → W → Y → Prop)
    (hready : ∀ a, on a → X.ready a.1)
    (hhands : ∀ a τ b', on a → p.ior.red.out a τ = some b' → on' b')
    (huniq : ∀ a w w' y y', on a → Bnd a w y → Bnd a w' y' → y = y')
    (hcarry : ∀ a τ b' w y, on a → p.ior.red.out a τ = some b' → Bnd b' w y → Bnd a w y)
    (hreads : p.Reads X.rd d) :
    p.GoodIn on on' (fun a w => ∃ y, Bnd a w y ∧ ∀ x ∈ terms (X.fixed a.1) y, x.2 = 0)
      (fun b' w => ∃ y, Bnd b' w y ∧ X.one b'.1 b'.1 y = 0) := by
  have hcard : ∀ a, (badAtF X terms on Bnd a).card ≤ d := by
    intro a
    unfold badAtF
    split
    · next h => exact badF_card_le _ d (hok a.1 _ (hready a h.1))
    · simp
  refine goodInOfBadFam S Cb W C F p on on' _ _
    (fun a => Classical.choose (hreads _ (hcard a) a.2)) ?_ ?_ ?_
  · intro a _
    exact (Classical.choose_spec (hreads _ (hcard a) a.2)).1
  · intro a τ b' ha _ hout
    exact hhands a τ b' ha hout
  · rintro a τ b' w ha hclean hout ⟨y, hB, hone⟩
    rw [hext]
    have hBa := hcarry a τ b' w y ha hout hB
    refine ⟨y, hBa, ?_⟩
    obtain ⟨hp, hw, hfold⟩ := Piece.out_below hb hout
    obtain ⟨k, hs⟩ := fold_one hfold
    obtain ⟨x, hx, _, hv⟩ := hval _ _ _ _ _ (hready a ha) hw hs
    have hnb := (Classical.choose_spec (hreads _ (hcard a) a.2)).2 τ hclean hp x hx
    have hex : on a ∧ ∃ y, ∃ w, Bnd a w y := ⟨ha, y, w, hBa⟩
    have hy : Classical.choose hex.2 = y := by
      obtain ⟨w', hw'⟩ := Classical.choose_spec hex.2
      exact huniq a w' w _ _ ha hw' hBa
    unfold badAtF at hnb
    rw [dif_pos hex, hy] at hnb
    exact zero_of_root _ _ ((hv y).symm.trans hone) hnb

omit [Fintype K] [DecidableEq K] in
/-- The piece hands on "behind". -/
theorem handsF (X : LinkSem K S Cl P Y) (b : Block S Cb) (terms : P → Y → List (ℕ × K))
    (hval : ValueF X b terms F.ft) (p : Piece C F S Cb W) (hb : p.b = below b) (a b' : S × F.E.Str)
    (τ : _root_.Iop.Tr (uLT C p.ds)) (hr : X.ready a.1) (hout : p.ior.red.out a τ = some b') :
    X.behind b'.1 := by
  obtain ⟨_, hw, hfold⟩ := Piece.out_below hb hout
  obtain ⟨k, hs⟩ := fold_one hfold
  obtain ⟨_, _, hbh, _⟩ := hval _ _ _ _ _ hr hw hs
  exact hbh

/-- **The same at the format's own kit of challenges, from the degree alone.** -/
theorem goodInF_real (X : LinkSem K S Cl P Y) (b : Block S Cb) (terms : P → Y → List (ℕ × K))
    (d : ℕ) (hok : ∀ s y, X.ready s → Desc.TermsOk K (terms (X.fixed s) y) d)
    (hval : ValueF X b terms F.ft) (p : Piece (ckP .two) F S Cb W) (hb : p.b = below b)
    (hext : ∀ a τ w, p.ext a τ w = w) (on on' : S × F.E.Str → Prop)
    (Bnd : S × F.E.Str → W → Y → Prop) (hready : ∀ a, on a → X.ready a.1)
    (hhands : ∀ a τ b', on a → p.ior.red.out a τ = some b' → on' b')
    (huniq : ∀ a w w' y y', on a → Bnd a w y → Bnd a w' y' → y = y')
    (hcarry : ∀ a τ b' w y, on a → p.ior.red.out a τ = some b' → Bnd b' w y → Bnd a w y)
    (hlog : ∀ r ∈ p.ds, r.entry.logN ≤ 64) (hback : ∀ r ∈ p.back, r.drawn.elems = [])
    (hinj : Function.Injective fun a : EV .two => X.rd (toU3 a))
    (herr : Err.le (allErr (fun _ _ => d) 0 p.ds) p.err) :
    p.GoodIn on on' (fun a w => ∃ y, Bnd a w y ∧ ∀ x ∈ terms (X.fixed a.1) y, x.2 = 0)
      (fun b' w => ∃ y, Bnd b' w y ∧ X.one b'.1 b'.1 y = 0) :=
  goodInF X b terms d hok hval p hb hext on on' Bnd hready hhands huniq hcarry
    (reads_allErr p X.rd d hlog hback hinj herr)

omit [Fintype K] [DecidableEq K] in
/-- LinkLaw2's premises, at a segment whose states behind the batching are full, give these. -/
theorem premisesF_of_link (X : LinkSem K S Cl P Y) (L : Link S Cl) (ft d : ℕ)
    (H : X.Premises L ft d) (hfull : ∀ s, X.behind s → X.full s) :
    PremisesF X L.batchB (claimsInBy L.each L.hear L.order)
      (fun p y => X.termsFrom p y L.order 0) ft d where
  later := H.later
  termsOk := fun s y hr => X.termsOk H.square (H.exps s hr) y
  fixedF := fun _ _ _ hg h => X.claimsIn_fixed H.later H.runs _ _ _ _ hg
    (claimsIn_of_claimsInBy _ _ _ _ _ h)
  batch := H.batch
  full := hfull

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.PremisesF.value
#print axioms VerifiableInference.Desc.K9L.badF_card_le
#print axioms VerifiableInference.Desc.K9L.goodInF
#print axioms VerifiableInference.Desc.K9L.handsF
#print axioms VerifiableInference.Desc.K9L.goodInF_real
#print axioms VerifiableInference.Desc.K9L.premisesF_of_link
