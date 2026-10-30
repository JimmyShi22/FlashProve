-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/H3/LeafOfCap.lean: the kind "lookup" (K3): the hypothesis of
the second mark's bound on its last event (`LeafFew`, Honest/K3/Good/MarkOut.lean: the factor of the
planes' value in the leaves' claim is 0), from a hypothesis on the kit (`KitCap`), one on the letter
kap (`CapsUnder`) and the form of that factor (`LeafForm`; all three Honest/K3/Good/H3/Defs.lean).
Conditional. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), sample, share and kit. In this
file: f is a lookup's face, C a kit, es the plan's entries at the lookup, dsb the data of the rounds
of the lookup's member; cap and kap are letters; pre and post are lists of sampled values in front
of and behind the round that samples alpha.

What is shown.
  `theta_cut`: the shift is read in front of alpha's round.
  `leavesR_cut`: the leaves' challenges are read behind alpha's round.
  `leafFew_at_alpha`: the hypothesis, with the round named: it is alpha's, by its number.
  `leafFew_of_cap`: the same at the name `LeafFew`, which names no round.
Helpers: `elemAt_behind`, `alpha_here`.

How the proof goes. The factor is alpha - 1 - T, where T reads the shift and the leaves' challenges
and not alpha. Its words are below the prime at all arguments (`okE_sub`,
Johnson/Top/H/P1Tie/Words.lean). So where the event holds, alpha, read in the field, is 1 + T: one
element, made of pre and post alone.

Hypotheses that remain.
  `hcap`, `hes`, `hk`, `hkap`: as in Honest/K3/Good/H3/FewOfCap.lean.
  `hp`: the face has one part of keys. It is the proof's, not the fact's: the closed forms of the
    stages' first rounds (`fr_leaves`, Honest/K3/HeardLaw.lean) speak at one part.
  `h2`: two planes at least. `hT`: `LeafForm f`.

The defaults. Alpha is read as the first element of its round's sample, 0 where there is none
(`elemAt`, Honest/K3/Heard.lean): `KitCap` asks nothing of an event at a sample without a first
element, and `hes`, `hk` and `h2` give that the round draws one element by the even rule. The shift
and the leaves' challenges are read in the same way out of pre and post, which stand under "for
all": pre's length is bounded, the numbers of its members' elements are not, and post is free. That
is `LeafFew`'s own form ("at every fixing"). Where it is spent, pre and post are what a kit's
messages show: `fence_all` (Honest/K3/Good/H3/Fence.lean [not in this library]).

Imported: the files of Honest/K3/Good/ beneath.

Users. Honest/K3/Good/H3/Member.lean.

Limits. Implications. cap and kap are letters: no number is named or evaluated. No instance of these
hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.FewOfCap
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.StoreStays
import Johnson.Top.H.P1Tie.Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open scoped ENNReal
open OnBytes (E zeroE oneE subE okE isZeroE)
open OnBytes.Slice (readE toE readE_sub readE_one readE_of_isZeroE readE_ofTriple)
open VerifiableInference.Desc.Part.MaskedSum (okE_sub)
open VerifiableInference.Desc.K3 (entriesV entriesFit drawEntry)
open OnBytes.Maker (RDT)
open _root_.Run.PQ (CK)

/-! ## 1 What reads which round -/

/-- A round behind the one that is exchanged is read the same. -/
theorem elemAt_behind (pre post : List Fmt.Drawn) (R R' : Fmt.Drawn) (j : Nat)
    (hj : pre.length < j) : elemAt (pre ++ R :: post) j = elemAt (pre ++ R' :: post) j := by
  obtain ⟨t, rfl⟩ : ∃ t, j = pre.length + (t + 1) := ⟨j - pre.length - 1, by omega⟩
  have e : pre.length + (t + 1) - pre.length = t + 1 := by omega
  unfold elemAt elemsAt
  rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), e,
    List.getElem?_cons_succ, List.getElem?_cons_succ]

/-- The shift is read in front of alpha's round. -/
theorem theta_cut (f : LFace) (pre post : List Fmt.Drawn) (R R' : Fmt.Drawn)
    (hl : pre.length = firstRound f .alpha) :
    (ptsOf f 0 (pre ++ R :: post)).theta = (ptsOf f 0 (pre ++ R' :: post)).theta := by
  rw [ptsOf_theta, ptsOf_theta]
  by_cases hs : f.shifted = true
  · have h0 : roundAt f 0 .shift < pre.length := by
      unfold roundAt
      rw [firstRound_shift f hs, hl, firstRound_alpha]
      unfold oAlpha
      rw [if_pos hs]
      exact Nat.zero_lt_one
    rw [if_pos hs, if_pos hs, elemAt_append pre (R :: post) _ h0,
      elemAt_append pre (R' :: post) _ h0]
  · rw [if_neg hs, if_neg hs]

/-- CONDITIONAL on one part of keys: the leaves' challenges are read behind alpha's round. -/
theorem leavesR_cut (f : LFace) (v : Nat) (hp : f.parts = [v]) (pre post : List Fmt.Drawn)
    (R R' : Fmt.Drawn) (hl : pre.length = firstRound f .alpha) :
    leavesR f 0 (pre ++ R :: post) = leavesR f 0 (pre ++ R' :: post) := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := o_chain f v
  have ha := fr_alpha f v hp
  have hv := fr_leaves f v hp
  unfold leavesR varChals
  refine congrArg List.toArray (List.map_congr_left fun l _ => ?_)
  refine elemAt_behind pre post R R' _ ?_
  unfold roundAt
  omega

/-- Alpha is the first element of its round's sample. -/
theorem alpha_here (f : LFace) (pre post : List Fmt.Drawn) (R : Fmt.Drawn) (w : Fmt.Ext3)
    (tl : List Fmt.Ext3) (hw : R.elems = w :: tl) (hl : pre.length = firstRound f .alpha) :
    (ptsOf f 0 (pre ++ R :: post)).alpha = E.ofTriple w := by
  rw [ptsOf_alpha]
  unfold roundAt elemAt elemsAt
  rw [Nat.zero_add, ← hl, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero]
  show (R.elems.map E.ofTriple).headD zeroE = E.ofTriple w
  rw [hw]
  rfl

/-! ## 2 The hypothesis -/

/-- CONDITIONAL on KitCap, one part of keys, two planes at least, the form of the leaf's factor, the
plan's entries, the data and CapsUnder: ALPHA's, BY ITS NUMBER, is a round of whose challenges, at
every fixing of all other rounds, at most the share kap make the factor 0. -/
theorem leafFew_at_alpha (C : CK) (cap : Fmt.Entry → Fmt.Kind → ℝ≥0∞) (hcap : KitCap C cap)
    (f : LFace) (v : Nat) (hp : f.parts = [v]) (h2 : 2 ≤ f.planes) (hT : LeafForm f)
    (es : List Fmt.Entry) (hes : entriesFit f es = true) (dsb : List RDT)
    (hk : List.Forall₂ KindFits dsb (es.map Law.declOf)) (kap : ℝ≥0∞)
    (hkap : CapsUnder cap f es kap) :
    ∃ (a : List RDT) (d : RDT) (b : List RDT), dsb = a ++ d :: b ∧
      a.length = firstRound f .alpha ∧
      ∀ pre post : List Fmt.Drawn, pre.length = a.length →
        shareAt C d (fun R => leafBad f (pre ++ R :: post) = true) ≤ kap := by
  unfold LeafForm at hT
  obtain ⟨T, hT⟩ := hT
  obtain ⟨e', he', e2⟩ := fit_at f es hes _ _ (alpha_laid f h2)
  have hzs : (es.map Law.declOf)[firstRound f .alpha]? = some (Law.declOf e') := by
    rw [List.getElem?_map, he']
    rfl
  obtain ⟨a, d, b, e1, ea, hd1, hd2⟩ := fits_at hk _ _ hzs
  have hd1' : d.entry = e' := hd1
  have hd2' : Fmt.kindOf e'.name = some d.kind := hd2
  have n1 : e'.name = "LKP" := congrArg (·.name) e2
  have n2 : e'.drawE = 1 := congrArg (·.drawE) e2
  have n3 : e'.drawNZ = 0 := congrArg (·.drawNZ) e2
  have n4 : e'.logN = 0 := congrArg (·.logN) e2
  have hkd : d.kind = .elems := by
    have hq : Fmt.kindOf "LKP" = some .elems := by decide
    rw [n1, hq] at hd2'
    exact (Option.some.inj hd2').symm
  have hi : P1K8.IsEl (Fmt.dsOf d.entry d.kind) 0 := by
    refine isEl_dsOf _ _ (by rw [hkd]; decide) _ ?_
    rw [hd1', n2, n3]
    exact Nat.zero_lt_one
  have hlog : d.entry.logN ≤ 64 := by
    rw [hd1', n4]
    exact Nat.zero_le _
  have hmem : firstRound f .alpha ∈ capRounds f := by
    unfold capRounds
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  have hcapk : cap d.entry d.kind ≤ kap := by
    rw [hd1']
    exact hkap _ hmem e' he' d.kind hd2'
  refine ⟨a, d, b, e1, ea, fun pre post hpl => le_trans ?_ hcapk⟩
  have hpl' : pre.length = firstRound f .alpha := hpl.trans ea
  refine hcap d.entry d.kind hlog 0 hi
    (1 + readE (T (ptsOf f 0 (pre ++ (⟨[], [], [], none⟩ : Fmt.Drawn) :: post)).theta
      (leavesR f 0 (pre ++ (⟨[], [], [], none⟩ : Fmt.Drawn) :: post))))
    (fun R => leafBad f (pre ++ R :: post) = true) (fun R _ hlen hb => ?_)
  obtain ⟨w, tl, hw⟩ : ∃ w tl, R.elems = w :: tl := by
    cases hR : R.elems with
    | nil =>
      rw [hR] at hlen
      exact absurd hlen (Nat.lt_irrefl 0)
    | cons w tl => exact ⟨w, tl, rfl⟩
  have hb' : (!(okE (f.leaf (ptsOf f 0 (pre ++ R :: post)).theta
      (ptsOf f 0 (pre ++ R :: post)).alpha (leavesR f 0 (pre ++ R :: post))) &&
      !isZeroE (f.leaf (ptsOf f 0 (pre ++ R :: post)).theta
        (ptsOf f 0 (pre ++ R :: post)).alpha (leavesR f 0 (pre ++ R :: post))))) = true := hb
  rw [hT, okE_sub] at hb'
  have hz : isZeroE (subE (subE (ptsOf f 0 (pre ++ R :: post)).alpha oneE)
      (T (ptsOf f 0 (pre ++ R :: post)).theta (leavesR f 0 (pre ++ R :: post)))) = true := by
    simpa using hb'
  have h0 := readE_of_isZeroE _ hz
  rw [readE_sub, readE_sub, readE_one, alpha_here f pre post R w tl hw hpl', readE_ofTriple,
    theta_cut f pre post R ⟨[], [], [], none⟩ hpl',
    leavesR_cut f v hp pre post R ⟨[], [], [], none⟩ hpl'] at h0
  unfold P1K8.AtEl
  refine ⟨toE w, by rw [hw]; rfl, ?_⟩
  show toE w = _
  linear_combination h0

/-- The same at the name `LeafFew`, which names no round. Same binders. -/
theorem leafFew_of_cap (C : CK) (cap : Fmt.Entry → Fmt.Kind → ℝ≥0∞) (hcap : KitCap C cap)
    (f : LFace) (v : Nat) (hp : f.parts = [v]) (h2 : 2 ≤ f.planes) (hT : LeafForm f)
    (es : List Fmt.Entry) (hes : entriesFit f es = true) (dsb : List RDT)
    (hk : List.Forall₂ KindFits dsb (es.map Law.declOf)) (kap : ℝ≥0∞)
    (hkap : CapsUnder cap f es kap) : LeafFew C f dsb kap := by
  obtain ⟨a, d, b, e1, _, h⟩ :=
    leafFew_at_alpha C cap hcap f v hp h2 hT es hes dsb hk kap hkap
  unfold LeafFew
  exact ⟨a, d, b, e1, h⟩

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.elemAt_behind
#print axioms ProofFile.Honest.K3.Good.theta_cut
#print axioms ProofFile.Honest.K3.Good.leavesR_cut
#print axioms ProofFile.Honest.K3.Good.alpha_here
#print axioms ProofFile.Honest.K3.Good.leafFew_at_alpha
#print axioms ProofFile.Honest.K3.Good.leafFew_of_cap
