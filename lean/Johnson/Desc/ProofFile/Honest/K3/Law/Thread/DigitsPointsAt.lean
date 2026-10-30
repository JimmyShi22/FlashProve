-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsPointsAt.lean: under the library's hypothesis
`P5J.AtMgA` (Johnson/P5J/MgAtAll.lean), behind an accepting step of the member at a lookup on the
digits, of what the smallness test's structure then holds as heard: the two points zx and zy have dT
and rK coordinates; and, where the words of every sampled element are below the prime, so are the
words of every coordinate of zy. Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: `lookHeardAt` (Honest/K3/HeardWhole.lean) is
the structure that the challenges alone make, from a shape, a base and a list of challenges.
`Good.Ok rs` (Honest/K3/Good/Levels.lean) says that the words of every sampled element of the rounds
rs are below the prime. `borderOf l d` (Johnson/Desc/Sound/MgAt/K3Open.lean) is the number of the
border in front of link l's lookup; d is true for the lookup on the digits.

What is shown.
  `ok_elemAt_of`, `ok_drawn_of`, `ok_set_at`, `ok_layBack`, `ok_varChals`, `ok_keyPt`,
    `ok_extract_at`: small lemmas. The first sample of a round; `Good.Ok` of the rounds, said of
    their challenges; an array with an entry set; `layBack`; a sumcheck's challenges; the point in
    front of a key level; a cut of an array: each has its words below the prime where the sampled
    elements have.
  `lookHeardAt_sizes`: the two sizes of the fields zx and zy of `lookHeardAt`, at every shape, base
    and list of challenges.
  `ok_zy_at`: the words of every coordinate of the field zy of `lookHeardAt` are below the prime.
  `digits_points_site`: the statement above at a site on the digits, at the member at the border
    `borderOf s.link true`.
  `digits_points_link`: at a link's number l < 25.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA`.
  `hs`, `hl`, `hd`: s is a site of the public part; its link is below 25; it is on the digits (`hl`
    follows from `h` and `hs`: `link_lt_head`, Honest/K3/Law/Thread/LinkLtHead.lean).
  `hr`: (in `digits_points_link`) as in Honest/K3/Law/Thread/DigitsHeardLink.lean. (`rng_at`,
    Johnson/AtFull/Shape/SitesAtHead.lean, a file that is not imported here, states it under
    `P5J.AtMgA` at every
    link below 25; so does `rng_head_paid`, Honest/K3/Law/Thread/RngWrittenHolds.lean.)
  Inside the statements: the member at the border; the acceptance of its step.
  `Good.Ok rs`: for the clause on the words alone. The step's acceptance alone does not give it: it
    follows from the library's test on rounds (`ok_of_okRoundsE`,
    Honest/K3/Law/Thread/OkOfRounds.lean) or from the frame's test on challenges (`ok_of_fit`,
    Honest/K3/Good/Gives.lean).
  In the helpers: `hD`, `hv`, `ha`, `hc`, `hn`: the words of what goes in (the sampled elements, the
    entry, the array, the challenges) are below the prime.

Follows. `ok_elemAt_of` and `ok_extract_at` follow `elemAt_ok` (Honest/K3/FastLaw/Lift.lean) and
`cut_ok` (Honest/K3/FastLaw/InY.lean) closely. They are stated a second time so that this file
imports nothing of that folder: two texts of each stand.

How the proof goes. By way of `OpenSame` (Honest/K3/HeardWhole.lean): the two fields zx and zy are
those that the challenges alone make. The theorems call `digits_heard_site`
(Honest/K3/Law/Thread/DigitsHeardLink.lean), `site_there_head`
(Honest/K3/Law/Thread/SiteThereHead.lean), `member_at_link` (Honest/K3/Law/Thread/AtLinkThere.lean)
and `size_keyPt` (Honest/K3/Law/SpecCourse.lean).

Limits. On the verifier's side alone. At the full size alone: that limit comes with `P5J.AtMgA`.
Whether a step accepts anywhere is not spoken of. Right behind the member's step: nothing on later
states. That the site's shape is the structure's own field f9 is not shown here. No instance of
these hypotheses is exhibited in this file. No state and no rounds are shown at which the step
accepts.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsHeardLink
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecCourse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes (E zeroE okE)
open VerifiableInference.Desc (Block Chain OpenedColumn)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.First.ProdV (layBack)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 Words below the prime -/

/-- The first element that a round sampled has its words below the prime. -/
theorem ok_elemAt_of {ds : List Fmt.Drawn}
    (hD : ∀ d ∈ ds, ∀ x ∈ d.elems, okE (E.ofTriple x) = true) (i : Nat) :
    okE (elemAt ds i) = true := by
  unfold elemAt elemsAt
  cases hd : ds[i]? with
  | none => rfl
  | some d =>
    have hm : d ∈ ds := List.mem_of_getElem? hd
    show okE ((d.elems.map E.ofTriple).headD zeroE) = true
    cases he : d.elems with
    | nil => rfl
    | cons x l => exact hD d hm x (by rw [he]; exact List.mem_cons_self)

/-- `Good.Ok` of the rounds, said of their challenges. -/
theorem ok_drawn_of {rs : List Fmt.RoundView} (h : Good.Ok rs) :
    ∀ d ∈ rs.map (·.drawn), ∀ x ∈ d.elems, okE (E.ofTriple x) = true := by
  intro d hd x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hd
  exact h r hr x hx

/-- An array with one entry set has words below the prime, where the array and the entry have. -/
theorem ok_set_at (a : Array E) (k : Nat) (v : E) (hv : okE v = true)
    (ha : ∀ j, okE (a.getD j zeroE) = true) (j : Nat) :
    okE ((a.set! k v).getD j zeroE) = true := by
  have h0 := ha j
  rw [Array.getD_eq_getD_getElem?] at h0 ⊢
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  split_ifs
  · exact hv
  · rfl
  · exact h0

/-- The challenges laid back at their bits have words below the prime, where the challenges have. -/
theorem ok_layBack (m : Nat) (order : List Nat) (cs : List E) (hc : ∀ c ∈ cs, okE c = true)
    (j : Nat) : okE ((layBack m order cs).getD j zeroE) = true := by
  unfold layBack
  have key : ∀ (l : List (Nat × E)) (a : Array E), (∀ x ∈ l, okE x.2 = true) →
      (∀ j, okE (a.getD j zeroE) = true) →
      ∀ j, okE ((l.foldl (fun (r : Array E) x => r.set! (m - 1 - x.1) x.2) a).getD j zeroE) =
        true := by
    intro l
    induction l with
    | nil => exact fun _ _ ha => ha
    | cons x l ih =>
      intro a hl ha
      exact ih (a.set! (m - 1 - x.1) x.2) (fun y hy => hl y (List.mem_cons_of_mem _ hy))
        (ok_set_at a _ _ (hl x List.mem_cons_self) ha)
  refine key _ _ (fun x hx => hc x.2 (List.of_mem_zip (a := x.1) (b := x.2) hx).2) (fun i => ?_) j
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split_ifs <;> rfl

/-- A sumcheck's challenges have words below the prime, where all sampled elements have. -/
theorem ok_varChals {ds : List Fmt.Drawn}
    (hD : ∀ d ∈ ds, ∀ x ∈ d.elems, okE (E.ofTriple x) = true) (f : LFace) (base : Nat) (s : Stage)
    (n : Nat) : ∀ c ∈ varChals f base ds s n, okE c = true := by
  intro c hc
  unfold varChals at hc
  obtain ⟨l, _, rfl⟩ := List.mem_map.1 hc
  exact ok_elemAt_of hD _

/-- **Every coordinate of the point in front of a key level.** -/
theorem ok_keyPt {ds : List Fmt.Drawn}
    (hD : ∀ d ∈ ds, ∀ x ∈ d.elems, okE (E.ofTriple x) = true) (f : LFace) (base i n j : Nat) :
    okE (((ptsOf f base ds).keyPt i n).getD j zeroE) = true := by
  cases n with
  | zero =>
    show okE ((#[] : Array E).getD j zeroE) = true
    rw [Array.getD_eq_getD_getElem?]
    rfl
  | succ m =>
    show okE ((behind m (f.orders i m) (varChals f base ds (.key i m) m)
      (elemAt ds (roundAt f base (.keyLine i m)))).getD j zeroE) = true
    unfold behind
    rw [Array.getD_eq_getD_getElem?]
    by_cases hj : j < 1
    · obtain rfl : j = 0 := by omega
      rw [Array.getElem?_append_left (by simp)]
      exact ok_elemAt_of hD _
    · have hj1 : 1 ≤ j := by omega
      rw [Array.getElem?_append_right (by simpa using hj1)]
      have h1 := ok_layBack m (f.orders i m) (varChals f base ds (.key i m) m)
        (ok_varChals hD f base _ m) (j - 1)
      rw [Array.getD_eq_getD_getElem?] at h1
      exact h1

/-- A cut of an array has words below the prime, where the array has. -/
theorem ok_extract_at (n : Array E) (hn : ∀ x, okE (n.getD x zeroE) = true) (s e i : Nat) :
    okE ((n.extract s e).getD i zeroE) = true := by
  by_cases h : i < min e n.size - s
  · have h2 : s + i < n.size := by omega
    have h3 := hn (s + i)
    simp [Array.getD, h2] at h3
    simp [Array.getD, h, h3]
  · simp [Array.getD, h]
    rfl

/-! ## 2 The structure that the challenges alone make -/

/-- **The sizes of its two points zx and zy.** -/
theorem lookHeardAt_sizes (h : OnBytes.Model.Forest.Shape) (base : Nat) (ds : List Fmt.Drawn) :
    (lookHeardAt h base ds).zx.size = h.dT ∧ (lookHeardAt h base ds).zy.size = h.rK := by
  have hp := Spec.size_keyPt (faceOf h) base ds 0 h.v
  have hv : h.v = h.dT + h.rK := rfl
  constructor
  · show (((ptsOf (faceOf h) base ds).keyPt 0 h.v).extract 0 h.dT).size = h.dT
    simp only [Array.size_extract]
    omega
  · show (((ptsOf (faceOf h) base ds).keyPt 0 h.v).extract h.dT
      ((ptsOf (faceOf h) base ds).keyPt 0 h.v).size).size = h.rK
    simp only [Array.size_extract]
    omega

/-- **Every coordinate of its zy has its words below the prime.** Conditional on the same of the
sampled elements. -/
theorem ok_zy_at {ds : List Fmt.Drawn}
    (hD : ∀ d ∈ ds, ∀ x ∈ d.elems, okE (E.ofTriple x) = true)
    (h : OnBytes.Model.Forest.Shape) (base j : Nat) :
    okE ((lookHeardAt h base ds).zy.getD j zeroE) = true :=
  ok_extract_at _ (ok_keyPt hD (faceOf h) base 0 h.v) _ _ j

/-! ## 3 Behind the member -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At a site on the digits, behind an accepting step of the member at the border in front of the
lookup**: the smallness test's structure holds a heard structure of the site's shape whose zx and zy
have dT and rK coordinates. Conditional on `P5J.AtMgA` and the site; the clause on the words of zy
also on `Good.Ok rs`. No instance of these hypotheses is exhibited in this file. -/
theorem digits_points_site (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hl : s.link < 25) (hd : s.digits = true) :
    ∀ blk, cF.blocksInOrder[borderOf s.link true]? = some blk →
      ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
        blk.step ft sj rs c = .ok (sj', n) →
        ∃ tl g, sj'.tl? = some tl ∧ tl.heard = some g ∧ g.shape = s.shape ∧
          g.zx.size = s.shape.dT ∧ g.zy.size = s.shape.rK ∧
          (Good.Ok rs → ∀ j, okE (g.zy.getD j zeroE) = true) := by
  intro blk hblk ft sj sj' n rs c hstep
  obtain ⟨tl, g, t1, t2, W, _, _, _⟩ :=
    digits_heard_site h s hs hl hd blk hblk ft sj sj' n rs c hstep
  obtain ⟨z1, z2⟩ := lookHeardAt_sizes s.shape 0 (rs.map (·.drawn))
  refine ⟨tl, g, t1, t2, W.shape, ?_, ?_, fun hok j => ?_⟩
  · rw [W.zx]
    exact z1
  · rw [W.zy]
    exact z2
  · rw [W.zy]
    exact ok_zy_at (ok_drawn_of hok) s.shape 0 j

/-- **At a link's number**: there are a site on the digits and a member at the border, and the same
holds there. Conditional on `P5J.AtMgA` and `hr`. No instance of these hypotheses is exhibited in
this file. -/
theorem digits_points_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (hr : (rngIn ((spotsOf Zp.cuts).getD []) l).isSome = true) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = true ∧
      ∃ blk, cF.blocksInOrder[borderOf l true]? = some blk ∧ blk.place = IM.k3Place l true ∧
        ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
          blk.step ft sj rs c = .ok (sj', n) →
          ∃ tl g, sj'.tl? = some tl ∧ tl.heard = some g ∧ g.shape = s.shape ∧
            g.zx.size = s.shape.dT ∧ g.zy.size = s.shape.rK ∧
            (Good.Ok rs → ∀ j, okE (g.zy.getD j zeroE) = true) := by
  obtain ⟨s, hs, e1, e2, _, _⟩ := site_there_head h l hl true fun _ => hr
  subst e1
  obtain ⟨blk, b1, b2⟩ := member_at_link h s.link hl true
  exact ⟨s, hs, rfl, e2, blk, b1, b2, digits_points_site h s hs hl e2 blk b1⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.ok_elemAt_of
#print axioms ProofFile.Honest.K3.Law.AtThr.ok_drawn_of
#print axioms ProofFile.Honest.K3.Law.AtThr.ok_set_at
#print axioms ProofFile.Honest.K3.Law.AtThr.ok_layBack
#print axioms ProofFile.Honest.K3.Law.AtThr.ok_varChals
#print axioms ProofFile.Honest.K3.Law.AtThr.ok_keyPt
#print axioms ProofFile.Honest.K3.Law.AtThr.ok_extract_at
#print axioms ProofFile.Honest.K3.Law.AtThr.lookHeardAt_sizes
#print axioms ProofFile.Honest.K3.Law.AtThr.ok_zy_at
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_points_site
#print axioms ProofFile.Honest.K3.Law.AtThr.digits_points_link
