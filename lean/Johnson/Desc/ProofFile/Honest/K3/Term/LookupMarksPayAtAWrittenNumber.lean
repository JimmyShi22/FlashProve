-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT NO FILLING: A COUNT OF THE VERIFIER's CHALLENGES ALONE: no prover, no filling, no run and no coin is read.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupMarksPayAtAWrittenNumber.lean: the kind "lookup" (K3): what the
lookups owe for their hundred marks (`k3Marks`, Honest/K3/Good/MarksList.lean), in the form in which the frame's
law on the first chain asks it (`FirstAsks`, field hM, Honest/Law/CoverAsks.lean), WITH NO LETTER LEFT: the two
hypotheses that `k3Marks_hM_blocks` (Honest/K3/Good/H3/Join.lean) left open, hcap and hkap, are shown here.

What is counted. CHALLENGES OF ONE ROUND, at the kit `Run.ckP .two` (strings of hash blocks). An event is "one named
drawn field element (three words) has one named value". A mark's stated numerator is its number of events.
  `shareOfOneValueAtARound e k`   the sealed bound of `P1K8.kit_count_blocks` at one value
  `shareOfOneValueHoldsAtHashBlocks`   hcap: `KitCap` at that bound: one call
  `widestRoundOfFace f`   max 1 (f.mu + f.d): no round of a lookup at the face f draws more field elements
      (`everyLookupRoundDrawsAtMostTheWidest`)
  `shareOfOneValue widest`   (1 + 2 ^ -128) ^ (3 * widest) / p ^ 3
  `lookupRoundsLieUnderTheWidest`   hkap at one face
  `everySiteIsUnderThirtySix`   at every site of every public part the widest round draws at most 36 field
      elements: 5 + d, and the public test on a shape's numbers (`FoNums.ok`) has 2 ^ (d + 32) below the prime
  `lookupMarksPayAtAWrittenNumber`   **the field hM's text at the lookups' marks**: each mark pays its number of
      events times `shareOfOneValue 36`
  `lookupEventsAtSite`, `lookupMarksAtAPlaceSumTo`, `lookupMarksElsewhereSumToZero`   what the lookups' marks at
      one member's place add up to

Limits. `lookupMarksPayAtAWrittenNumber` is conditional on the library's head `P5J.AtMgA`: the full size alone. At
one kit. The uniform law on a member's messages is named, not derived. THE MARKS' STATED SHARES (events over the
field's size) ARE NOT HELD AT THIS KIT: the number here is larger by the factor (1 + 2 ^ -128) ^ 108, and by a count by
hand, through no Lean, the stated shares are too small there: a string of hash blocks shows the word 0 a little more
often than any other. So a law that reads `mk.share.val` of these marks at this kit cannot be met; one that reads
`mk.share.num` times a number can. 108 IS WIDER THAN NEED BE: it bounds every round of a lookup, while the events read
no round that draws more than f.mu elements. What `markOut`'s silence gives has no user in this folder yet; its events
are paid all the same. The numbers of events are evaluated in LookupEventsInClosedForm.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.Join
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.Guards

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open scoped ENNReal
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Part (MaskedSum.entries MaskedSum.entry)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open VerifiableInference.Desc.K3 (entriesV entriesFit drawEntry faceOf)
open VerifiableInference.Desc.First.ProdV (levelEntries runEntries)
open OnBytes.Maker (RDT WholeD)
open Iop (kapSl)
open ProofFile.Honest.K3.Good

/-- The sealed bound at one round and one value: of the strings of hash blocks at the entry e and the kind k, the
share that show one named element at one named value. -/
noncomputable def shareOfOneValueAtARound (e : Fmt.Entry) (k : Fmt.Kind) : ℝ≥0∞ :=
  kapSl 128 ^ _root_.Run.exAll (Fmt.dsOf e k) * ((1 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)

/-- **The hypothesis hcap, shown**: one call of the sealed count. -/
theorem shareOfOneValueHoldsAtHashBlocks : KitCap (_root_.Run.ckP .two) shareOfOneValueAtARound :=
  fun e k hlog i hi y Q hQ => P1K8.kit_count_blocks e k hlog i (· = y) 1 (P1K8.cnt_eq_le y) hi Q hQ

/-- No round of a lookup at the face f draws more field elements than this. -/
def widestRoundOfFace (f : LFace) : ℕ := max 1 (f.mu + f.d)

/-- The bound at one value, at a round that draws at most `widest` field elements. -/
noncomputable def shareOfOneValue (widest : ℕ) : ℝ≥0∞ :=
  kapSl 128 ^ (3 * widest) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)

/-- A round of a masked sumcheck draws at most one field element. -/
theorem maskedSumRoundDrawsAtMostOne (k : Call) : ∀ e ∈ MaskedSum.entries k, e.drawE ≤ 1 := by
  intro e he
  unfold MaskedSum.entries at he
  rcases List.mem_append.1 he with h | h
  · rcases List.mem_append.1 h with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact Nat.le_refl _
    · obtain ⟨_, _, e2⟩ := List.mem_map.1 h
      subst e2
      exact Nat.le_refl _
  · cases hc : k.ends with
    | none => simp [hc] at h
    | some e' =>
      simp only [hc, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · subst h
        exact Nat.le_refl _
      · subst h
        exact Nat.zero_le _

/-- So does a round of a run of levels of a product tree. -/
theorem levelRunRoundDrawsAtMostOne (m0 n : ℕ) : ∀ e ∈ runEntries m0 n, e.drawE ≤ 1 := by
  intro e he
  unfold runEntries at he
  obtain ⟨i, _, h⟩ := List.mem_flatMap.1 he
  unfold levelEntries at h
  rcases List.mem_append.1 h with h | h
  · exact maskedSumRoundDrawsAtMostOne _ e h
  · obtain rfl := List.mem_singleton.1 h
    exact Nat.le_refl _

/-- Every round of the verifier's list at a face draws at most the widest number of field elements. -/
theorem everyLookupRoundDrawsAtMostTheWidest (f : LFace) :
    ∀ e ∈ entriesV f, e.drawE ≤ widestRoundOfFace f := by
  intro e he
  have one : 1 ≤ widestRoundOfFace f := Nat.le_max_left _ _
  have wide : f.mu + f.d ≤ widestRoundOfFace f := Nat.le_max_right _ _
  unfold entriesV at he
  simp only [List.mem_append] at he
  rcases he with (((((((((hA | hB) | hC) | hD) | hE) | hF) | hG) | hH) | hI) | hJ) | hK
  · split at hA
    · obtain rfl := List.mem_singleton.1 hA
      exact one
    · exact absurd hA List.not_mem_nil
  · obtain rfl := List.mem_singleton.1 hB
    exact one
  · exact (maskedSumRoundDrawsAtMostOne _ e hC).trans one
  · obtain ⟨_, _, h⟩ := List.mem_flatMap.1 hD
    exact (maskedSumRoundDrawsAtMostOne _ e h).trans one
  · obtain ⟨_, _, h⟩ := List.mem_flatMap.1 hE
    exact (maskedSumRoundDrawsAtMostOne _ e h).trans one
  · obtain rfl := List.mem_singleton.1 hF
    exact (Nat.le_add_right f.mu f.d).trans wide
  · obtain ⟨_, _, h⟩ := List.mem_flatMap.1 hG
    exact (levelRunRoundDrawsAtMostOne _ _ e h).trans one
  · exact (levelRunRoundDrawsAtMostOne _ _ e hH).trans one
  · exact (maskedSumRoundDrawsAtMostOne _ e hI).trans one
  · obtain rfl := List.mem_singleton.1 hJ
    exact wide
  · exact (maskedSumRoundDrawsAtMostOne _ e hK).trans one

/-- The number of field elements among copies of one draw that is no element. -/
theorem noElementAmongPositions (n k : ℕ) (ds : List Fmt.Draw) :
    OnBytes.Slice.nE (List.replicate n (Fmt.Draw.pos k) ++ ds) = OnBytes.Slice.nE ds := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    exact ih

theorem elementsAmongEvenDraws (n : ℕ) (ds : List Fmt.Draw) :
    OnBytes.Slice.nE (List.replicate n Fmt.Draw.elem ++ ds) = n + OnBytes.Slice.nE ds := by
  induction n with
  | zero => rw [Nat.zero_add]; rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    show OnBytes.Slice.nE (List.replicate n Fmt.Draw.elem ++ ds) + 1 = _
    rw [ih]
    omega

theorem elementsAmongNeverZeroDraws (n : ℕ) (ds : List Fmt.Draw) :
    OnBytes.Slice.nE (List.replicate n Fmt.Draw.elemNZ ++ ds) = n + OnBytes.Slice.nE ds := by
  induction n with
  | zero => rw [Nat.zero_add]; rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    show OnBytes.Slice.nE (List.replicate n Fmt.Draw.elemNZ ++ ds) + 1 = _
    rw [ih]
    omega

/-- A round whose kind is not "seeds", and that draws no more never-0 elements than elements, draws just as many
field elements as its entry says. -/
theorem roundDrawsItsEntrysElements (e : Fmt.Entry) (k : Fmt.Kind) (notSeeds : k ≠ .seeds)
    (neverZeroAmong : e.drawNZ ≤ e.drawE) : OnBytes.Slice.nE (Fmt.dsOf e k) = e.drawE := by
  unfold Fmt.dsOf Fmt.dsElems
  rw [if_neg notSeeds, noElementAmongPositions, List.append_assoc, elementsAmongEvenDraws,
    elementsAmongNeverZeroDraws]
  have tail : OnBytes.Slice.nE (Fmt.Draw.trits e.trits :: (if k = .sealed then [Fmt.Draw.sealed] else [])) = 0 := by
    split <;> rfl
  rw [tail]
  omega

/-- 1 ≤ 1 + 2 ^ -128. -/
theorem oneIsUnderTheSlack : (1 : ℝ≥0∞) ≤ kapSl 128 := by
  unfold Iop.kapSl
  exact le_self_add

/-- **The hypothesis hkap at one face, shown.** -/
theorem lookupRoundsLieUnderTheWidest (f : LFace) (planEntries : List Fmt.Entry)
    (planEntriesFit : entriesFit f planEntries = true) (widest : ℕ)
    (faceIsUnder : widestRoundOfFace f ≤ widest) :
    CapsUnder shareOfOneValueAtARound f planEntries (shareOfOneValue widest) := by
  intro n _ e he k hk
  have hmem := fit_mem f planEntries planEntriesFit e (List.mem_of_getElem? he)
  obtain ⟨_, t2, k0, t3, _, t4⟩ := entriesV_tame f _ hmem
  have hw := everyLookupRoundDrawsAtMostTheWidest f _ hmem
  have hk0 : k = k0 := by
    have t3' : Fmt.kindOf e.name = some k0 := t3
    rw [hk] at t3'
    exact Option.some.inj t3'
  have hn : OnBytes.Slice.nE (Fmt.dsOf e k) = e.drawE :=
    roundDrawsItsEntrysElements e k (by rw [hk0]; exact t4) t2
  have hle : _root_.Run.exAll (Fmt.dsOf e k) ≤ 3 * widest := by
    rw [P1K8.exAll_eq, hn]
    have hw' : e.drawE ≤ widestRoundOfFace f := hw
    omega
  unfold shareOfOneValueAtARound shareOfOneValue
  rw [Nat.cast_one, mul_one]
  exact ENNReal.div_le_div_right (pow_le_pow_right₀ oneIsUnderTheSlack hle) _

/-- **At every site of every public part the widest round draws at most 36 field elements.** No hypothesis but the
site: the face is the shape's, with mu = 5, and the public test on a shape's numbers bounds d. -/
theorem everySiteIsUnderThirtySix (Zp : ProofFile.Pub) :
    ∀ s ∈ lookSites Zp, widestRoundOfFace s.at_.face ≤ 36 := by
  intro s hs
  obtain ⟨h1, h2⟩ := Law.sites_shape_ok Zp s hs
  rw [h1]
  have hd : 2 ^ (s.shape.d + 32) < OnBytes.pW.toNat := by
    unfold FoNums.ok at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    exact h2.2
  have hp : OnBytes.pW.toNat < 2 ^ 64 := OnBytes.pW.toNat_lt
  have hlt : s.shape.d + 32 < 64 := (Nat.pow_lt_pow_iff_right (by omega)).1 (hd.trans hp)
  show max 1 (5 + s.shape.d) ≤ 36
  omega

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FIELD hM OF `FirstAsks` AT THE LOOKUPS' MARKS, AT STRINGS OF HASH BLOCKS, NO LETTER LEFT.** Conditional
on the head and the cut alone. The end is the end of `k3Marks_hM_blocks` with the written number for its letter. -/
theorem lookupMarksPayAtAWrittenNumber (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G₀ : ProofFile.Ground}
    {pre₁ : List (Block P5J.TS ProofFile.Cl)} {e₁ : Block P5J.TS ProofFile.Cl} (cut : cF.blocksInOrder = pre₁ ++ [e₁])
    {PM : Block P5J.TS ProofFile.Cl → List Fmt.Drawn → Prop} :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K3.Good.k3Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) ((mk.share.num : ℝ≥0∞) * shareOfOneValue 36) := by
  refine k3Marks_hM_blocks shareOfOneValueAtARound shareOfOneValueHoldsAtHashBlocks h (shareOfOneValue 36)
    (fun s hs => ?_) cut
  obtain ⟨A, b, b', B, hpre, hp⟩ := site_has_behind h cut s hs
  have hb : b ∈ cF.blocksInOrder := by
    rw [cut, hpre]
    exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
  exact lookupRoundsLieUnderTheWidest _ _ (member_at_site h s hs b hb hp).2 36
    (everySiteIsUnderThirtySix Zp s hs)

/-- The number of events of both marks of one lookup. -/
def lookupEventsAtSite (s : Site) : ℕ := events s.at_.face + eventsOut s.at_.face

/-- Among the marks of a list of sites with distinct places, those at one site's place are that site's two. -/
theorem marksAtOneSitesPlace (s : Site) : ∀ sites : List Site, (sites.map (·.at_.place)).Nodup → s ∈ sites →
    (sites.flatMap fun t => [markK3 t.at_.place t.at_.face, markOut t.at_.place t.at_.face]).filter
      (fun m => m.place == s.at_.place) = [markK3 s.at_.place s.at_.face, markOut s.at_.place s.at_.face]
  | [], _, h => absurd h List.not_mem_nil
  | t :: rest, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.flatMap_cons, List.filter_append]
    by_cases e : t.at_.place = s.at_.place
    · have hrest : (rest.flatMap fun t => [markK3 t.at_.place t.at_.face, markOut t.at_.place t.at_.face]).filter
          (fun m => m.place == s.at_.place) = [] := by
        rw [List.filter_eq_nil_iff]
        intro mk hmk hpl
        obtain ⟨t', ht', hm⟩ := List.mem_flatMap.1 hmk
        have e' : t'.at_.place = s.at_.place := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl
          · exact eq_of_beq hpl
          · exact eq_of_beq hpl
        exact hnd.1 (List.mem_map.2 ⟨t', ht', e'.trans e.symm⟩)
      have hst : s = t := by
        rcases List.mem_cons.1 h with hs | hs
        · exact hs
        · exact absurd (List.mem_map.2 ⟨s, hs, e.symm⟩) hnd.1
      subst hst
      rw [hrest, List.append_nil,
        List.filter_cons_of_pos (by show (s.at_.place == s.at_.place) = true; exact beq_self_eq_true _),
        List.filter_cons_of_pos (by show (s.at_.place == s.at_.place) = true; exact beq_self_eq_true _),
        List.filter_nil]
    · have hs : s ∈ rest := by
        rcases List.mem_cons.1 h with hs | hs
        · exact absurd (by rw [hs]) e
        · exact hs
      have hhead : [markK3 t.at_.place t.at_.face, markOut t.at_.place t.at_.face].filter
          (fun m => m.place == s.at_.place) = [] := by
        rw [List.filter_eq_nil_iff]
        intro mk hm hpl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl
        · exact e (eq_of_beq hpl)
        · exact e (eq_of_beq hpl)
      rw [hhead, List.nil_append]
      exact marksAtOneSitesPlace s rest hnd.2 hs

/-- **What the lookups' marks at one site's place add up to**: the site's number of events times the bound at one
value. No hypothesis but the site. -/
theorem lookupMarksAtAPlaceSumTo (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (s : Site) (hs : s ∈ lookSites Zp)
    (oneValue : ℝ≥0∞) :
    (((k3Marks Zp G₀).filter fun m => m.place == s.at_.place).map
      fun mk => (mk.share.num : ℝ≥0∞) * oneValue).sum = (lookupEventsAtSite s : ℝ≥0∞) * oneValue := by
  have hl : (k3Marks Zp G₀).filter (fun m => m.place == s.at_.place) =
      [markK3 s.at_.place s.at_.face, markOut s.at_.place s.at_.face] :=
    marksAtOneSitesPlace s (lookSites Zp) (Law.AtThr.site_places_once Zp) hs
  rw [hl]
  show ((events s.at_.face : ℕ) : ℝ≥0∞) * oneValue + (((eventsOut s.at_.face : ℕ) : ℝ≥0∞) * oneValue + 0) = _
  unfold lookupEventsAtSite
  rw [add_zero, Nat.cast_add, add_mul]

/-- At a place that is no site's the lookups' marks add up to nothing. -/
theorem lookupMarksElsewhereSumToZero (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (a : Place)
    (noSite : ∀ s ∈ lookSites Zp, s.at_.place ≠ a) (oneValue : ℝ≥0∞) :
    (((k3Marks Zp G₀).filter fun m => m.place == a).map
      fun mk => (mk.share.num : ℝ≥0∞) * oneValue).sum = 0 := by
  have hnil : (k3Marks Zp G₀).filter (fun m => m.place == a) = [] := by
    rw [List.filter_eq_nil_iff]
    intro mk hmk hpl
    obtain ⟨s, hs, hor⟩ := k3Marks_mem Zp G₀ mk hmk
    rcases hor with rfl | rfl
    · exact noSite s hs (eq_of_beq hpl)
    · exact noSite s hs (eq_of_beq hpl)
  rw [hnil]
  rfl

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.shareOfOneValueHoldsAtHashBlocks
#print axioms ProofFile.Honest.K3.Term.everyLookupRoundDrawsAtMostTheWidest
#print axioms ProofFile.Honest.K3.Term.roundDrawsItsEntrysElements
#print axioms ProofFile.Honest.K3.Term.lookupRoundsLieUnderTheWidest
#print axioms ProofFile.Honest.K3.Term.everySiteIsUnderThirtySix
#print axioms ProofFile.Honest.K3.Term.lookupMarksPayAtAWrittenNumber
#print axioms ProofFile.Honest.K3.Term.marksAtOneSitesPlace
#print axioms ProofFile.Honest.K3.Term.lookupMarksAtAPlaceSumTo
#print axioms ProofFile.Honest.K3.Term.lookupMarksElsewhereSumToZero
