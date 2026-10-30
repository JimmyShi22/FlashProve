-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06EveryList.lean: THE OUTPUT HEAD'S OWN ROUNDS AT THE TRUTH: THE DECISION'S
YES, Block.step'S YES AND WHAT IS OPENED, ALSO WHERE A PLAIN CHALLENGE IS 0. NO EXAMPLE WITH SUCH A
CHALLENGE IS SHOWN: that the premises here are met more widely than the library's own is by form
alone.
WHAT IT IS NOT. No prover: that any rounds meet the premises is not shown here. Nothing on chance:
"no bad draw" is neither asked nor concluded. Nothing on soundness, on completeness or on what a
proof hides. CONDITIONAL throughout: on the hearing's return, on the rounds' shape, and, for what is
opened, on the values that the hearing left AND ON THE FOUR SUMCHECKS' OWN FORMS BEING WORTH 0
(NormTruthW, HeadTruth: the fields sqRow, prRow, nmRow; row): OF THE 35 FORMS THAT ARE CONCLUDED TO
BE WORTH 0 THESE FOUR GO IN AS THEY COME OUT; 31 are derived. (Law/K06Honest.lean's head says the
same of HonestRun.)
WHY. Law/K06Honest.lean's HonestRun has the field nonzero: no drawn element is (0,0,0). Its theorems
take the structure whole, so they cannot be called at rounds in which a plain challenge is 0. The
verifier's own text asks less: of a round's drawn elements the LAST drawNZ are not (0,0,0)
(Johnson/Desc/First/Tape/Tape.lean: roundT, seventh clause; Johnson/Desc/Block.lean: drawsMarkedNonzeroHaveNonzeroWords). In the
table of the head's rounds that is the one element of each of the four rounds "PSC Y".
WHAT IS TYPED ANEW, AND WHY. Two library lemmas take "no element of D is (0,0,0)" as a premise,
where the verifier's text needs it of a round's last drawNZ elements alone; a third takes the list D
alone. Each is typed again over ShapedNZ, with the lemma that lifts it to a list of rounds:
  roundT_returnsNZ | tape_returnsNZ      after Law/TapeShape.lean's roundT_returns | tape_returns
  roundFit_oneNZ | roundsFit_shapedNZ    after Law/StepFits.lean's roundFit_one | roundsFit_shaped
  noDigest_shapedNZ | step_of_shapedNZ   after Law/StepFits.lean's noDigest_shaped and
                                         Law/K06HonestStep.lean's step_of_shaped
  noSeeds_of | rounds_noSeeds            after Law/TapeShape.lean's plain_of | rounds_plain (and
                                         Law/StepFits.lean's rounds_known): the same unfolding of
                                         the table and the same cases
and the two tops' texts, with the fields that they do not read left out:
  truthHeard_opens    after honestRun_opens' second half · yes_of_heard | yes_opened after
                      nine_of_honest (both Law/K06Honest.lean).
EVERY LEMMA OF THE LIBRARY WITH CONTENT IS CALLED AS IT IS: opened_all (Law/OpenedAll.lean),
hear_parts, norm_parts, batch_okConst, decide_returns, letters_of_lookup (Law/K06ToyParts.lean),
lays_of (Law/K06Honest.lean), seatBack_at (Law/HeardBack.lean), rounds_plain, elemsOf_of,
groups_none, blockAt_rounds, Came.decide_step (Law/StepBack.lean), triple_ne_zero, given_ok,
planFacts, ls_le_lPd.
  ShapedNZ rs Rs      round for round as the table says; the last drawNZ drawn elements are not 0.
  knownNoSeeds        the format knows the round's name, and its kind is not "seeds" (at that kind
                      the format marks other elements than the last as never 0).
  TruthHeard          HonestRun less can, shaped, nonzero and truth.
  HeardK6 | TruthK6   the same at a state of the verifier.
  shapedNZ_of_shapedAs | truthHeard_of_honest | truthK6_of_honest   from the library's structures.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06HonestStep

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE zeroE oneE)
open OnBytes.Model (Aff Fork World)
open Norm (lt ls d lPd T S2)
open Part.MaskedSum (rvOf)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Tape (elemsOf roundT tapeT)

/-! ## 1 The shape -/

/-- **Round for round as the table says**: scalars and drawn elements alone, in the table's counts;
of the drawn elements the last one, where the table's round says "not 0", is not (0,0,0). -/
def ShapedNZ (rs : List Fmt.RoundView) (Rs : List Round) : Prop :=
  List.Forall₂ (fun (r : Fmt.RoundView) (R : Round) => ∃ s d, r = rvOf s d ∧ s.length = R.sent ∧
    d.length = R.drawn ∧
    ∀ x ∈ d.drop (R.drawn - (if R.notZero then 1 else 0)), OnBytes.isZeroE x = false) rs Rs

/-- The library's shape with "no element of D is (0,0,0)" gives it. -/
theorem shapedNZ_of_shapedAs (D : List E) (hz : ∀ x ∈ D, OnBytes.isZeroE x = false) :
    ∀ (rs : List Fmt.RoundView) (Rs : List Round), ShapedAs D rs Rs → ShapedNZ rs Rs
  | _, _, .nil => .nil
  | _, _, .cons (a := r) (b := R) (l₁ := rs) (l₂ := Rs) h1 h2 => by
    obtain ⟨s, d, e, hs, hd, hD⟩ := h1
    exact .cons ⟨s, d, e, hs, hd, fun x hx => hz x (hD x (List.mem_of_mem_drop hx))⟩
      (shapedNZ_of_shapedAs D hz rs Rs h2)

/-! ## 2 The decision's strict reading of the rounds returns -/

/-- One round. -/
theorem roundT_returnsNZ (work : Nat) (R : Round) (s d : List E) (hs : s.length = R.sent)
    (hd : d.length = R.drawn) (hp : plainRound R = true)
    (hz : ∀ x ∈ d.drop (R.drawn - (if R.notZero then 1 else 0)), OnBytes.isZeroE x = false) :
    (roundT headRule (rvOf s d) (R.entry work)).isSome = true := by
  unfold plainRound at hp
  rw [Bool.and_eq_true] at hp
  obtain ⟨p1, p2⟩ := hp
  have hall : (((d.map (·.triple)).drop (R.drawn - (if R.notZero then 1 else 0))).all fun x =>
      !OnBytes.isZeroE (E.ofTriple x)) = true := by
    rw [List.all_eq_true]
    intro x hx
    rw [← List.map_drop] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [E.ofTriple_triple, hz y hy]
    rfl
  unfold roundT
  have he : elemsOf (rvOf s d).vals = some s := elemsOf_of s
  rw [he]
  simp only [rvOf, Round.entry, headRule, List.length_map, hd, hs, beq_self_eq_true,
    List.isEmpty_nil, Bool.and_self, p1, p2, hall, if_true, Option.isSome_some]

/-- **The strict reading returns.** -/
theorem tape_returnsNZ (work : Nat) :
    ∀ (rs : List Fmt.RoundView) (Rs : List Round), ShapedNZ rs Rs →
      (∀ R ∈ Rs, plainRound R = true) →
      (tapeT headRule rs (Rs.map fun R => R.entry work)).isSome = true
  | _, _, .nil, _ => rfl
  | _, _, .cons (a := r) (b := R) (l₁ := rs) (l₂ := Rs) h1 h2, hp => by
    obtain ⟨s, d, rfl, hs, hd, hD⟩ := h1
    have a := roundT_returnsNZ work R s d hs hd (hp R List.mem_cons_self) hD
    have b := tape_returnsNZ work rs Rs h2 fun R' h' => hp R' (List.mem_cons_of_mem _ h')
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp a
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp b
    show (tapeT headRule (rvOf s d :: rs) (R.entry work :: Rs.map fun R => R.entry work)).isSome
      = true
    unfold tapeT
    rw [hx, ht]
    rfl

/-! ## 3 Block.step's own tests on the rounds -/

/-- The format knows the round's name, and its kind is not "seeds". -/
def knownNoSeeds (R : Round) : Bool := (Fmt.kindOf R.name).any fun k => k != .seeds

/-- One round passes the step's test on the rounds. -/
theorem roundFit_oneNZ (work : Nat) (R : Round) (s d : List E) (hs : s.length = R.sent)
    (hd : d.length = R.drawn) (hk : knownNoSeeds R = true)
    (hz : ∀ x ∈ d.drop (R.drawn - (if R.notZero then 1 else 0)), OnBytes.isZeroE x = false)
    (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView) (h : roundsFit ds rs = true) :
    roundsFit (({ entry := R.entry work } : Fmt.DeclaredRound) :: ds) (rvOf s d :: rs) = true := by
  obtain ⟨k, hk', hks⟩ : ∃ k, Fmt.kindOf R.name = some k ∧ k ≠ .seeds := by
    unfold knownNoSeeds at hk
    cases hq : Fmt.kindOf R.name with
    | none =>
      rw [hq] at hk
      cases hk
    | some k =>
      rw [hq] at hk
      exact ⟨k, rfl, by simpa using hk⟩
  have hv : (rvOf s d).vals.map itemOf = List.replicate R.sent Fmt.Item.e := by
    rw [← hs]
    show (s.map fun x => Fmt.ItemValue.e x.triple).map itemOf = _
    rw [List.map_map]
    exact List.eq_replicate_iff.mpr ⟨by simp, fun b hb => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
      rfl⟩
  have hi : (({ entry := R.entry work } : Fmt.DeclaredRound).items.filter (· != .root))
      = List.replicate R.sent Fmt.Item.e := by
    show ((R.entry work).cut.filter (· != .root)) = _
    unfold Fmt.Entry.cut Round.entry
    simp
  have hnz : drawsMarkedNonzeroHaveNonzeroWords ({ entry := R.entry work } : Fmt.DeclaredRound) (rvOf s d) = true := by
    unfold drawsMarkedNonzeroHaveNonzeroWords
    show ((Fmt.kindOf R.name).any fun k => _) = true
    rw [hk']
    simp only [Option.any_some, List.all_eq_true]
    intro x hx
    have hx' : x ∈ (List.replicate (R.drawn - (if R.notZero then 1 else 0)) Fmt.Draw.elem ++
        List.replicate (if R.notZero then 1 else 0) Fmt.Draw.elemNZ).zip
          ((d.take (R.drawn - (if R.notZero then 1 else 0))).map (·.triple) ++
            (d.drop (R.drawn - (if R.notZero then 1 else 0))).map (·.triple)) := by
      rw [← List.map_append, List.take_append_drop]
      have h0 := hx
      unfold Fmt.dsElems at h0
      rw [if_neg hks] at h0
      exact h0
    rw [List.zip_append (by
      rw [List.length_replicate, List.length_map, List.length_take, hd,
        Nat.min_eq_left (Nat.sub_le _ _)])] at hx'
    rcases List.mem_append.mp hx' with h1 | h1
    · rw [List.eq_of_mem_replicate (List.of_mem_zip h1).1]
      rfl
    · obtain ⟨y, hy, e⟩ := List.mem_map.mp (List.of_mem_zip h1).2
      have := triple_ne_zero y (hz y hy)
      rw [e] at this
      simp [this]
  unfold roundsFit
  rw [hv, hi, hnz, h]
  simp [rvOf, Round.entry, hd]

/-- **The rounds pass.** -/
theorem roundsFit_shapedNZ (work : Nat) :
    ∀ (rs : List Fmt.RoundView) (Rs : List Round), ShapedNZ rs Rs →
      (∀ R ∈ Rs, knownNoSeeds R = true) →
      roundsFit (Rs.map fun R => ({ entry := R.entry work } : Fmt.DeclaredRound)) rs = true
  | _, _, .nil, _ => rfl
  | _, _, .cons (a := r) (b := R) (l₁ := rs) (l₂ := Rs) h1 h2, hp => by
    obtain ⟨s, d, rfl, hs, hd, hD⟩ := h1
    exact roundFit_oneNZ work R s d hs hd (hp R List.mem_cons_self) hD _ _
      (roundsFit_shapedNZ work rs Rs h2 fun R' h' => hp R' (List.mem_cons_of_mem _ h'))

/-- Rounds of that shape bear no sealed digest: striking it turns nothing. -/
theorem noDigest_shapedNZ : ∀ (rs : List Fmt.RoundView) (Rs : List Round), ShapedNZ rs Rs →
    rs.map noDigest = rs
  | _, _, .nil => rfl
  | _, _, .cons (a := r) (b := R) (l₁ := rs) (l₂ := Rs) h1 h2 => by
    obtain ⟨s, d, rfl, _, _, _⟩ := h1
    rw [List.map_cons, noDigest_shapedNZ rs Rs h2]
    rfl

theorem noSeeds_of (n : String) (h : ((Fmt.kindOf n).any fun k => k != .seeds) = true)
    (a b : Nat) (z : Bool) (r : Nat) :
    knownNoSeeds { name := n, sent := a, drawn := b, notZero := z, rows := r } = true := h

/-- Every round of the kind's table has a name that the format knows, of another kind than
"seeds". -/
theorem rounds_noSeeds [Sizes] : ∀ R ∈ (rounds : List Round), knownNoSeeds R = true := by
  intro R hR
  simp only [rounds, Norm.rounds, FinalNorm.rounds, drawPoint.rounds, drawJoin.rounds,
    sendThenBatch.rounds, level.rounds, sumcheck.rounds, List.mem_append, List.mem_cons,
    List.mem_replicate, List.not_mem_nil, or_false] at hR
  simp only [or_assoc] at hR
  rcases hR with rfl | rfl | h | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl | rfl | rfl | ⟨_, rfl⟩ | rfl |
    rfl | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl | ⟨_, rfl⟩ | rfl | rfl
  · exact noSeeds_of "ZERO" (by decide) _ _ _ _
  · exact noSeeds_of "BAT-sigma" (by decide) _ _ _ _
  · have hN0 : Norm.lNI = 0 := rfl
    rw [hN0] at h
    simp at h
  · exact noSeeds_of "PSC epsilon" (by decide) _ _ _ _
  · exact noSeeds_of "PSC round" (by decide) _ _ _ _
  · exact noSeeds_of "PSC Y" (by decide) _ _ _ _
  · exact noSeeds_of "PSC values" (by decide) _ _ _ _
  · exact noSeeds_of "LINE" (by decide) _ _ _ _
  · exact noSeeds_of "BAT-sigma" (by decide) _ _ _ _
  · exact noSeeds_of "PSC epsilon" (by decide) _ _ _ _
  · exact noSeeds_of "PSC round" (by decide) _ _ _ _
  · exact noSeeds_of "PSC Y" (by decide) _ _ _ _
  · exact noSeeds_of "PSC values" (by decide) _ _ _ _
  · exact noSeeds_of "PSC epsilon" (by decide) _ _ _ _
  · exact noSeeds_of "PSC round" (by decide) _ _ _ _
  · exact noSeeds_of "PSC Y" (by decide) _ _ _ _
  · exact noSeeds_of "PSC values" (by decide) _ _ _ _
  · exact noSeeds_of "PSC epsilon" (by decide) _ _ _ _
  · exact noSeeds_of "PSC round" (by decide) _ _ _ _
  · exact noSeeds_of "PSC Y" (by decide) _ _ _ _
  · exact noSeeds_of "PSC values" (by decide) _ _ _ _

/-- **From a yes of the seated block's decision at rounds of that shape to a yes of Block.step**,
which takes no column. -/
theorem step_of_shapedNZ (h : OnBytes.Model.Head.Shape) (iU3 work l firstTree : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (cols : List OpenedColumn)
    (hs : ShapedNZ rs (@rounds (parOf h work).sizes))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    (blockAt h iU3 work l).step firstTree s rs cols = .ok (s', 0) := by
  have hg : groupsOf firstTree (blockAt h iU3 work l).rounds (rs.map (·.drawn)) = [] := by
    rw [blockAt_rounds]
    exact groups_none firstTree _ _ _
  have hw : wantOf firstTree (blockAt h iU3 work l) rs = [] := by
    unfold wantOf
    rw [hg]
    rfl
  have hfit : roundsFit (blockAt h iU3 work l).rounds rs = true := by
    rw [blockAt_rounds]
    exact roundsFit_shapedNZ _ rs _ hs (@rounds_noSeeds (parOf h work).sizes)
  have key := Came.decide_step firstTree (blockAt h iU3 work l) s rs cols s' hfit
    (by rw [hw]; rfl)
    (by rw [noDigest_shapedNZ rs _ hs]; exact hd)
  rw [hw] at key
  exact key

/-! ## 4 What is opened, from the values that the hearing left -/

section Letters

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- **THE HEARING RETURNS, AND WHAT IT LEFT IS THE TRUTH OF THE CELLS, AND THE FOUR SUMCHECKS' OWN
FORMS ARE WORTH 0**: Law/K06Honest.lean's HonestRun less its fields can, shaped, nonzero and
truth. -/
structure TruthHeard (c : NCells) (mask : Nat → E) (F : Fork) (rs : List Fmt.RoundView)
    (H : HeardAll) (G : Fork) : Prop where
  hears : hear F rs = some (H, G, [])
  sPV : H.1.pV.size = lt
  sS : H.1.squares.r.size = lPd + lt
  sP : H.1.products.r.size = lt
  sN : H.2.1.normed.r.size = lt
  normT : letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : FinalNorm.Reads := normReadsAtCells c
    NormTruthW (worldE G mask noEnt) c
  headT : letI : Heard := H.2.2
    letI : Reads := readsAt c.toCells
    HeadTruth c.toCells G mask noEnt

theorem truthHeard_of_honest {c : NCells} {mask : Nat → E} {F G : Fork} {D : List E}
    {rs : List Fmt.RoundView} {H : HeardAll} (R : HonestRun c mask F D rs H G) :
    TruthHeard c mask F rs H G :=
  ⟨R.hears, R.sPV, R.sS, R.sP, R.sN, R.normT, R.headT⟩

/-- **Behind such rounds**: the claim on the weights is true and all 35 forms are worth 0 at the
ledger behind: 31 are derived; the four sumchecks' own forms are fields of the premise
(NormTruthW.sqRow, prRow, nmRow; HeadTruth.row). Whatever was sampled. -/
theorem truthHeard_opens (c : NCells) (mask : Nat → E) {F G : Fork}
    {rs : List Fmt.RoundView} {H : HeardAll} (hW : WellLaid F) (R : TruthHeard c mask F rs H G)
    (hH : (dataOf c).Holds) (hC : HonestHead c.toCells) (hreq : Request.ok = true) (hy : y < V)
    (hw : WeightsOk) (hzt : (FinalNorm.zt).size = lt) (hls : ls ≤ lPd) (hdS : S2 ∣ d)
    (hblock : ∀ x, x < d →
      FinalNorm.ew .remLow x = FinalNorm.ewh .remLow (x / S2) * eq FinalNorm.zl (x % S2)) :
    (let _ : Norm.Heard := H.1
     let _ : FinalNorm.Heard := H.2.1
     let _ : Heard := H.2.2
     let _ : FinalNorm.Reads := normReadsAtCells c
     let _ : Reads := readsAt c.toCells
     WeightTrue c.toCells G mask noEnt ∧
      ∀ name fs, claims.lookup name = some fs → ∀ f, f ∈ fs → atWorld G mask noEnt f = 0) := by
  obtain ⟨Fa, Fb, lr, hNorm, _, _, _, hsL, _⟩ := Came.hear_parts hW R.hears
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h4, _, _⟩ := norm_parts hW hNorm
  have h6 : okE (H.1.P.getD 6 {}).var.const = true := batch_okConst h4 6
  exact opened_all H G c mask hreq hy hw hzt hls hdS hblock R.sPV R.sS R.sP R.sN hH hC R.normT h6
    R.headT

end Letters

/-! ## 5 At a state of the verifier -/

section At

variable (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat)

/-- **What the yes asks of the rounds at the state s**: the head's letters are read at s; the rounds
are canonical and of the table's shape; the hearing takes them all, from the state's own ledger, and
returns H and G. NO WORD ON WHAT THE ROUNDS HOLD: the decision tests no sent value. The table rounds
and the hearing hear are read at g's letters, through the class Given
(Johnson/Desc/Kinds/HeadFrame.lean), as in Law/K06Honest.lean's HonestRunK6. -/
def HeardK6 (s : S) (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork) : Prop :=
  ∃ g : Given, given (parOf h work) (seatAt h iU3) s = .ok g ∧ Canonical rs ∧
    ShapedNZ rs rounds ∧ hear ((seatAt h iU3).ledger s) rs = some (H, G, [])

/-- **THE DECISION ACCEPTS**, and behind it the seat reads back the ledger, what was heard, the same
letters and the same points of the lookup. CONDITIONAL: that the letters are read and that the
hearing returns and uses the rounds up are premises in their own form (inside HeardK6). -/
theorem yes_of_heard (s : S) (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork)
    (hWL : WellLaid ((seatAt h iU3).ledger s)) (hfail : s.failed = none) (hopen : HeadOpen s)
    (R : HeardK6 h iU3 work s rs H G) :
    ∃ s' : S, (blockAt h iU3 work l).decide s rs [] = .ok s' ∧
      (seatAt h iU3).ledger s' = G ∧ (seatAt h iU3).heard s' = some H ∧
      given (parOf h work) (seatAt h iU3) s' = given (parOf h work) (seatAt h iU3) s ∧
      (seatAt h iU3).lookup s' = (seatAt h iU3).lookup s := by
  obtain ⟨g, hg, hcan, hsh, hh⟩ := R
  obtain ⟨z, y, hz, hty, hP, rfl⟩ := Came.given_ok (parOf h work) (seatAt h iU3) s g hg
  letI : Sizes := (parOf h work).sizes
  letI : Policy := (parOf h work).policy
  letI : Request := (seatAt h iU3).request s
  letI : Token := ⟨y⟩
  letI : FinalNorm.In := (fromLookup (parOf h work).floor z.1 z.2).norm
  letI : In := (fromLookup (parOf h work).floor z.1 z.2).head
  have htape := tape_returnsNZ (parOf h work).work rs rounds hsh rounds_plain
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp htape
  have ht' : tapeT { rows := fun e => e.name == "BAT-sigma" } rs
      (((parOf h work).declare rounds).map (·.entry)) = some t := by
    rw [← ht]
    unfold Par.declare headRule
    rw [List.map_map]
    rfl
  obtain ⟨s1, s2, e1, e2⟩ := lays_of h iU3 s hfail hopen G H
  obtain ⟨w, hd⟩ := decide_returns (fun _ => ()) (seatAt h iU3) l 4 (parOf h work) s s1 s2 rs []
    _ t H G hg ht' hh e1 e2
  obtain ⟨bL, bH, bG, bZ⟩ := seatBack_at h iU3 work s _ rs [] G H w s1 s2 hg hWL hcan hh e1 e2
  exact ⟨_, hd, bL, bH, bG, bZ⟩

/-- **Block.step SAYS YES**, to the same state, and takes no column. -/
theorem step_of_heard (firstTree : Nat) (cols : List OpenedColumn) (s : S) (rs : List Fmt.RoundView)
    (H : HeardAll) (G : Fork) (hWL : WellLaid ((seatAt h iU3).ledger s))
    (hfail : s.failed = none) (hopen : HeadOpen s) (R : HeardK6 h iU3 work s rs H G) :
    ∃ s' : S, (blockAt h iU3 work l).step firstTree s rs cols = .ok (s', 0) ∧
      (blockAt h iU3 work l).decide s rs [] = .ok s' ∧
      (seatAt h iU3).ledger s' = G ∧ (seatAt h iU3).heard s' = some H ∧
      given (parOf h work) (seatAt h iU3) s' = given (parOf h work) (seatAt h iU3) s ∧
      (seatAt h iU3).lookup s' = (seatAt h iU3).lookup s := by
  obtain ⟨s', hd, a, b, c, e⟩ := yes_of_heard h iU3 work l s rs H G hWL hfail hopen R
  obtain ⟨g, hg, _, hsh, _⟩ := R
  obtain ⟨z, y, _, _, _, rfl⟩ := Came.given_ok (parOf h work) (seatAt h iU3) s g hg
  exact ⟨s', step_of_shapedNZ h iU3 work l firstTree s s' rs [] cols hsh hd, hd, a, b, c, e⟩

/-- **THE ROUNDS AT THE STATE s ARE AT THE TRUTH OF THE CELLS c**: Law/K06Honest.lean's HonestRunK6
with ShapedNZ in the place of shaped and nonzero, and without truth; read at g's letters
likewise. -/
def TruthK6 (s : S) (c : NCells) (mask : Nat → E) (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork) :
    Prop :=
  ∃ g : Given, given (parOf h work) (seatAt h iU3) s = .ok g ∧ (dataOf c).Holds ∧
    HonestHead c.toCells ∧ Canonical rs ∧ ShapedNZ rs rounds ∧
    TruthHeard c mask ((seatAt h iU3).ledger s) rs H G

theorem TruthK6.heard {s : S} {c : NCells} {mask : Nat → E} {rs : List Fmt.RoundView} {H : HeardAll}
    {G : Fork} (R : TruthK6 h iU3 work s c mask rs H G) : HeardK6 h iU3 work s rs H G := by
  obtain ⟨g, hg, _, _, hcan, hsh, T⟩ := R
  exact ⟨g, hg, hcan, hsh, T.hears⟩

theorem truthK6_of_honest {s : S} {c : NCells} {mask : Nat → E} {rs : List Fmt.RoundView}
    (R : HonestRunK6 h iU3 work s c mask rs) : ∃ H G, TruthK6 h iU3 work s c mask rs H G := by
  obtain ⟨g, D, H, G, hg, hH, hC, R⟩ := R
  exact ⟨H, G, g, hg, hH, hC, R.can, shapedNZ_of_shapedAs D R.nonzero _ _ R.shaped,
    truthHeard_of_honest R⟩

/-- **IT ACCEPTS, AND OPENED.** Block.step accepts and takes no column; at the state behind: the
claim on the weights is true and all 35 forms are worth 0: 31 are derived; the four sumchecks' own
forms are fields of the premise (NormTruthW.sqRow, prRow, nmRow; HeadTruth.row). The premises on the
state and the plan are nine_of_honest's own. -/
theorem yes_opened (firstTree : Nat) (cols : List OpenedColumn) (s : S) (c : NCells) (mask : Nat → E)
    (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork)
    (hWL : WellLaid ((seatAt h iU3).ledger s)) (hplan : (parOf h work).ok = true)
    (hfeat : hasFeatures (parOf h work))
    (hstart : (parOf h work).okStart ((seatAt h iU3).request s) = true)
    (htok : ∀ y, Reply.token (seatAt h iU3).toSeat s = some y → y < (parOf h work).sizes.V)
    (hfail : s.failed = none) (hopen : HeadOpen s) (R : TruthK6 h iU3 work s c mask rs H G) :
    ∃ s' : S, (blockAt h iU3 work l).step firstTree s rs cols = .ok (s', 0) ∧
      (blockAt h iU3 work l).decide s rs [] = .ok s' ∧
      (seatAt h iU3).ledger s' = G ∧ (seatAt h iU3).heard s' = some H ∧
      Opened (parOf h work) (seatAt h iU3) s' c mask := by
  obtain ⟨s', hst, hd, bL, bH, bG, _⟩ :=
    step_of_heard h iU3 work l firstTree cols s rs H G hWL hfail hopen R.heard
  obtain ⟨g, hg, hH, hC, _, _, R⟩ := R
  obtain ⟨z, y, hz, hty, hP, rfl⟩ := Came.given_ok (parOf h work) (seatAt h iU3) s g hg
  letI : Sizes := (parOf h work).sizes
  letI : Policy := (parOf h work).policy
  letI : Request := (seatAt h iU3).request s
  letI : Token := ⟨y⟩
  obtain ⟨hw, hzt, hblock⟩ :=
    letters_of_lookup (parOf h work).sT (parOf h work).floor z.1 z.2 hplan hP
  letI : FinalNorm.In := (fromLookup (parOf h work).floor z.1 z.2).norm
  letI : In := (fromLookup (parOf h work).floor z.1 z.2).head
  have P := planFacts hplan
  have hdS : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  have hls : ls ≤ lPd := Came.ls_le_lPd hfeat hdS
  have hopen' := truthHeard_opens c mask hWL R hH hC hstart (htok y hty) hw hzt hls hdS hblock
  refine ⟨s', hst, hd, bL, bH, _, H, bG.trans hg, bH, ?_⟩
  rw [bL]
  exact hopen'

end At

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.shapedNZ_of_shapedAs
#print axioms VerifiableInference.Desc.Kinds.Head.Law.roundT_returnsNZ
#print axioms VerifiableInference.Desc.Kinds.Head.Law.tape_returnsNZ
#print axioms VerifiableInference.Desc.Kinds.Head.Law.roundFit_oneNZ
#print axioms VerifiableInference.Desc.Kinds.Head.Law.roundsFit_shapedNZ
#print axioms VerifiableInference.Desc.Kinds.Head.Law.noDigest_shapedNZ
#print axioms VerifiableInference.Desc.Kinds.Head.Law.noSeeds_of
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rounds_noSeeds
#print axioms VerifiableInference.Desc.Kinds.Head.Law.step_of_shapedNZ
#print axioms VerifiableInference.Desc.Kinds.Head.Law.truthHeard_of_honest
#print axioms VerifiableInference.Desc.Kinds.Head.Law.truthHeard_opens
#print axioms VerifiableInference.Desc.Kinds.Head.Law.yes_of_heard
#print axioms VerifiableInference.Desc.Kinds.Head.Law.step_of_heard
#print axioms VerifiableInference.Desc.Kinds.Head.Law.TruthK6.heard
#print axioms VerifiableInference.Desc.Kinds.Head.Law.truthK6_of_honest
#print axioms VerifiableInference.Desc.Kinds.Head.Law.yes_opened
