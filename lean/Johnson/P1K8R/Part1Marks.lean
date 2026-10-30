-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/Part1Marks.lean: THE LAWS ON PART 1's LIST OF MARKS AT THE PROOF FILE's FIRST CHAIN AT
THE FULL SIZE (`part1Marks`: a definition with code in a light file of its own,
Johnson/P1K8R/Part1MarksCode.lean), IN THE FORM THAT THE HONEST SIDE's FRAME's AUTHORS ASK OF EVERY
KIND's AUTHORS: EACH MARK STANDS AT A MARK's SEAT; UNDER THE LIBRARY's ONE HEAD THE LIST HAS 26
RECORDS AND EACH MARK's PLACE IS A MEMBER's; AND AT EACH MEMBER OF THE CHAIN THE BOUND `MarkDebt` IN
THE FORM OF THE FRAME's FIELD hM. Lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness,
soundness or hiding.

  `walkCode_eq`, `mergeBadCode_eq`, **`deadRec_eq`**, **`mergeRec_eq`**, **`part1Marks_eq`**   the
      light file's four second texts are the named definitions, with no hypothesis: `anyBad`,
      `mergeBad`, `deadMark`, `headMergeMark`; so its list is the list of the named marks
  **`part1Marks_seat`**   (1): `markSeat` (Johnson/Desc/ProofFile/Honest/Law/CoverSeats.lean)
  `part1Marks_at`, **`part1Marks_member`**   (1b): each mark's place is the place of a member of
      the chain: under an opening; under the head (P5J.AtMgA) and the maker's base
  `len_filterMap_some`, `part1Marks_len`, **`part1Marks_26`**   (2): the length
  `dead_hM`, `mergeAtB`, `mergeAtB_full`, `merge_place`, `merge_hM`, **`part1_hM`**,
      **`part1_hM_head`**   (3): mark by mark at its member's number; then at every member, in hM's
      form: `dead_markDebt_blocks` (Johnson/P1K8R/DebtsK8.lean), K8.onlyTrits, K8.kind_rng
      (Johnson/Desc/First/K8/Law.lean), P1K8S.sitsAt_open, `draw_place`, `draw_there`
      (DeadMark.lean), `headMergeMarkDebtSeat`
      (Johnson/Desc/ProofFile/Honest/K11/Mark/AtRounds.lean), IM.k11_of
Limits. THE LIST HOLDS THE MARKS THAT PART 1 OWNS, NOT ALL THAT ITS BOUNDS WANT SILENT: the second
fall's bound wants other authors' marks too (the lookups', at the lookup on the digits; the
segments' own kinds'). What a mark's silence gives is not said here. WHERE A BUILT SEGMENT HAD NO
MATRIX, `szAt`'s columns would be 0, the mark's test would never speak, its share would be 0 of 2 ^
tau, and (3) would be met for nothing there: that it has one is not shown here (the member's own
test on the plan asks it, Johnson/Desc/First/K8/Hear.lean; a younger file of ours has it at each
built segment under the tests on the plan: not joined here). (3) stands at strings of hash blocks
alone, in the goals' scope, under an opening of the description. That the sum of `szAt`'s columns is
the number of columns that the first fall's stated share names wants one more fact on the built
segment (as many matrices as the list is long): not joined here. `mergeAtB_full` is decided by
`decide +kernel` on the library's written list of 358 places. The uniform law on the rounds'
messages is named, not derived. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.Part1MarksCode
import Johnson.P1K8R.DebtsK8
import Johnson.Desc.ProofFile.Honest.Law.CoverSeats
import Johnson.Desc.ProofFile.Honest.Law.Due
import Johnson.Desc.ProofFile.Honest.K11.Mark.AtRounds
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open ProofFile.Honest (Odds Mark MarkDebt KindFits markSeat)
open scoped ENNReal

/-- The light file's walk is `anyBad` (Johnson/P1K8R/MarkRounds.lean). -/
theorem walkCode_eq (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) :
    ∀ (l : List Fmt.Drawn) (j : ℕ), walkCode bad mk j l = anyBad bad mk j l
  | [], _ => rfl
  | x :: l, j => by
    show ((mk j && bad x) || walkCode bad mk (j + 1) l) =
      ((mk j && bad x) || anyBad bad mk (j + 1) l)
    rw [walkCode_eq bad mk l (j + 1)]

/-- The light file's test at one round is the merge's `mergeBad`. -/
theorem mergeBadCode_eq : mergeBadCode = ProofFile.Honest.K11.mergeBad := rfl

/-- **The first record written out is `deadMark` (Johnson/P1K8R/DeadMark.lean).** -/
theorem deadRec_eq (link o : Nat) (sz : Size) : deadRec link o sz = deadMark link o sz := rfl

/-- **The second record written out is `headMergeMark`
(Johnson/Desc/ProofFile/Honest/K11/Mark/Statement.lean).** -/
theorem mergeRec_eq (P : HeadMergeP) : mergeRec P = ProofFile.Honest.K11.headMergeMark P := by
  have h : ∀ mk : ℕ → Bool, walkCode mergeBadCode mk 0 = anyBad ProofFile.Honest.K11.mergeBad mk 0 :=
    fun mk => funext fun l => by rw [walkCode_eq, mergeBadCode_eq]
  unfold mergeRec ProofFile.Honest.K11.headMergeMark
  simp only [h]
  rfl

/-- **THE LIGHT FILE's LIST IS THE LIST OF THE NAMED MARKS.** -/
theorem part1Marks_eq (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    part1Marks Zp G₀ =
      ((List.range 25).filterMap fun l => (G₀.built[l]?).map fun X =>
        deadMark l (if l = 24 then 1 else 0) (szAt Zp G₀ X l)) ++
      [ProofFile.Honest.K11.headMergeMark (_root_.K11.parOf Zp G₀)] := by
  unfold part1Marks
  simp only [deadRec_eq, mergeRec_eq]

/-- **(1) EACH STANDS AT A MARK's SEAT.** -/
theorem part1Marks_seat (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    ∀ mk ∈ part1Marks Zp G₀, markSeat mk.place = true := by
  intro mk h
  rw [part1Marks_eq] at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨l, -, hl⟩ := List.mem_filterMap.1 h
    obtain ⟨X, -, rfl⟩ := Option.map_eq_some_iff.1 hl
    rfl
  · obtain rfl := List.mem_singleton.1 h
    rfl

/-- Where the function returns at every member, nothing is left out. -/
theorem len_filterMap_some {α β : Type} (f : α → Option β) :
    ∀ L : List α, (∀ a ∈ L, ∃ b, f a = some b) → (L.filterMap f).length = L.length
  | [], _ => rfl
  | a :: L, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    rw [List.filterMap_cons_some hb, List.length_cons, List.length_cons,
      len_filterMap_some f L fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- The test at the written list: the merge's place stands at number 346 and nowhere else. -/
def mergeAtB : Bool := onlyAt (flatPlacesOf linksFull true) IM.k11Place 346

set_option maxRecDepth 1000000 in
theorem mergeAtB_full : mergeAtB = true := by decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- The length, under an opening of the description. -/
theorem part1Marks_len (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) :
    (part1Marks Z Bs.G₀).length = 26 := by
  rw [part1Marks_eq]
  rw [List.length_append, List.length_singleton, len_filterMap_some _ _ fun l hl => ?_,
    List.length_range]
  have hp : (l, if l = 24 then 5 else 4) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, hl, rfl⟩
  obtain ⟨-, -, Xl, -, -, -, hXl, -⟩ := P1K8S.sitsAt_open hS hR O _ hp
  exact ⟨_, by rw [hXl]; rfl⟩

/-- **(3), the first 25: `MarkDebt` of the mark "a column is all 0" at all data that fit the
declared rounds of the member that hears the draw**, at strings of hash blocks, at the mark's own
stated share's value, whatever is handed of the challenges in front. -/
theorem dead_hM (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    {X : LinkH} (hX : Bs.G₀.built[l]? = some X) {b : Block S Claim}
    (hb : c.blocksInOrder[14 * l + (if l = 24 then 5 else 4) + 2]? = some b) (dsb : List RDT)
    (hd : List.Forall₂ KindFits dsb b.rounds) (PM : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ckP .two) (deadMark l (if l = 24 then 1 else 0) (szAt Z Bs.G₀ X l)) dsb PM
      (deadMark l (if l = 24 then 1 else 0) (szAt Z Bs.G₀ X l)).share.val := by
  have hp : (l, if l = 24 then 5 else 4) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  obtain ⟨-, b8, Xl, -, -, hf8, hXl, hL, -⟩ := P1K8S.sitsAt_open hS hR O _ hp
  obtain rfl : Xl = X := Option.some.inj (hXl.symm.trans hX)
  obtain rfl : b8 = b := Option.some.inj (hf8.symm.trans hb)
  rw [IM.alone_rounds hL] at hd
  have hd' : List.Forall₂ KindFits dsb [K8.round (ProofFile.k8Par Z Bs.G₀ Xl l)] := hd
  cases hd' with
  | cons h1 ht =>
    cases ht
    obtain ⟨e1, e2⟩ := h1
    have ek := Option.some.inj ((K8.kind_rng (ProofFile.k8Par Z Bs.G₀ Xl l)).symm.trans e2)
    have hT := K8.onlyTrits (s := szAt Z Bs.G₀ Xl l) (K8.fits_sizeAt (ProofFile.k8Par Z Bs.G₀ Xl l) _)
    unfold OnlyTrits at hT
    refine dead_markDebt_blocks l _ (szAt Z Bs.G₀ Xl l) _ ?_ ?_ PM
    · rw [e1, ← ek]
      exact hT
    · rw [e1]
      exact Nat.zero_le _

/-- The merge's mark stands at the merge's address. -/
theorem merge_place (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) :
    (ProofFile.Honest.K11.headMergeMark (_root_.K11.parOf Z Bs.G₀)).place = IM.k11Place := by
  obtain ⟨-, -, -, -, -, h⟩ := IM.k11_of hS hR O
  show (⟨1, some (_root_.K11.parOf Z Bs.G₀).link, (_root_.K11.parOf Z Bs.G₀).piece, .K11⟩ :
    Place) = IM.k11Place
  rw [h]
  rfl

/-- **(3), the merge's**: the merge's authors' `headMergeMarkDebtSeat`
(Johnson/Desc/ProofFile/Honest/K11/Mark/AtRounds.lean) at the member number 346. -/
theorem merge_hM (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {b : Block S Claim}
    (hb : c.blocksInOrder[346]? = some b) (dsb : List RDT) (hd : List.Forall₂ KindFits dsb b.rounds)
    (PM : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ckP .two) (ProofFile.Honest.K11.headMergeMark (_root_.K11.parOf Z Bs.G₀)) dsb PM
      (ProofFile.Honest.K11.headMergeMark (_root_.K11.parOf Z Bs.G₀)).share.val := by
  obtain ⟨Lk, b₀, e1, e2, hla, -⟩ := IM.k11_of hS hR O
  have h3 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by decide) 8] at h3
  obtain rfl : b₀ = b := Option.some.inj (h3.symm.trans hb)
  rw [IM.alone_rounds hla] at hd
  exact ProofFile.Honest.K11.headMergeMarkDebtSeat (_root_.K11.parOf Z Bs.G₀) "" IM.k11Place dsb PM hd

/-- **(3) IN THE FORM OF THE FRAME's FIELD hM**: at every member b of the first chain, every mark of
the list that stands at b's place, all data that fit b's declared rounds: C := Run.ckP .two, PM any
sentence, the number the mark's own stated share's value. -/
theorem part1_hM (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {n : ℕ} {b : Block S Claim}
    (hb : c.blocksInOrder[n]? = some b) (PM : List Fmt.Drawn → Prop) :
    ∀ mk ∈ (part1Marks Z Bs.G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb PM mk.share.val := by
  intro mk hmk dsb hd
  obtain ⟨hm, hq⟩ := List.mem_filter.1 hmk
  rw [part1Marks_eq] at hm
  have hpl : mk.place = b.place := eq_of_beq hq
  have hbp : (c.blocksInOrder[n]?).map (·.place) = some mk.place := by
    rw [hb, hpl]
    rfl
  rcases List.mem_append.1 hm with h1 | h1
  · obtain ⟨l, hl, h2⟩ := List.mem_filterMap.1 h1
    obtain ⟨X, hX, rfl⟩ := Option.map_eq_some_iff.1 h2
    have hl' := List.mem_range.1 hl
    obtain rfl := draw_place hS hR O hl' hbp
    exact dead_hM hS hR O hl' hX hb dsb hd PM
  · obtain rfl := List.mem_singleton.1 h1
    rw [merge_place hS hR O] at hbp
    obtain rfl := onlyAt_gives mergeAtB_full ((place_at hS hR O n).trans hbp)
    exact merge_hM hS hR O hb dsb hd PM

/-- (1b) under an opening: each mark's place is the place of a member of the chain. -/
theorem part1Marks_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) :
    ∀ mk ∈ part1Marks Z Bs.G₀, ∃ b ∈ c.blocksInOrder, b.place = mk.place := by
  intro mk hm
  rw [part1Marks_eq] at hm
  rcases List.mem_append.1 hm with h1 | h1
  · obtain ⟨l, hl, h2⟩ := List.mem_filterMap.1 h1
    obtain ⟨X, -, rfl⟩ := Option.map_eq_some_iff.1 h2
    obtain ⟨b, hb, hp⟩ := Option.map_eq_some_iff.1 (draw_there hS hR O (List.mem_range.1 hl))
    exact ⟨b, List.mem_of_getElem? hb, hp⟩
  · obtain rfl := List.mem_singleton.1 h1
    obtain ⟨b, hb, hp⟩ := Option.map_eq_some_iff.1
      ((place_at hS hR O 346).symm.trans (onlyAt_there mergeAtB_full))
    exact ⟨b, List.mem_of_getElem? hb, hp.trans (merge_place hS hR O).symm⟩

end

/-- **(2) NOT HOLLOW**: under the library's one head, at the base that the maker yields, the list
has 26 records: every look-up returns. -/
theorem part1Marks_26 {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (part1Marks Zp Bs.G₀).length = 26 := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  exact part1Marks_len h.scope h.reads O

/-- **(1b) NOT HOLLOW IN THE SECOND WAY**: under the same two premises each mark's place is the
place of a member of the chain: so each mark is asked by somebody. -/
theorem part1Marks_member {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∀ mk ∈ part1Marks Zp Bs.G₀, ∃ b ∈ cF.blocksInOrder, b.place = mk.place := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  exact part1Marks_at h.scope h.reads O

/-- **(3) under the same two premises as (2).** -/
theorem part1_hM_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {n : ℕ}
    {b : Block P5J.TS ProofFile.Cl} (hb : cF.blocksInOrder[n]? = some b) (PM : List Fmt.Drawn → Prop) :
    ∀ mk ∈ (part1Marks Zp Bs.G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb PM mk.share.val := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  exact part1_hM h.scope h.reads O hb PM

end P1K8

#print axioms P1K8.walkCode_eq
#print axioms P1K8.mergeBadCode_eq
#print axioms P1K8.deadRec_eq
#print axioms P1K8.mergeRec_eq
#print axioms P1K8.part1Marks_eq
#print axioms P1K8.part1Marks_seat
#print axioms P1K8.len_filterMap_some
#print axioms P1K8.mergeAtB
#print axioms P1K8.mergeAtB_full
#print axioms P1K8.part1Marks_len
#print axioms P1K8.dead_hM
#print axioms P1K8.merge_place
#print axioms P1K8.merge_hM
#print axioms P1K8.part1_hM
#print axioms P1K8.part1Marks_at
#print axioms P1K8.part1Marks_26
#print axioms P1K8.part1Marks_member
#print axioms P1K8.part1_hM_head
