-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/Items.lean: the proof of `HeadMergeItems`
(Honest/K11/Plays/ItemsStatement.lean), to the letter. Lemmas; none of the library's goals.

How. The law on the honest rounds stands at the rounds that the row plays (`headMergeInnerPlayed`,
Honest/K11/Plays/Inner.lean): it hands a tape, what the hearing leaves, and two equations. The
decision's yes is taken apart by the library's `decide_inv` (Johnson/Top/H0/MergeLaw/Says.lean): its
tape and its hearing are these, since the maker of the tape does not read the sealed digest
(`mergeTapeE_noDigest`). So what the law speaks of is what lies in the state behind. The mask row is
read alike at the two states (`dataQ_behind`; the library's `isLocal`,
Johnson/Top/H0/MergeLaw/Law.lean, and `segAt_reads`, Johnson/Top/H0/MergeLaw/MaskFront.lean). The
first equation goes into `mergedBehind` (Johnson/Desc/K11/Exchange/Proofs.lean), the second into
`rowHoldsBehind` (Johnson/Desc/K11/Exchange/RowProofs.lean). What the hearing leaves, in its own
form: `mergeHear_inv` (Johnson/Top/H0/MergeLaw/Hear.lean); the form names no entry: `rowForm_ents`
(Johnson/Top/H0/MergeLaw/MergeMakesForms.lean).

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ItemsStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.Inner
import Johnson.Desc.K11.Exchange.Proofs
import Johnson.Desc.K11.Exchange.RowProofs
import Johnson.Top.H0.MergeLaw.MergeMakesForms
import Johnson.Top.H0.MergeLaw.MaskFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E zeroE oneE)
open OnBytes.Model (Reading WsClaim powers)
open VerifiableInference.Desc (noDigest named need)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.Look (tapeS roundS)
open VerifiableInference.Desc.First.Close (leftHead)
open VerifiableInference.Desc.First.MergeLaw (decide_inv mergeHear_inv rowForm_ents isLocal
  segAt_reads)
open VerifiableInference.Desc.Kinds.Head.Law (seg_fork)
open VerifiableInference.Desc.Sound (dataQ)
open Johnson.Desc.First.Walk.Law (leftOf leftOf_of_head)
open Johnson.Desc.First.ForkMerge (mergeTapeE mergeEntries)
open Johnson.Desc.First.ForkMerge.Exchange (mergedBehind rowHoldsBehind)

/-- The strict maker of a tape does not read the sealed digest. -/
theorem tapeS_noDigest : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry),
    tapeS (rs.map noDigest) es = tapeS rs es
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | r :: rs, e :: es => by
    show (match roundS (noDigest r) e, tapeS (rs.map noDigest) es with
      | some x, some t => some (x :: t)
      | _, _ => none) = _
    rw [tapeS_noDigest rs es]
    rfl

/-- Nor does the merge's. -/
theorem mergeTapeE_noDigest (rs : List Fmt.RoundView) (es : List Fmt.Entry) :
    mergeTapeE (rs.map noDigest) es = mergeTapeE rs es := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    cases es with
    | nil => rfl
    | cons e es =>
      unfold mergeTapeE
      simp only [List.map_cons]
      rw [tapeS_noDigest rs es]
      rfl

/-- The decision leaves what the table's sentences read the witness's data off: the open segment's
context, the statement and the book of trees. -/
theorem dataQ_behind (P : Johnson.Desc.First.ForkMerge.HeadMergeP) (own : List (ℕ × ℕ))
    (rd : ℕ × ℕ → VerifiableInference.Desc.Sound.MsgQ) {s s' : S} {rs : List Fmt.RoundView}
    {b9 a9 : VerifiableInference.Desc.K9.Part}
    (h : Johnson.Desc.First.ForkMerge.headMergeDecide P s rs = .ok s')
    (hb : VerifiableInference.Desc.K9.segAt? s = some b9)
    (ha : VerifiableInference.Desc.K9.segAt? s' = some a9) : dataQ own a9 rd = dataQ own b9 rd := by
  obtain ⟨a, a', e1, e2, e3, e4, _⟩ := isLocal P s rs s' h
  obtain ⟨l1, s1, k1⟩ := segAt_reads hb
  obtain ⟨l2, s2, k2⟩ := segAt_reads ha
  have hL : s'.link? = s.link? := by
    unfold S.link?
    rw [e1, e2, e4]
  have eL : a9.L = b9.L := by
    rw [hL, l1] at l2
    exact (Option.some.inj l2).symm
  have est : a9.d.st = b9.d.st := by rw [s1, s2, e3]
  have ebk : a9.d.book = b9.d.book := by rw [k1, k2, e3]
  unfold dataQ
  rw [eL, est, ebk]

/-- **The two sentences behind the step, at the rounds that the row plays.** -/
theorem headMergeItems : HeadMergeItems := by
  intro W₀ Rc Xi Tr X P claims weights c d₀ ds m s s' a claim x0 own rd b9 a9 cells idx n lin nR kC
    wK hd hdec hhere hcl hx hready hfil hunit hT2 hT3 h9 hmask hidx hb9 htrue hin hk hn hzero hmat
    hmk
  have hdq := dataQ_behind P own rd hdec hb9 h9
  obtain ⟨x, _, tail⟩ := headMergeInnerPlayed W₀ Rc Xi Tr X P claims weights c d₀ ds m hd
  have hp : powers (E.ofTriple x) 1 = #[oneE] := rfl
  obtain ⟨tp, wo, F', t1, t2, _, _, _, i1, Gam, g1, g2⟩ :=
    tail P.work #[claim] #[x0.sV] a.F cells (dataQ own a9 rd).mask (fun _ _ _ => 0)
      (by
        show #[claim] = (claims m.st.input.x (m.st.heard ++ [d₀]).dropLast).toArray
        rw [List.dropLast_concat, hT2])
      (by simp) (by simp) rfl
      (by
        intro q hq
        have e : q = claim := by simpa using hq
        rw [e]
        exact hunit)
      hT3
      (by
        show VerifiableInference.Desc.Part.MaskedSum.LedgerReady
          (OnBytes.Model.wsForkStart #[x0.sV] (powers (E.ofTriple x) 1)) _ _
        rw [hp]
        exact hready)
      (by
        intro j hj
        have e : j = x0.sV := by simpa using hj
        rw [e]
        exact hfil)
      hmask
      (by
        intro i hi
        have e : i = 0 := by
          have h1 : i < 1 := hi
          omega
        rw [e, hdq]
        exact htrue)
  -- the decision's own tape and hearing are these
  obtain ⟨a1, a', tp', F'', claim', x', wo', e1, e2, e3, e4, e5, e6, e7, e8, _⟩ := decide_inv hdec
  have ea : a1 = a := by
    rw [hhere] at e1
    exact (VerifiableInference.Desc.First.Here.head.inj e1).symm
  subst ea
  have ec : claim' = claim := by
    rw [hcl] at e3
    exact (Option.some.inj e3).symm
  subst ec
  have ex : x' = x0 := by
    rw [hx] at e4
    exact (Option.some.inj e4).symm
  subst ex
  rw [mergeTapeE_noDigest] at e6
  have et : tp' = tp := Except.ok.inj (e6.symm.trans t1)
  subst et
  have ew := Except.ok.inj (e7.symm.trans t2)
  have ew1 : wo' = wo := congrArg (·.1) ew
  have ew2 : F'' = F' := congrArg (·.2.1) ew
  subst ew1
  subst ew2
  obtain ⟨xb, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrecs, _, _,
    hstart, _⟩ := mergeHear_inv t2
  obtain ⟨G, p', r1, r2⟩ := i1 P.nLin
  have hop : a'.opened = true := by
    have h0 : (if a'.opened then some a'.F else none) = some a9.F := by
      have h1 := seg_fork h9
      unfold S.fork? at h1
      rw [e2] at h1
      exact h1
    by_cases ho : a'.opened = true
    · exact ho
    · rw [if_neg ho] at h0
      cases h0
  refine ⟨mergedBehind own s' a' wo' a9 rd (fun _ _ _ => 0) G p' e2 hop e5 h9
    (rowForm_ents wo'.p wo'.fvp _ _ hstart) (by rw [e8]; exact r1) r2 hin, ?_⟩
  have hleft : leftOf s' = some wo' := leftOf_of_head (by
    unfold leftHead
    rw [e2]
    exact e5)
  have hrecs' : wo'.recs = [(claim', oneE)].map fun y =>
      OnBytes.Model.wsRowPart P.lay y.1
        (OnBytes.mulE y.2 (OnBytes.Model.wsEpsT P.lay y.1 wo'.rm)) := by
    rw [hrecs]
    have hq : powers xb 1 = #[oneE] := rfl
    show ((#[claim'].zip (powers xb 1)).toList.map _) = _
    rw [hq]
    simp
  exact rowHoldsBehind leftOf P.lay n lin s' wo' [(claim', oneE)] Gam cells idx nR kC wK hk hleft
    hrecs' g1 (fun l c' l' h1 h2 => by rw [hidx l c' l' h1 h2]; exact g2) hn hzero hmat hmk

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.tapeS_noDigest
#print axioms ProofFile.Honest.K11.mergeTapeE_noDigest
#print axioms ProofFile.Honest.K11.dataQ_behind
#print axioms ProofFile.Honest.K11.headMergeItems
