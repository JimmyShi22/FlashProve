-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Starts.lean: at the member of a chain's thread at which the
honest side of an attention segment's own rounds (kind K5) is seated: the values under the slots BY
THE NAMES under which the verifier's hearing hands their numbers on, and THE WORTH OF THE START
FORMS that are one slot: the form that a sumcheck's sum is claimed to equal is worth the honest
summand's total. Statements with their proofs. EVERY STATEMENT IS CONDITIONAL, and all hang on the
ties (K5Script, Honest/K5/Law/Script.lean), WHICH ARE NOT SHOWN.

  laid_at        where the kind's hearing returns at the rounds as played: all is laid as the row's
                 parts (Laid, Johnson/Desc/K5/Honest/Law/Numbers.lean)
  fronts_agree, fronts_key   the challenges in front of two parts are one in the rounds in front of
                 the earlier; the key points are the same words
  pts_front      the verifier's function for the points returns at the challenges in front of every
                 part
  lead_slots     under the slots in front of the sumcheck that is part q lie the part's lead values
  alone_iSE, alone_iVM, alone_iM6   what the row's jobs send by itself at three parts
  start_below, start_on   **the value product's two start forms** are worth the two summands'
                 totals, each at the challenges in front of its own part
  start_division   **the division's start form** is worth the total of denominator times output
  maxima_slots   under the maxima's slots lie the maxima

Not here: a softmax-table unit's start form; the three start forms that are sums of slots.

Limits. Nothing is said on who sees what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Slots
import Johnson.Desc.ProofFile.Honest.K5.Law.Heard
import Johnson.Desc.K5.Honest.Law.Numbers
import Johnson.Desc.K5.Honest.Law.StableKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ worldOwn)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)
open VerifiableInference.Desc.First.Att.P (Par Heard hear)
open H2K5.Honest (PartShape shapes slotsTo LeadPut SumPut K5In Laid laid_of_hear Agree Pub5 Chal
  ptsOf iSE iGam iVM iVD iM6 sSE sVM sVD m6 leadSE)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-! ## 1 What the row's jobs send by itself -/

theorem alone_iSE (P : Pub5) (w : K5In) (c : Chal) :
    (jobs P).alone (iSE P.x) w c = leadSE P w c (sSE P w c).total := by
  simp [jobs, iSE]

theorem alone_iVM (P : Pub5) (w : K5In) (c : Chal) :
    (jobs P).alone (iVM P.x) w c = [(sVM P w c).total, (sVD P w c).total] := by
  simp [jobs, iVM, iSE]

theorem alone_iM6 (P : Pub5) (w : K5In) (c : Chal) : (jobs P).alone (iM6 P.x) w c = m6 P w c := by
  simp [jobs, iM6, iVM, iSE]

/-! ## 2 The fronts -/

/-- **Where the kind's hearing returns at the rounds as played: all is laid as the row's parts.**
CONDITIONAL: the half's seat; the challenges are such as the member's rounds can draw; the prover's
side of the step; the ledger's arrays have their length; the hearing's return. -/
theorem laid_at (Hs : K5Seated T b cells Z p blk) {k : Coins Bk} {m : Mid (Local W₀ Rc Xi Tr) X}
    {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List OpenedColumn} (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
    {F G : Fork} (hz : OnBytes.Model.Road.Sized F) {hd5 : Heard} {rest : List Fmt.RoundView} {lead : Nat}
    (hh : hear p.own (F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, rest, lead)) :
    Laid Z.P.x F.next (roundsOf y.1) hd5 G := by
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  rw [k5_bare T Hs hd hy, Hs.own] at hh
  exact laid_of_hear hh hz

/-- The challenges in front of two rounds are one in front of the earlier. CONDITIONAL: the half's
seat; the thread's clause on the challenges heard; n is at most n'. -/
theorem fronts_agree (Hs : K5Seated T b cells Z p blk) {m : Mid (Local W₀ Rc Xi Tr) X}
    (hF : T.Fit b m) (ds : List Fmt.Drawn) {n n' : Nat} (hn : n ≤ n') :
    Agree n (chalOf Z (m.st.heard ++ ds.take n)) (chalOf Z (m.st.heard ++ ds.take n')) :=
  fun i hi => by
    rw [chalOf_own Hs hF, chalOf_own Hs hF, List.getElem?_take_of_lt hi,
      List.getElem?_take_of_lt (Nat.lt_of_lt_of_le hi hn)]

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  (hT : Thr T b k s m E) (hd : drawsFit blk.rounds ds = true)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att)

include Sc hT hd e in
/-- The key points in front of two rounds are the same words. CONDITIONAL: on the ties; the thread
in front. -/
theorem fronts_key (n n' : Nat) :
    (chalOf Z (m.st.heard ++ ds.take n)).zk = (chalOf Z (m.st.heard ++ ds.take n')).zk := by
  obtain ⟨g, -, hk, -⟩ := key_at Sc hT e hd
  rw [hk n, hk n']

include Hs Sc hT hd e in
/-- **The verifier's function for the points returns at the challenges in front of every round.**
CONDITIONAL: on the ties; the half's seat, whose test on the public data says so at the challenges
in front of the member; the thread in front. -/
theorem pts_front (n : Nat) : ∃ q, ptsOf Z.P (chalOf Z (m.st.heard ++ ds.take n)) = some q := by
  have h := Hs.fits m.st.heard hT.2.1
  unfold Seat5.fits at h
  have h2 := (Bool.and_eq_true_iff.1 h).2
  unfold H2K5.Honest.aloneOk at h2
  cases hp : ptsOf Z.P (chalOf Z m.st.heard) with
  | none =>
    rw [hp] at h2
    cases h2
  | some q0 =>
    have hz := fronts_key Sc hT hd e 0 n
    rw [List.take_zero, List.append_nil] at hz
    obtain ⟨q, hq, -⟩ := H2K5.Honest.ptsOf_key Z.P hz hp
    exact ⟨q, hq⟩

end

/-! ## 3 The values under the slots, by name -/

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
  (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {dc : List Fmt.Drawn}
  {D : Bound GQ} (hD : MaskIs T own rdOf k s att m dc D)
include Hs Sc hT hd hM e hD

/-- **Under the slots in front of the sumcheck that is part q lie the part's lead values.**
CONDITIONAL: as `sum_slots` (Honest/K5/Law/Slots.lean). -/
theorem lead_slots {q ld : Nat} {vs : List Var} {en : Ends}
    (hq : (shapes Z.P.x)[q]? = some (.sum ⟨ld, vs, some en⟩)) {G : Fork} {hhq : MaskedSum.Heard}
    (SP : SumPut ⟨ld, vs, some en⟩ (att.F.next + slotsTo Z.P.x q)
      ((roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q)) hhq G) :
    ∀ i, i < ld → (worldOwn (behindPart s att G) [] D).slot (att.F.next + slotsTo Z.P.x q + i) =
      Reading.gl.val (((jobs Z.P).alone q (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q)))).getD i zeroE) := by
  have hM' := hM
  obtain ⟨⟨l, hst, hy⟩, -⟩ := hM'
  obtain ⟨cq, hl, -⟩ := k5_cut T Hs hd hst hy q _ hq
  exact (sum_slots Hs Sc hT hd hM e hD hq SP hl).2.1

variable {G : Fork} {hd5 : Heard} (L : Laid Z.P.x att.F.next (roundsOf y.1) hd5 G)
include L

/-- **The start form of the value product below the diagonal is worth that summand's total**, at
the challenges in front of its part. CONDITIONAL: as `sum_slots`, and `Laid`. -/
theorem start_below :
    (Aff.slot hd5.values).value Reading.gl (worldOwn (behindPart s att G) [] D) =
      Reading.gl.val (sVM Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iVM Z.P.x))))).total := by
  have SP := L.below _ (H2K5.Honest.shape_iVM Z.P.x)
  have h := lead_slots Hs Sc hT hd hM e hD (H2K5.Honest.shape_iVM Z.P.x) SP 0 (by omega)
  have hv : hd5.values = att.F.next + slotsTo Z.P.x (iVM Z.P.x) + 0 := by
    have h1 := L.values
    have h2 : hd5.below.first = att.F.next + slotsTo Z.P.x (iVM Z.P.x) + 2 := SP.first
    omega
  rw [Aff.value_slot, hv, h, alone_iVM]
  rfl

/-- **The start form of the value product on the diagonal is worth that summand's total**, at the
challenges in front of ITS part, though the value is sent one part earlier. CONDITIONAL: as
`sum_slots`, and `Laid`. -/
theorem start_on :
    (Aff.slot (hd5.values + 1)).value Reading.gl (worldOwn (behindPart s att G) [] D) =
      Reading.gl.val (sVD Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iVD Z.P.x))))).total := by
  have SP := L.below _ (H2K5.Honest.shape_iVM Z.P.x)
  have h := lead_slots Hs Sc hT hd hM e hD (H2K5.Honest.shape_iVM Z.P.x) SP 1 (by omega)
  have hv : hd5.values + 1 = att.F.next + slotsTo Z.P.x (iVM Z.P.x) + 1 := by
    have h1 := L.values
    have h2 : hd5.below.first = att.F.next + slotsTo Z.P.x (iVM Z.P.x) + 2 := SP.first
    omega
  rw [Aff.value_slot, hv, h, alone_iVM]
  show Reading.gl.val (sVD Z.P _ _).total = _
  rw [H2K5.Honest.stable_sVD Z.P _ (q := iVM Z.P.x) (fronts_key Sc hT hd e _ _)
    (fronts_agree Hs hT.2.1 ds (H2K5.Honest.HeardIs.firstOf_mono Z.P.x
      (show iVM Z.P.x ≤ iVD Z.P.x from Nat.le_succ _))) (Nat.lt_succ_self _)]

/-- **The division's start form is worth the total of denominator times output.** CONDITIONAL: as
`sum_slots`, and `Laid`; there is a softmax-table unit. -/
theorem start_division (hsc : Z.P.x.score.isEmpty = false) :
    (Aff.slot (hd5.five + 1)).value Reading.gl (worldOwn (behindPart s att G) [] D) =
      Reading.gl.val (sSE Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iSE Z.P.x))))).total := by
  have hq := H2K5.Honest.shape_iSE Z.P.x
  rw [H2K5.Honest.leadBehind_zero Z.P.x hsc] at hq
  have SP := L.division _ hq
  have h := lead_slots Hs Sc hT hd hM e hD hq SP 1 (by omega)
  have hv : hd5.five + 1 = att.F.next + slotsTo Z.P.x (iSE Z.P.x) + 1 := by
    have h1 := L.five
    have h2 : hd5.division.first =
        att.F.next + slotsTo Z.P.x (iSE Z.P.x) + (0 + 5 + Z.P.x.lt + 2) := SP.first
    omega
  obtain ⟨q0, hp⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x (iSE Z.P.x))
  rw [Aff.value_slot, hv, h, alone_iSE]
  unfold leadSE
  rw [hp]
  rfl

/-- **Under the maxima's slots lie the maxima.** CONDITIONAL: as `sum_slots`, and `Laid`; there is
a pair. -/
theorem maxima_slots {n : Nat} (hn : Z.P.x.pairs = n + 1) :
    ∀ i, i < n + 1 → (worldOwn (behindPart s att G) [] D).slot (hd5.maxima + i) =
      Reading.gl.val ((padTo (n + 1) (m6 Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iM6 Z.P.x)))))).getD i
          zeroE) := by
  have hq := H2K5.Honest.shape_iM6 Z.P.x
  have LP := L.maxima
  rw [hn] at hq LP
  intro i hi
  rw [L.max, one_slots Hs Sc hT hd hM e hD hq LP i hi, alone_iM6]

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.alone_iSE
#print axioms ProofFile.Honest.K5.alone_iVM
#print axioms ProofFile.Honest.K5.alone_iM6
#print axioms ProofFile.Honest.K5.laid_at
#print axioms ProofFile.Honest.K5.fronts_agree
#print axioms ProofFile.Honest.K5.fronts_key
#print axioms ProofFile.Honest.K5.pts_front
#print axioms ProofFile.Honest.K5.lead_slots
#print axioms ProofFile.Honest.K5.start_below
#print axioms ProofFile.Honest.K5.start_on
#print axioms ProofFile.Honest.K5.start_division
#print axioms ProofFile.Honest.K5.maxima_slots
