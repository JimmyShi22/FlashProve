-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06ClosedTruth.lean: THE OUTPUT HEAD'S OWN ROUNDS AT THE TRUTH: WHAT THE
SUB-PROTOCOL CLOSES, AND THE FORM OF "join", WITHOUT A WORD ON CHANCE.
WHAT IT IS NOT. No prover: that any rounds meet the premises is not shown here, and no example is
given. "No bad sample" (the library's comments say "no bad draw") is neither asked nor concluded.
Nothing on soundness, on completeness or on what a proof hides. CONDITIONAL throughout: on
Law/K06EveryList.lean's TruthK6, on ONE MORE VALUE (NormedClaimed, below), and, for "join", on the
keys' sentence at the state in front (KeysWorth), which is the lookup's to pay, and on CEndFilled.
TruthK6 HOLDS, THROUGH THE LIBRARY'S NormTruthW AND HeadTruth, FOUR OF Opened'S 35 FORMS IN THEIR
OWN FORM (the four sumchecks' own: sqRow, prRow, nmRow; row): THESE GO IN AS THEY COME OUT; 31 are
derived.
WHY. Law/JoinFromFront.lean's join_of_keys takes Closed (Law/RowAtDecide.lean) and reads its second
clause alone: each of the six calls' key vectors is worth the extension of the call's table at its
key point. The library's road to that clause (rowHalf, outTrue, outBlock_at, outJoin_at) spends "no
bad sample" at two places, each to learn that a claimed sum is true: of "normed" (normed_at) and of
the head's own sumcheck (k06Out_at). Where both are known outright the clause needs no chance:
outCall (Law/OutCall.lean; its statement: Johnson/Desc/Kinds/HeadOutLaw.lean) is deterministic.
  NormedClaimed       THE ONE MORE VALUE: what lies hidden under the claimed sum of "normed", at the
                      ledger G, reads as trueNormed c. It is no field of NormTruthW or HeadTruth; in
                      Law/K06Honest.lean's HonestRun it stands inside the field truth in another
                      form (NormedTrue, Law/RowTrue.lean: at the ledger in front of that sumcheck);
                      no lemma here carries it over: so TruthK6N is not shown here to hold at the
                      library's honest run.
  Came.closedAt_truth at the letters that fromLookup makes: HonestHead, the head's claimed sum true
                      (HeadTruth's field claimed) and NormedClaimed give Closed's four clauses. Of
                      the four the first is HonestHead's two fields mean and count, in as out; the
                      third and the fourth follow term by term from its field guests; the second
                      alone (the six key vectors' worth) is made, by the library's outCall, of the
                      two claimed sums.
  TruthK6N            TruthK6 with NormedClaimed.
  yes_out             Block.step accepts and takes no column; at the state behind: Opened, Closed,
                      and for every gk with CEndFilled and KeysWorth in front: JoinOpened.
CALLED AS THEY STAND IN THE LIBRARY: k06Glue (Law/Clamp.lean), corners (Law/K06Proof.lean), outCall,
fromLookup_law, lens_small, S2_dvd_len, planFacts, keys_back, join_of_keys (Law/JoinFromFront.lean),
keeps_hear, Came.given_ok, and small lemmas on values (rd_atWorld, rd_sumTo, rd_mul, rd_zero,
eq_of_rd, okE_sumTo, okE_zero, val_coe); of Law/K06EveryList.lean: step_of_heard, yes_opened.
NO STATEMENT OF THE LIBRARY IS TYPED ANEW; thirteen lines of closedAt_truth's proof (the letters are
the weights that they are taken for; zt has lt coordinates) are those of the library's outJoin_at
(Law/OutJoin.lean), as in letters_of_lookup (Law/K06ToyParts.lean).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06EveryList
import Johnson.Desc.Kinds.Law.JoinFromFront

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE zeroE oneE)
open OnBytes.Model (Aff Fork World)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd T S2)
open VerifiableInference.Desc.First (S)

/-- **THE ONE MORE VALUE**: what lies hidden under the claimed sum of "normed", at the ledger G and
the mask row, reads as the true sum. -/
def NormedClaimed [Sizes] [Policy] [Request] [Token] [FinalNorm.In] (c : NCells) (mask : Nat → E)
    (H : HeardAll) (G : Fork) : Prop :=
  letI : FinalNorm.Heard := H.2.1
  Came.val (worldE G mask noEnt) FinalNorm.normed.claimed.var = rd (trueNormed c)

namespace Came

/-- **WHAT THE SUB-PROTOCOL CLOSES, AT THE TRUTH**, at the letters that fromLookup makes. No chance
in it. -/
theorem closedAt_truth [Sizes] [Policy] [Request] [Token] [nI : FinalNorm.In] [hI : In]
    (sT floor : Nat) (zx : Point) (zk : Nat → Point) (c : NCells) (mask : Nat → E) (H : HeardAll)
    (G : Fork) (hplan : planOk sT = true) (hreq : Request.ok = true) (hy : y < V)
    (hP : PointsOk floor zx zk) (hn : nI = (fromLookup floor zx zk).norm)
    (hh : hI = (fromLookup floor zx zk).head) (hC : HonestHead c.toCells)
    (hnm : NormedClaimed c mask H G) :
    (let _ : Norm.Heard := H.1
     let _ : FinalNorm.Heard := H.2.1
     let _ : Heard := H.2.2
     let _ : FinalNorm.Reads := normReadsAtCells c
     let _ : Reads := readsAt c.toCells
     (2 ^ lPd : E) * atWorld G mask noEnt logits.claimed.var = trueSum c.toCells →
     (meanAt c.toCells = 0 ∧ countAt c.toCells = 0) ∧
     (∀ call, call < 6 →
       rd (atWorld G mask noEnt
           (keyVector key ((fromLookup floor zx zk).calls.getD call (0, [])).1 (callKeys call)))
         = (Finset.range (2 ^ (zk call).size)).sum fun i =>
             rd (eq (zk call) i) * rd (keyTable c call (i / T) (i % T))) ∧
     (∑ t < T, eq FinalNorm.zt t * clipAt c.toCells (corner 0 t)) = 0 ∧
     (∑ t < T, eq FinalNorm.zt t * tableAt c.toCells (corner 0 t)) = 0) := by
  intro _ _ _ _ _ hcl
  have P := planFacts hplan
  have hV : 0 < V := by have := P.hV2; omega
  have L := fromLookup_law floor zx zk hV (lens_small hplan) hP
  have hS2 : ∀ k : Key, S2 ∣ len k := S2_dvd_len P
  have hw : WeightsOk := by
    subst hn
    subst hh
    letI : FinalNorm.In := (fromLookup floor zx zk).norm
    letI : In := (fromLookup floor zx zk).head
    exact ⟨fun k x hx => L.block (.inr k) (hS2 k) x hx, fun k => L.wsum (.inr k), L.wx, L.below⟩
  have hzt : (FinalNorm.zt).size = lt := by
    subst hn
    exact L.zt
  have hreads : TrueReads c.toCells G mask noEnt := fun _ _ _ => rfl
  obtain ⟨hk, _, _, _, _⟩ := k06Glue c.toCells G mask noEnt hreq hy hw hzt hreads hcl
  obtain ⟨_, _, c3⟩ := corners c.toCells ptOf hreq hy hzt
  refine ⟨⟨hC.mean, hC.count⟩, fun call hcall => ?_, ?_, ?_⟩
  · rw [rd_atWorld]
    refine outCall sT floor zx zk c (worldE G mask noEnt) hplan hP hn hh (fun k => ?_)
      ⟨fun _ _ => val_coe _ _, fun _ _ => val_coe _ _, fun _ _ => val_coe _ _, hnm⟩ call hcall
    show vW (worldE G mask noEnt) (key k) = _
    rw [← rd_atWorld, hk k, c3 k]
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun t _ => ?_
    rw [hw.ew k x (Finset.mem_range.mp hx)]
    rfl
  · apply eq_of_rd (okE_sumTo _ _) okE_zero
    rw [rd_sumTo, rd_zero]
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [rd_mul, (hC.guests t (Finset.mem_range.mp ht)).1, rd_zero, mul_zero]
  · apply eq_of_rd (okE_sumTo _ _) okE_zero
    rw [rd_sumTo, rd_zero]
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [rd_mul, (hC.guests t (Finset.mem_range.mp ht)).2, rd_zero, mul_zero]

end Came

section At

variable (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat)

/-- **THE ROUNDS AT THE STATE s ARE AT THE TRUTH OF THE CELLS c, THE CLAIMED SUM OF "normed" WITH
THEM**: Law/K06EveryList.lean's TruthK6 with NormedClaimed; read at g's letters, through the class
Given. MORE THAN VALUES STANDS IN IT: through TruthHeard it holds that the four sumchecks' own forms
are worth 0 (NormTruthW.sqRow, prRow, nmRow; HeadTruth.row). -/
def TruthK6N (s : S) (c : NCells) (mask : Nat → E) (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork) :
    Prop :=
  ∃ g : Given, given (parOf h work) (seatAt h iU3) s = .ok g ∧ (dataOf c).Holds ∧
    HonestHead c.toCells ∧ Canonical rs ∧ ShapedNZ rs rounds ∧
    TruthHeard c mask ((seatAt h iU3).ledger s) rs H G ∧ NormedClaimed c mask H G

theorem TruthK6N.truth {s : S} {c : NCells} {mask : Nat → E} {rs : List Fmt.RoundView} {H : HeardAll}
    {G : Fork} (R : TruthK6N h iU3 work s c mask rs H G) : TruthK6 h iU3 work s c mask rs H G := by
  obtain ⟨g, hg, hH, hC, hcan, hsh, T, _⟩ := R
  exact ⟨g, hg, hH, hC, hcan, hsh, T⟩

/-- **ACCEPTED, OPENED, CLOSED, AND "join".** Block.step accepts and takes no column; at the state
behind: all 35 forms are worth 0 and the claim on the weights is true (Opened): 31 of the 35 are
derived; the four sumchecks' own forms are fields of the premise; the two plain sums, the six key
vectors' worth and the two guests' sums (Closed); and for every gk (meant: what the lookup has
heard): if each number that its last claim names is filled in the ledger in front, and the keys'
sentence holds in front, the form of "join" is worth 0 behind (JoinOpened). The premises on the
state and the plan are nine_of_honest's own (Law/K06Honest.lean). That the letters and the lookup's
points are read behind as in front is not said again here: step_of_heard says it, of the same state,
since the decision is a function. -/
theorem yes_out (firstTree : Nat) (cols : List OpenedColumn) (s : S) (c : NCells) (mask : Nat → E)
    (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork)
    (hWL : WellLaid ((seatAt h iU3).ledger s)) (hplan : (parOf h work).ok = true)
    (hfeat : hasFeatures (parOf h work))
    (hstart : (parOf h work).okStart ((seatAt h iU3).request s) = true)
    (htok : ∀ y, Reply.token (seatAt h iU3).toSeat s = some y → y < (parOf h work).sizes.V)
    (hfail : s.failed = none) (hopen : HeadOpen s) (R : TruthK6N h iU3 work s c mask rs H G) :
    ∃ s' : S, (blockAt h iU3 work l).step firstTree s rs cols = .ok (s', 0) ∧
      (blockAt h iU3 work l).decide s rs [] = .ok s' ∧
      (seatAt h iU3).ledger s' = G ∧ (seatAt h iU3).heard s' = some H ∧
      Opened (parOf h work) (seatAt h iU3) s' c mask ∧
      Closed (parOf h work) (seatAt h iU3) s' c mask ∧
      ∀ gk : OnBytes.Model.Forest.Heard, CEndFilled gk ((seatAt h iU3).ledger s) →
        KeysWorth (parOf h work) (seatAt h iU3) s c mask gk →
        JoinOpened (parOf h work) (seatAt h iU3) s' c mask gk := by
  obtain ⟨s', hst, hd, bL, bH, hO⟩ := yes_opened h iU3 work l firstTree cols s c mask rs H G hWL
    hplan hfeat hstart htok hfail hopen R.truth
  obtain ⟨s2, _, hd2, _, _, bG, bZ⟩ :=
    step_of_heard h iU3 work l firstTree cols s rs H G hWL hfail hopen R.truth.heard
  obtain rfl : s' = s2 := Except.ok.inj (hd.symm.trans hd2)
  have hCl : Closed (parOf h work) (seatAt h iU3) s' c mask := by
    obtain ⟨g, hg, _, hC, _, _, T, hnm⟩ := R
    obtain ⟨z, y, hz, hty, hP, rfl⟩ := Came.given_ok (parOf h work) (seatAt h iU3) s g hg
    letI : Sizes := (parOf h work).sizes
    letI : Policy := (parOf h work).policy
    letI : Request := (seatAt h iU3).request s
    letI : Token := ⟨y⟩
    letI : FinalNorm.In := (fromLookup (parOf h work).floor z.1 z.2).norm
    letI : In := (fromLookup (parOf h work).floor z.1 z.2).head
    refine ⟨_, H, z, bG.trans hg, bH, bZ.trans hz, ?_⟩
    rw [bL]
    have hcl : (letI : Heard := H.2.2
        (2 ^ lPd : E) * atWorld G mask noEnt logits.claimed.var = trueSum c.toCells) := by
      letI : Heard := H.2.2
      letI : Reads := readsAt c.toCells
      have hT : HeadTruth c.toCells G mask noEnt := T.headT
      exact hT.claimed
    exact Came.closedAt_truth (parOf h work).sT (parOf h work).floor z.1 z.2 c mask H G hplan
      hstart (htok y hty) hP rfl rfl hC hnm hcl
  refine ⟨s', hst, hd, bL, bH, hO, hCl, fun gk hf hK => ?_⟩
  have hL : Later ((seatAt h iU3).ledger s) ((seatAt h iU3).ledger s') := by
    obtain ⟨g, _, _, _, _, _, T, _⟩ := R
    rw [bL]
    exact keeps_hear _ _ _ _ _ T.hears
  exact join_of_keys _ _ s' c mask gk hCl (keys_back _ _ s s' c mask gk bG bZ hL hf hK)

end At

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.closedAt_truth
#print axioms VerifiableInference.Desc.Kinds.Head.Law.TruthK6N.truth
#print axioms VerifiableInference.Desc.Kinds.Head.Law.yes_out
