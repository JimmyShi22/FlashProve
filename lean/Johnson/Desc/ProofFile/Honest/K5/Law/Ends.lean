-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Ends.lean: at the member of a chain's thread at which the
honest side of an attention segment's own rounds (kind K5) is seated: what lies under the END
VALUES' slots of a masked sumcheck of the kind's hearing, and THE WORTH OF THE TWO START FORMS THAT
ARE SUMS OF SLOTS, each as a sum over the pairs. Statements with their proofs. EVERY STATEMENT IS
CONDITIONAL, and all hang on the ties (K5Script, Honest/K5/Law/Script.lean), WHICH ARE NOT SHOWN.

  along_at       where the kind's hearing returns at the rounds as played: each of its sumchecks was
                 heard on its part's stretch (Along, Honest/K5/Law/Along.lean)
  end_slots      **under the end values' slots of the sumcheck that is part q lie the summand's end
                 values**, at the challenges of the part's own rounds
  start_atIndex  the start form of the score at the index is worth the sum over the pairs of the
                 batching element's power times the maximum
  start_key      the start form of the key at the index is worth the sum over the pairs of the
                 batching element's power times the second end value of the score at the index

Not here: that these two sums are the totals of the two summands: these are identities on the
segment's cells.

Limits. Nothing is said on who sees what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Starts
import Johnson.Desc.ProofFile.Honest.K5.Law.Along
import Johnson.Desc.First.Att.K05Prem

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
open VerifiableInference.Desc.First.Att.P (Par Heard hear batched batched_value)
open H2K5.Honest (shapes slotsTo SumPut K5In Laid iM6 iSF m6 sSF)
open ProofFile.Honest.SumLaw

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **Where the kind's hearing returns at the rounds as played: each of its sumchecks was heard on
its part's stretch.** CONDITIONAL: the half's seat; the challenges are such as the member's rounds
can draw; the prover's side of the step; the ledger's arrays have their length; the hearing's
return. -/
theorem along_at (Hs : K5Seated T b cells Z p blk) {k : Coins Bk} {m : Mid (Local W₀ Rc Xi Tr) X}
    {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List OpenedColumn} (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
    {F G : Fork} (hz : OnBytes.PscRun.Sized F) {hd5 : Heard} {rest : List Fmt.RoundView} {lead : Nat}
    (hh : hear p.own (F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, rest, lead)) :
    Along Z.P.x (roundsOf y.1) G hd5 := by
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  rw [k5_bare T Hs hd hy, Hs.own] at hh
  exact along_of_hear hz hh

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
  (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {dc : List Fmt.Drawn}
  {D : Bound GQ} (hD : MaskIs T own rdOf k s att m dc D)
include Hs Sc hT hd hM e hD

/-- **Under the end values' slots of the sumcheck that is part q lie the summand's end values**, at
the challenges of the part's own rounds. SP: what lies in the ledger; H: the sumcheck as the kind's
hearing heard it. CONDITIONAL: as sum_slots (Honest/K5/Law/Slots.lean). -/
theorem end_slots {q ld : Nat} {vs : List Var} {en : Ends}
    (hq : (shapes Z.P.x)[q]? = some (.sum ⟨ld, vs, some en⟩)) {G : Fork} {hhq : MaskedSum.Heard}
    (SP : SumPut ⟨ld, vs, some en⟩ (att.F.next + slotsTo Z.P.x q)
      ((roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q)) hhq G) {C : Aff}
    (H : SumHeardAt Z.P.x (roundsOf y.1) G q C vs en hhq) :
    ∀ j, j < en.n → (worldOwn (behindPart s att G) [] D).slot (hhq.sEnd + j) =
      Reading.gl.val ((((jobs Z.P).sum q (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q)))).endsAt
          ((varsOf ⟨ld, vs, some en⟩
            ((ds.drop (H2K5.Honest.firstOf Z.P.x q)).take (vs.length + 3))).take
              vs.length)).getD j zeroE) := by
  have hM' := hM
  obtain ⟨⟨l, hst, hy⟩, -⟩ := hM'
  obtain ⟨cq, hl, -⟩ := k5_cut T Hs hd hst hy q _ hq
  obtain ⟨ld', F', G', hq', hhear, hz', hlat⟩ := H
  obtain rfl : ld' = ld := by
    have h1 := Option.some.inj (hq'.symm.trans hq)
    cases h1
    rfl
  exact (sum_slots Hs Sc hT hd hM e hD hq SP hl).2.2.2.2 C F' G'
    (k5_drawsOk T Hs hd q _ hq) hz' hhear hlat

variable {G : Fork} {hd5 : Heard} (L : Laid Z.P.x att.F.next (roundsOf y.1) hd5 G)
include L

/-- **The start form of the score at the index**, as a sum over the pairs. CONDITIONAL: as
sum_slots, and Laid; there is a pair. -/
theorem start_atIndex {n : Nat} (hn : Z.P.x.pairs = n + 1) :
    (batched Z.P.x.pairs hd5.om hd5.maxima 1 0).value Reading.gl
        (worldOwn (behindPart s att G) [] D) =
      ∑ i ∈ Finset.range Z.P.x.pairs, Reading.gl.val (hd5.om.getD i zeroE) *
        Reading.gl.val ((padTo (n + 1) (m6 Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
          (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iM6 Z.P.x)))))).getD i
            zeroE) := by
  rw [batched_value]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n + 1 := by
    rw [← hn]
    exact Finset.mem_range.1 hi
  rw [show 1 * i + 0 = i by omega, maxima_slots Hs Sc hT hd hM e hD L hn i hi']

/-- **The start form of the key at the index**, as a sum over the pairs. Al: the kind's sumchecks as
its hearing heard them. CONDITIONAL: as sum_slots, Laid and Along. -/
theorem start_key (Al : Along Z.P.x (roundsOf y.1) G hd5) :
    (batched Z.P.x.pairs hd5.om' hd5.atIndex.sEnd 2 1).value Reading.gl
        (worldOwn (behindPart s att G) [] D) =
      ∑ i ∈ Finset.range Z.P.x.pairs, Reading.gl.val (hd5.om'.getD i zeroE) *
        Reading.gl.val ((((jobs Z.P).sum (iSF Z.P.x) (inOf Z.P.S Z.link (cells m.st.input.trace))
          (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iSF Z.P.x))))).endsAt
            ((varsOf ⟨0, prodVs Z.P.x.attained, some (prodEnds Z.P.x.pairs)⟩
              ((ds.drop (H2K5.Honest.firstOf Z.P.x (iSF Z.P.x))).take
                ((prodVs Z.P.x.attained).length + 3))).take
                  (prodVs Z.P.x.attained).length)).getD (2 * i + 1) zeroE) := by
  have hq : (shapes Z.P.x)[iSF Z.P.x]? =
      some (.sum ⟨0, prodVs Z.P.x.attained, some (prodEnds Z.P.x.pairs)⟩) :=
    H2K5.Honest.shape_iSF Z.P.x
  rw [batched_value]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : 2 * i + 1 < (prodEnds Z.P.x.pairs).n := by
    have := Finset.mem_range.1 hi
    show 2 * i + 1 < 2 * Z.P.x.pairs
    omega
  rw [end_slots Hs Sc hT hd hM e hD hq (L.atIndex _ hq) Al.atIndex (2 * i + 1) hi']

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.along_at
#print axioms ProofFile.Honest.K5.end_slots
#print axioms ProofFile.Honest.K5.start_atIndex
#print axioms ProofFile.Honest.K5.start_key
