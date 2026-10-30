-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/OutBlock.lean: OUT, BY THE CALL, AT THE BLOCK's ONE HEARING, UNDER ONE RULE ON THE BLOCK's OWN ROUNDS:
STATED AND PROVED. Law/OutWhole.lean's law has two rules, one inside the other: the second may hang on the ledger
behind "normed". The rule of composition wants ONE rule for a block: from a front of the block's rounds to a list
of elements. Here it is made, and the law is said of Head.lean's hear, the hearing that the block's decision runs.
  (That a hearing is fixed by the rounds that it consumes: Law/Consumes.lean.)
  tailRule   THE RULE: at a front h of the block's rounds: run the normalization's hearing on h; if it returns,
      leaving l1: where l1 has at most zt.size + 3 rounds the front ends in "normed": that sumcheck's rule at l1;
      else run "normed" on l1, leaving l2: the head's sumcheck's rule, AT THE LEDGER BEHIND "normed", at l2. Empty
      where the normalization's hearing does not return (the front ends inside it: its own rules are other
      files', to be laid beside this one).
  OutBlockStatement   fixed first: the cells, the mask entries, the lookup's points, the ledger F in front of the
      block. There is ONE rule with the ceiling. Then: hear F rs = some (H, F1, []), rs canonical, no bad draw;
      at any ledger G later than F1, with "logits" and normedForms 0, the reads true below their lengths and the
      claim on the weights true, AT WHAT WAS HEARD (H): each call's key vector is its table's extension at the
      call's key point; the two guests are the sums of their corner values.
THE RULE HAS A NAME (blockRule: tailRule at normedRule and Law/Lemma2b.lean's badP): NO RULE HERE IS TAKEN OUT OF A "there is": so that
what is known of these rules' sets (empty at the truth) still reaches the block's rule. The law is said of it
(outBlock_at); the statement with "there is a rule" follows.
THE RULE READS THE CELLS AND THE MASK ENTRIES: letters here, in front of "there is a rule". In the rule of
composition a rule is a function of the statement: there these letters are to be what the statement's pinned
oracles decode to: not shown here.
IMPORTED, NOT TYPED HERE: as Law/OutWhole.lean.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.OutWhole
import Johnson.Desc.Kinds.Law.Consumes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork World)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd S2 T)
open Came (val)

/-- What the law says of a rule. -/
def OutBlockAt [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (floor : Nat) (zx : Point)
    (zk : Nat → Point) (c : NCells) (mask : Nat → E) (F : Fork) (bad : List Fmt.RoundView → List E) : Prop :=
  ∀ (rs : List Fmt.RoundView) (H : HeardAll) (F1 G : Fork) (ent : Nat → Nat → Nat → E)
    [FinalNorm.Reads] [Reads],
    Canonical rs → hear F rs = some (H, F1, []) → Later F1 G → NoBad bad rs →
    let _ : Norm.Heard := H.1
    let _ : FinalNorm.Heard := H.2.1
    let _ : Heard := H.2.2
    TrueReads c.toCells G mask ent → WeightTrue c.toCells G mask ent →
    NormKeyReads (worldE G mask ent) c → NormedReads (worldE G mask ent) c →
    (∀ fs, claims.lookup "logits" = some fs → ∀ f, f ∈ fs → atWorld G mask ent f = 0) →
    (∀ f, f ∈ FinalNorm.normedForms → atWorld G mask ent f = 0) →
    (∀ call, call < 6 →
      rd (atWorld G mask ent
          (keyVector key ((fromLookup floor zx zk).calls.getD call (0, [])).1 (callKeys call)))
        = (Finset.range (2 ^ (zk call).size)).sum fun i =>
            rd (eq (zk call) i) * rd (keyTable c call (i / T) (i % T))) ∧
    atWorld G mask ent clip = (∑ t < T, eq FinalNorm.zt t * clipAt c.toCells (corner 0 t)) ∧
    atWorld G mask ent table = (∑ t < T, eq FinalNorm.zt t * tableAt c.toCells (corner 0 t))

/-- **OUT, BY THE CALL, AT THE BLOCK's ONE HEARING.** -/
def OutBlockStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] [nI : FinalNorm.In] [hI : In] (sT floor : Nat) (zx : Point)
    (zk : Nat → Point) (c : NCells) (mask : Nat → E) (F : Fork),
    planOk sT = true → Request.ok = true → y < V → WellLaid F → PointsOk floor zx zk →
    nI = (fromLookup floor zx zk).norm → hI = (fromLookup floor zx zk).head →
    ∃ bad : List Fmt.RoundView → List E,
      (∀ h, (bad h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1) ∧
      OutBlockAt floor zx zk c mask F bad

namespace Came

/-! ## The rule -/

/-- The block's rule behind the normalization's own rounds, of the two sumchecks' rules as functions of the
ledger in front of each. -/
def tailRule [Sizes] [FinalNorm.In] (bN bL : Fork → List Fmt.RoundView → List E) (F : Fork)
    (h : List Fmt.RoundView) : List E :=
  match Norm.hear F h with
  | none => []
  | some (_, Fa, l1) =>
    if l1.length ≤ (FinalNorm.zt).size + 3 then bN Fa l1
    else match sumcheck FinalNorm.zt 2 Fa l1 with
      | none => []
      | some (_, Fb, l2) => bL Fb l2

/-- **THE BLOCK's RULE BEHIND THE NORMALIZATION's OWN ROUNDS, BY NAME**: "normed"'s rule (Law/Normed.lean: normedRule) and the
head's sumcheck's (badP), each at the ledger in front of its sumcheck. -/
def blockRule [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (c : NCells) (mask : Nat → E)
    (F : Fork) : List Fmt.RoundView → List E :=
  tailRule (normedRule c mask) (badP c.toCells mask) F

theorem tailRule_length [Sizes] [FinalNorm.In] (bN bL : Fork → List Fmt.RoundView → List E)
    (hbN : ∀ Fa h, (bN Fa h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1)
    (hbL : ∀ Fb h, (bL Fb h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1)
    (F : Fork) (h : List Fmt.RoundView) :
    (tailRule bN bL F h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1 := by
  unfold tailRule
  cases hN : Norm.hear F h with
  | none => simp
  | some v =>
    obtain ⟨x, Fa, l1⟩ := v
    obtain ⟨p1, rfl, _⟩ := consumes_norm _ _ _ _ _ hN
    dsimp only
    split
    · exact ceil_tail (bN Fa) (hbN Fa) p1 l1
    · cases hS : sumcheck FinalNorm.zt 2 Fa l1 with
      | none => simp
      | some u =>
        obtain ⟨SN, Fb, l2⟩ := u
        obtain ⟨p2, rfl, _⟩ := consumes_sumcheck _ _ _ _ _ _ _ hS
        dsimp only
        rw [← List.append_assoc]
        exact ceil_tail (bL Fb) (hbL Fb) (p1 ++ p2) l2

theorem blockRule_length [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (c : NCells)
    (mask : Nat → E) (F : Fork) (h : List Fmt.RoundView) : (blockRule c mask F h).length
      ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1 :=
  tailRule_length _ _ (fun Fa h => normedRule_length c mask Fa h)
    (fun Fb h => bad_length _ _ _ _ h) F h

/-- **OUT, BY THE CALL, AT THE BLOCK's ONE HEARING, AT THE RULE BY NAME.** -/
theorem outBlock_at [Sizes] [Policy] [Request] [Token] [nI : FinalNorm.In] [hI : In] (sT floor : Nat)
    (zx : Point) (zk : Nat → Point) (c : NCells) (mask : Nat → E) (F : Fork)
    (hplan : planOk sT = true) (hreq : Request.ok = true) (hy : y < V) (hWL : WellLaid F)
    (hP : PointsOk floor zx zk) (hn : nI = (fromLookup floor zx zk).norm)
    (hh : hI = (fromLookup floor zx zk).head) :
    OutBlockAt floor zx zk c mask F (blockRule c mask F) := by
  have P := planFacts hplan
  have hV : 0 < V := by have := P.hV2; omega
  have hd : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  have L := fromLookup_law floor zx zk hV (lens_small hplan) hP
  have hzt : (FinalNorm.zt).size = lt := by
    subst hn
    exact L.zt
  have hblock : ∀ x, x < d →
      FinalNorm.ew .remLow x = FinalNorm.ewh .remLow (x / S2) * eq FinalNorm.zl (x % S2) := by
    subst hn
    intro x hx
    exact L.block (.inl .remLow) hd x hx
  intro rs H F1 G ent _ _ hcan hhear hLater hnb _ _ _ hreads hwt hNR hNdR hlog hnf
  obtain ⟨Fa, Fb, l1, hNorm, hWa, hWb, hsN, hsL, hleft⟩ := hear_parts hWL hhear
  obtain ⟨pre0, hrs, eN⟩ := consumes_norm _ _ _ _ _ hNorm
  obtain ⟨pN, hpN, eS⟩ := consumes_sumcheck _ _ _ _ _ _ _ hsN
  rw [List.append_nil] at hpN
  -- the rounds, cut
  have hlenN : (l1.take ((FinalNorm.zt).size + 3)).length = (FinalNorm.zt).size + 3 := by
    have h0 : (l1.take ((FinalNorm.zt).size + 3)).length = (FinalNorm.zt).size + 3 := by
      obtain ⟨_, _, h3⟩ := sumcheck_cut hsN
      rw [List.length_take] at h3 ⊢
      omega
    exact h0
  have hL' : (l1.drop ((FinalNorm.zt).size + 3)).take
      ((FinalNorm.zt ++ halves Norm.lPd).size + 3) = l1.drop ((FinalNorm.zt).size + 3) := by
    apply List.take_of_length_le
    have h0 := congrArg List.length hleft
    rw [List.length_nil, List.length_drop] at h0
    omega
  rw [hL'] at hsL
  have hcut : rs = pre0 ++ l1.take ((FinalNorm.zt).size + 3) ++ l1.drop ((FinalNorm.zt).size + 3) := by
    rw [List.append_assoc, List.take_append_drop]
    exact hrs
  have hcanN : Canonical (l1.take ((FinalNorm.zt).size + 3)) := fun r hr =>
    hcan r (by rw [hcut]; exact List.mem_append_left _ (List.mem_append_right _ hr))
  have hcanL : Canonical (l1.drop ((FinalNorm.zt).size + 3)) := fun r hr =>
    hcan r (by rw [hcut]; exact List.mem_append_right _ hr)
  -- no bad draw under either rule
  have hnbN : NoBad (normedRule c mask Fa) (l1.take ((FinalNorm.zt).size + 3)) := by
    have hnb0 : NoBad (tailRule (normedRule c mask) (badP c.toCells mask) F) rs := hnb
    rw [hcut] at hnb0
    refine noBad_sub (fun i r hi => ?_) hnb0
    have hil : i < (l1.take ((FinalNorm.zt).size + 3)).length :=
      (List.getElem?_eq_some_iff.mp hi).1
    unfold tailRule
    rw [eN]
    dsimp only
    rw [if_pos]
    rw [List.length_append, List.length_take, List.length_singleton]
    omega
  have hnbL : NoBad (badP c.toCells mask Fb) (l1.drop ((FinalNorm.zt).size + 3)) := by
    have hnb' : NoBad (tailRule (normedRule c mask) (badP c.toCells mask) F)
        ((pre0 ++ l1.take ((FinalNorm.zt).size + 3)) ++ l1.drop ((FinalNorm.zt).size + 3) ++ []) := by
      rw [List.append_nil, ← hcut]
      exact hnb
    refine noBad_sub (fun i r hi => ?_) hnb'
    unfold tailRule
    rw [List.append_assoc, eN]
    dsimp only
    rw [if_neg (by rw [List.length_append, hlenN, List.length_append, List.length_singleton]; omega),
      hpN, eS]
  -- the two laws
  have hLb : Later Fb G := (keeps_sumcheck _ _ _ _ _ _ _ hsL).trans hLater
  have hclaimed := normed_at c mask Fa hWa hzt hd hblock Fb _
    H.2.1.normed (worldE G mask ent)
    (fun j h1 h2 => world_laterG FinalNorm.zt 2 mask hWa hsN hLb j h1 h2) hcanN hsN hNdR
    (fun f hf => by
      show vW (worldE G mask ent) f = 0
      rw [← rd_atWorld, hnf f hf, rd_zero]) hnbN
  exact outJoin_at sT floor zx zk c mask Fb hplan hreq hy hWb hP hn hh F1 _ H.2.2.logits G ent
    hcanL hsL hLater hreads hwt hlog hnbL ⟨hNR.act, hNR.row, hNR.wide, hclaimed⟩

theorem outBlock : OutBlockStatement := fun sT floor zx zk c mask F hplan hreq hy hWL hP hn hh =>
  ⟨blockRule c mask F, blockRule_length c mask F,
    outBlock_at sT floor zx zk c mask F hplan hreq hy hWL hP hn hh⟩

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.outBlock_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.outBlock
