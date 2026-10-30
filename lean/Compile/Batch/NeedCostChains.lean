-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/NeedCostChains.lean: what it costs the lazy prover to make the proof strings, the
second part of the compiled prover `proveBU`. The cost is that over one hash function, if only the
marked blocks are queried; it is stated over the typed oracles, at the weight "marked blocks" (the
weight of a typed query is the number of its marked blocks: the head of
Compile/Batch/NeedCostP.lean). For any Batch IOP and any wire record, with or without proof-of-work
bits (words of this library: lean/GLOSSARY.md).
    The first part, all chains of a batch, at the weight "marked blocks", is not in this library.
    For the weights that meet `TryW` of Compile/Batch/OneCallCostW.lean, and under `RuleSh`
    (Compile/Batch/OneCallCostR.lean), it is `swv_chainsU` of Compile/Batch/OneCallCostPL.lean; such
    a weight may depend on the answer and is nowhere above the weight of the rule "block 0 first"
    (`ruleT`, Compile/Batch/SpecOneCall.lean).
    `swa_finishSlotG`          a proof string with given openings costs nothing
    `ca_opensExtL`, `ca_finishSlotL`, `ca_finishAllL`
                               the proof strings with openings made when they are needed: if an
                               opening costs at most cO, a slot's verifier reads at most nE
                               positions of the external strings and the wire record's list of these
                               positions has no repetition, then at most (slots with a request) · nE
                               · cO
Notation:
  `SWo c n P`, `CAo c n P`: `SWA` (Compile/CostAt.lean; c a program with tokens) and `OComp.CA`
    (Compile/CostPost.lean; c an oracle algorithm) at the weight `Rom.Need.num (needOf nb m)`: on
    every path the weights of the queries add up to at most n, and the result has the property P
  `T1`: the property fun _ => True
  `opL`: ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam))); opL q: the salt and the path of leaf q, or
    none (`opensExtL`, Compile/Batch/SeedLazyDefs.lean)
  `fl`: ℕ → Bool; fl says for which slots a proof string is made at all (`finishAll`,
    Compile/Batch/Prover.lean; `slotL`, Compile/Batch/SeedLazyDefs.lean)
  `c0`: `H.Coin0`, the shared coins (`chainsU`, the same file); `a0`: `Acc0`, what the shared part
    has accumulated (Compile/Batch/Prover.lean); `vs`: List Bits, the store (`finishSlotL`)
  the lazy prover: `PL` (Compile/Batch/SeedLazyDefs.lean)
Limits: what the head of Compile/Batch/NeedCostP.lean lists as not said is not said here either.
Nothing on what the programs return. Upper bounds on every path; worst case over the oracle.
-/
import Compile.Batch.NeedCostP
import Compile.Batch.SeedLazyDefs
import Compile.CostPost

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Rom Iop

namespace Compile.Batch
namespace Need
open Compile.CostP (SWA)
open Seed

section Rounds
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam K L) lam} (hm : Std m) {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

local notation "T1" => fun _ => True
local notation "SWo" => SWA (S := spec lam K L) (sp := split lam K L) (Rom.Need.num (needOf nb m))

include hm
variable (depthReq : ℕ)

end Rounds

section Prove
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam K L) lam}

local notation "T1" => fun _ => True
local notation "SWo" => SWA (S := spec lam K L) (sp := split lam K L) (Rom.Need.num (needOf nb m))
local notation "CAo" => OComp.CA (S := spec lam K L) (Rom.Need.num (needOf nb m))

variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q)
  (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ) (cms : List (Dig lam)) (w : Wt)

/-- a proof string with given openings costs nothing -/
theorem swa_finishSlotG (ext : (E.Pos → Bool) → ExtF lam E) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ)
    (x : Y) (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    SWo (finishSlotG (L := L) Q H wq wp w ext c0 a0 j x cj acc) 0 T1 := by
  unfold finishSlotG
  dsimp only
  split_ifs
  · trivial
  · exact fun vs =>
      SWA.bind' (swa_opensB nb _ _ _ _ _ _ _) (m' := 0) (fun _ _ => trivial) (Nat.le_refl _)

variable (opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam)))) {cO : ℕ}

theorem ca_opensExtL (hO : ∀ q, CAo (opL q) cO fun _ => True) (we : WireE E) (y : E.Str)
    (isRead : E.Pos → Bool) (ps : List E.Pos) :
    CAo (opensExtL we y opL isRead ps) (ps.countP isRead * cO) fun _ => True := by
  induction ps with
  | nil => exact trivial
  | cons p ps ih =>
    unfold opensExtL
    refine OComp.CA.bind' (Q := fun _ => True) ih
      (m' := if isRead p = true then cO else 0) ?_ (le_of_eq ?_)
    · intro of _
      cases of with
      | none => exact trivial
      | some f =>
        dsimp only
        split_ifs
        · exact OComp.CA.bind' (P := fun _ => True) (Q := fun _ => True) (hO (we.leaf p)) (m' := 0)
            (fun _ _ => trivial) (Nat.le_refl _)
        · exact trivial
    · rw [List.countP_cons]
      split_ifs <;> simp [Nat.add_mul]

variable {nE : ℕ}

/-- The proof string of one slot, with openings made when they are needed. -/
theorem ca_finishSlotL (hO : ∀ q, CAo (opL q) cO fun _ => True)
    (hE : ∀ x ρ, (Q.loc.extReads x ρ).card ≤ nE) (hnd : wq.ext.all.Nodup) (c0 : H.Coin0) (a0 : Acc0)
    (j : ℕ) (x : Y) (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    CAo (finishSlotL (L := L) Q H wq wp w opL c0 a0 j x cj acc vs) (nE * cO) fun _ => True := by
  unfold finishSlotL
  dsimp only
  split_ifs
  · exact trivial
  · refine OComp.CA.bind' (Q := fun _ => True)
      (ca_opensExtL nb opL hO wq.ext (H.ext w) _ wq.ext.all) (m' := 0) (fun og _ => ?_) ?_
    · cases og with
      | none => exact trivial
      | some gx =>
        exact OComp.CA.bind' (Q := fun _ => True)
          ((swa_finishSlotG nb Q H wq wp w (fun _ => gx) c0 a0 j x cj acc).ca vs) (m' := 0)
          (fun _ _ => trivial) (Nat.le_refl _)
    · rw [Nat.add_zero]
      refine Nat.mul_le_mul_right _ (le_trans ?_ (hE x (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)))
      letI := wq.ext.dec
      rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _)]
      refine Finset.card_le_card fun q hq => ?_
      have := (List.mem_filter.1 (List.mem_toFinset.1 hq)).2
      simpa using this

/-- Under the hypotheses below: the proof strings of all slots: a slot without a request costs
nothing. -/
theorem ca_finishAllL (hO : ∀ q, CAo (opL q) cO fun _ => True)
    (hE : ∀ x ρ, (Q.loc.extReads x ρ).card ≤ nE) (hnd : wq.ext.all.Nodup) (fl : ℕ → Bool)
    (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (zs : List (SlotAcc lam K (Y × H.Coin))) (j : ℕ) (vs : List Bits),
      CAo (Seed.finishAllL (L := L) Q H wq wp w opL fl c0 a0 j zs vs)
        ((zs.map fun a => a.x.isSome).count true * (nE * cO)) fun _ => True := by
  intro zs
  induction zs with
  | nil => exact fun _ _ => trivial
  | cons acc zs ih =>
    intro j vs
    unfold Seed.finishAllL slotL
    refine OComp.CA.bind' (P := fun _ => True) (Q := fun _ => True)
      (m := if acc.x.isSome = true then nE * cO else 0) ?_
      (m' := (zs.map fun a => a.x.isSome).count true * (nE * cO)) (fun o1 _ => ?_) (le_of_eq ?_)
    · cases hx : acc.x with
      | none => exact trivial
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        dsimp only
        rw [if_pos (show (some (x, cj) : Option (Y × H.Coin)).isSome = true from rfl)]
        split_ifs
        · exact ca_finishSlotL nb Q H wq wp w opL hO hE hnd c0 a0 j x cj acc vs
        · exact trivial
    · cases o1 with
      | none => exact trivial
      | some o =>
        exact OComp.CA.bind' (Q := fun _ => True) (ih (j + 1) o.2) (m' := 0)
          (fun _ _ => trivial) (Nat.le_refl _)
    · rw [List.map_cons, List.count_cons]
      cases acc.x.isSome <;> simp [Nat.add_mul, Nat.add_comm]

end Prove

end Need
end Compile.Batch
