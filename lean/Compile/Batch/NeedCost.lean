-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/NeedCost.lean: what the compiled verifier costs over one hash function, if only the
  marked blocks are queried. It uses `sumNb`, `cnt_le_of` and `CostBoundAt.weight` of
  Compile/NeedCost.lean (words of this library: lean/GLOSSARY.md).

  Over one hash function (Rom/Family.lean) a typed query costs as many queries as blocks of its
  answer are queried. In Compile/Batch/VCost.lean every Fiat-Shamir query costs K + 1, where K is
  the number of challenge blocks of every Fiat-Shamir answer (`W.K`), the same for all rounds. With
  the table of marked blocks of Compile/Batch/NeedTable.lean the Fiat-Shamir query of round i of
  protocol t costs at most nb t i + 1: the blocks of the challenge of that round, and the chaining
  value. The number nb t i is a parameter. For a query encoding m that splits an answer as
  Compile/Batch/ImplOf.lean does (`Std m`, the hypothesis of `num_le_blk` and of Parts 3 to 5 but
  for `cn_askFb`, `actOf_lo`, `outs_chainB_lo`, `cn_chainB_lo`) every other query costs one, as
  before: the query to g in the joining round, and each leaf and node query, in the trees over
  oracles and in the request tree.
    Part 1  the number of marked blocks at a typed query (`num_fb_le`, `num_le_blk`)
    Part 2  the bounds `cVQLN`, `cVQBN`, `cVBN`. `cVBN_eq`: cVBN W nb = cChain L nb + cOpens W +
            (W.depthReq + 2): the part of the chains (a sum over the rounds: `sumNb`,
            Compile/NeedCost.lean) and the part of the openings (for each opened position a leaf and
            a path); only the first part depends on nb, and it does not depend on the wire record
    Part 3  the verifier of one slot, for any Batch IOP (`cn_verifyBS`): the chain, one query to g,
            the openings, a leaf and a path in the request tree
    Part 4  a protocol with local rounds only (`RoundSplits.AllLo`, `cn_verifyBS_lo`): its chain never
            joins, so g and the request tree are never queried
    Part 5  `cn_vTS`, `cn_vLS`, `cn_vBS`: the three verifiers that the scheme runs, each on any
            inputs; `cn_vTS0`, `cn_vLS0`: the coarser bounds, with g and the request tree.
            `costBoundAt_V`: V, with the bound `cVBN W nb`
  Notation:
    `Std m` (Compile/Batch/NeedTable.lean): the query encoding splits an answer as
      Compile/Batch/ImplOf.lean does: one block at leaf, node, the oracles of request trees, g and
      the auxiliary oracle `other`; none at ann; at a Fiat-Shamir oracle the K blocks in their
      order, then the chaining value;
    `cms`: a list of digests; in `verifyB` (Compile/Batch/Verifier.lean): the external roots, as
      inputs;
    `rtreq`, `pls` (`OneProtocolProof`, Compile/Batch/Verifier.lean): the request root; the plain parts;
    `ph.joins` (`Phase.joins`, Compile/Batch/GlueTools.lean): how often the chain can still join:
      once before the shared rounds, never afterwards;
    `sMT`, `sFS`: natural numbers; sMT is the length of the salt of a leaf, sFS that of the salt
      of a chain (Compile/Batch/Verifier.lean).
  Limits: nothing on C and P. Nothing on whether V reads only marked blocks
  (Compile/Batch/NeedBlocks.lean): a bound on the marked blocks holds for any nb. The bounds are
  upper bounds on every path, not exact counts. The statements are over the typed oracles, at the
  weight "marked blocks" (`CN`): the step to queries to the one hash function
  (`queryBound_overOneN`, Rom/OverOneN.lean) is not made in this file; for `vTS`, `vLS`, `vBS` it is
  made in Top/BatchVQueriesN.lean.
  The proofs follow Compile/Batch/VCost.lean.
-/
import Compile.Batch.NeedTable
import Compile.Batch.VCost
import Compile.NeedCost

set_option autoImplicit false

open Rom Iop

/-! ## Two tools on oracle algorithms -/

namespace Rom
variable {S : OSpec} {α β : Type}

/-- every output of the algorithm, whatever the answers and the coins, has the property -/
def OComp.Outs (post : α → Prop) : OComp S α → Prop
  | .pure a => post a
  | .sample _ k => ∀ r, (k r).Outs post
  | .query _ _ k => ∀ r, (k r).Outs post

theorem OComp.Outs.bind {post : α → Prop} {post' : β → Prop} {g : α → OComp S β}
    (hg : ∀ a, post a → (g a).Outs post') {c : OComp S α} :
    c.Outs post → (c.bind g).Outs post' := by
  induction c with
  | pure a => exact fun h => hg a h
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih => exact fun h r => ih r (h r)

/-- the bound of a sequence, if the second part is bounded after those outputs that the first part
can have -/
theorem OComp.CostBoundAt.bind_outs {w : (o : S.ι) → S.Dom o → ℕ} {post : α → Prop}
    {g : α → OComp S β} {t : ℕ} (hg : ∀ a, post a → (g a).CostBoundAt w t) {c : OComp S α} :
    c.Outs post → ∀ {s : ℕ}, c.CostBoundAt w s → (c.bind g).CostBoundAt w (s + t) := by
  induction c with
  | pure a => exact fun hp _ _ => (hg a hp).mono (by omega)
  | sample n k ih => exact fun hp _ h r => ih r (hp r) (h r)
  | query o q k ih =>
    rintro hp s ⟨s', rfl, h⟩
    exact ⟨s' + t, by omega, fun r => ih r (hp r) (h r)⟩

end Rom

/-- local rounds only -/
def Iop.RoundSplits.AllLo : (s : Shape) → RoundSplits s → Prop
  | [], _ => True
  | _ :: s, (a, A) => a.kind = .lo ∧ RoundSplits.AllLo s A

theorem Iop.RoundSplits.allLo_allLocal : ∀ s : Shape, RoundSplits.AllLo s (RoundSplits.allLocal s)
  | [] => trivial
  | _ :: s => ⟨rfl, RoundSplits.allLo_allLocal s⟩

namespace Compile.Batch
namespace Need
open Compile.Need (sumNb sumNb_le cnt_le_of)

/-! ## Part 1. The number of marked blocks -/

section Num
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ) (m : OracleCoding (spec lam K L) lam)

/-- a Fiat-Shamir query of round i of protocol t has at most nb t i + 1 marked blocks -/
theorem num_fb_le (t : Tag) (q : FbIn lam L t) : (needOf nb m).num (.fb t) q ≤ nb t q.round + 1 :=
  cnt_le_of _ K _

/-- never more than the answer has -/
theorem num_le_blocks (o : OracleName) (q : domOf lam L o) : (needOf nb m).num o q ≤ m.blocks o :=
  cnt_le _ _

variable {m}

theorem num_le_blk (hm : Std m) (o : OracleName) (q : domOf lam L o) : (needOf nb m).num o q ≤ blk K o :=
  (num_le_blocks nb m o q).trans (le_of_eq (hm.blocks o))

end Num

/-! ## Part 2. The bounds -/

section Bounds
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- the part of the openings: for each opened position a leaf and a path -/
def cOpen {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) : ℕ :=
  wq.nOpen * (wq.maxDepth + 1)

/-- the bound on the queries to the one hash function by the compiled verifier of a protocol with
local rounds only (in this file: on the marked blocks of its queries, `CN`; the step to the one hash
function, for `vTS`, `vLS`: Top/BatchVQueriesN.lean): for each round of the chain the blocks of its
challenge and the chaining value; the openings -/
def cVQLN (nbf : ℕ → ℕ) {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) : ℕ :=
  sumNb nbf Q.loc.shape 0 + cOpen wq

/-- the bound on the queries to the one hash function by the compiled verifier of one slot (in this
file: on the marked blocks of its queries, `CN`; the step to the one hash function, for `vBS`:
Top/BatchVQueriesN.lean): for each round of the chain the blocks of its challenge and the chaining
value; one to g; the openings; a leaf and a path in the request tree -/
def cVQBN (nbf : ℕ → ℕ) {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    (wq : ProtocolQueryLayout lam K Q) (depthReq : ℕ) : ℕ :=
  (sumNb nbf Q.loc.shape 0 + 1) + (cOpen wq + (depthReq + 1))

/-- the bound on the queries of V to the one hash function, if only the marked blocks are queried
(in this file: on the marked blocks of V's queries, `costBoundAt_V`; the step to the one hash
function is not made in this file): Test, one Link, one slot of Batch -/
def cVBN (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ) : ℕ :=
  cVQLN (nb .test) W.T + cVQLN (nb .link) W.Lk + cVQBN (nb .onl) W.B W.depthReq

/-- the part of the chains: for each round of Test, of Link and of Batch the blocks of its challenge
and the chaining value. It depends on the numbers of rounds and on nb only, not on the wire
record -/
def cChain (L : BatchProtocol I X) (nb : Tag → ℕ → ℕ) : ℕ :=
  sumNb (nb .test) L.offline.shape 0 + sumNb (nb .link) L.link.shape 0 +
    sumNb (nb .onl) L.onlineBatch.loc.shape 0

/-- the part of the openings of Test, of Link and of Batch. It does not depend on nb -/
def cOpens (W : QueryLayout lam L) : ℕ := cOpen W.T + cOpen W.Lk + cOpen W.B

/-- the parts: the chains; the openings; one query to g, and a leaf and a path in the request
tree -/
theorem cVBN_eq (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ) :
    cVBN W nb = cChain L nb + cOpens W + (W.depthReq + 2) := by
  show (sumNb (nb .test) L.offline.shape 0 + cOpen W.T) +
      (sumNb (nb .link) L.link.shape 0 + cOpen W.Lk) +
      ((sumNb (nb .onl) L.onlineBatch.loc.shape 0 + 1) + (cOpen W.B + (W.depthReq + 1))) =
    (sumNb (nb .test) L.offline.shape 0 + sumNb (nb .link) L.link.shape 0 +
        sumNb (nb .onl) L.onlineBatch.loc.shape 0) +
      (cOpen W.T + cOpen W.Lk + cOpen W.B) + (W.depthReq + 2)
  omega

/-- on every path the marked blocks of the queries of c add up to at most t -/
abbrev CN (nb : Tag → ℕ → ℕ) (m : OracleCoding (spec lam K L) lam) {α : Type} (c : TypedOracleComputation lam K L α) (t : ℕ) :
    Prop :=
  OComp.CostBoundAt (S := spec lam K L) (needOf nb m).num c t

variable (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam K L) lam}

/-! ## Part 3. The verifier of one slot -/

theorem cn_askFb (t : Tag) (q : FbIn lam L t) :
    CN nb m (askTypedOracle (L := L) (K := K) (OracleName.fb t) q) (nb t q.round + 1) :=
  (OComp.CostBoundAt.ask (S := spec lam K L) (OracleName.fb t) q).mono (num_fb_le nb m t q)

variable (hm : Std m)
include hm

theorem cn_askV (o : OracleName) (q : domOf lam L o) : CN nb m (askTypedOracle (L := L) (K := K) o q) (blk K o) :=
  (OComp.CostBoundAt.ask (S := spec lam K L) o q).mono (num_le_blk nb hm o q)

/-- For `Std m`: a bound with the weights of Compile/Batch/VCost.lean holds for the marked blocks
too. -/
theorem cn_of_cb {α : Type} {c : TypedOracleComputation lam K L α} {t : ℕ} (h : VCost.CB c t) : CN nb m c t :=
  OComp.CostBoundAt.weight (w := fun o _ => blk K o)
    (w' := (needOf nb m).num) (fun o q => num_le_blk nb hm o q) (OComp.CostBoundAt.of_costBound h)

theorem cn_chainB (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s),
      CN nb m (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls)
        (sumNb (nb t) s i + ph.joins)
  | [], _, _, _, _, _, _, _ => OComp.CostBoundAt.pure _ _
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [recomputeChain]
      split
      · rename_i h next e
        split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine (OComp.CostBoundAt.bind (s := nb t i + 1)
            (t := sumNb (nb t) s (i + 1) + ph.joins + 0)
            (fun ans =>
              OComp.CostBoundAt.bind (t := 0) (fun r => OComp.CostBoundAt.pure _ _)
                ((cn_chainB t cms x salt rtreq s A W _ _ _ rts' pls).mono
                  (Nat.add_le_add_left (joins_of_one e _) _)))
            (cn_askFb nb t _)).mono ?_
          simp only [sumNb]
          omega
        · exact OComp.CostBoundAt.pure _ _
      · rename_i h next e
        split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine (OComp.CostBoundAt.bind (s := nb t i + 1)
            (t := sumNb (nb t) s (i + 1) + ph.joins + 0)
            (fun ans =>
              OComp.CostBoundAt.bind (t := 0) (fun r => OComp.CostBoundAt.pure _ _)
                ((cn_chainB t cms x salt rtreq s A W _ _ _ rts' pls).mono
                  (Nat.add_le_add_left (joins_of_one e _) _)))
            (cn_askFb nb t _)).mono ?_
          simp only [sumNb]
          omega
        · exact OComp.CostBoundAt.pure _ _
      · rename_i ρ e
        split
        · rename_i rtj rts1 _
          split
          · rename_i rt0 rts' _
            simp only [bind_eq]
            refine (OComp.CostBoundAt.bind (s := 1)
              (t := (nb t i + 1) + (sumNb (nb t) s (i + 1) + 0 + 0))
              (fun c =>
                OComp.CostBoundAt.bind (s := nb t i + 1) (t := sumNb (nb t) s (i + 1) + 0 + 0)
                  (fun ans =>
                    OComp.CostBoundAt.bind (t := 0) (fun r => OComp.CostBoundAt.pure _ _)
                      (cn_chainB t cms x salt rtreq s A W _ _
                        (.shr _ (show Dig lam from c)) rts' pls))
                  (cn_askFb nb t _))
              (cn_askV nb hm (OracleName.g t) _)).mono ?_
            simp only [sumNb, joins_of_join e]
            omega
          · exact OComp.CostBoundAt.pure _ _
        · exact OComp.CostBoundAt.pure _ _
      · exact OComp.CostBoundAt.pure _ _

theorem cn_afterB {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    CN nb m (afterB Q wq embS embE depthReq cms x π ρ rts ph) (cOpen wq + (depthReq + 1)) :=
  cn_of_cb nb hm (VCost.cb_afterB Q wq embS embE depthReq cms x π ρ rts ph)

/-- For `Std m`: the last part of the strict verifier, with pruned Merkle paths, has the bound of
`afterB`. -/
theorem cn_afterBO {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    CN nb m (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph) (cOpen wq + (depthReq + 1)) :=
  cn_of_cb nb hm (VCost.cb_afterBO Q wq embS embE depthReq cms x π ρ rts ph)

theorem cn_verifyBS (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    CN nb m (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π)
      (cVQBN (nb t) wq depthReq) := by
  unfold verifyOneProtocol recomputeChainOfProof cVQBN
  refine OComp.CostBoundAt.bind (fun r => ?_)
    (cn_chainB nb hm t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0
      .first π.roots π.plains)
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact OComp.CostBoundAt.pure _ _
  · dsimp only
    split_ifs
    · exact cn_afterBO nb hm Q wq embS embE depthReq cms x π ρ rts ph
    · exact OComp.CostBoundAt.pure _ _

/-! ## Part 4. Local rounds only: the chain never joins -/

omit hm in
/-- in a local round a chain that has not joined stays so, and makes one Fiat-Shamir query -/
theorem actOf_lo (cms : List (Dig lam)) (x : Option X) (salt : Bits)
    (ph : Phase lam) (hp : ph.slotVal = none) :
    ∃ h next, actOf cms x salt .lo ph = some (.one h true next) ∧ ∀ v, (next v).slotVal = none := by
  cases ph with
  | first => exact ⟨_, _, rfl, fun _ => rfl⟩
  | loc ρ => exact ⟨_, _, rfl, fun _ => rfl⟩
  | shr ρ c => exact absurd hp (by simp [Phase.slotVal])
  | aft ρ c => exact absurd hp (by simp [Phase.slotVal])

omit hm in
/-- With local rounds only, from a phase without a slot value: the last phase has no slot value. -/
theorem outs_chainB_lo (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (_ : RoundSplits.AllLo s A) (W : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
        (_ : ph.slotVal = none) (rts : List (Dig lam)) (pls : Plains s),
      (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls).Outs fun r =>
        ∀ z, r = some z → z.2.2.slotVal = none
  | [], _, _, _, _, _, ph, hp, _, _ => by
      intro z hz
      obtain rfl := Option.some.inj hz
      exact hp
  | _ :: s, (a, A), hA, (w, W), embP, i, ph, hp, rts, (pl, pls) => by
      obtain ⟨h, next, e, hn⟩ := actOf_lo (X := X) cms (x.map L.early) salt ph hp
      simp only [recomputeChain, hA.1, e]
      cases takeRt w.hasJ rts with
      | none => exact fun z hz => nomatch hz
      | some y =>
        obtain ⟨rt, rts'⟩ := y
        simp only [bind_eq]
        intro ans
        refine OComp.Outs.bind (post := fun r => ∀ z, r = some z → z.2.2.slotVal = none)
          (fun r hr => ?_) (outs_chainB_lo t cms x salt rtreq s A hA.2 W _ _ _ (hn _) rts' pls)
        intro z hz
        cases r with
        | none => exact nomatch hz
        | some y =>
          obtain rfl := Option.some.inj hz
          exact hr y rfl

omit hm in
theorem cn_chainB_lo (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (_ : RoundSplits.AllLo s A) (W : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
        (_ : ph.slotVal = none) (rts : List (Dig lam)) (pls : Plains s),
      CN nb m (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls) (sumNb (nb t) s i)
  | [], _, _, _, _, _, _, _, _, _ => OComp.CostBoundAt.pure _ _
  | _ :: s, (a, A), hA, (w, W), embP, i, ph, hp, rts, (pl, pls) => by
      obtain ⟨h, next, e, hn⟩ := actOf_lo (X := X) cms (x.map L.early) salt ph hp
      simp only [recomputeChain, hA.1, e]
      cases takeRt w.hasJ rts with
      | none => exact OComp.CostBoundAt.pure _ _
      | some y =>
        obtain ⟨rt, rts'⟩ := y
        simp only [bind_eq]
        refine (OComp.CostBoundAt.bind (s := nb t i + 1) (t := sumNb (nb t) s (i + 1) + 0) (fun ans =>
          OComp.CostBoundAt.bind (t := 0) (fun r => OComp.CostBoundAt.pure _ _)
            (cn_chainB_lo t cms x salt rtreq s A hA.2 W _ _ _ (hn _) rts' pls))
          (cn_askFb nb t _)).mono ?_
        simp only [sumNb]
        omega

/-- after a chain that has not joined: the openings only -/
theorem cn_afterB_lo {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) (hp : ph.slotVal = none) :
    CN nb m (afterB Q wq embS embE depthReq cms x π ρ rts ph) (cOpen wq) := by
  unfold afterB cOpen
  rw [hp]
  split
  · rename_i a b _ _
    split_ifs with hc
    · simp only [bind_eq]
      refine (OComp.CostBoundAt.bind (t := 0) (fun ok => ?_)
          (cn_of_cb nb hm
            ((VCost.cb_runChecks wq.maxDepth (a ++ b) ?_).mono
              (Nat.mul_le_mul_right (wq.maxDepth + 1) hc.1)))).mono
        (Nat.le_of_eq (Nat.add_zero _))
      · exact OComp.CostBoundAt.pure _ _
      · intro c hmem
        have := List.all_eq_true.1 hc.2 c hmem
        simp only [Check.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at this
        omega
    · exact OComp.CostBoundAt.pure _ _
  · exact OComp.CostBoundAt.pure _ _

/-- the same for the last part of the strict verifier -/
theorem cn_afterBO_lo {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) (hp : ph.slotVal = none) :
    CN nb m (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph) (cOpen wq) := by
  have h := VCost.cb_afterBO' Q wq embS embE depthReq cms x π ρ rts ph
  have e : reqCost depthReq ph = 0 := by unfold reqCost; rw [hp]; rfl
  rw [e, Nat.add_zero] at h
  exact cn_of_cb nb hm h

theorem cn_verifyBS_lo (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (hQ : RoundSplits.AllLo Q.loc.shape Q.ann) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    CN nb m (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π) (cVQLN (nb t) wq) := by
  unfold verifyOneProtocol recomputeChainOfProof cVQLN
  refine OComp.CostBoundAt.bind_outs (fun r hr => ?_)
    (outs_chainB_lo t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann hQ wq.sh embP 0
      .first rfl π.roots π.plains)
    (cn_chainB_lo nb t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann hQ wq.sh embP 0
      .first rfl π.roots π.plains)
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact OComp.CostBoundAt.pure _ _
  · dsimp only
    split_ifs
    · exact cn_afterBO_lo nb hm Q wq embS embE depthReq cms x π ρ rts ph (hr _ rfl)
    · exact OComp.CostBoundAt.pure _ _

end Bounds

/-! ## Part 5. The three verifiers that the scheme runs, and V -/

section Three
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ)
  {m : OracleCoding (spec lam W.K L) lam} (hm : Std m)
include hm

/-- the verifier of Test, on any root and any proof string -/
theorem cn_vTS (sMT sFS : ℕ) (cm : Dig lam) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline)) :
    CN nb m (vTS W sMT sFS cm π) (cVQLN (nb .test) W.T) :=
  cn_verifyBS_lo nb hm _ _ _ _ (RoundSplits.allLo_allLocal _) W.T _ _ _ _ _ _ _ _

/-- the verifier of Link, on any two roots and any proof string -/
theorem cn_vLS (sMT sFS : ℕ) (cm cm' : Dig lam) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) :
    CN nb m (vLS W sMT sFS cm cm' π) (cVQLN (nb .link) W.Lk) :=
  cn_verifyBS_lo nb hm _ _ _ _ (RoundSplits.allLo_allLocal _) W.Lk _ _ _ _ _ _ _ _

/-- the verifier of one slot of Batch, on any root, any request and any proof string -/
theorem cn_vBS (sMT sFS : ℕ) (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    CN nb m (vBS W sMT sFS cm x π) (cVQBN (nb .onl) W.B W.depthReq) :=
  cn_verifyBS nb hm _ _ _ _ W.B _ _ _ _ _ _ _ _

theorem cn_vTS0 (sMT sFS : ℕ) (cm : Dig lam) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline)) :
    CN nb m (vTS W sMT sFS cm π) (cVQBN (nb .test) W.T W.depthReq) :=
  cn_verifyBS nb hm _ _ _ _ W.T _ _ _ _ _ _ _ _

theorem cn_vLS0 (sMT sFS : ℕ) (cm cm' : Dig lam) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) :
    CN nb m (vLS W sMT sFS cm cm' π) (cVQBN (nb .link) W.Lk W.depthReq) :=
  cn_verifyBS nb hm _ _ _ _ W.Lk _ _ _ _ _ _ _ _

/-- For `Std m`: on every path the marked blocks of the queries of the compiled verifier add up to
at most cVBN W nb. -/
theorem costBoundAt_V (p : Params) (v : IVK lam L) (x : X) (π : Prf lam L) :
    (V W p v x π).CostBoundAt (needOf nb m).num (cVBN W nb) := by
  unfold V cVBN
  split
  · split_ifs
    · simp only [bind_eq]
      refine (OComp.CostBoundAt.bind
        (t := cVQLN (nb .link) W.Lk + (cVQBN (nb .onl) W.B W.depthReq + 0))
        (fun a =>
          OComp.CostBoundAt.bind (t := cVQBN (nb .onl) W.B W.depthReq + 0)
            (fun b =>
              OComp.CostBoundAt.bind (t := 0)
                (fun c => OComp.CostBoundAt.pure _ _) (cn_vBS W nb hm _ _ _ _ _))
            (cn_vLS W nb hm _ _ _ _ _))
        (cn_vTS W nb hm _ _ _ _)).mono ?_
      omega
    · exact OComp.CostBoundAt.pure _ _
  · exact OComp.CostBoundAt.pure _ _

end Three

end Need
end Compile.Batch
