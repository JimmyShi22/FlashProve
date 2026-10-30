-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LensAtFront.lean: "THE RUNS' CLAIMS ARE AT MOST THE PLAN's NUMBER" (the
field hlen of `EqTake`, ExpsAt.lean): THE RUNS' NUMBER OF CLAIMS WRITTEN OUT, SORT BY SORT, AS A SUM
OF SEVEN, TEN AND ELEVEN SUMMANDS BY THE SEGMENT's OWN ORDER. Statements and proofs: counting.

  `lenRuns_le`: the number of claims of the runs that the order names (`lenRuns q (rlOf L tm len)`)
    is at most the sum of len o q over the whole order (an entry without a run counts nothing).
  `lens_layers`: **at a layers' segment: at most l3 (1, "objects") q + lenFront p4 (·.own) q + l3
    (6, "objects") q + len8 pi8 q + 4.**
  `lens_att`: **at an attention segment: at most l3 (1, "objects") q + lenStill (fsFirst rd c) q +
    l3 (2, "join") q + lenStill (fsSecond rd c) q + l3 (1, "planes") q + l3 (6, "objects") q + len8
    pi8 q.**
  `lens_head`: **at the head's: at most l3 (2, "objects") q + the three runs' lenStill + lenStill
    (fsJoin ..) q + l3 (2, "planes") q + l3 (7, "objects") q + len8 pi8 q + 1.**
  `len8_at`: len8 pi8 q = 4 + (NM + the number of reads) where the fixed part holds the structure
    and the tables.
Limits. Sums alone: nothing is compared with the plan's number here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.LinkLawAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port (readsList)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (ParC)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.K4Run (lenFront)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open K5Law

variable {β : Type}

/-- An entry without a run counts nothing. -/
theorem lenRuns_filter {T P K : Type} (hear : List (VerifiableInference.Desc.Block T Claim))
    (tm : ℕ × String → ℕ → P → Bound K → List (ℕ × K)) (len : ℕ × String → P → ℕ) (q : P) :
    ∀ ord : List (ℕ × String),
      lenRuns q (ord.filterMap fun o =>
        ((hear[o.1]?).bind fun b => b.claims.lookup o.2).map fun r =>
          (⟨(o.2, r), tm o, len o⟩ : TermedRun T P K)) ≤ (ord.map fun o => len o q).sum
  | [] => Nat.le_refl _
  | o :: ord => by
    rw [List.filterMap_cons, List.map_cons, List.sum_cons]
    have ih := lenRuns_filter hear tm len q ord
    cases h : (((hear[o.1]?).bind fun b => b.claims.lookup o.2).map fun r =>
        (⟨(o.2, r), tm o, len o⟩ : TermedRun T P K)) with
    | none => exact Nat.le_trans ih (Nat.le_add_left _ _)
    | some r =>
      obtain ⟨r0, _, rfl⟩ := Option.map_eq_some_iff.1 h
      show len o q + _ ≤ _
      exact Nat.add_le_add_left ih _

theorem lenRuns_le {T P K : Type} (L : Link T Claim)
    (tm : ℕ × String → ℕ → P → Bound K → List (ℕ × K)) (len : ℕ × String → P → ℕ) (q : P) :
    lenRuns q (rlOf L tm len) ≤ (L.order.map fun o => len o q).sum :=
  lenRuns_filter L.hear tm len q L.order

theorem lenNone (q : Q β) : lenStill fsNone q = 0 := rfl

theorem lenKeys (q : Q β) : lenStill fsKeys q = 0 := rfl

/-- **AT A LAYERS' SEGMENT.** -/
theorem lens_layers {l : ℕ} {L : Link S Claim} (hL : SegAt l .layers L)
    (p4 : OnBytes.Desc.First.K4.Par) (tm : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (l3 : ℕ × String → Q β → ℕ) (q : Q β) :
    lenRuns q (rlOf L tm (lenL p4 l3)) ≤
      l3 (1, "objects") q + lenFront p4 (·.own) q + l3 (6, "objects") q + len8 pi8 q + 4 := by
  refine Nat.le_trans (lenRuns_le L tm _ q) (Nat.le_of_eq ?_)
  rw [hL.order]
  show lenL p4 l3 (1, "objects") q + (lenL p4 l3 (1, "guests") q + (lenL p4 l3 (2, "front") q +
    (lenL p4 l3 (6, "objects") q + (lenL p4 l3 (6, "guests") q +
      (lenL p4 l3 (4, "K8.equations") q + (lenL p4 l3 (2, "back") q + 0)))))) = _
  have e1 : lenL p4 l3 (1, "objects") q = l3 (1, "objects") q := rfl
  have e2 : lenL p4 l3 (1, "guests") q = 0 := rfl
  have e3 : lenL p4 l3 (2, "front") q = lenFront p4 (·.own) q := rfl
  have e4 : lenL p4 l3 (6, "objects") q = l3 (6, "objects") q := rfl
  have e5 : lenL p4 l3 (6, "guests") q = 0 := rfl
  have e6 : lenL p4 l3 (4, "K8.equations") q = len8 pi8 q := rfl
  have e7 : lenL p4 l3 (2, "back") q = 4 := rfl
  rw [e1, e2, e3, e4, e5, e6, e7]
  omega

/-- **AT AN ATTENTION SEGMENT.** -/
theorem lens_att {l : ℕ} {L : Link S Claim} (hL : SegAt l .attention L)
    (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : ParC)
    (tm : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (q : Q β) :
    lenRuns q (rlOf L tm (lenA rd c l3)) ≤
      l3 (1, "objects") q + lenStill (fsFirst rd c) q + l3 (2, "join") q +
        lenStill (fsSecond rd c) q + l3 (1, "planes") q + l3 (6, "objects") q + len8 pi8 q := by
  refine Nat.le_trans (lenRuns_le L tm _ q) (Nat.le_of_eq ?_)
  rw [hL.order]
  show lenA rd c l3 (1, "objects") q + (lenA rd c l3 (1, "guests") q +
    (lenA rd c l3 (2, "first") q + (lenA rd c l3 (2, "keys") q + (lenA rd c l3 (2, "join") q +
      (lenA rd c l3 (2, "second") q + (lenA rd c l3 (1, "planes") q +
        (lenA rd c l3 (6, "objects") q + (lenA rd c l3 (6, "guests") q +
          (lenA rd c l3 (4, "K8.equations") q + 0))))))))) = _
  have e1 : lenA rd c l3 (1, "objects") q = l3 (1, "objects") q := rfl
  have e2 : lenA rd c l3 (1, "guests") q = 0 := rfl
  have e3 : lenA rd c l3 (2, "first") q = lenStill (fsFirst rd c) q := rfl
  have e4 : lenA rd c l3 (2, "keys") q = 0 := rfl
  have e5 : lenA rd c l3 (2, "join") q = l3 (2, "join") q := rfl
  have e6 : lenA rd c l3 (2, "second") q = lenStill (fsSecond rd c) q := rfl
  have e7 : lenA rd c l3 (1, "planes") q = l3 (1, "planes") q := rfl
  have e8 : lenA rd c l3 (6, "objects") q = l3 (6, "objects") q := rfl
  have e9 : lenA rd c l3 (6, "guests") q = 0 := rfl
  have e10 : lenA rd c l3 (4, "K8.equations") q = len8 pi8 q := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  omega

/-- **AT THE HEAD's SEGMENT.** -/
theorem lens_head {l : ℕ} {L : Link S Claim} (hL : SegAt l .head L)
    (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par) (kap : Phi β → Option Seen)
    (tm : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (q : Q β) :
    lenRuns q (rlOf L tm (lenH h iU3 p kap l3)) ≤
      l3 (2, "objects") q + lenStill (fsK6 h iU3 p kap "norm") q +
        lenStill (fsJoin h iU3 p kap) q + lenStill (fsK6 h iU3 p kap "policy") q +
        l3 (2, "planes") q + l3 (7, "objects") q + len8 pi8 q +
        lenStill (fsK6 h iU3 p kap "logits") q + 1 := by
  refine Nat.le_trans (lenRuns_le L tm _ q) (Nat.le_of_eq ?_)
  rw [hL.order]
  show lenH h iU3 p kap l3 (2, "objects") q + (lenH h iU3 p kap l3 (2, "guests") q +
    (lenH h iU3 p kap l3 (3, "norm") q + (lenH h iU3 p kap l3 (3, "join") q +
      (lenH h iU3 p kap l3 (3, "policy") q + (lenH h iU3 p kap l3 (2, "planes") q +
        (lenH h iU3 p kap l3 (7, "objects") q + (lenH h iU3 p kap l3 (7, "guests") q +
          (lenH h iU3 p kap l3 (5, "K8.equations") q + (lenH h iU3 p kap l3 (3, "logits") q +
            (lenH h iU3 p kap l3 (8, "the merge") q + 0)))))))))) = _
  have e1 : lenH h iU3 p kap l3 (2, "objects") q = l3 (2, "objects") q := rfl
  have e2 : lenH h iU3 p kap l3 (2, "guests") q = 0 := rfl
  have e3 : lenH h iU3 p kap l3 (3, "norm") q = lenStill (fsK6 h iU3 p kap "norm") q := rfl
  have e4 : lenH h iU3 p kap l3 (3, "join") q = lenStill (fsJoin h iU3 p kap) q := rfl
  have e5 : lenH h iU3 p kap l3 (3, "policy") q = lenStill (fsK6 h iU3 p kap "policy") q := rfl
  have e6 : lenH h iU3 p kap l3 (2, "planes") q = l3 (2, "planes") q := rfl
  have e7 : lenH h iU3 p kap l3 (7, "objects") q = l3 (7, "objects") q := rfl
  have e8 : lenH h iU3 p kap l3 (7, "guests") q = 0 := rfl
  have e9 : lenH h iU3 p kap l3 (5, "K8.equations") q = len8 pi8 q := rfl
  have e10 : lenH h iU3 p kap l3 (3, "logits") q = lenStill (fsK6 h iU3 p kap "logits") q := rfl
  have e11 : lenH h iU3 p kap l3 (8, "the merge") q = 1 := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  omega

/-- K8's share, where the fixed part holds the structure and the tables. -/
theorem len8_at {q : Q β} {tlb : HTailF2} {funs : Array HFun}
    (h : pi8 q.1 = (some tlb, some funs)) :
    len8 pi8 q = 4 + (tlb.NM + (readsList tlb funs).length) := by
  unfold len8
  rw [h]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.lenRuns_filter
#print axioms VerifiableInference.Desc.LinkJoin.lenRuns_le
#print axioms VerifiableInference.Desc.LinkJoin.lenNone
#print axioms VerifiableInference.Desc.LinkJoin.lenKeys
#print axioms VerifiableInference.Desc.LinkJoin.lens_layers
#print axioms VerifiableInference.Desc.LinkJoin.lens_att
#print axioms VerifiableInference.Desc.LinkJoin.lens_head
#print axioms VerifiableInference.Desc.LinkJoin.len8_at
