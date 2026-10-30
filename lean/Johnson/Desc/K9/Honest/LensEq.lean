-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K9/Honest/LensEq.lean (kind K9): "the runs' claims are just the plan's number": the library's law of its
test `lensFitB` (Johnson/Desc/First/Link/Law/K9LensAskLaw.lean and LensAtFront.lean: "at most") with "=" for "at most",
at what is fixed at every state reached in front of each of the 25 batchings. For the honest side: the verifier's test
behind the adding asks "=". Over the sealed library alone. Two definitions, statements and proofs; no goal is stated.
  `lenRuns_filter_sum`, `lenRuns_sum`   where every entry of a link's order has a run, the runs' numbers of claims add
      up to the entries' numbers (the library's `lenRuns_le` says "at most", without that premise)
  `lens_layers_eq`, `lens_att_eq`, `lens_head_eq`   that sum written out, sort by sort: the library's `lens_layers`,
      `lens_att`, `lens_head` with "=": their statements and proofs, cut by program, with the premise laid in and one
      line turned
  `lensEqB W l X`   a test with code on public numbers, a definition of this file: the library's `lensFitB` with "=" for
      "at most": the closed numbers of claims of the segment's runs, added up, are the plan's nLin. Every "none" ends in
      false
  `lensEqB_iff`   its yes, written out: an "if and only if" · `lensFit_of_eq`, `lensAsked_of_eq`: its yes gives the
      library's test's yes
  `LensEqAsked Z`   the named public premise, a definition of this file: at each l < 25 a segment stands in
      Z.p.built.links and the test says yes of it
  `len8_eq`   the smallness test's share at what is fixed at a state that holds the structure and the tables: 4 + (NM +
      the reads off the skeleton), at the built segment's numbers · `lensEq_at`: the test's yes at the blank letters'
      own segment and public parameters
  **`hlenEq_layers`, `hlenEq_att`, `hlenEq_head`**   LensEqAsked Z; the scope; reached in front of the batching; the
      segment has its sort's order; every entry of the order has a run; each run's own number is its closed number ⊢
      lenRuns q (rlOf L tm ‹the sort's len›) = the plan's nLin, q := fixed9 (phiAll u ψ) s'. After the library's
      `hlen_layers`, `hlen_att`, `hlen_head`, line by line, with two turns: "=" for "at most", and the plan's nLin off
      the public part (W.G[g]?, W.A[g]?, W.H) for the ledger's planned number at a snapshot: the lines that read the
      ledger are dropped

The runs' numbers, each a premise, as in the library's law, with "=": the lookups' entries: l3 o q is Forest.lins of the
plan's shape at "objects" (the calls': y.fo, a.fs, HLy.fs; the digits': the built segment's tl.f9), 3 at "planes", 1 at
the attention's "join"; the sort's own runs: lenFront is frontB; the attention's two together are attOwnB; the head's
three are 29, 4 and 2, its join 1.

What is not claimed. `LensEqAsked` is a premise in this file, and no verifier asks the test. It is proved in the goals'
scope, and so under the library's head, in Johnson/Desc/K9/Honest/LensPaid/Paid.lean (`lensEqAsked_in_scope`,
`lensEqAsked_of_head`): the equality at the feed-forward segments and the head does lean on further numbers of the plan
(xl = 5, p3, tscCalls ≠ []), and the scope pins them.
`LensEqAsked` is stronger than the library's candidate `LensAsked` (`lensAsked_of_eq`). Not claimed either: that any
other premise is met. No member; the three are called by Johnson/Desc/ProofFile/Honest/K9/LensAtStand.lean. No property
of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.First.Link.Law.K9LensAskLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail.Port (readsList)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes attShapes nScores)
open Cb.Pv.Tail (Tab)
open VerifiableInference.Desc (Block Chain FileDescription Link Claim)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (ParC)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.K4Run (lenFront)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Kinds.Head.Law (tabsOfPlan Seen fsK6 fsJoin)
open VerifiableInference.Desc (K9Asks.pairsAt)
open VerifiableInference.Desc.K9Asks hiding pairsAt
open Johnson.Desc.First.Walk.Tied (Reach)
open K5Law

variable {β : Type}

/-! ## Where every entry of the order has a run, the runs' numbers add up to the entries' -/

theorem lenRuns_filter_sum {T P K : Type} (hear : List (Block T Claim))
    (tm : ℕ × String → ℕ → P → Bound K → List (ℕ × K)) (len : ℕ × String → P → ℕ) (q : P) :
    ∀ ord : List (ℕ × String),
      (∀ o ∈ ord, ∃ run, ((hear[o.1]?).bind fun b => b.claims.lookup o.2) = some run) →
      lenRuns q (ord.filterMap fun o =>
        ((hear[o.1]?).bind fun b => b.claims.lookup o.2).map fun r =>
          (⟨(o.2, r), tm o, len o⟩ : TermedRun T P K)) = (ord.map fun o => len o q).sum
  | [], _ => rfl
  | o :: ord, h => by
    obtain ⟨run, hr⟩ := h o (List.mem_cons.2 (Or.inl rfl))
    have ih := lenRuns_filter_sum hear tm len q ord fun o' ho' => h o' (List.mem_cons.2 (Or.inr ho'))
    rw [List.filterMap_cons_some (b := (⟨(o.2, run), tm o, len o⟩ : TermedRun T P K))
      (by simp only [hr, Option.map_some]), List.map_cons, List.sum_cons]
    show len o q + _ = _
    rw [ih]

theorem lenRuns_sum {T P K : Type} (L : Link T Claim)
    (tm : ℕ × String → ℕ → P → Bound K → List (ℕ × K)) (len : ℕ × String → P → ℕ) (q : P)
    (hAt : ∀ o ∈ L.order, ∃ run, At L o run) :
    lenRuns q (rlOf L tm len) = (L.order.map fun o => len o q).sum :=
  lenRuns_filter_sum L.hear tm len q L.order hAt

/-- **At a layers' segment.** -/
theorem lens_layers_eq {l : ℕ} {L : Link S Claim} (hL : SegAt l .layers L)
    (hAt : ∀ o ∈ L.order, ∃ run, At L o run)
    (p4 : OnBytes.Desc.First.K4.Par) (tm : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8))
    (l3 : ℕ × String → Q β → ℕ) (q : Q β) :
    lenRuns q (rlOf L tm (lenL p4 l3)) =
      l3 (1, "objects") q + lenFront p4 (·.own) q + l3 (6, "objects") q + len8 pi8 q + 4 := by
  refine (lenRuns_sum L tm _ q hAt).trans ?_
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

/-- **At an attention segment.** -/
theorem lens_att_eq {l : ℕ} {L : Link S Claim} (hL : SegAt l .attention L)
    (hAt : ∀ o ∈ L.order, ∃ run, At L o run)
    (rd : Phi β → Option (Forest.Heard × VerifiableInference.Desc.First.Att.P.Heard)) (c : ParC)
    (tm : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (q : Q β) :
    lenRuns q (rlOf L tm (lenA rd c l3)) =
      l3 (1, "objects") q + lenStill (fsFirst rd c) q + l3 (2, "join") q +
        lenStill (fsSecond rd c) q + l3 (1, "planes") q + l3 (6, "objects") q + len8 pi8 q := by
  refine (lenRuns_sum L tm _ q hAt).trans ?_
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

/-- **At the head's segment.** -/
theorem lens_head_eq {l : ℕ} {L : Link S Claim} (hL : SegAt l .head L)
    (hAt : ∀ o ∈ L.order, ∃ run, At L o run)
    (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : VerifiableInference.Desc.Kinds.Head.Par) (kap : Phi β → Option Seen)
    (tm : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (q : Q β) :
    lenRuns q (rlOf L tm (lenH h iU3 p kap l3)) =
      l3 (2, "objects") q + lenStill (fsK6 h iU3 p kap "norm") q +
        lenStill (fsJoin h iU3 p kap) q + lenStill (fsK6 h iU3 p kap "policy") q +
        l3 (2, "planes") q + l3 (7, "objects") q + len8 pi8 q +
        lenStill (fsK6 h iU3 p kap "logits") q + 1 := by
  refine (lenRuns_sum L tm _ q hAt).trans ?_
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

/-! ## The public test, with "=" -/

/-- **The test**: the library's `lensFitB`, with "=" for "at most". -/
def lensEqB (W : Verify.Public) (l : Nat) (X : Stages.LinkH) : Bool :=
  match ownLenB W l, K9Asks.pairsAt W l, claimsAt W l with
  | some a, some ps, some n =>
    decide (a + (4 + (X.tl.NM + readsB X.tl.NM X.tl.mats ps)) + Forest.lins X.tl.f9 = n)
  | _, _, _ => false

theorem lensEqB_iff (W : Verify.Public) (l : ℕ) (X : LinkH) :
    lensEqB W l X = true ↔ ∃ a ps n, ownLenB W l = some a ∧ K9Asks.pairsAt W l = some ps ∧
      claimsAt W l = some n ∧
      a + (4 + (X.tl.NM + readsB X.tl.NM X.tl.mats ps)) + Forest.lins X.tl.f9 = n := by
  unfold lensEqB
  constructor
  · intro h
    split at h
    · rename_i a ps n e1 e2 e3
      exact ⟨a, ps, n, e1, e2, e3, of_decide_eq_true h⟩
    · exact nomatch h
  · rintro ⟨a, ps, n, e1, e2, e3, h⟩
    rw [e1, e2, e3]
    exact decide_eq_true h

/-- Its yes gives the library's test's yes. -/
theorem lensFit_of_eq {W : Verify.Public} {l : ℕ} {X : LinkH} (h : lensEqB W l X = true) :
    lensFitB W l X = true := by
  obtain ⟨a, ps, n, e1, e2, e3, e⟩ := (lensEqB_iff W l X).1 h
  exact (lensFitB_iff W l X).2 ⟨a, ps, n, e1, e2, e3, Nat.le_of_eq e⟩

/-- **The named public premise**: at each segment's number a segment stands, and the test says yes of it. -/
def LensEqAsked (Z : ProofFile.Pub) : Prop :=
  ∀ l < 25, ∃ X, Z.p.built.links[l]? = some X ∧ lensEqB Z.p.X l X = true

theorem lensAsked_of_eq {Z : ProofFile.Pub} (h : LensEqAsked Z) : LensAsked Z := fun l hl => by
  obtain ⟨X, e, t⟩ := h l hl
  exact ⟨X, e, lensFit_of_eq t⟩

/-- The smallness test's share at what is fixed at a state that holds the structure and the tables. -/
theorem len8_eq (u : HTailF2) (ψ : S → β) (s : S) (tlP : HTailF2) (sh : List Tab) {tl : HTailF2}
    {funs : Array HFun} (h1 : s.tl? = some tl) (h2 : s.funs? = some funs)
    (hf : ∀ tl : HTailF2, (readsList tl funs).length = readsLenOf tl.NM tl.mats sh)
    (ht : rowsRead tl = rowsRead tlP) :
    len8 pi8 (fixed9 (phiAll u ψ) s) = 4 + (tlP.NM + readsLenOf tlP.NM tlP.mats sh) := by
  unfold len8
  show (match ((s.tl?.map (blank u), s.funs?) : Option HTailF2 × Option (Array HFun)) with
    | (some tlb, some funs) => 4 + (tlb.NM + (readsList tlb funs).length)
    | _ => 0) = _
  rw [h1, h2]
  show 4 + ((blank u tl).NM + (readsList (blank u tl) funs).length) = _
  rw [hf (blank u tl)]
  have e1 : (blank u tl).NM = tlP.NM := congrArg (·.1) ht
  have e2 : (blank u tl).mats = tlP.mats := congrArg (·.2.1) ht
  rw [e1, e2]

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The test's yes at the blank letters' own segment and public parameters. -/
theorem lensEq_at (hE : LensEqAsked Z)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) :
    ∃ a ps n, ownLenB Bs.G₀.W l = some a ∧ K9Asks.pairsAt Bs.G₀.W l = some ps ∧
      claimsAt Bs.G₀.W l = some n ∧
      a + (4 + (Xl.tl.NM + readsB Xl.tl.NM Xl.tl.mats ps)) + Forest.lins Xl.tl.f9 = n := by
  obtain ⟨X, x1, x2⟩ := built_tl O.blank e3
  obtain ⟨X', y1, y2⟩ := hE l hl
  obtain rfl : X = X' := Option.some.inj (x1.symm.trans y1)
  rw [← ProofFile.Law.blankBy_W O.blank] at y2
  rw [x2]
  exact (lensEqB_iff _ l X).1 y2

/-! ## The law -/

/-- **At the layers' segments.** -/
theorem hlenEq_layers (hE : LensEqAsked Z) (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s' : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (28 * g + 9) (z, s'))
    {l' : ℕ} {L : Link S Claim} (hL : SegAt l' .layers L)
    (hAt : ∀ o ∈ L.order, ∃ run, At L o run) (p4 : OnBytes.Desc.First.K4.Par)
    (tm : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (u : HTailF2) (ψ : S → β)
    (hC : l3 (1, "objects") (fixed9 (phiAll u ψ) s') = Forest.lins Bs.G₀.W.layers.y.fo)
    (hD : ∀ Xl, Bs.G₀.built[2 * g]? = some Xl →
      l3 (6, "objects") (fixed9 (phiAll u ψ) s') = Forest.lins Xl.tl.f9)
    (hF : lenFront p4 (·.own) (fixed9 (phiAll u ψ) s') = frontB Bs.G₀.W.layers.y g) :
    ∀ hp, Bs.G₀.W.G[g]? = some hp →
      lenRuns (fixed9 (phiAll u ψ) s') (rlOf L tm (lenL p4 l3)) = hp.nLin := by
  intro hp hhp
  obtain ⟨funs, f1, f2⟩ := reads_length_at_batch hS hR O hg h
  obtain ⟨G, funs', Xl, n, tl, a1, _, a3, hX, hn, _⟩ := rowsNumber_layers hS hR O hg h
  have hx : ((2 * g, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by omega : ¬ 2 * g = 24)]⟩
  have hr := planned_at_batch planned_rows hS hR O hx hX (z, s') (by
    show Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + 4 + 3 + 2) (z, s')
    have e : 14 * (2 * g) + 4 + 3 + 2 = 28 * g + 9 := by omega
    rw [e]
    exact h)
  have K8 := len8_eq u ψ s' Xl.tl (layShapes Bs.G₀.W.layers g) a3 f1 f2 (of_readTl hr tl a3)
  obtain ⟨a, ps, m, b1, b2, b3, b4⟩ := lensEq_at hE O (l := 2 * g) (by omega) hX
  have n24 : 2 * g ≠ 24 := by omega
  have ev : 2 * g % 2 = 0 := by omega
  have dv : 2 * g / 2 = g := by omega
  unfold ownLenB at b1
  unfold K9Asks.pairsAt at b2
  unfold claimsAt at b3
  rw [if_neg n24, if_pos ev, dv] at b1 b2 b3
  rw [hhp] at b3
  obtain rfl := Option.some.inj b1
  have hm : hp.nLin = m := Option.some.inj b3
  rw [layPairs_is b2, readsB_is] at b4
  have T := lens_layers_eq hL hAt p4 tm l3 (fixed9 (phiAll u ψ) s')
  have hD' := hD Xl hX
  omega

/-- **At the attention segments.** -/
theorem hlenEq_att (hE : LensEqAsked Z) (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s' : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s'))
    {l' : ℕ} {L : Link S Claim} (hL : SegAt l' .attention L)
    (hAt : ∀ o ∈ L.order, ∃ run, At L o run)
    (rd : Phi β → Option (Forest.Heard × VerifiableInference.Desc.First.Att.P.Heard)) (cA : ParC)
    (tm : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (u : HTailF2) (ψ : S → β)
    (hC : ∀ a, Bs.G₀.W.A[g]? = some a →
      l3 (1, "objects") (fixed9 (phiAll u ψ) s') = Forest.lins a.fs)
    (hD : ∀ Xl, Bs.G₀.built[2 * g + 1]? = some Xl →
      l3 (6, "objects") (fixed9 (phiAll u ψ) s') = Forest.lins Xl.tl.f9)
    (hJ : l3 (2, "join") (fixed9 (phiAll u ψ) s') = 1)
    (hP : l3 (1, "planes") (fixed9 (phiAll u ψ) s') = 3)
    (hF : ∀ a, Bs.G₀.W.A[g]? = some a →
      lenStill (fsFirst rd cA) (fixed9 (phiAll u ψ) s') +
        lenStill (fsSecond rd cA) (fixed9 (phiAll u ψ) s') = attOwnB a.S) :
    ∀ a, Bs.G₀.W.A[g]? = some a →
      lenRuns (fixed9 (phiAll u ψ) s') (rlOf L tm (lenA rd cA l3)) = a.nLin := by
  intro a₀ ha₀
  obtain ⟨a, funs, ha, f1, f2⟩ := reads_length_att hS hR O hg h
  obtain rfl : a = a₀ := Option.some.inj (ha.symm.trans ha₀)
  obtain ⟨G, funs', Xl, a', tl, a1, _, a3, hX, ha', _⟩ := rowsNumber_att hS hR O hg h
  have hx : ((2 * g + 1, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩
  have hr := planned_at_batch planned_rows hS hR O hx hX (z, s') h
  have K8 := len8_eq u ψ s' Xl.tl (attShapes a.S (nScores a.S)) a3 f1 f2 (of_readTl hr tl a3)
  obtain ⟨b, ps, m, b1, b2, b3, b4⟩ := lensEq_at hE O (l := 2 * g + 1) (by omega) hX
  have n24 : 2 * g + 1 ≠ 24 := by omega
  have od : ¬ (2 * g + 1) % 2 = 0 := by omega
  have dv : (2 * g + 1) / 2 = g := by omega
  unfold ownLenB at b1
  unfold K9Asks.pairsAt at b2
  unfold claimsAt at b3
  rw [if_neg n24, if_neg od, dv, ha] at b1 b2 b3
  obtain rfl := Option.some.inj b1
  obtain rfl := Option.some.inj b2
  obtain rfl := Option.some.inj b3
  have b5 : Forest.lins a.fs + attOwnB a.S + 1 + 3 +
      (4 + (Xl.tl.NM + readsB Xl.tl.NM Xl.tl.mats (attPairs a.S))) + Forest.lins Xl.tl.f9 =
      a.nLin := b4
  rw [attPairs_is, readsB_is] at b5
  have T := lens_att_eq hL hAt rd cA tm l3 (fixed9 (phiAll u ψ) s')
  have hC' := hC a ha
  have hD' := hD Xl hX
  have hF' := hF a ha
  omega

/-- **At the head.** -/
theorem hlenEq_head (hE : LensEqAsked Z) (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {z : ProofFile.InstPub} {s' : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s'))
    {l' : ℕ} {L : Link S Claim} (hL : SegAt l' .head L)
    (hAt : ∀ o ∈ L.order, ∃ run, At L o run)
    (hh : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p6 : VerifiableInference.Desc.Kinds.Head.Par) (kap : Phi β → Option Seen)
    (tm : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (u : HTailF2) (ψ : S → β)
    (hC : l3 (2, "objects") (fixed9 (phiAll u ψ) s') = Forest.lins Bs.G₀.W.HLy.fs)
    (hD : ∀ Xl, Bs.G₀.built[24]? = some Xl →
      l3 (7, "objects") (fixed9 (phiAll u ψ) s') = Forest.lins Xl.tl.f9)
    (hP : l3 (2, "planes") (fixed9 (phiAll u ψ) s') = 3)
    (hN : lenStill (fsK6 hh iU3 p6 kap "norm") (fixed9 (phiAll u ψ) s') = 29)
    (hPo : lenStill (fsK6 hh iU3 p6 kap "policy") (fixed9 (phiAll u ψ) s') = 4)
    (hLo : lenStill (fsK6 hh iU3 p6 kap "logits") (fixed9 (phiAll u ψ) s') = 2)
    (hJ : lenStill (fsJoin hh iU3 p6 kap) (fixed9 (phiAll u ψ) s') = 1) :
    lenRuns (fixed9 (phiAll u ψ) s') (rlOf L tm (lenH hh iU3 p6 kap l3)) = Bs.G₀.W.H.nLin := by
  obtain ⟨funs, t0, f1, f0, f2⟩ := reads_length_head hS hR O h
  obtain ⟨G, funs', Xl, t0', tl, a1, _, a3, hX, _, _⟩ := rowsNumber_head hS hR O h
  have hx : ((24, 5, 3) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨24, List.mem_range.2 (by omega), rfl⟩
  have hr := planned_at_batch planned_rows hS hR O hx hX (z, s') h
  have K8 := len8_eq u ψ s' Xl.tl (shapesOf t0.funs) a3 f1 f2 (of_readTl hr tl a3)
  obtain ⟨b, ps, m, b1, b2, b3, b4⟩ := lensEq_at hE O (l := 24) (by omega) hX
  unfold ownLenB at b1
  unfold K9Asks.pairsAt at b2
  unfold claimsAt at b3
  rw [if_pos rfl] at b1 b2 b3
  obtain rfl := Option.some.inj b1
  obtain rfl := Option.some.inj b3
  obtain ⟨t1, h1, rfl⟩ := headPairs_is b2
  obtain rfl : t0 = t1 := Option.some.inj (f0.symm.trans h1)
  rw [readsB_is] at b4
  have T := lens_head_eq hL hAt hh iU3 p6 kap tm l3 (fixed9 (phiAll u ψ) s')
  have hD' := hD Xl hX
  omega

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.lenRuns_filter_sum
#print axioms ProofFile.Honest.K9.lenRuns_sum
#print axioms ProofFile.Honest.K9.lens_layers_eq
#print axioms ProofFile.Honest.K9.lens_att_eq
#print axioms ProofFile.Honest.K9.lens_head_eq
#print axioms ProofFile.Honest.K9.lensEqB
#print axioms ProofFile.Honest.K9.lensEqB_iff
#print axioms ProofFile.Honest.K9.lensFit_of_eq
#print axioms ProofFile.Honest.K9.LensEqAsked
#print axioms ProofFile.Honest.K9.lensAsked_of_eq
#print axioms ProofFile.Honest.K9.len8_eq
#print axioms ProofFile.Honest.K9.lensEq_at
#print axioms ProofFile.Honest.K9.hlenEq_layers
#print axioms ProofFile.Honest.K9.hlenEq_att
#print axioms ProofFile.Honest.K9.hlenEq_head
