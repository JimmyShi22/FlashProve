-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/K8BehindTop.lean: THE SMALLNESS TEST: ANOTHER HOUSE's NAMED PREMISE
`K8Behind` (Johnson/Desc/ProofFile/Honest/K9/TotalFront.lean: at a stand of the batching the kind's
last run returns outside the kind's own share) AT A LINK OF EACH OF THE THREE SORTS, WHERE THE
THREAD's BLOCKS ARE THE FIRST CHAIN's OWN, IN THE GOALS' SCOPE: ONE SENTENCE A SORT, IN WHICH ALL
THAT IS STILL OWED STANDS AS PREMISES SIDE BY SIDE. A chain of three calls; nothing is shown here
that the called lemmas do not show. None of the library's goals.

  `ChainThread T b c Z l`   the six ties of the thread to the chain that `allFrontAtStand_of`
                   (Johnson/Desc/ProofFile/Honest/K8/FrontOfReach.lean) asks, as one structure
  **`k8Behind_layers`**, **`k8Behind_att`**, **`k8Behind_head`**   ⊢ K8Behind Lk p φ Ok nU T b
                   (k8Share nU)
THE CHAIN: `k8Behind_ok` (Johnson/Desc/ProofFile/Honest/K8/RestJoinOk.lean) asks `ValuesAtStand`;
that by `valuesAtStand_layers` | `_att` | `_head` (ValuesJoin.lean) from `AllFrontAtStand`; that by
`allFrontAtStand_of` from `LeftOverAtStand`.
WHAT IS STILL OWED, AS THE PREMISES STAND: (1) of the link: that the kind sits in it (K8At), that
its runs leave the batching element (ThetaAt), the order's cut at the kind's entry, that the runs
behind leave the powers (PowOn) · (2) of the letters φ, π, Ok: what φ shows; that Ok holds the
static clauses · (3) `FrontAtStandN` (RestJoinOk.lean): the other half of the cut, in front ·
(4) the scope, the files read, an opening of the description, its test on its plan, l < 25, the
built segment number l · (5) `ChainThread` · (6) `LeftOverAtStand`: `FrontLeftOver`'s eight and
the link's list · (7) the sort's ties, the ties of the runs "objects" (two), "join" and "planes",
the sort's order · (8) at every stand what the sort's lemmas ask of the state in front.
Limits. AN IMPLICATION: (1) TO (8) ARE PAID BY NOBODY HERE AND, TOGETHER, SHOWN OF NO THREAD AND NO
LINK. NO MEMBER: that they can hold together is not shown; where there is no stand all is idle.
NOTHING TIES THE LINK's SORT, OR THE SORT's LETTERS (the layers' numbers, the attention's plan, the
head's shape and numbers), TO THE SEGMENT's NUMBER l AND THE BUILT SEGMENT: each sentence holds its
premises at every l below 25; whoever fills the letters must take the segment's own, or (6) and (8)
will not meet. PAYERS IN SIGHT: those that the called files' Limits name; and of (5): the first two
ties are clauses of another house's premise on its first thread (`Sits.one`,
Johnson/Desc/ProofFile/Honest/Thread/File.lean); of (8): the equation on the third vector's array:
`u2_at_batch` (Johnson/P1K8R/ThirdTie.lean); the attention's own state and its third vector:
`here_at_batch` (Johnson/P1K8R/HereAtBatch.lean). No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.RestJoinOk
import Johnson.Desc.ProofFile.Honest.K8.FrontOfReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9L (Pub9)
open VerifiableInference.Desc.LinkJoin (PowOn StaticOk)
open ProofFile.Honest.K9 (BatStand K8Behind k8Entry)
open _root_.P1K8

/-- The thread's blocks are the first chain's own, and its border stands in front of segment number
l's batching. -/
structure ChainThread {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Claim V W X Pb) (b : ℕ)
    (c : Chain S Claim) (Z : ProofFile.Pub) (l : ℕ) : Prop where
  ft : T.ft = 0
  bs : T.bs = c.blocksInOrder
  border : b = 14 * l + (if l = 24 then 11 else 9)
  len : b ≤ T.bs.length
  begun : ∀ (κ : Coins Bk) (m : Mid W X), ∃ q : ProofFile.InstPub,
    ∀ s₀, T.begun κ m.st.input (m.st.heard.take T.front) s₀ → s₀ = ProofFile.startS Z q
  stored : ∀ w i x u, T.stored w i x = some u → ∀ a ∈ u, a < fieldPrimeWord

section
variable {α : Type} {Lk : Link S Claim} {p : Desc.K9.Where} {φ : S → α}
  {Ok : α × Option Pub9 → Prop} {nU : Array ℕ}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}
  {u : HTailF2} {π : α → Option HTailF2 × Option (Array HFun)}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT A LAYERS' LINK.** -/
theorem k8Behind_layers {k : Desc.K9.SegSort} {pW : K8.ParW} (hK : K8At Lk k pW)
    (hTh : ThetaAt Lk Lk.order) {pre post : List (ℕ × String)}
    (hsp : Lk.order = pre ++ k8Entry k :: post) (hPw : PowOn Lk post)
    (hrd : ∀ s : S, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hOkS : ∀ q tlb v, Ok q → (π q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F)
    (hFront : FrontAtStandN Lk p φ Ok nU T b)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (C : ChainThread T b c Z l) (hL : LeftOverAtStand Lk p T b)
    (p4 : OnBytes.Desc.First.K4.Par) (ties : LinkJoin.LayersTies Lk p4 nU)
    (tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits)
    (hord : Lk.order = First.orderOf .layers)
    (hs : ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
      ∀ tl, s.tl? = some tl → LayAsks p4 ((tl.ix.U.getD 2 none).getD 0) s) :
    K8Behind Lk p φ Ok nU T b (k8Share nU) :=
  k8Behind_ok hK hTh hsp hPw hrd hOkS hFront
    (valuesAtStand_layers p4 ties tC tD hord
      (allFrontAtStand_of hS hR O hOk hl e3 C.ft C.bs C.border C.len C.begun C.stored hL) hs)

/-- **AT AN ATTENTION LINK.** -/
theorem k8Behind_att {k : Desc.K9.SegSort} {pW : K8.ParW} (hK : K8At Lk k pW)
    (hTh : ThetaAt Lk Lk.order) {pre post : List (ℕ × String)}
    (hsp : Lk.order = pre ++ k8Entry k :: post) (hPw : PowOn Lk post)
    (hrd : ∀ s : S, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hOkS : ∀ q tlb v, Ok q → (π q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F)
    (hFront : FrontAtStandN Lk p φ Ok nU T b)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (C : ChainThread T b c Z l) (hL : LeftOverAtStand Lk p T b)
    (At : Attention.Plan) (ties : LinkJoin.AttTies Lk (Att.P.parCOf At) nU)
    (tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits)
    (tJ : ∀ run, LinkJoin.At Lk (2, "join") run → LinkJoin.Under run
      (Desc.K9.joinCalls (Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf At)) (Att.P.parCOf At))))
    (tP : ∀ run, LinkJoin.At Lk (1, "planes") run → ∃ lm, LinkJoin.Under run
      (Desc.K9.planesCalls lm
        (Att.P.readersOfK (Att.P.seatCO (Att.P.parCOf At)) (Att.P.parCOf At))))
    (hord : Lk.order = First.orderOf .attention)
    (hs : ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
      ∀ tl, s.tl? = some tl → AttAsks s ∧ tl.ix.U.getD 2 none = some At.iU3 ∧
        ∃ a : AttOwn, s.here = .att a ∧ Att.P.U3At At (Att.P.plannedK At) a.F) :
    K8Behind Lk p φ Ok nU T b (k8Share nU) :=
  k8Behind_ok hK hTh hsp hPw hrd hOkS hFront
    (valuesAtStand_att At ties tC tD tJ tP hord
      (allFrontAtStand_of hS hR O hOk hl e3 C.ft C.bs C.border C.len C.begun C.stored hL) hs)

/-- **AT THE HEAD's LINK.** -/
theorem k8Behind_head {k : Desc.K9.SegSort} {pW : K8.ParW} (hK : K8At Lk k pW)
    (hTh : ThetaAt Lk Lk.order) {pre post : List (ℕ × String)}
    (hsp : Lk.order = pre ++ k8Entry k :: post) (hPw : PowOn Lk post)
    (hrd : ∀ s : S, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hOkS : ∀ q tlb v, Ok q → (π q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F)
    (hFront : FrontAtStandN Lk p φ Ok nU T b)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (C : ChainThread T b c Z l) (hL : LeftOverAtStand Lk p T b)
    (h : Model.Head.Shape) (iU3 lh piece : Nat) (p6 : Kinds.Head.Par)
    (ties : LinkJoin.HeadTies Lk h iU3 lh piece p6 nU)
    (tC : ∀ run, LinkJoin.At Lk (2, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At Lk (7, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits)
    (tP : ∀ run, LinkJoin.At Lk (2, "planes") run → ∃ lm, LinkJoin.Under run
      (Desc.K9.planesCalls lm (Kinds.Head.callerReaders (Kinds.Head.planesAt iU3))))
    (hord : Lk.order = First.orderOf .head)
    (hs : ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
      ∀ tl, s.tl? = some tl → HeadWants h iU3 p6 s ∧ tl.ix.U.getD 2 none = some iU3) :
    K8Behind Lk p φ Ok nU T b (k8Share nU) :=
  k8Behind_ok hK hTh hsp hPw hrd hOkS hFront
    (valuesAtStand_head h iU3 lh piece p6 ties tC tD tP hord
      (allFrontAtStand_of hS hR O hOk hl e3 C.ft C.bs C.border C.len C.begun C.stored hL) hs)

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8Behind_layers
#print axioms ProofFile.Honest.K8.k8Behind_att
#print axioms ProofFile.Honest.K8.k8Behind_head
