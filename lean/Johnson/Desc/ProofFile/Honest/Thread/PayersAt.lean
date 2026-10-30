-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/PayersAt.lean: the conclusions of K3ReadersAtHead.lean and
K1RelsDigits.lean with "the item is open at border b" in the form that the clause of `keeps` bears:
membership in `IM.openAt P5J.At.links P5J.At.ps b` (as in `formsBehind`, FHeadF.lean). The lemmas
that these two files call state it at other spellings of the same two lists: `IM.linksW`,
`IM.placesW` (equal by the library's `P5J.linksW_at`, `P5J.placesW_at`, Johnson/P5J/FoldJ3.lean),
and `K13.Law.openAt` at `linksFull` (the same term after unfolding). No definition.

  1  `k3_readers_at`   after the lookup on the digits of segment `l`: the readers' answers stay at
     the runs of every item `forms` that is open on both sides
  2  `k1_rels_at`   after the sending of the digits of segment `l`: `RecRides`, `AheadMeets`, and
     the readers' answers at every item `forms` that is open before it

Both take the invariant together with what has been said (`ThrS` at `SaidOk`) and the sub-protocol's
step (`Stepped`).

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The number of the sub-protocol is written as `k3K l true` and `noL l true`. That it is the
    number of a place's border is not shown here.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.K3ReadersAtHead
import Johnson.Desc.ProofFile.Honest.Thread.K1RelsDigits
import Johnson.P5J.FoldJ3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K1 (noL RecRides AheadMeets ReadersStay)
open VerifiableInference.OnPublicFiles (k3K)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The readers' answers stay over the lookup on the digits of segment `l`. -/
theorem k3_readers_at {l : Nat} (hl : l < 25) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[k3K l true]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (k3K l true) k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    ∀ mm kk ρ, Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps (k3K l true) →
      Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps (k3K l true + 1) →
      ∀ q ∈ h.𝔇.pubD.runs mm kk ρ, Fwd (h.𝔇.pubD.Rd mm) q.1 q.2 s s' :=
  fun mm kk ρ ho ho' =>
    k3_readers_behindS h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hblk hT hS mm kk ρ
      (by rw [P5J.linksW_at, P5J.placesW_at]; exact ho)
      (by rw [P5J.linksW_at, P5J.placesW_at]; exact ho')

/-- The three relations over the sending of the digits of segment `l`. -/
theorem k1_rels_at {l : Nat} (hl : l < 25) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[noL l true]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (noL l true) k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    ∃ new, RecRides new s s' ∧
      AheadMeets (h.𝔇.pubD.N.sent l) (h.𝔇.pubD.N.group l) new s s' ∧
      ∀ mm kk ρ, Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps (noL l true) →
        mm = l ∧ ReadersStay h.𝔇.pubD mm kk ρ s s' := by
  obtain ⟨new, h1, h2, h3⟩ :=
    k1_rels_digits h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hblk hT.1 hS
  exact ⟨new, h1, h2, fun mm kk ρ ho => h3 mm kk ρ ho⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k3_readers_at
#print axioms ProofFile.Honest.FirstThread.k1_rels_at
