-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Accepted.lean: CONDITIONAL: the yes of the member of the first
chain that stands at an attention segment's own rounds (kind K5), in the form of the debt `Accepted`
(Honest/Thread/Pays.lean); and what the state behind such a yes is.

The kind's decision compares no value (Johnson/Desc/K5/Honest/Law/Returns.lean). So the yes follows
from the state's book-keeping in front and from the shape of the rounds as played, for every letter
`fall`: the kind has no test that could fail on a prover's coin.

  `step_is`       GENERAL in `Thread`: at rounds as played and columns as laid, the member's step
                  says yes with a state just where the kind's decision does, the state bears no
                  mark, and the reply is as in front
  `behind_is`     GENERAL in `Thread`: the state behind a member's step is `behind s a hd G`, with
                  hd and G the hearing's return from the open ledger at the rounds as played
  `accepted_of_ready`   GENERAL in `Thread`, CONDITIONAL: from "`Thr` in front gives a ready
                  state": `Accepted T fall b`. That the rounds as played have the plan's shape is
                  `fits_of_played` (Honest/K5/Law/Plays.lean)
  `seated_decides`   under the hypothesis `P5J.AtMgA`: the member of `K5Seated` is the
                  one of which `k5_member` speaks
  `k5_accepted`   CONDITIONAL: **`Accepted` at the kind's member of group g of the first chain's
                  `Thread` at the library's own letters, for every fall**

Which road. The yes is shown outright, from the table's own promise at the border: its test on where
the chain stands and three of its public items (the ledger, "free above", the caller's condition in
front), by the library's lemmas; no projection of the state onto a shape is used.

Who is meant to pay the premises of `k5_accepted`. h: not shown here. `K5Seated`: whoever lays the
list of halves (`Thread.hs`) and makes the place's public data.

Limits. Every theorem is conditional. Where `Thr` holds at no run `Accepted` is met for
nothing. No value that is sent is spoken of.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.Returns
import Johnson.Desc.ProofFile.Honest.K5.Law.Ready
import Johnson.Desc.ProofFile.Honest.K5.Law.Plays

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place OpenedColumn Strs Chain Claim First.S noDigest)
open VerifiableInference.Desc.First.Att.P
open H2K5.Honest (k5_returns k5_yes_is)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

/-! ## 1 General in `Thread` -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
  {b : Nat} {cells : Tr → Cells} {Z5 : Seat5} {p : Par} {blk : Block First.S Claim}

/-- **The member's step, at rounds as played and columns as laid, against the kind's decision.**
CONDITIONAL: `K5Seated`, "blk decides as the kind's decision", and the prover's side of the
step. An equivalence: no yes is concluded. -/
theorem step_is (Hs : K5Seated T b cells Z5 p blk) (Dc : DecidesAs p blk)
    {k : Coins Bk} (s s' : First.S) {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols) :
    blk.step T.ft s (roundsOf y.1) cols = .ok (s', cols.length) ↔
      decide seatSO p s ((roundsOf y.1).map noDigest) = .ok s' ∧ s'.failed = none ∧
        ProofFile.sameReply s s' = true := by
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  obtain ⟨ho, hr⟩ := half_counts Hs.half hl
  obtain ⟨c, -, rfl⟩ := steps_one_half Hs.half hl
  exact (step_iff_decide s s' hr ho hy hd hc).trans (Dc.decides _ _ _ _)

/-- **What the state behind a member's step is.** CONDITIONAL: as `step_is`, with the step's yes in
hand. -/
theorem behind_is (Hs : K5Seated T b cells Z5 p blk) (Dc : DecidesAs p blk)
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hd : drawsFit blk.rounds ds = true) (hS : T.Stepped blk k s m E ds y cols s') :
    ∃ a hd5 G, s.here = .att a ∧
      hear p.own (a.F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, [], 0) ∧
      s' = behind s a hd5 G :=
  k5_yes_is p ((step_is T Hs Dc s s' hd hS.1).1 hS.2).1

/-- **The yes.** CONDITIONAL: `K5Seated`; "blk decides as the kind's decision"; hR: `Thr`
in front gives a ready state. For every letter fall. -/
theorem accepted_of_ready (Hs : K5Seated T b cells Z5 p blk) (Dc : DecidesAs p blk)
    (hR : ∀ k s m E, Thr T b k s m E → ReadyO p s)
    (fall : Nat → First.S → List Fmt.Drawn → Option String) : Accepted T fall b := by
  intro blk' hblk' k s m E ds y cols hA hd _ _ hMv
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hblk')
  have R := hR k s m E hA
  obtain ⟨a, hd5, G, -, -, hdec⟩ := k5_returns p Dc.plan R (fits_of_played T Hs hd hMv)
  exact ⟨behind s a hd5 G, hMv,
    (step_is T Hs Dc s _ hd hMv).2 ⟨hdec, R.clean, same_of_out s _ rfl⟩⟩

end

/-! ## 2 At the library's own letters -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

include h in
/-- The member at the kind's border decides as the kind's decision. CONDITIONAL: under the
hypothesis h; a is the plan of group g; blk is the member at the border. -/
theorem seated_decides {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[borderOf g]? = some blk) : PlanAt Zp g a ∧ DecidesAs (parAt Zp g a) blk := by
  obtain ⟨blk', a', hfl, Pl, Dc⟩ := k5_member h hg
  obtain rfl : blk' = blk := Option.some.inj (hfl.symm.trans hb)
  obtain rfl : a' = a := Option.some.inj (Pl.plan.symm.trans ha)
  exact ⟨Pl, Dc⟩

/-- **IT IS ACCEPTED, AT THE KIND's MEMBER OF GROUP g, FOR EVERY fall.** CONDITIONAL: under the
hypothesis h and `K5Seated`. -/
theorem k5_accepted {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    Accepted (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) fall
      (borderOf g) := by
  obtain ⟨Pl, Dc⟩ := seated_decides h hg ha Hs.member
  exact accepted_of_ready _ Hs Dc
    (fun k s m E hT =>
      readyO_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg Pl hT)
    fall

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.step_is
#print axioms ProofFile.Honest.K5.behind_is
#print axioms ProofFile.Honest.K5.accepted_of_ready
#print axioms ProofFile.Honest.K5.seated_decides
#print axioms ProofFile.Honest.K5.k5_accepted
