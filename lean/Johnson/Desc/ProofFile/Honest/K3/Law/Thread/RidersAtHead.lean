-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RidersAtHead.lean: the kind "lookup" (K3): `Behind`
(Honest/Thread/Pays.lean) at a lookup's member, called at the letters `lettersHead`
(Honest/Thread/FirstHead.lean) under the library's hypothesis `P5J.AtMgA`, with their letter for the
riders given as a list of clauses. The theorems conclude `Behind` only from a hypothesis (`hFormOf`)
that is itself one of its three conjuncts: they do not show `Behind` outright. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: `Behind T b` (Honest/Thread/Pays.lean) is a form of
hypothesis at the member number b, with three conjuncts behind the member's accepted step: the form
behind, the rider behind, and keeps. `BehindS` (Honest/Thread/PaysS.lean) is the same from the pair:
the thread's relation with a sentence Said beside it.

What is shown.
  `k3KeepsAt_out`: the lookups' clause by place leaves what the chain hands on (the field out) as it
    was.
  `behind_of_pay_and`, `behindS_of_pay_and`: `behind_of_pay`
    (Honest/K3/Law/Thread/RidersAtSite.lean) over `behind_of_keeps_and`
    (Honest/Thread/RidersAnd.lean): the rider is a sentence R₀ and a list of clauses.
    `behindS_of_pay_and` takes `hl` in the form `LaysAtS`; `behindS_of_pay` (RidersAtSite.lean)
    takes it in the form `LaysAt`.
  `behind_atPlace_and`, `behindS_atPlace_and`: the same at a site, the thread a variable.
  `behind_lettersHead`, `behindS_lettersHead`: the call at `lettersHead`.

What the call shows, of the hypotheses on the thread's letters that
Honest/K3/Law/Thread/RidersAtPlace.lean leaves:
  `hKeeps`: by `head_keepsAt` (Honest/Thread/HeadForm.lean: keeps at a member is the letter Kp at
    that member's own place) and `hKp`.
  `hr`: by `head_rides_and` (Honest/Thread/RidersAnd.lean), by unfolding.
  `h₀`: the reply's clause one border on (`head_reply_next`, Honest/Thread/RidersAnd.lean): a
    lookup's member leaves the reply as it was: `k3KeepsAt_out`.

Hypotheses that remain in the call.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hS`: the structure `K3AtSite` (Honest/K3/Law/Thread/AtThreadSite.lean) at that thread.
  `hKp`: see below.
  `hb`: a member, blk, stands at number b of the thread's list.
  `hb₀`: the lookup's member is not the one in front of the border from which the reply's clause
    speaks: an inequality of numbers, on public data.
  `hFormOf`, the form behind: one of the three conjuncts of `Behind`, under the prefix of `Behind`
    itself and two facts more: the lookups' clause `k3KeepsAt` from the state in front to the state
    behind, and the lookup's promise behind (`k3OnOut`).
  `hst`: each clause that spans b stays; by Honest/Thread/Riders.lean it is no kind's to show.
  `hl`: each clause that begins at b + 1 is laid.
The letter for "keeps" by place, Kp, is a variable. `hKp`: at the site's own place it is the
lookups' clause `k3KeepsAt` (Honest/K3/Law/Thread/K3KeepsAt.lean), in both directions; the two
proofs use one direction alone, from the lookups' clause to Kp. So the theorems hold at every value
of that letter that has the lookups' clause there. At `kpBy` (Honest/Thread/KeepsBy.lean):
`hKp_kind` (Honest/K3/Law/Thread/KeepsKind.lean [not in this library]) shows `hKp`, where f at the
kind K3 is the lookups' clause; see also Honest/K3/Law/Thread/KeepsAtKind.lean [not in this
library].

Imported. Files under Honest/Thread/.

In the others. `k3KeepsAt_out`: `h`, `hs`, `hT3`: the clause at the site's place; the site; one test
with code on public data, on the slots in use. `behind_of_pay_and`, `behindS_of_pay_and`: `hFront`:
from the thread in front, the lookup's promise in front; `hPay`: from that promise and the member's
accepting step, Kp and the promise behind; `hKeeps`: Kp gives the thread's keeps; `hFormOf`, `hst`,
`hl`: as above; `hr`, `h₀`: the thread's rider is a sentence R₀ and the list of clauses; R₀ holds
behind. The local notation "LH" in the last two statements is `lettersHead` at `h` and at twelve
letters more.

Users. `behind_headSite` and `behindS_headSite` (Honest/K3/Law/Thread/RidersAtHeadSite.lean) call
`behind_lettersHead` and `behindS_lettersHead`.

Limits. At the full size alone: that limit comes with the letters `lettersHead`. Nothing here shows
that the thread's relation holds at any run. The proofs of `behind_lettersHead` and
`behindS_lettersHead` unfold `Thr` (Honest/Thread/Thr.lean) and take its conjuncts by position, so
they depend on the version of that file over which this one is written. No instance of these
hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RidersAnd
import Johnson.Desc.ProofFile.Honest.Thread.HeadForm
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RidersAtPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn Strs)
open VerifiableInference.Desc.K3 (k3OnIn k3OnOut)
open VerifiableInference.Desc.First.Look (P)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead head_keepsAt head_rides_and head_reply_next Script WtF)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **The lookups' clause by place leaves what the chain hands on as it was.** Conditional on the
site and on one public test, on the slots in use. -/
theorem k3KeepsAt_out {Z : Pub} {s : Site} {st s' : FS} (h : k3KeepsAt Z s.at_.place st s')
    (hs : s ∈ lookSites Z)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true) : s'.out = st.out := by
  cases hd : s.digits with
  | false => exact (keepsCalls_sameBut (k3KeepsAt_calls h hs hd)).out
  | true =>
    rcases quiet_sorts hs hd hT3 with hq | ⟨used, claims, hq⟩
    · exact (keepsHead_sameBut (k3KeepsAt_head h hs hd hq)).out
    · exact (keepsDigits_sameBut (k3KeepsAt_digits h hs hd hq)).out

section
variable {Bk : ProverCoinCounts} {V W X Pb Wj : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)

/-- `behind_of_pay` where the rider is a sentence and a list of clauses. -/
theorem behind_of_pay_and {p : P} {Kp : FS → FS → Prop} {R₀ : Nat → W → FS → Prop}
    {cs : List (RiderCl W FS)} {b : Nat}
    (hFront : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), Thr T b k st m E →
      k3OnIn p st = true)
    (hPay : ∀ blk, T.bs[b]? = some blk → ∀ (st s' : FS) (n : Nat) (rs : List Fmt.RoundView)
      (c : List OpenedColumn), k3OnIn p st = true → blk.step T.ft st rs c = .ok (s', n) →
      Kp st s' ∧ k3OnOut p s' = true)
    (hKeeps : ∀ t t', Kp t t' → T.keeps b t t')
    (hFormOf : ∀ blk, T.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env)
      (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : FS),
      Thr T b k st m E → drawsFit blk.rounds ds = true → T.Stepped blk k st m E ds y cols s' →
      Kp st s' → k3OnOut p s' = true → T.Form (b + 1) k s' y.2)
    (hr : ∀ c w s, T.rides c w s ↔ R₀ c w s ∧ ridersOf cs c w s)
    (h₀ : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env) (s' : FS), Thr T b k st m E →
      Kp st s' → R₀ (b + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt T b c) : Behind T b := by
  refine behind_of_keeps_and T hr ?_ ?_ hst hl
  · intro blk hblk k st m E ds y cols s' hA hd hSt
    obtain ⟨hK, hO⟩ := hPay blk hblk st s' _ _ cols (hFront k st m E hA) hSt.2
    exact ⟨hFormOf blk hblk k st m E ds y cols s' hA hd hSt hK hO, hKeeps _ _ hK⟩
  · intro blk hblk k st m E ds y cols s' hA _ hSt
    exact h₀ k st m E s' hA (hPay blk hblk st s' _ _ cols (hFront k st m E hA) hSt.2).1

/-- The same from the pair. -/
theorem behindS_of_pay_and (Said : Nat → Coins Bk → Mid W X → Prop) {p : P}
    {Kp : FS → FS → Prop} {R₀ : Nat → W → FS → Prop} {cs : List (RiderCl W FS)} {b : Nat}
    (hFront : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), Thr T b k st m E →
      k3OnIn p st = true)
    (hPay : ∀ blk, T.bs[b]? = some blk → ∀ (st s' : FS) (n : Nat) (rs : List Fmt.RoundView)
      (c : List OpenedColumn), k3OnIn p st = true → blk.step T.ft st rs c = .ok (s', n) →
      Kp st s' ∧ k3OnOut p s' = true)
    (hKeeps : ∀ t t', Kp t t' → T.keeps b t t')
    (hFormOf : ∀ blk, T.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env)
      (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : FS),
      ThrS T Said b k st m E → drawsFit blk.rounds ds = true →
      T.Stepped blk k st m E ds y cols s' → Kp st s' → k3OnOut p s' = true →
      T.Form (b + 1) k s' y.2)
    (hr : ∀ c w s, T.rides c w s ↔ R₀ c w s ∧ ridersOf cs c w s)
    (h₀ : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env) (s' : FS), Thr T b k st m E →
      Kp st s' → R₀ (b + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAtS T Said b c) : BehindS T Said b := by
  refine behindS_of_keeps_and T Said hr ?_ ?_ hst hl
  · intro blk hblk k st m E ds y cols s' hA hd hSt
    obtain ⟨hK, hO⟩ := hPay blk hblk st s' _ _ cols (hFront k st m E hA.1) hSt.2
    exact ⟨hFormOf blk hblk k st m E ds y cols s' hA hd hSt hK hO, hKeeps _ _ hK⟩
  · intro blk hblk k st m E ds y cols s' hA _ hSt
    exact h₀ k st m E s' hA.1 (hPay blk hblk st s' _ _ cols (hFront k st m E hA.1) hSt.2).1

variable (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
  {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
  (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
  {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : W → Wj}
  (hS : K3AtSite T b Z Bs ch s lot J wit) {cs : List (RiderCl W FS)}
  {R₀ : Nat → W → FS → Prop}
include O hS

/-- **At a lookup's member, of whatever sort**, the rider a sentence and a list of clauses. -/
theorem behind_atPlace_and (hKeeps : ∀ t t', k3KeepsAt Z s.at_.place t t' → T.keeps b t t')
    (hFormOf : ∀ blk, T.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env)
      (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : FS),
      Thr T b k st m E → drawsFit blk.rounds ds = true → T.Stepped blk k st m E ds y cols s' →
      k3KeepsAt Z s.at_.place st s' → k3OnOut s.p s' = true → T.Form (b + 1) k s' y.2)
    (hr : ∀ c w s, T.rides c w s ↔ R₀ c w s ∧ ridersOf cs c w s)
    (h₀ : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env) (s' : FS), Thr T b k st m E →
      k3KeepsAt Z s.at_.place st s' → R₀ (b + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt T b c) : Behind T b :=
  behind_of_pay_and T (fun k st m E hA => (hS.front k st m E hA).1)
    (fun blk hblk st s' n rs c hIn h =>
      ⟨k3KeepsAt_pays o pol lay KL Fd Z Bs base ch A B O s.at_.place lot blk hS.inLot hS.lotPlace
        (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' n rs c h,
       onOut_atSite o pol lay KL Fd Z Bs base ch A B O s hS.site hS.usedIs lot blk hS.inLot
        hS.lotPlace (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' n rs c hIn
        h⟩)
    hKeeps hFormOf hr h₀ hst hl

/-- The same from the pair. -/
theorem behindS_atPlace_and (Said : Nat → Coins Bk → Mid W X → Prop)
    (hKeeps : ∀ t t', k3KeepsAt Z s.at_.place t t' → T.keeps b t t')
    (hFormOf : ∀ blk, T.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env)
      (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : FS),
      ThrS T Said b k st m E → drawsFit blk.rounds ds = true →
      T.Stepped blk k st m E ds y cols s' → k3KeepsAt Z s.at_.place st s' →
      k3OnOut s.p s' = true → T.Form (b + 1) k s' y.2)
    (hr : ∀ c w s, T.rides c w s ↔ R₀ c w s ∧ ridersOf cs c w s)
    (h₀ : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env) (s' : FS), Thr T b k st m E →
      k3KeepsAt Z s.at_.place st s' → R₀ (b + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAtS T Said b c) : BehindS T Said b :=
  behindS_of_pay_and T Said (fun k st m E hA => (hS.front k st m E hA).1)
    (fun blk hblk st s' n rs c hIn h =>
      ⟨k3KeepsAt_pays o pol lay KL Fd Z Bs base ch A B O s.at_.place lot blk hS.inLot hS.lotPlace
        (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' n rs c h,
       onOut_atSite o pol lay KL Fd Z Bs base ch A B O s hS.site hS.usedIs lot blk hS.inLot
        hS.lotPlace (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' n rs c hIn
        h⟩)
    hKeeps hFormOf hr h₀ hst hl

end

/-! ## The call -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X Wj : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LH" =>
  lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w

variable (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Bs : PureBase}
  (base : List (Block FS ProofFile.Cl)) (A : SharedSeat) (B : SecondSeat)
  (O : IM.Open o pol lay KL Fd Zp Bs base cF A B) {b : Nat} {s : Site} {lot : Block FS ProofFile.Cl}
  {J : LookJobs Wj} {wit : Local W₀ Rc ProofFile.Inst Tr → Wj}
include O

/-- **`Behind` at a lookup's member, at the letters `lettersHead` under `P5J.AtMgA`.** `hKeeps`,
`hr` and the reply's clause are shown; `hFormOf` remains. No instance of these hypotheses is
exhibited in this file. -/
theorem behind_lettersHead (hS : K3AtSite (LH).thread b Zp Bs cF s lot J wit)
    (hKp : ∀ t t', Kp s.at_.place t t' ↔ k3KeepsAt Zp s.at_.place t t')
    {blk : Block FS ProofFile.Cl} (hb : (LH).thread.bs[b]? = some blk) (hb₀ : b₀ ≠ b + 1)
    (hFormOf : ∀ blk, (LH).thread.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS)
      (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env) (ds : List Fmt.Drawn)
      (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X) (cols : List OpenedColumn) (s' : FS),
      Thr (LH).thread b k st m E → drawsFit blk.rounds ds = true →
      (LH).thread.Stepped blk k st m E ds y cols s' → k3KeepsAt Zp s.at_.place st s' →
      k3OnOut s.p s' = true → (LH).thread.Form (b + 1) k s' y.2)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy (LH).thread b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt (LH).thread b c) : Behind (LH).thread b := by
  have hpl : blk.place = s.at_.place := (hS.place blk hb).trans hS.lotPlace
  refine behind_atPlace_and (LH).thread o pol lay KL Fd base A B O hS
    (R₀ := fun c v t => b₀ ≤ c → t.out.reply = some v.x.asked) ?_ hFormOf
    (head_rides_and h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w) ?_ hst hl
  · intro t t' hk
    refine (head_keepsAt h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w hb t
      t').2 ?_
    rw [hpl]
    exact (hKp t t').2 hk
  · intro k st m E s' hA hk
    have hA' := hA
    unfold Thr at hA'
    have hR := ((head_rides_and h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w b
      m.st.input st).1 hA'.2.2.2.2.2.1).1
    exact head_reply_next (asked := fun v : Local W₀ Rc ProofFile.Inst Tr => v.x.asked) hR
      (fun e => absurd e hb₀)
      (fun _ => by rw [k3KeepsAt_out hk hS.site hS.usedIs])

/-- **The same from the pair.** No instance of these hypotheses is exhibited in this file. -/
theorem behindS_lettersHead (hS : K3AtSite (LH).thread b Zp Bs cF s lot J wit)
    (hKp : ∀ t t', Kp s.at_.place t t' ↔ k3KeepsAt Zp s.at_.place t t')
    {blk : Block FS ProofFile.Cl} (hb : (LH).thread.bs[b]? = some blk) (hb₀ : b₀ ≠ b + 1)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hFormOf : ∀ blk, (LH).thread.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS)
      (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env) (ds : List Fmt.Drawn)
      (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X) (cols : List OpenedColumn) (s' : FS),
      ThrS (LH).thread Said b k st m E → drawsFit blk.rounds ds = true →
      (LH).thread.Stepped blk k st m E ds y cols s' → k3KeepsAt Zp s.at_.place st s' →
      k3OnOut s.p s' = true → (LH).thread.Form (b + 1) k s' y.2)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy (LH).thread b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAtS (LH).thread Said b c) :
    BehindS (LH).thread Said b := by
  have hpl : blk.place = s.at_.place := (hS.place blk hb).trans hS.lotPlace
  refine behindS_atPlace_and (LH).thread o pol lay KL Fd base A B O hS Said
    (R₀ := fun c v t => b₀ ≤ c → t.out.reply = some v.x.asked) ?_ hFormOf
    (head_rides_and h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w) ?_ hst hl
  · intro t t' hk
    refine (head_keepsAt h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w hb t
      t').2 ?_
    rw [hpl]
    exact (hKp t t').2 hk
  · intro k st m E s' hA hk
    have hA' := hA
    unfold Thr at hA'
    have hR := ((head_rides_and h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w b
      m.st.input st).1 hA'.2.2.2.2.2.1).1
    exact head_reply_next (asked := fun v : Local W₀ Rc ProofFile.Inst Tr => v.x.asked) hR
      (fun e => absurd e hb₀)
      (fun _ => by rw [k3KeepsAt_out hk hS.site hS.usedIs])

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.k3KeepsAt_out
#print axioms ProofFile.Honest.K3.Law.AtThr.behind_of_pay_and
#print axioms ProofFile.Honest.K3.Law.AtThr.behindS_of_pay_and
#print axioms ProofFile.Honest.K3.Law.AtThr.behind_atPlace_and
#print axioms ProofFile.Honest.K3.Law.AtThr.behindS_atPlace_and
#print axioms ProofFile.Honest.K3.Law.AtThr.behind_lettersHead
#print axioms ProofFile.Honest.K3.Law.AtThr.behindS_lettersHead
