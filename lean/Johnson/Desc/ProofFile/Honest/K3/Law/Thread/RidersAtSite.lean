-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RidersAtSite.lean: the kind "lookup" (K3): what the
lookups' files show, and what they leave as hypotheses, where a thread's rider is a list of clauses
(Honest/Thread/Riders.lean). The theorems on `Behind` (Honest/Thread/Pays.lean) conclude it only
from a hypothesis (`hFormOf`) that is itself one of its three conjuncts: they do not show `Behind`
outright. The thread is a variable. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: `Behind T b` (Honest/Thread/Pays.lean) is a form of
hypothesis at the member number b, with three conjuncts behind the member's accepted step: the form
behind, the rider behind, and keeps. `BehindS` (Honest/Thread/PaysS.lean) is the same from the pair:
the thread's relation with a sentence Said beside it. The member number b of a thread T lays the
clause c if c holds behind the member's own accepted step: `LaysAt T b c`
(Honest/Thread/Riders.lean).

What is shown.
  `lays_claim`: the lookups' own clause: the member at the digits of the head's link lays "the claim
    on the weights is laid": `LaysAt` at that member.
  `atSite_headReturns`: the structure `K3AtSite` (Honest/K3/Law/Thread/AtThreadSite.lean) with its
    field headReturns given by `headReturns_of_thr` (Honest/K3/Law/Thread/HeadReturnsOf.lean). Its
    conclusion is its own hypothesis `hS` again: what Lean checks is that the theorem's conclusion
    and the field's text are one.
  `behind_of_pay`: `Behind` by `behind_of_keeps` (Honest/Thread/Riders.lean), at letters for the
    clause of keeps and the lookup's parameters.
  `behindS_of_pay`: the same from the pair.
  `behind_atCalls`, `behind_atDigits`, `behind_atHead`: the same at a site, one theorem for each
    sort of member.
  `behindS_atCalls`: at the calls, from the pair.

What the theorems `behind_at…` show and what they leave. Shown from the lookups' own theorems: keeps
(the clauses of Honest/K3/Law/KeepsDefs.lean and the theorems of Honest/K3/Law/Thread/K3Keeps.lean)
and, towards the form, the lookup's promise behind (Honest/K3/Law/Thread/OnOutMember.lean). Left as
hypotheses, by name, each on the thread's letters:
  `hKeeps`: the lookups' clause gives the thread's keeps at b.
  `hFormOf`, the form behind: the first conjunct of `Behind`, under the prefix of `Behind` itself
    (the thread's relation in front, the challenges' test, the step), with two more facts given to
    whoever shows it: the lookups' clause and the lookup's promise behind. It is one of the three
    conjuncts, left as a hypothesis. It cannot be cut down to an implication between the form at b
    and at b + 1: at the first chain's letters the form behind a lookup on the calls rests on the
    library's law at reached states and on the decision on the played rounds. That its form fits the
    theorems that conclude the form behind there: Honest/K3/Law/Thread/RidersBridge.lean
    [not in this library]. By that file's head it
    is had there only under these theorems' own hypotheses: `SiteAt`, `HeadReturns`, two on the
    letters' meaning, public facts on the list of places and the links, one on the stored tables'
    words, and other kinds' public items behind the lookup's step, which had not been shown.
  `hr`: the thread's rider is a list of clauses.
  `hst`: each clause that spans b stays. It follows from keeps alone; by Honest/Thread/Riders.lean
    it is no kind's to show.
  `hl`: each clause that begins at b + 1 is laid. At the head's digits the lookups' own is:
    `lays_claim`.
So these theorems do not show `Behind` outright: two of its three conjuncts (keeps; the rider) come
from the lookups' theorems and `behind_of_keeps`; the third is left as a named hypothesis.

Hypotheses that remain besides.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hS`: the structure `K3AtSite`.
  `hq`: at the digits: which step without a round stands behind the lookup (a condition on public
    data).
  `hd`: the site's sort. `hFront`, `hPay`: (in `behind_of_pay`, `behindS_of_pay`) from the thread in
    front, the lookup's promise in front; from that promise and the member's accepting step, the
    clause of keeps and the promise behind. `hHead`, `hN`, `hRest`: (in `atSite_headReturns`) those
    of `headReturns_of_thr` (Honest/K3/Law/Thread/HeadReturnsOf.lean).

Imported. Files under Honest/Thread/.

Users. `behind_atPlace` and `behindS_atPlace` (Honest/K3/Law/Thread/RidersAtPlace.lean) call
`behind_of_pay` and `behindS_of_pay`; `lays_of_claim` (Honest/K3/Law/Thread/LaysNext.lean) calls
`lays_claim`.

Limits. Nothing here shows that a thread with such letters exists. `hr` is a hypothesis of
`behind_of_keeps` itself. At the letters `lettersHead` (Honest/Thread/FirstHead.lean), on a reading
of that file, the rider is the reply's clause, which has no last border, and a
letter: it is not, to the letter, a list of clauses; whether `hr` can be met there is not stated
here. Honest/K3/Law/Thread/RidersAtHead.lean treats a rider that is a sentence and a list of
clauses. In `behind_atCalls`, `behind_atDigits` and `behind_atHead` the hypothesis `hKeeps` goes
from the clause at the one site; where keeps is given by place see
Honest/K3/Law/Thread/RidersAtPlace.lean. On the verifier's side and the frame's own play alone.
No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Riders
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.OnOutMember
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadReturnsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (quietAt quietDigits quietHead k3OnIn k3OnOut)
open VerifiableInference.Desc.First.Look (P weightsClaim)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {V W X Pb Wj : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)

/-- **`Behind` from a hypothesis at the member's step (`hPay`) and five hypotheses on the letters.**
-/
theorem behind_of_pay {p : P} {Kp : FS → FS → Prop} {cs : List (RiderCl W FS)} {b : Nat}
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
    (hr : ∀ c w s, T.rides c w s ↔ ridersOf cs c w s)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt T b c) : Behind T b := by
  refine behind_of_keeps T hr ?_ hst hl
  intro blk hblk k st m E ds y cols s' hA hd hSt
  obtain ⟨hK, hO⟩ := hPay blk hblk st s' _ _ cols (hFront k st m E hA) hSt.2
  exact ⟨hFormOf blk hblk k st m E ds y cols s' hA hd hSt hK hO, hKeeps _ _ hK⟩

/-- **The same from the pair** (Honest/Thread/PaysS.lean): the thread's relation with a sentence
Said beside it. -/
theorem behindS_of_pay (Said : Nat → Coins Bk → Mid W X → Prop) {p : P} {Kp : FS → FS → Prop}
    {cs : List (RiderCl W FS)} {b : Nat}
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
    (hr : ∀ c w s, T.rides c w s ↔ ridersOf cs c w s)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt T b c) : BehindS T Said b := by
  refine behindS_of_keeps T Said hr ?_ hst hl
  intro blk hblk k st m E ds y cols s' hA hd hSt
  obtain ⟨hK, hO⟩ := hPay blk hblk st s' _ _ cols (hFront k st m E hA.1) hSt.2
  exact ⟨hFormOf blk hblk k st m E ds y cols s' hA hd hSt hK hO, hKeeps _ _ hK⟩

section
variable (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
  {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
  (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
  {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : W → Wj}
  (hS : K3AtSite T b Z Bs ch s lot J wit)
include O hS

/-- **The lookups' own clause of the rider is laid.** No instance of these hypotheses is exhibited
in this file. -/
theorem lays_claim (hd : s.digits = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X)) (hi : Nat) :
    LaysAt T b (riderHead (b + 1) hi fun a => a.claim.isSome = true) := by
  intro blk hblk k st m E ds y cols s' _ _ hSt
  obtain ⟨_, hstep⟩ := hSt
  obtain ⟨_, tl, F, H, G, a₀, claim, _, _, _, _, e, _⟩ := k3Keeps_head o pol lay KL Fd Z Bs base ch
    A B O s hS.site hd lot blk hS.inLot hS.lotPlace (hS.mem blk hblk) (hS.place blk hblk)
    (hS.plan blk hblk) hq T.ft st s' _ _ cols hstep
  show ∃ a, s'.here = .head a ∧ a.claim.isSome = true
  exact ⟨_, by rw [e], rfl⟩

variable {cs : List (RiderCl W FS)}

/-- **At a lookup on the calls.** No instance of these hypotheses is exhibited in this file. At the
first chain's letters Honest/K3/Law/Thread/RidersBridge.lean [not in this library] gives `hFormOf`
for `behindS_atCalls`, not for this theorem:
there the form behind rests on the library's "reached", which is had from the pair alone. A caller
should take `behindS_atCalls`. -/
theorem behind_atCalls (hd : s.digits = false)
    (hKeeps : ∀ t t', K3KeepsCalls s.shape t t' → T.keeps b t t')
    (hFormOf : ∀ blk, T.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env)
      (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : FS),
      Thr T b k st m E → drawsFit blk.rounds ds = true → T.Stepped blk k st m E ds y cols s' →
      K3KeepsCalls s.shape st s' → k3OnOut s.p s' = true → T.Form (b + 1) k s' y.2)
    (hr : ∀ c w s, T.rides c w s ↔ ridersOf cs c w s)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt T b c) : Behind T b :=
  behind_of_pay T (fun k st m E hA => (hS.front k st m E hA).1)
    (fun blk hblk st s' n rs c hIn h =>
      ⟨k3Keeps_calls o pol lay KL Fd Z Bs base ch A B O s hS.site hd lot blk hS.inLot hS.lotPlace
        (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' n rs c h,
       onOut_atCalls o pol lay KL Fd Z Bs base ch A B O s hS.site hd lot blk hS.inLot hS.lotPlace
        (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' n rs c hIn h⟩)
    hKeeps hFormOf hr hst hl

/-- **At a lookup on the calls, from the pair.** No instance of these hypotheses is exhibited in
this file. -/
theorem behindS_atCalls (Said : Nat → Coins Bk → Mid W X → Prop) (hd : s.digits = false)
    (hKeeps : ∀ t t', K3KeepsCalls s.shape t t' → T.keeps b t t')
    (hFormOf : ∀ blk, T.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env)
      (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : FS),
      ThrS T Said b k st m E → drawsFit blk.rounds ds = true →
      T.Stepped blk k st m E ds y cols s' → K3KeepsCalls s.shape st s' →
      k3OnOut s.p s' = true → T.Form (b + 1) k s' y.2)
    (hr : ∀ c w s, T.rides c w s ↔ ridersOf cs c w s)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt T b c) : BehindS T Said b :=
  behindS_of_pay T Said (fun k st m E hA => (hS.front k st m E hA).1)
    (fun blk hblk st s' n rs c hIn h =>
      ⟨k3Keeps_calls o pol lay KL Fd Z Bs base ch A B O s hS.site hd lot blk hS.inLot hS.lotPlace
        (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' n rs c h,
       onOut_atCalls o pol lay KL Fd Z Bs base ch A B O s hS.site hd lot blk hS.inLot hS.lotPlace
        (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' n rs c hIn h⟩)
    hKeeps hFormOf hr hst hl

/-- **At a lookup on the digits of a layers' or an attention link.** No instance of these hypotheses
is exhibited in this file. -/
theorem behind_atDigits (hd : s.digits = true) (used claims : Nat)
    (hq : quietAt Z.p.X s.link true = some (quietDigits used claims))
    (hKeeps : ∀ t t', K3KeepsDigits s.shape claims t t' → T.keeps b t t')
    (hFormOf : ∀ blk, T.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env)
      (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : FS),
      Thr T b k st m E → drawsFit blk.rounds ds = true → T.Stepped blk k st m E ds y cols s' →
      K3KeepsDigits s.shape claims st s' → k3OnOut s.p s' = true → T.Form (b + 1) k s' y.2)
    (hr : ∀ c w s, T.rides c w s ↔ ridersOf cs c w s)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt T b c) : Behind T b :=
  behind_of_pay T (fun k st m E hA => (hS.front k st m E hA).1)
    (fun blk hblk st s' n rs c hIn h =>
      ⟨k3Keeps_digits o pol lay KL Fd Z Bs base ch A B O s hS.site hd lot blk hS.inLot hS.lotPlace
        (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) used claims hq T.ft st s' n rs c
        h,
       onOut_atDigits o pol lay KL Fd Z Bs base ch A B O s hS.site hd lot blk hS.inLot hS.lotPlace
        (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) used claims hq T.ft st s' n rs c
        hIn h⟩)
    hKeeps hFormOf hr hst hl

/-- **At the lookup on the digits of the head's link.** No instance of these hypotheses is exhibited
in this file. -/
theorem behind_atHead (hd : s.digits = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X))
    (hKeeps : ∀ t t', K3KeepsHead s.shape t t' → T.keeps b t t')
    (hFormOf : ∀ blk, T.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env)
      (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : FS),
      Thr T b k st m E → drawsFit blk.rounds ds = true → T.Stepped blk k st m E ds y cols s' →
      K3KeepsHead s.shape st s' → k3OnOut s.p s' = true → T.Form (b + 1) k s' y.2)
    (hr : ∀ c w s, T.rides c w s ↔ ridersOf cs c w s)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt T b c) : Behind T b :=
  behind_of_pay T (fun k st m E hA => (hS.front k st m E hA).1)
    (fun blk hblk st s' n rs c hIn h =>
      ⟨k3Keeps_head o pol lay KL Fd Z Bs base ch A B O s hS.site hd lot blk hS.inLot hS.lotPlace
        (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) hq T.ft st s' n rs c h,
       onOut_atHead o pol lay KL Fd Z Bs base ch A B O s hS.site hd lot blk hS.inLot hS.lotPlace
        (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) hq T.ft st s' n rs c hIn h⟩)
    hKeeps hFormOf hr hst hl

end

/-- **The structure with its field headReturns given by `headReturns_of_thr`**: Lean checks that
the theorem's conclusion is the field's own text. -/
theorem atSite_headReturns {b : Nat} {Z : Pub} {Bs : PureBase} {ch : Chain FS ProofFile.Cl} {s : Site}
    {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : W → Wj}
    (hS : K3AtSite T b Z Bs ch s lot J wit)
    (hHead : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), Thr T b k st m E →
      ∃ a, st.here = .head a ∧ a.opened = true ∧ a.x.isSome = true ∧ a.t.isSome = true)
    (hN : (Z.p.X.H.NCL == 1) = true)
    (hRest : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env) a x tt, Thr T b k st m E →
      st.here = .head a → a.x = some x → a.t = some tt →
      ∃ cov claim, st.covered Z.p.X.T Z.p.X.P.h.V = .ok cov ∧ weightsClaim
        { h := Z.p.X.hS, L := Z.p.X.HLy, b := OnBytes.Model.Verify.borderOf Z.p.X.y,
          hp := Z.p.X.H, cov := cov, x := x, t := tt,
          iU3 := (Z.p.X.H.tl.ix.U.getD 2 none).getD 0 } Z.p.X.layers.wsLay = .ok claim) :
    K3AtSite T b Z Bs ch s lot J wit :=
  { hS with headReturns := headReturns_of_thr T b Z s hHead hN hRest }

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.behind_of_pay
#print axioms ProofFile.Honest.K3.Law.AtThr.behindS_of_pay
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_claim
#print axioms ProofFile.Honest.K3.Law.AtThr.behind_atCalls
#print axioms ProofFile.Honest.K3.Law.AtThr.behindS_atCalls
#print axioms ProofFile.Honest.K3.Law.AtThr.behind_atDigits
#print axioms ProofFile.Honest.K3.Law.AtThr.behind_atHead
#print axioms ProofFile.Honest.K3.Law.AtThr.atSite_headReturns
