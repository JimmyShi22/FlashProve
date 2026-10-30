-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RidersAtPlace.lean: the kind "lookup" (K3): `Behind`
(Honest/Thread/Pays.lean) at a lookup's member, with the lookups' clause of "keeps" taken by place
(`k3KeepsAt`, Honest/K3/Law/Thread/K3KeepsAt.lean): one theorem for all three sorts of member. The
theorems conclude `Behind` only from a hypothesis (`hFormOf`) that is itself one of its three
conjuncts: they do not show `Behind` outright. The thread is a variable. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: `Behind T b` (Honest/Thread/Pays.lean) is a form of
hypothesis at the member number b, with three conjuncts behind the member's accepted step: the form
behind, the rider behind, and keeps. `BehindS` (Honest/Thread/PaysS.lean) is the same from the pair:
the thread's relation with a sentence Said beside it.

Why beside Honest/K3/Law/Thread/RidersAtSite.lean. There `hKeeps` goes from the clause at the one
site to the thread's keeps. Where keeps is given by place as `k3KeepsAt Z p`, that hypothesis would
ask the clause at every site at the place: it wants "no two sites share a place", which is not shown
in this file. Since: `site_of_place` (Honest/K3/Law/Thread/SitesOnce.lean) shows it, at every public
part. Here `hKeeps` goes from `k3KeepsAt Z s.at_.place` itself: where keeps at b is that sentence,
it is the identity.

What is shown.
  `behind_atPlace`: `Behind T b`.
  `behindS_atPlace`: `BehindS T Said b`: from the pair.
Shown from the lookups' own theorems: the clause (`k3KeepsAt_pays`,
Honest/K3/Law/Thread/K3KeepsAt.lean) and the lookup's promise behind (`onOut_atSite`,
Honest/K3/Law/Thread/QuietSorts.lean): no hypothesis says which sort of site it is.

Hypotheses that remain.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hS`: the structure `K3AtSite` (Honest/K3/Law/Thread/AtThreadSite.lean).
  Left by name, as in RidersAtSite.lean: `hKeeps`; `hFormOf`, the form behind: one of the three
    conjuncts of `Behind`, under the prefix of `Behind` itself; `hr`, `hst`, `hl`: the three of
    `behind_of_keeps` (Honest/Thread/Riders.lean) itself.
That the form of `hFormOf` fits the theorems that conclude the form behind at the first chain's
letters: Honest/K3/Law/Thread/RidersBridgePlace.lean [not in this library].
By that file's head it is had there only under these theorems' own
hypotheses, other kinds' public items behind the lookup's step among them, which had not been shown.

Imported, through Honest/K3/Law/Thread/RidersAtSite.lean. Files under Honest/Thread/.

Users. Honest/K3/Law/Thread/RidersAtHead.lean imports this file.

Limits. Those of Honest/K3/Law/Thread/RidersAtSite.lean; above all: whether `hr` can be met at the
letters `lettersHead` (Honest/Thread/FirstHead.lean) is not stated here. No instance of these
hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RidersAtSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3KeepsAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.QuietSorts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (k3OnOut)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {V W X Pb Wj : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)
  (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
  {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
  (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
  {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : W → Wj}
  (hS : K3AtSite T b Z Bs ch s lot J wit) {cs : List (RiderCl W FS)}
include O hS

/-- **At a lookup's member, of whatever sort.** No instance of these hypotheses is exhibited in this
file. -/
theorem behind_atPlace (hKeeps : ∀ t t', k3KeepsAt Z s.at_.place t t' → T.keeps b t t')
    (hFormOf : ∀ blk, T.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env)
      (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : FS),
      Thr T b k st m E → drawsFit blk.rounds ds = true → T.Stepped blk k st m E ds y cols s' →
      k3KeepsAt Z s.at_.place st s' → k3OnOut s.p s' = true → T.Form (b + 1) k s' y.2)
    (hr : ∀ c w s, T.rides c w s ↔ ridersOf cs c w s)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt T b c) : Behind T b :=
  behind_of_pay T (fun k st m E hA => (hS.front k st m E hA).1)
    (fun blk hblk st s' n rs c hIn h =>
      ⟨k3KeepsAt_pays o pol lay KL Fd Z Bs base ch A B O s.at_.place lot blk hS.inLot hS.lotPlace
        (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' n rs c h,
       onOut_atSite o pol lay KL Fd Z Bs base ch A B O s hS.site hS.usedIs lot blk hS.inLot
        hS.lotPlace (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' n rs c hIn
        h⟩)
    hKeeps hFormOf hr hst hl

/-- **The same from the pair.** No instance of these hypotheses is exhibited in this file. -/
theorem behindS_atPlace (Said : Nat → Coins Bk → Mid W X → Prop)
    (hKeeps : ∀ t t', k3KeepsAt Z s.at_.place t t' → T.keeps b t t')
    (hFormOf : ∀ blk, T.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env)
      (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : FS),
      ThrS T Said b k st m E → drawsFit blk.rounds ds = true →
      T.Stepped blk k st m E ds y cols s' → k3KeepsAt Z s.at_.place st s' →
      k3OnOut s.p s' = true → T.Form (b + 1) k s' y.2)
    (hr : ∀ c w s, T.rides c w s ↔ ridersOf cs c w s)
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAt T b c) : BehindS T Said b :=
  behindS_of_pay T Said (fun k st m E hA => (hS.front k st m E hA).1)
    (fun blk hblk st s' n rs c hIn h =>
      ⟨k3KeepsAt_pays o pol lay KL Fd Z Bs base ch A B O s.at_.place lot blk hS.inLot hS.lotPlace
        (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' n rs c h,
       onOut_atSite o pol lay KL Fd Z Bs base ch A B O s hS.site hS.usedIs lot blk hS.inLot
        hS.lotPlace (hS.mem blk hblk) (hS.place blk hblk) (hS.plan blk hblk) T.ft st s' n rs c hIn
        h⟩)
    hKeeps hFormOf hr hst hl

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.behind_atPlace
#print axioms ProofFile.Honest.K3.Law.AtThr.behindS_atPlace
