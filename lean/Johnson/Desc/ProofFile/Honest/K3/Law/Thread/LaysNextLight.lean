-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LaysNextLight.lean: the kind "lookup" (K3): the clause
"the ledger's next free slot" of a thread's rider, which the lookup on the digits of the head's link
lays, in a light form: under what its proof uses and no more; then at the thread of `lettersHead`
(Honest/Thread/FirstHead.lean), which is stated under the library's hypothesis `P5J.AtMgA`
(Johnson/P5J/MgAtAll.lean); then with the slot as a closed term, and as a numeral. In the form
`LaysAt` (Honest/Thread/Riders.lean). Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: the member number b of a thread T lays the clause c if c
holds behind the member's own accepted step: `LaysAt T b c` (Honest/Thread/Riders.lean). The
sentence on the slot: the chain stands in the head's link, and the next free slot of that link's own
ledger is the lookup's first slot plus its number of hidden values (`OnBytes.Model.Forest.elems` of
its shape).

Why. `lays_of_nextHead` (Honest/K3/Law/Thread/LaysNext.lean) assumes the whole structure `K3AtSite`
(Honest/K3/Law/Thread/AtThreadSite.lean), of 16 fields. Its proof names 8 of them. Among the 8 that
it does not name are the field ok, "the face passes the hearing's own test on its numbers",
and the field half, on the prover's
halves. So, as it is stated, it asks at the thread of `lettersHead`
fields that its proof does not read. That file is
not imported here. `face_ok_site` (Johnson/AtFull/Shape/FaceAtSites.lean)
states the field ok at every site of every public part.

What is shown.
  `lays_of_nextHead_light`: `LaysAt T b c`, the thread T a variable, at every clause c that follows
    from the sentence on the slot (`hc`). Its proof is that of `lays_of_nextHead`
    (Honest/K3/Law/Thread/LaysNext.lean), with the single hypotheses in the place of the fields of
    `K3AtSite`, and with four lines more behind the first, which show the field usedIs from `hcl`.
  `lays_nextHead_head`: the case of the clause `riderHead (b + 1) hi` (Honest/Thread/Riders.lean).
  `site_p_is`: a site's parameters are the value of the library's `placeAt`
    (Johnson/Desc/First/Look/LookKind.lean) at the site's link and sort, from `site_facts`
    (Honest/K3/Law/MemberSite.lean).
  `lays_nextHead_thread`: at the thread of `lettersHead`, with "keeps" by the place's kind, under
    `P5J.AtMgA`: `O`, `hlp`, `hM`, `hcl` and `hq` are shown, as `lays_foldDrawn_thread`
    (Honest/K3/Law/Thread/HeadDigitsAtLink.lean) shows them.
  `lays_nextHead_closed`: no site in the statement: at the borders 345 and 346; the slot is p.first
    + Forest.elems sh, where `placeAt` at the digits of link 24 returns p and the shape of p is sh.
    The site comes from `site_there_head` (Honest/K3/Law/Thread/SiteThereHead.lean) under its one
    public test `hr`.
  `lays_nextHead_3531`: the slot as a numeral: 2168 + 1363.

Hypotheses of the first two theorems.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`: s is a site of the public part (`lookSites Z`).
  `hlp`: the sub-protocol lot stands at the site's place.
  `hM`: the structure `K3MemberAt` (Honest/K3/Law/Thread/K3KeepsStep.lean), of four fields.
  `hd`, `hcl`, `hq`: this is the lookup on the digits (`hd`) of the head's link (`hcl`: the site's
    caller; `hq`: which step without a round stands behind).
  `hfront`, the promise in front: at every state at which the thread's relation `Thr T b` holds, the
    lookup's promise in front holds (`k3OnIn`, Johnson/Desc/First/Look/K3Borders.lean).

Hypotheses that remain in the last theorem.
  `h`: `P5J.AtMgA`.
  `hr`: a test with code on the public part: `rngIn` (Honest/K3/Lot.lean) returns a number at link
    24. `rng_at` (Johnson/AtFull/Shape/SitesAtHead.lean) states it under
    `P5J.AtMgA`; that file is not imported here.
    So does `rng_head_paid`
    (Honest/K3/Law/Thread/RngWrittenHolds.lean), which is not imported here either.
  `hfront`: it remains in all five theorems on the rider. At the thread of `lettersHead` it is not
    shown in this file. The proof of `lays_of_nextHead_light` spends it for the hypothesis `hIn` of
    `next_atSite` (Honest/K3/Law/Thread/NextBehind.lean) alone; see that file's head, "Beside it".
In the others besides: `e`: (in `lays_nextHead_thread`) the site's link is 24. `hp`, `hsh`: (in
`lays_nextHead_closed`) `placeAt` returns the parameters p at link 24's digits; they have the shape
sh.

Which thread. From `lays_nextHead_thread` on: `lettersHead` at a "keeps" of the form `kpBy f`
(Honest/Thread/KeepsBy.lean: by the place's kind), for an arbitrary rider Rd and an arbitrary f. At
another thread: the first two theorems, where the thread is a variable.

Imported. Beneath this file lie, among others:
  files on the frame for the honest prover and its threads, directly under Honest/ and under
    Honest/Law/ and Honest/Thread/ (Thread/Riders, Thread/Thr, Thread/First, Thread/KeepsBy and
    Thread/Shape among them);
  files on the masked sumcheck's law, under Honest/SumLaw/ and
    Honest/Member/;
  three on the chain's shape (Johnson/Desc/First/Shape/Chain, Parts, Tail);
  one of the kind K9's (Johnson/Desc/K9/Honest/SlotsLive).
They come in through HeadDigitsAtLink.lean and SiteThereHead.lean. The first three theorems of the
list above need of them Honest/Thread/Riders.lean and Honest/Thread/Thr.lean alone.

Credit. The two numerals are the library's, in the goals' scope. `digits_place`
(Johnson/Desc/Kinds/Law/K6PubInScope.lean): p.first = 2168, and the shape of p is that of the head's
plan. `plan_in_scope`, in its field elems (Johnson/Desc/Kinds/Law/HeadPlanWritten.lean): 1363. That
they lie there comes from K11's files' own count of slots at the
border 346.

Users. For a caller at the thread of `lettersHead` these theorems take the place of
`lays_of_nextHead`.

Limits. The conclusion is drawn from the step's acceptance alone (`LaysAt`). At the full size alone
from `lays_nextHead_thread` on. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadDigitsAtLink
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.NextBehind
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteThereHead
import Johnson.Desc.Kinds.Law.K6PubInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs OpenedColumn)
open VerifiableInference.Desc.K3 (quietAt quietHead k3OnIn)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (digits_place plan_in_scope)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **A site's parameters are the value of `placeAt` at the site's link and sort.** Conditional on
the site (`hs`). No instance of these hypotheses is exhibited in this file. -/
theorem site_p_is {Z : Pub} {s : Site} (hs : s ∈ lookSites Z) :
    placeAt Z.p.X s.link s.digits = some s.p := by
  unfold lookSites at hs
  obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs
  obtain ⟨f1, _, f3, f4, _⟩ := site_facts _ _ x s hsx
  rw [f3, f4]
  exact f1

section
variable {Bk : ProverCoinCounts} {V W X Pb : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)
  (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
  {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
  (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
  {lot : Block FS ProofFile.Cl} (hs : s ∈ lookSites Z) (hlp : lot.place = s.at_.place)
  (hM : K3MemberAt T b Z Bs ch lot)
include O hs hlp hM

/-- **Behind the member the next free slot of the head's link's own ledger is the lookup's first
slot plus its number of hidden values**, at every clause c that follows from that sentence (`hc`).
Conditional on the hypotheses that the head of this file lists. No instance of these hypotheses is
exhibited in this file. -/
theorem lays_of_nextHead_light (hd : s.digits = true) (hcl : s.caller = .head)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X))
    (hfront : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), Thr T b k st m E →
      k3OnIn s.p st = true) (c : RiderCl W FS)
    (hc : ∀ w t, (∃ a, t.here = .head a ∧
      a.F.next = s.p.first + OnBytes.Model.Forest.elems s.shape) → c.prop (b + 1) w t) :
    LaysAt T b c := by
  intro blk hblk k st m E ds y cols s' hA _ hSt
  have hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true := by
    rw [hcl]
    simp
  obtain ⟨G, hG, hn⟩ := next_atSite o pol lay KL Fd Z Bs base ch A B O s hs hT3 lot blk
    hM.inLot hlp (hM.mem blk hblk) (hM.place blk hblk) (hM.plan blk hblk) T.ft st s' _ _
    cols (hfront k st m E hA) hSt.2
  obtain ⟨_, tl, F, H, G', a₀, claim, _, _, _, _, e, _⟩ := k3Keeps_head o pol lay KL Fd Z Bs base ch
    A B O s hs hd lot blk hM.inLot hlp (hM.mem blk hblk) (hM.place blk hblk)
    (hM.plan blk hblk) hq T.ft st s' _ _ cols hSt.2
  obtain ⟨a', hh⟩ : ∃ a', s'.here = .head a' := ⟨_, by rw [e]⟩
  exact hc _ _ ⟨a', hh, by rw [fork_head hh hG]; exact hn⟩

/-- The case of the clause `riderHead (b + 1) hi` (Honest/Thread/Riders.lean). Conditional on the
same hypotheses. No instance of these hypotheses is exhibited in this file. -/
theorem lays_nextHead_head (hd : s.digits = true) (hcl : s.caller = .head)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X))
    (hfront : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), Thr T b k st m E →
      k3OnIn s.p st = true) (hi : Nat) :
    LaysAt T b (riderHead (b + 1) hi fun a =>
      a.F.next = s.p.first + OnBytes.Model.Forest.elems s.shape) :=
  lays_of_nextHead_light T o pol lay KL Fd base A B O hs hlp hM hd hcl hq hfront _ fun _ _ h => h

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LK" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w

/-- **At the thread of `lettersHead`.** Conditional on `P5J.AtMgA`, the site at the digits of link
24, and `hfront`. No instance of these hypotheses is exhibited in this file. -/
theorem lays_nextHead_thread (s : Site) (hs : s ∈ lookSites Zp) (e : s.link = 24)
    (hd : s.digits = true)
    (hfront : ∀ (k : Coins Bk) (st : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env),
      Thr (LK).thread (borderOf s.link true) k st m E →
      k3OnIn s.p st = true) (hi : Nat) :
    LaysAt (LK).thread (borderOf s.link true)
      (riderHead (borderOf s.link true + 1) hi fun a =>
        a.F.next = s.p.first + OnBytes.Model.Forest.elems s.shape) := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hp, hM⟩ :=
    memberAt_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd f w s.link (by omega) true
  have hlp : lot.place = s.at_.place := by
    have e' := site_place_head h s hs
    rw [hd] at e'
    exact hp.trans e'.symm
  exact lays_nextHead_head (LK).thread _ _ _ _ Fd base A B O hs hlp hM hd
    (caller_head_site h s hs e) (quiet_head_site h s e) hfront hi

/-- **No site in the statement: the slot as a closed term.** Conditional on `P5J.AtMgA`; `hr`; what
`placeAt` returns at the digits of link 24, and its shape; `hfront`. No instance of these hypotheses
is exhibited in this file. -/
theorem lays_nextHead_closed (hr : (rngIn ((spotsOf Zp.cuts).getD []) 24).isSome = true)
    {p : VerifiableInference.Desc.First.Look.P} {sh : OnBytes.Model.Forest.Shape}
    (hp : placeAt Zp.p.X 24 true = some p) (hsh : p.shape = some sh)
    (hfront : ∀ (k : Coins Bk) (st : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env),
      Thr (LK).thread 345 k st m E →
      k3OnIn p st = true) (hi : Nat) :
    LaysAt (LK).thread 345
      (riderHead 346 hi fun a => a.F.next = p.first + OnBytes.Model.Forest.elems sh) := by
  obtain ⟨s, hs, e, hd, -, -⟩ := site_there_head h 24 (by omega) true fun _ => hr
  have hp' := site_p_is hs
  rw [e, hd] at hp'
  have ep : s.p = p := Option.some.inj (hp'.symm.trans hp)
  have es : s.shape = sh := by
    have h1 := site_shape hs
    rw [ep, hsh] at h1
    exact (Option.some.inj h1).symm
  have L := lays_nextHead_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd f w s hs e hd (by
    rw [e, ep]
    exact hfront) hi
  rw [e, ep, es] at L
  exact L

/-- **The slot as a numeral.** Conditional on `P5J.AtMgA`; `hr`; `hfront` at whatever `placeAt`
returns at the digits of link 24. No instance of these hypotheses is exhibited in this file. -/
theorem lays_nextHead_3531 (hr : (rngIn ((spotsOf Zp.cuts).getD []) 24).isSome = true)
    (hfront : ∀ p, placeAt Zp.p.X 24 true = some p →
      ∀ (k : Coins Bk) (st : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env),
      Thr (LK).thread 345 k st m E →
      k3OnIn p st = true) (hi : Nat) :
    LaysAt (LK).thread 345 (riderHead 346 hi fun a => a.F.next = 3531) := by
  obtain ⟨p, hp, hsh, hf⟩ := digits_place h.scope h.reads h.pubOne
  have hel := (plan_in_scope h.scope h.reads h.pubOne).elems
  have L := lays_nextHead_closed h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hr hp hsh
    (hfront p hp) hi
  rw [hf, hel] at L
  exact L

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.lays_of_nextHead_light
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_nextHead_head
#print axioms ProofFile.Honest.K3.Law.AtThr.site_p_is
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_nextHead_thread
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_nextHead_closed
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_nextHead_3531
