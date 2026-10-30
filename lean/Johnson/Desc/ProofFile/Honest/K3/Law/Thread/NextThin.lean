-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/NextThin.lean: the kind "lookup" (K3): "behind a lookup the
ledger's next free slot is the lookup's first slot plus its number of hidden values", and the clause
of a thread's rider that the lookup on the digits of the head's link lays with it: the theorems of
Honest/K3/Law/Thread/NextBehind.lean and LaysNextLight.lean once more, under fewer hypotheses. The last
stands under the library's hypothesis `P5J.AtMgA` alone. Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md; the heads of NextBehind.lean and LaysNextLight.lean.

What is shown, and what each lacks that its fuller theorem has.
  `next_atSite_thin`: `next_atSite` (NextBehind.lean) without the lookup's promise in front (`hIn`),
    without the public test `hT3`, and without a sub-protocol of the lot (`lot`, `hb`, `hbs`): the member
    stands at the site's place (`hmp`).
  `lays_of_nextHead_thin`, `lays_nextHead_head_thin`: `lays_of_nextHead_light` and
    `lays_nextHead_head` (LaysNextLight.lean) without `hcl` and `hfront`.
  `lays_nextHead_thread_thin`: `lays_nextHead_thread` without `hfront`.
  `lays_nextHead_closed_thin`: `lays_nextHead_closed` without `hr` and `hfront`.
  `lays_nextHead_3531_thin`: `lays_nextHead_3531` without `hr` and `hfront`: `P5J.AtMgA` alone remains.

Why they can go. The seated decision itself tests that the ledger's next slot in front is the place's
first: so `next_behind` (Honest/K3/Good/Live/Windows.lean) has the sentence from the lookups' form, the
place's shape and the step's acceptance alone. In the fuller theorems `hfront` is spent for `hIn`
alone and `hcl` for `hT3` alone. `lot_of_site` (Honest/K3/Law/LotOfSite.lean) gives the
sub-protocol of the lot. `site_digits_paid` (Honest/K3/Law/Thread/RngWrittenHolds.lean) gives the site at
the digits of link 24, for which the elder theorem spends `hr`.

Hypotheses that remain. As in the elder theorems' heads, but for those named above.

How the proof goes. `next_atSite_thin`: `lot_of_site`, `site_block`, `memberAtSite`, `site_shape`,
`next_behind`, `fork_seat`. The five on the rider: the elder proofs, line for line, with
`next_atSite_thin` in the place of `next_atSite`: a second text of these proofs; the elder files are
unchanged.

Limits. Those of the fuller theorems. At the full size alone from `lays_nextHead_thread_thin` on. No
instance of `P5J.AtMgA` is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LaysNextLight
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngWrittenHolds
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.OutSite
import Johnson.Desc.ProofFile.Honest.K3.Law.LotOfSite
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Windows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs OpenedColumn)
open VerifiableInference.Desc.K3 (quietAt quietHead)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (digits_place plan_in_scope)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Good.Live (next_behind)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **Behind the accepting step of the description's own member at a lookup's place the ledger's next
free slot is the lookup's first slot plus its number of hidden values.** Conditional on the
description's return, the site, the member at its place, its test on the plan and the acceptance. No
instance of these hypotheses is exhibited in this file. -/
theorem next_atSite_thin (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (m : Block FS ProofFile.Cl) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = s.at_.place) (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    ∃ G, sj'.fork? = some G ∧ G.next = s.p.first + OnBytes.Model.Forest.elems s.shape := by
  obtain ⟨lot, hb, hbs⟩ := lot_of_site o pol lay KL Fd Z Bs base ch A B O s hs
  have hmp' : m.place = lot.place := hmp.trans hbs.symm
  obtain ⟨Fm, _⟩ := site_block o pol lay KL Fd Z Bs base ch A B O s hs lot m hb hbs hm hmp' hpk
  obtain ⟨_, _, _, _, hst⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hb m hm hmp'
  obtain ⟨G, hG, hn⟩ := next_behind Fm (site_shape hs) ft sj sj' n rs c
    ((hst ft sj sj' n rs c).1 h).1
  rw [fork_seat] at hG
  exact ⟨G, hG, hn⟩

section
variable {Bk : ProverCoinCounts} {V W X Pb : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)
  (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
  {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
  (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
  {lot : Block FS ProofFile.Cl} (hs : s ∈ lookSites Z) (hlp : lot.place = s.at_.place)
  (hM : K3MemberAt T b Z Bs ch lot)
include O hs hlp hM

/-- `lays_of_nextHead_light` without `hcl` and `hfront`. No instance of these hypotheses is exhibited
in this file. -/
theorem lays_of_nextHead_thin (hd : s.digits = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X)) (c : RiderCl W FS)
    (hc : ∀ w t, (∃ a, t.here = .head a ∧
      a.F.next = s.p.first + OnBytes.Model.Forest.elems s.shape) → c.prop (b + 1) w t) :
    LaysAt T b c := by
  intro blk hblk k st m E ds y cols s' hA _ hSt
  obtain ⟨G, hG, hn⟩ := next_atSite_thin o pol lay KL Fd Z Bs base ch A B O s hs blk
    (hM.mem blk hblk) ((hM.place blk hblk).trans hlp) (hM.plan blk hblk) T.ft st s' _ _ cols hSt.2
  obtain ⟨_, tl, F, H, G', a₀, claim, _, _, _, _, e, _⟩ := k3Keeps_head o pol lay KL Fd Z Bs base ch
    A B O s hs hd lot blk hM.inLot hlp (hM.mem blk hblk) (hM.place blk hblk)
    (hM.plan blk hblk) hq T.ft st s' _ _ cols hSt.2
  obtain ⟨a', hh⟩ : ∃ a', s'.here = .head a' := ⟨_, by rw [e]⟩
  exact hc _ _ ⟨a', hh, by rw [fork_head hh hG]; exact hn⟩

/-- `lays_nextHead_head` without `hcl` and `hfront`. No instance of these hypotheses is exhibited in
this file. -/
theorem lays_nextHead_head_thin (hd : s.digits = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X)) (hi : Nat) :
    LaysAt T b (riderHead (b + 1) hi fun a =>
      a.F.next = s.p.first + OnBytes.Model.Forest.elems s.shape) :=
  lays_of_nextHead_thin T o pol lay KL Fd base A B O hs hlp hM hd hq _ fun _ _ h => h

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

/-- `lays_nextHead_thread` without `hfront`. Conditional on `P5J.AtMgA` and the site at the digits of
link 24. No instance of these hypotheses is exhibited in this file. -/
theorem lays_nextHead_thread_thin (s : Site) (hs : s ∈ lookSites Zp) (e : s.link = 24)
    (hd : s.digits = true) (hi : Nat) :
    LaysAt (LK).thread (borderOf s.link true)
      (riderHead (borderOf s.link true + 1) hi fun a =>
        a.F.next = s.p.first + OnBytes.Model.Forest.elems s.shape) := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hp, hM⟩ :=
    memberAt_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd f w s.link (by omega) true
  have hlp : lot.place = s.at_.place := by
    have e' := site_place_head h s hs
    rw [hd] at e'
    exact hp.trans e'.symm
  exact lays_nextHead_head_thin (LK).thread _ _ _ _ Fd base A B O hs hlp hM hd
    (quiet_head_site h s e) hi

/-- `lays_nextHead_closed` without `hr` and `hfront`. Conditional on `P5J.AtMgA`, and on what `placeAt`
returns at the digits of link 24, and its shape. No instance of these hypotheses is exhibited in
this file. -/
theorem lays_nextHead_closed_thin {p : VerifiableInference.Desc.First.Look.P}
    {sh : OnBytes.Model.Forest.Shape} (hp : placeAt Zp.p.X 24 true = some p)
    (hsh : p.shape = some sh) (hi : Nat) :
    LaysAt (LK).thread 345
      (riderHead 346 hi fun a => a.F.next = p.first + OnBytes.Model.Forest.elems sh) := by
  obtain ⟨s, hs, e, hd, -, -⟩ := site_digits_paid h 24 (by omega) true
  have hp' := site_p_is hs
  rw [e, hd] at hp'
  have ep : s.p = p := Option.some.inj (hp'.symm.trans hp)
  have es : s.shape = sh := by
    have h1 := site_shape hs
    rw [ep, hsh] at h1
    exact (Option.some.inj h1).symm
  have L := lays_nextHead_thread_thin h H Q test carryX item n₁ n₂ b₀ Vd Rd f w s hs e hd hi
  rw [e, ep, es] at L
  exact L

/-- **The slot as a numeral, under `P5J.AtMgA` alone**: `lays_nextHead_3531` without `hr` and
`hfront`. No instance of this hypothesis is exhibited in this file. -/
theorem lays_nextHead_3531_thin (hi : Nat) :
    LaysAt (LK).thread 345 (riderHead 346 hi fun a => a.F.next = 3531) := by
  obtain ⟨p, hp, hsh, hf⟩ := digits_place h.scope h.reads h.pubOne
  have hel := (plan_in_scope h.scope h.reads h.pubOne).elems
  have L := lays_nextHead_closed_thin h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hp hsh hi
  rw [hf, hel] at L
  exact L

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.next_atSite_thin
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_of_nextHead_thin
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_nextHead_head_thin
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_nextHead_thread_thin
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_nextHead_closed_thin
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_nextHead_3531_thin
