-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/TablesBehindDigits.lean: behind an accepting step of the lookup on the
digits at the output head's segment, `TablesLaid` (SpeaksOfTables.lean) holds: the reads' tables
that lie
in the state are the ones that `tablesAt` computes there: where, in front of the step, whatever
tables lie are what the reads' quiet step would lay off that very state. One relation on two states,
and theorems with their proofs.

How. The sub-protocol at that address is the kind's own with a quiet step joined behind
(`K3.theStated`, `K3.theWhole`, `K3.quietHead`, Johnson/Desc/First/Look/K3Stated.lean,
K3Whole.lean).
The lookup's own step writes the smallness test's part and the ledger alone. The quiet step asks
that the segment is open, that the covered positions are there, that what the head heard is laid
and that the head's tables are laid, and writes one field, the claim on the weights. So behind the
two, tables lie; they are the ones that lay in front; and what `tablesAt` reads (the request's
words, the reply that was heard, what the head heard) is as it was in front.

Main names.
  `HeadKeeps s s'`: the request's words and the reply are the same; and where the state behind
    stands in the output head's part, so does the state in front, with the same "opened", the same
    heard values and the same tables.
  `headKeeps_putTl`, `headKeeps_putFork`, `headKeeps_mark`, `HeadKeeps.trans`.
  `digits_keeps`: the lookup's own step. `quietHead_lies`: the quiet step; behind it tables lie.
  `tablesLaid_of_keeps`: the relation carries the premise in front to `TablesLaid` behind, where
    tables lie behind.
  `tablesLaid_behind_digits`: at the sub-protocol at the address (chain 1, segment 24, piece 8).

Limits. The premise hok on the state in front is shown here of no state. No accepting step is
exhibited. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.RunsAreAtLink
import Johnson.Top.H0.MergeLaw.SpeaksOfTables
import Johnson.Desc.First.Batch.ReadersAt
import Johnson.Desc.K8.ReadsQuietLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes.Model (Fork HTailF2)
open VerifiableInference.Desc (Block Claim Place need named)
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.K8.ReadsQuiet (bind_ok named_ok need_ok)
open VerifiableInference.Desc.Kinds.Head.Law (tablesAt)

/-- What `tablesAt` reads, and the tables that lie, are as they were. -/
def HeadKeeps (s s' : S) : Prop :=
  s'.req = s.req ∧ s'.out.reply = s.out.reply ∧
    ∀ o', s'.here = .head o' → ∃ o, s.here = .head o ∧ o'.opened = o.opened ∧ o'.x = o.x ∧
      o'.t = o.t

theorem headKeeps_refl (s : S) : HeadKeeps s s :=
  ⟨rfl, rfl, fun o' h => ⟨o', h, rfl, rfl, rfl⟩⟩

theorem HeadKeeps.trans {a b c : S} (h : HeadKeeps a b) (k : HeadKeeps b c) : HeadKeeps a c := by
  refine ⟨k.1.trans h.1, k.2.1.trans h.2.1, fun o'' ho'' => ?_⟩
  obtain ⟨o', ho', a1, a2, a3⟩ := k.2.2 o'' ho''
  obtain ⟨o, ho, b1, b2, b3⟩ := h.2.2 o' ho'
  exact ⟨o, ho, a1.trans b1, a2.trans b2, a3.trans b3⟩

theorem headKeeps_putFork (s : S) (F : Fork) : HeadKeeps s (s.putFork F) := by
  unfold S.putFork
  split
  · exact ⟨rfl, rfl, fun o' h => nomatch h⟩
  · exact ⟨rfl, rfl, fun o' h => nomatch h⟩
  · rename_i a ha
    split
    · refine ⟨rfl, rfl, fun o' h => ?_⟩
      have e : ({ a with F := F } : HeadOwn) = o' := Here.head.inj h
      rw [← e]
      exact ⟨a, ha, rfl, rfl, rfl⟩
    · exact headKeeps_refl s
  · exact headKeeps_refl s

theorem headKeeps_putTl (s : S) (tl : HTailF2) : HeadKeeps s (s.putTl tl) := by
  unfold S.putTl
  split
  · exact ⟨rfl, rfl, fun o' h => nomatch h⟩
  · exact ⟨rfl, rfl, fun o' h => nomatch h⟩
  · rename_i a ha
    split
    · refine ⟨rfl, rfl, fun o' h => ?_⟩
      have e : ({ a with tl := tl } : HeadOwn) = o' := Here.head.inj h
      rw [← e]
      exact ⟨a, ha, rfl, rfl, rfl⟩
    · exact headKeeps_refl s
  · exact headKeeps_refl s

theorem headKeeps_mark (s : S) (n : String) : HeadKeeps s (s.mark n) := by
  unfold S.mark
  split
  · exact headKeeps_refl s
  · exact ⟨rfl, rfl, fun o' h => ⟨o', h, rfl, rfl, rfl⟩⟩

/-- **The lookup on the digits: its own step.** -/
theorem digits_keeps (claim : OnBytes.Model.Aff → Claim) (p : Look.P) {s s1 : S}
    {rs : List Fmt.RoundView} (h : K3.Law.decideVia (K3.seatDigits claim) p s rs = .ok s1) :
    HeadKeeps s s1 := by
  unfold K3.Law.decideVia at h
  obtain ⟨F, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨_, -, h⟩ := bind_ok h
  obtain ⟨x, -, h⟩ := bind_ok h
  rw [← Except.ok.inj h]
  show HeadKeeps s (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := x.2.next,
        heard := some x.1 }).putFork x.2
    | _, _ => s.mark "K3 seat: no record of the smallness test")
  split
  · exact (headKeeps_putTl s _).trans (headKeeps_putFork _ _)
  · exact headKeeps_mark s _

/-- **The quiet step behind it**: and behind it tables lie. -/
theorem quietHead_lies (X : OnBytes.Model.Verify.Public) {s1 s' : S}
    (h : K3.quietHead X s1 = .ok s') :
    HeadKeeps s1 s' ∧ ∃ o' t, s'.here = .head o' ∧ o'.t = some t := by
  unfold K3.quietHead at h
  split at h
  · rename_i a ha
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨cov, -, h⟩ := bind_ok h
    obtain ⟨x, -, h⟩ := bind_ok h
    obtain ⟨t, ht, h⟩ := bind_ok h
    obtain ⟨cl, -, h⟩ := bind_ok h
    obtain ⟨_, -, h⟩ := bind_ok h
    rw [← Except.ok.inj h]
    refine ⟨⟨rfl, rfl, fun o' ho' => ?_⟩, _, t, rfl, named_ok ht⟩
    have e : ({ a with claim := some cl } : HeadOwn) = o' := Here.head.inj ho'
    rw [← e]
    exact ⟨a, ha, rfl, rfl, rfl⟩
  · cases h

/-- The relation carries the premise in front to `TablesLaid` behind, where tables lie behind. -/
theorem tablesLaid_of_keeps (P : K8.ReadsQuiet.PH) {s s' : S} (k : HeadKeeps s s')
    (hlie : ∃ o' t, s'.here = .head o' ∧ o'.t = some t)
    (hok : ∀ a t, s.here = .head a → a.t = some t → ∃ cov x, s.covered P.h.T P.h.V = .ok cov ∧
      a.x = some x ∧ K8.ReadsQuiet.tables P.h P.L P.hp cov x = .ok t) : TablesLaid P s' := by
  intro o t' ho ht'
  obtain ⟨o', t, ho', hto⟩ := hlie
  obtain rfl : o' = o := Here.head.inj (ho'.symm.trans ho)
  obtain ⟨a, ha, e1, e2, e3⟩ := k.2.2 o' ho
  obtain ⟨cov, x, hc, hx, htb⟩ := hok a t ha (e3.symm.trans hto)
  have hc' : s'.covered P.h.T P.h.V = .ok cov := by
    rw [← hc]
    unfold S.covered S.replyTok? S.coveredAt
    rw [k.1, k.2.1]
  unfold tablesAt at ht'
  rw [ho] at ht'
  have ht2 : (if o'.opened = true then
      (s'.covered P.h.T P.h.V).toOption.bind fun cov =>
        o'.x.bind fun x => (K8.ReadsQuiet.tables P.h P.L P.hp cov x).toOption
      else none) = some t' := ht'
  split at ht2
  · rw [hc', e2, hx] at ht2
    have ht3 : (K8.ReadsQuiet.tables P.h P.L P.hp cov x).toOption = some t' := ht2
    rw [htb] at ht3
    rw [hto]
    exact ht3
  · cases ht2

/-- **BEHIND THE LOOKUP ON THE DIGITS AT THE OUTPUT HEAD's SEGMENT.** -/
theorem tablesLaid_behind_digits (X : OnBytes.Model.Verify.Public)
    (claim : OnBytes.Model.Aff → Claim) (readers : ℕ → Option (K3.Readers S))
    (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape) {B : Block S Claim}
    (hB : K3.theStated claim readers X codes shape (IM.k3Place 24 true) = some B) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hd : B.decide s rs gs = .ok s')
    (hok : ∀ a t, s.here = .head a → a.t = some t → ∃ cov x,
      s.covered X.hS.T X.hS.V = .ok cov ∧ a.x = some x ∧
      K8.ReadsQuiet.tables X.hS X.HLy X.H cov x = .ok t) : TablesLaid (K9.phAt X 24) s' := by
  obtain ⟨B₁, hB₁, -, hdec, -⟩ := K3.theStated_is claim readers X codes shape _ B hB
  rw [hdec] at hd
  obtain ⟨b, hb, hW⟩ := K3.theWhole_is claim true X codes shape _ B₁ hB₁
  obtain ⟨i, dg, p, sent, laid, hi, hp, -, -, -, -, hbd, -⟩ :=
    K3.theOwn_is claim true X codes shape _ b hb
  obtain rfl : 24 = i := Option.some.inj hi
  obtain ⟨rfl, hH⟩ := piece_digits (show 8 = K3.pieceAt X 24 dg from hp)
  have hq : ((IM.k3Place 24 true).link.bind fun i =>
      K3.quietAt X i ((IM.k3Place 24 true).piece == K3.pieceAt X i true)) =
      some (K3.quietHead X) := by
    have e8 : K3.pieceAt X 24 true = 8 := hp.symm
    show K3.quietAt X 24 ((8 : ℕ) == K3.pieceAt X 24 true) = _
    rw [e8]
    simp [K3.quietAt, hH]
  rcases hW with ⟨hn, -⟩ | ⟨f, hf, rfl⟩
  · rw [hq] at hn
    cases hn
  · obtain rfl : K3.quietHead X = f := Option.some.inj (hq.symm.trans hf)
    have hd' : (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind (fun s1 =>
        K3.quietHead X s1) = .ok s' := hd
    obtain ⟨s1, h1, h2⟩ := bind_ok hd'
    rw [hbd] at h1
    have h1' : K3.Law.decideVia (K3.seatDigits claim) p s (rs.take b.rounds.length) = .ok s1 := h1
    obtain ⟨k2, hlie⟩ := quietHead_lies X h2
    exact tablesLaid_of_keeps (K9.phAt X 24) ((digits_keeps claim p h1').trans k2) hlie hok

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.digits_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.quietHead_lies
#print axioms VerifiableInference.Desc.First.MergeLaw.tablesLaid_of_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.tablesLaid_behind_digits
