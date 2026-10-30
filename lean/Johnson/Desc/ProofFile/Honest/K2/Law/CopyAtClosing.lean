-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopyAtClosing.lean: the kind "the code switch" (K2): THE WHOLE
JOIN FOR THE MESSAGES OF A SWITCH's OWN SENDING: where the closing as the kind's lot lays it
(`lotClosingAt`, Honest/K2/Exact.lean) returns at the sender p₀ and at a later switch p, the later
closing has laid the rows of the segment into which p₀ leads AT WHAT THE SENDER's OWN CLOSING
RETURNED; and these rows are, message by message, the rows that the sender laid. One abbreviation;
statements with their proofs.

  `lotOwn`             the own data as `lotClosingAt` hands them to the closing: an abbreviation
  `closingFor_inv`, `lotClosingAt_inv`   what a return of these two says of `closingFrom`
  `closingFrom_next`   the number of the next stretch: the first, and all the segments' messages
  `lays_at_closing`    the later closing has laid that segment's rows at the sender's own W₀
  `copy_at_closing`    THE END: R.rows[n]? = some (V n)

ITS PREMISES, BY KIND. RETURNS: both switches are handed their stretches; both closings return; the
sender's laying returns V. PUBLIC, ON THE PLACES AND SEGMENTS: p₀.link ≤ p.link; S is the segment
number p₀.link; its sizes and first sending are the sender's. PUBLIC, ON THE BOOK: hT: number by
number, what p carries names the runs that p₀'s entries name (`carriedSame_gives`,
Honest/K2/Law/CarriedAsks.lean, has that end); THE BOOK's TIE of `copy_carried` at the entry whose
number is n behind all messages of the segments in front of p₀. ON THE DATA AND THE CHALLENGES: ho:
the own data of the segments in front of p₀ are one at both places; hg: their folds' challenges read
alike; hd: the main rows of message n are one.

By: `closing_lays_at` (Honest/K2/Law/ClosingPasses.lean) · `givesAll_carried`
(Honest/K2/Law/CarriedSame.lean) · `copy_at_segment` (Honest/K2/Law/CopyAtSegment.lean).

Limits. The Limits of CopyAtSegment.lean stand, but one that it takes over from CopyOne.lean: that p
does not come in front of p₀ is a premise here (hl). None of the premises is paid here. Not the last
message of the sending, the next fold's mask; not the later sendings of a segment; not the first
segment. An equation at each run's coins: what is WRITTEN where. NO LOT IS LAID. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingPasses
import Johnson.Desc.ProofFile.Honest.K2.Law.CarriedSame
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyAtSegment
import Johnson.Desc.ProofFile.Honest.K2.Exact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left mainRows)

variable {Bk : ProverCoinCounts}

/-- The own data as `lotClosingAt` hands them to the closing: an abbreviation of its text. -/
abbrev lotOwn (segs : List SegmentPub) (p : SwitchPlace) (D : RowData) (Rd : Readers)
    (heard : List Fmt.Drawn) : Nat → Nat → Nat → Nat → Cb.Gl.E :=
  ownBy D Rd p.addrs (fun s m => (((segs[s]?).map (·.ownShapes (s == 0))).getD []).getD m {})
    heard

/-- What a return of `closingFor` says of `closingFrom`. -/
theorem closingFor_inv {table : FreshTable} {segs : List SegmentPub}
    {next : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard : List Fmt.Drawn} {k : Nat → Except String Stretch} {W : Left}
    (h : closingFor table segs next own heard k = .ok W) :
    ∃ x kept, closingFrom table own heard k segs 0 0 none = .ok x ∧ x.1 = some (W, kept) := by
  have g : OkGives (fun W : Left =>
      ∃ x kept, closingFrom table own heard k segs 0 0 none = .ok x ∧ x.1 = some (W, kept))
      (closingFor table segs next own heard k) := by
    unfold closingFor
    refine OkGives.bind fun x hx => ?_
    obtain ⟨x1, x2⟩ := x
    cases x1 with
    | none => exact fun _ ha => by cases ha
    | some Wk =>
      obtain ⟨W', kept⟩ := Wk
      refine OkGives.ite (fun _ _ ha => by cases ha) fun _ a ha => ?_
      obtain rfl := Except.ok.inj ha
      exact ⟨_, kept, hx, rfl⟩
  exact g W h

/-- The like of the closing as the kind's lot lays it. -/
theorem lotClosingAt_inv {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub}
    {p : SwitchPlace} {D : RowData} {Rd : Readers} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {W : Left}
    (h : lotClosingAt lay segs p D Rd heard k = .ok W) :
    ∃ x kept, closingFrom freshTable
      (lotOwn segs p D Rd heard)
      heard k (segs.take p.link) 0 0 none = .ok x ∧ x.1 = some (W, kept) := by
  have g : OkGives (fun W : Left => ∃ x kept, closingFrom freshTable
      (lotOwn segs p D Rd heard)
      heard k (segs.take p.link) 0 0 none = .ok x ∧ x.1 = some (W, kept))
      (lotClosingAt lay segs p D Rd heard k) := by
    unfold lotClosingAt
    exact OkGives.bind fun _ _ a ha => closingFor_inv ha
  exact g W h

/-- The number of the next stretch. -/
theorem closingFrom_next (table : FreshTable) (own : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (heard : List Fmt.Drawn) (k : Nat → Except String Stretch) :
    ∀ (segs : List SegmentPub) (j base : Nat) (prev : Option (Left × List OnBytes.OracleShape)),
      OkGives (fun x => x.2 = base + (segs.map (·.messages)).sum)
        (closingFrom table own heard k segs j base prev)
  | [], _, base, prev => fun x hx => by
    obtain rfl : (prev, base) = x := Except.ok.inj hx
    simp
  | S :: rest, j, base, prev => by
    show OkGives _ ((segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard
      k base).bind fun W =>
        closingFrom table own heard k rest (j + 1) (base + S.messages) (some W))
    refine OkGives.bind fun W _ x hx => ?_
    have e := closingFrom_next table own heard k rest (j + 1) (base + S.messages) (some W) x hx
    rw [e, List.map_cons, List.sum_cons]
    omega

/-- **The later closing has laid that segment's rows at the sender's own W₀.** -/
theorem lays_at_closing (ch : Nat) (p₀ p : SwitchPlace) (k : Coins Bk)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c)
    (hT : ∀ (i : Nat) (e₀ : Ahead),
      ((Bk.ahead.filter fun x => x.spender == ⟨p₀.place, 0⟩).filter (!·.once))[i]? = some e₀ →
      ∃ e, ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e ∧
        e.owner = e₀.owner ∧ e.start = e₀.start ∧ e.count = e₀.count)
    {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub} {D : RowData} {Rd : Readers}
    {heard₀ heard : List Fmt.Drawn} {W₀ W : Left}
    (hW₀ : lotClosingAt lay segs p₀ D Rd heard₀ (Stretch.carried p₀.carries c₀.2.2) = .ok W₀)
    (hW : lotClosingAt lay segs p D Rd heard (Stretch.carried p.carries c.2.2) = .ok W)
    (hl : p₀.link ≤ p.link)
    (ho : ∀ i, i < (segs.take p₀.link).length →
      lotOwn segs p₀ D Rd heard₀ (0 + i) =
        lotOwn segs p D Rd heard (0 + i))
    (hg : ∀ S ∈ segs.take p₀.link, challengesOr0 heard₀ S.gamma = challengesOr0 heard S.gamma)
    {S : SegmentPub} {rest : List SegmentPub} (hS : (segs.take p.link).drop p₀.link = S :: rest) :
    ∃ R kept, segmentGroupRows freshTable S (some W₀) kept
      (lotOwn segs p D Rd heard
        (0 + (segs.take p₀.link).length))
      (Stretch.carried p.carries c.2.2) (0 + ((segs.take p₀.link).map (·.messages)).sum) true =
        .ok R := by
  obtain ⟨x₀, kept, hx₀, e₀⟩ := lotClosingAt_inv hW₀
  obtain ⟨y, _, hy, _⟩ := lotClosingAt_inv hW
  obtain ⟨R, hR⟩ := closing_lays_at freshTable (givesAll_carried ch p₀ p k c₀ h₀ c h hT) segs hl ho
    hg hx₀ hS hy
  have eb := closingFrom_next freshTable _ heard₀ _ (segs.take p₀.link) 0 0 none x₀ hx₀
  rw [e₀, eb] at hR
  exact ⟨R, kept, hR⟩

/-- **THE END.** V: the rows that the sender laid. -/
theorem copy_at_closing (ch : Nat) (p₀ p : SwitchPlace) (k : Coins Bk)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (h : handed ch p k = some c)
    (hT : ∀ (i : Nat) (e₀ : Ahead),
      ((Bk.ahead.filter fun x => x.spender == ⟨p₀.place, 0⟩).filter (!·.once))[i]? = some e₀ →
      ∃ e, ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[i]? = some e ∧
        e.owner = e₀.owner ∧ e.start = e₀.start ∧ e.count = e₀.count)
    {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub} {D : RowData} {Rd : Readers}
    {heard₀ heard : List Fmt.Drawn} {W₀ W : Left}
    (hW₀ : lotClosingAt lay segs p₀ D Rd heard₀ (Stretch.carried p₀.carries c₀.2.2) = .ok W₀)
    (hW : lotClosingAt lay segs p D Rd heard (Stretch.carried p.carries c.2.2) = .ok W)
    (hl : p₀.link ≤ p.link)
    (ho : ∀ i, i < (segs.take p₀.link).length →
      lotOwn segs p₀ D Rd heard₀ (0 + i) = lotOwn segs p D Rd heard (0 + i))
    (hg : ∀ S ∈ segs.take p₀.link, challengesOr0 heard₀ S.gamma = challengesOr0 heard S.gamma)
    {S : SegmentPub} {rest : List SegmentPub} (hS : (segs.take p.link).drop p₀.link = S :: rest)
    (hSz : S.sizes = p₀.sizes) (hSent : S.sent.headD #[] = (switchSent p₀.sizes p₀.others))
    {own₀ : Nat → Nat → Nat → Cb.Gl.E} {V : Nat → Johnson.Prover.Send.Rows}
    (hV : rowsAll freshTable p₀.sizes.codes (switchSent p₀.sizes p₀.others)
      (switchFresh p₀.sizes p₀.others p₀.foldVars) (mainRows p₀.sizes W₀ own₀) c₀.1 = .ok V) :
    ∃ R kept, segmentGroupRows freshTable S (some W₀) kept
        (lotOwn segs p D Rd heard (0 + (segs.take p₀.link).length))
        (Stretch.carried p.carries c.2.2) (0 + ((segs.take p₀.link).map (·.messages)).sum) true =
          .ok R ∧
      ∀ n, n < (switchSent p₀.sizes p₀.others).size - 1 →
        mainRows p₀.sizes W₀ (lotOwn segs p D Rd heard (0 + (segs.take p₀.link).length)) n =
          mainRows p₀.sizes W₀ own₀ n →
        ∀ e : Ahead,
          ((Bk.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[
            0 + ((segs.take p₀.link).map (·.messages)).sum + n]? = some e →
          e.owner = ⟨p₀.place, 0⟩ →
          e.start = dueBefore p₀.sizes.codes (switchSent p₀.sizes p₀.others)
            (switchFresh p₀.sizes p₀.others p₀.foldVars) n →
          e.count = messageDue p₀.sizes.codes ((switchSent p₀.sizes p₀.others).getD n default).shape
            (foldAt (switchFresh p₀.sizes p₀.others p₀.foldVars) n) →
          R.rows[n]? = some (V n) := by
  obtain ⟨R, kept, hR⟩ := lays_at_closing ch p₀ p k c₀ h₀ c h hT hW₀ hW hl ho hg hS
  exact ⟨R, kept, hR, fun n hn hd e he t1 t2 t3 =>
    copy_at_segment ch p₀ p k c₀ h₀ c h hR hSz hSent hV hn hd e he t1 t2 t3⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.lotOwn
#print axioms ProofFile.Honest.K2.Law.closingFor_inv
#print axioms ProofFile.Honest.K2.Law.lotClosingAt_inv
#print axioms ProofFile.Honest.K2.Law.closingFrom_next
#print axioms ProofFile.Honest.K2.Law.lays_at_closing
#print axioms ProofFile.Honest.K2.Law.copy_at_closing
