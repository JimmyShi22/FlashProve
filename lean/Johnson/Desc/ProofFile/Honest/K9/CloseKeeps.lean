-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/CloseKeeps.lean: K9's TWO MEMBERS WITHOUT A ROUND, "the one equation" AND "the
segment is shut": WHERE THE DESCRIPTION SEATS THEM, AND WHAT A YES OF EACH LEAVES AND TURNS (what is left, field by
field: Honest/K9/CloseLeaves.lean). The sealed library's neighbours `K9.oneEquation_writes`, `oneEquation_keeps`,
`shut_keeps` (Johnson/Desc/First/Batch/Law/Keeps.lean) say less ("there is a part"; a reading that does not see the
writings stays): no twins. Definitions, statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and
no goal is stated.
  `EqKeeps s s'`     A CLOSED SENTENCE on the state in front of "the one equation" (s) and behind it (s'): s' bears no
      mark of failure · its reply is the reply in front · K9's lens reads a part a at s, K9's `door`
      (Johnson/Desc/First/Batch/Text.lean) returns o at that part, and s' IS s with that part laid back, its fields
      owed, L, F, d turned into o's: AN EQUATION ON THE WHOLE STATE
  `ShutKeeps s s'`   the like for "the segment is shut": no mark · the reply · a segment's book-keeping L is open at
      s, and s' IS s with `closed L L.check.frame` laid in its stead
  `eq_pays`, `shut_pays`   THE PAYERS, at a block that seats the lot's block alone (`IM.LaidAlone` under the
      description's own test on the reply, at a place that is not K7's): a yes of its decision, at whatever rounds and
      columns, gives the clause
  `SeatedClose c Z l Lk p Q bE bS`   what the description's makers have laid: bE and bS are the first and the third of
      the link's closing blocks (that there is no fourth is not claimed); they stand at the numbers 14 l + ‹the
      hearing blocks› + 4 and + 6 of the flat list; each seats the lot's block alone, retyped, at the sealed library's
      `IM.cAt l (IM.subAt l) 0 | 2 .K9`; the closing's numbers Q are the lot's own reading at p (`ProofFile.k10Par`): AT
      K9's TWO MEMBERS EVERY CONJUNCT OF THE SEALED ASSEMBLY IS KEPT (the middle block is K10's)
  `SeatedClose.quiet`   neither block has a round or an oracle message
  **`close_at_seat`**   WHEREVER THE DESCRIPTION CAN BE OPENED IN THE GOALS' SCOPE: at each l < 25 there are such Lk,
      p, Q, bE, bS (the sealed `IM.close_of` and `IM.close_numbers`) · `close_at_head`: so under the library's one
      head `P5J.AtMgA`
  **`SeatedClose.eqKeeps`**, **`SeatedClose.shutKeeps`**   the payers at these blocks' STEPS
On a member: the head is met under four premises on the public files, at D := dpZ Z and r := theProofRun (asDescriptionFiles Z)
alone (the library's `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean): under these `close_at_head` gives
`SeatedClose` at each l < 25; evaluated at no written description. `eq_pays` and `shut_pays` are called by the two
last and by Honest/K9/CloseYes.lean; the two last by Honest/K9/ThrClose.lean, XkClose.lean and KeepsAtPlace.lean, the
last also by XkSamples.lean; `SeatedClose.quiet` by ThrClose.lean and CloseYes.lean; `close_at_seat` by
`close_at_head`, that by Honest/K9/XkAtHead.lean.
WHAT IS NOT CLAIMED. That either block says yes at any state. That the plan's own test on the closing's numbers says
yes: neither the decision nor the step reads it. What `door` asks and lays (its text is the library's). Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K9.AtHead
import Johnson.IMR.CloseSeat
import Johnson.IMR.FirstSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- **K9's clause at "the one equation".** -/
structure EqKeeps (s s' : S) : Prop where
  mark : s'.failed = none
  reply : s'.out.reply = s.out.reply
  laid : ∃ a o, Desc.K9.atS.get? s = some a ∧ Desc.K9.door a.owed a.laid a.L a.F a.d = .ok o ∧
    s' = Desc.K9.atS.set s { a with owed := o.owed, L := o.L, F := o.F, d := o.d }

/-- **K9's clause at "the segment is shut".** -/
structure ShutKeeps (s s' : S) : Prop where
  mark : s'.failed = none
  reply : s'.out.reply = s.out.reply
  laid : ∃ L, s.link? = some L ∧ s' = s.putLink (Desc.K9.closed L L.check.frame)

/-- The payer at "the one equation". -/
theorem eq_pays {b : Block S Claim} {p : Desc.K9.Where} {ok : Bool} {name : String} {a : Place}
    (hb : IM.LaidAlone ProofFile.sameReply b
      ({ Desc.K9.oneEquation (Cl := Unit) Desc.K9.atS p with planOk := ok } : Block S Unit).retype name a)
    (hk : a.kind ≠ KindName.K7) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : b.decide s rs gs = .ok s') : EqKeeps s s' := by
  obtain ⟨h, hf, hsame⟩ := (IM.yes_alone hb hk s s' rs gs).1 hd
  have h' : (Desc.K9.atS.part s).bind (fun x => (Desc.K9.door x.owed x.laid x.L x.F x.d).bind fun o =>
      .ok (Desc.K9.atS.set s { x with owed := o.owed, L := o.L, F := o.F, d := o.d })) = .ok s' := h
  unfold ProofFile.sameReply at hsame
  refine ⟨hf, (eq_of_beq hsame).symm, ?_⟩
  cases hg : Desc.K9.atS.get? s with
  | none =>
    have e : Desc.K9.atS.part s = .error "K9.in-a-segment" := by unfold Desc.K9.Lens.part; rw [hg]; rfl
    rw [e] at h'
    exact nomatch h'
  | some x =>
    have e : Desc.K9.atS.part s = .ok x := by unfold Desc.K9.Lens.part; rw [hg]; rfl
    rw [e] at h'
    cases hdo : Desc.K9.door x.owed x.laid x.L x.F x.d with
    | error m =>
      have h2 : (Desc.K9.door x.owed x.laid x.L x.F x.d).bind (fun o =>
        (.ok (Desc.K9.atS.set s { x with owed := o.owed, L := o.L, F := o.F, d := o.d }) : Except String S)) =
          .ok s' := h'
      rw [hdo] at h2
      exact nomatch h2
    | ok o =>
      have h2 : (Desc.K9.door x.owed x.laid x.L x.F x.d).bind (fun o =>
        (.ok (Desc.K9.atS.set s { x with owed := o.owed, L := o.L, F := o.F, d := o.d }) : Except String S)) =
          .ok s' := h'
      rw [hdo] at h2
      exact ⟨x, o, rfl, hdo, (Except.ok.inj h2).symm⟩

/-- The payer at "the segment is shut". -/
theorem shut_pays {b : Block S Claim} {p : Desc.K9.Where} {piece : ℕ} {name : String} {a : Place}
    (hb : IM.LaidAlone ProofFile.sameReply b (Desc.K9.shut (Cl := Unit) p piece).retype name a)
    (hk : a.kind ≠ KindName.K7) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : b.decide s rs gs = .ok s') : ShutKeeps s s' := by
  obtain ⟨h, hf, hsame⟩ := (IM.yes_alone hb hk s s' rs gs).1 hd
  have h' : (Desc.K9.there "K9.in-a-segment" s.link?).bind (fun L =>
      (.ok (s.putLink (Desc.K9.closed L L.check.frame)) : Except String S)) = .ok s' := h
  unfold ProofFile.sameReply at hsame
  refine ⟨hf, (eq_of_beq hsame).symm, ?_⟩
  cases hl : s.link? with
  | none => rw [hl] at h'; exact nomatch h'
  | some L =>
    rw [hl] at h'
    exact ⟨L, rfl, (Except.ok.inj h').symm⟩

/-- **What the description's makers have laid at the link number l**: bE: "the one equation"; bS: "the segment is
shut". -/
structure SeatedClose (c : Chain S Claim) (Z : ProofFile.Pub) (l : ℕ) (Lk : Link S Claim) (p : Desc.K9.Where)
    (Q : Close.Par) (bE bS : Block S Claim) : Prop where
  link : c.links[l]? = some Lk
  numbers : IM.k9At Z l = some p
  par : ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q
  closeE : Lk.close[0]? = some bE
  closeS : Lk.close[2]? = some bS
  atE : c.blocksInOrder[14 * l + Lk.hear.length + 4]? = some bE
  atS : c.blocksInOrder[14 * l + Lk.hear.length + 6]? = some bS
  aloneE : IM.LaidAlone ProofFile.sameReply bE
    ({ Desc.K9.oneEquation (Cl := Unit) Desc.K9.atS p with planOk := Desc.K9.fits p Q } : Block S Unit).retype bE.name
    (IM.cAt l (IM.subAt l) 0 .K9)
  aloneS : IM.LaidAlone ProofFile.sameReply bS (Desc.K9.shut (Cl := Unit) p (Q.piece + 1)).retype bS.name
    (IM.cAt l (IM.subAt l) 2 .K9)

/-- **At each of the 25 segments**, wherever the description can be opened in the goals' scope. -/
theorem close_at_seat {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) :
    ∃ Lk p Q bE bS, SeatedClose c Z l Lk p Q bE bS := by
  obtain ⟨Lk, p, Q, e1, e2, e3, h⟩ := IM.close_of hS hR O l hl
  obtain ⟨bE, xE, hE1, hE2, hE3⟩ := h 0 .K9 rfl
  obtain ⟨bS, xS, hS1, hS2, hS3⟩ := h 2 .K9 rfl
  obtain rfl := Option.some.inj hE2
  obtain rfl := Option.some.inj hS2
  exact ⟨Lk, p, Q, bE, bS, e1, e2, e3, hE1, hS1, IM.close_numbers hS hR O hl e1 hE1,
    IM.close_numbers hS hR O hl e1 hS1, hE3, hS3⟩

/-- So under the library's one head. -/
theorem close_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) :
    ∃ Lk p Q bE bS, SeatedClose cF Zp l Lk p Q bE bS := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact close_at_seat h.scope h.reads O l hl

variable {c : Chain S Claim} {Z : ProofFile.Pub} {l : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where} {Q : Close.Par}
  {bE bS : Block S Claim}

/-- Neither block has a round or an oracle message. -/
theorem SeatedClose.quiet (H : SeatedClose c Z l Lk p Q bE bS) :
    bE.rounds = [] ∧ bE.oracles = [] ∧ bS.rounds = [] ∧ bS.oracles = [] :=
  ⟨IM.alone_rounds H.aloneE, IM.alone_oracles H.aloneE, IM.alone_rounds H.aloneS, IM.alone_oracles H.aloneS⟩

/-- **The payer at the step of "the one equation".** -/
theorem SeatedClose.eqKeeps (H : SeatedClose c Z l Lk p Q bE bS) (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List Desc.OpenedColumn) (n : ℕ) (hy : bE.step ft s rs cols = .ok (s', n)) : EqKeeps s s' :=
  eq_pays H.aloneE (show KindName.K9 ≠ KindName.K7 by decide) s s' _ _
    ((Sound.step_ok_iff ft bE s s' rs cols n).1 hy).2.2.2

/-- **The payer at the step of "the segment is shut".** -/
theorem SeatedClose.shutKeeps (H : SeatedClose c Z l Lk p Q bE bS) (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List Desc.OpenedColumn) (n : ℕ) (hy : bS.step ft s rs cols = .ok (s', n)) : ShutKeeps s s' :=
  shut_pays H.aloneS (show KindName.K9 ≠ KindName.K7 by decide) s s' _ _
    ((Sound.step_ok_iff ft bS s s' rs cols n).1 hy).2.2.2

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.close_at_seat
#print axioms ProofFile.Honest.K9.close_at_head
#print axioms ProofFile.Honest.K9.SeatedClose.quiet
#print axioms ProofFile.Honest.K9.SeatedClose.eqKeeps
#print axioms ProofFile.Honest.K9.SeatedClose.shutKeeps
#print axioms ProofFile.Honest.K9.eq_pays
#print axioms ProofFile.Honest.K9.shut_pays
#print axioms ProofFile.Honest.K9.EqKeeps
#print axioms ProofFile.Honest.K9.ShutKeeps
#print axioms ProofFile.Honest.K9.SeatedClose
