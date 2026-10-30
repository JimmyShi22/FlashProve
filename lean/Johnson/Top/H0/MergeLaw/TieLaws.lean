-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/TieLaws.lean: what the merge's authors owe where a written description lays
the merge's block, in the words of the table of joints (`SeatLaws`,
Johnson/Desc/Sound/TiedSeat.lean). Two theorems with their proofs.

What is said. `merge_seatLaws`: `SeatLaws links ps k q Nn Mg (headClaimMergeKind P)`: the row's own law at
the table; what rides; a mark stays; "decodes" rides: each over every block B' that narrows the
kind's block and whose yes bears no mark. FROM:
  (a) the law's five premises on public numbers (hlay h1 hk0 hnum hunit);
  (b) four on the reading of the oracles (hinM hinI hsmp hdec);
  (c) FIVE FACTS ON THE PIECE q: its written rounds have the block's own entries (he hkd); no round
    behind (hback); its errors are the cap (herr); the two members' trees lie in front of it (hF);
  (d) FIVE TIES BETWEEN THE MERGE's OWN WORDS AND THE TABLE's, each with the promise in front, "no
    mark", the merge's own decision's yes, "the strings behind are the library's `behind` of the
    strings in front, at the piece's own base and rounds, at some transcript" and `BehindOk` in
    hand: t1: the promise in front gives `frontW`; t2: `BehindOk` gives the promise behind; t3: what
    the row opens gives `RelBehind`; t4: `RelFront` gives what the row closes; t5: what rides;
  (e) hD: "decodes" rides past the merge's yes, with the same two facts in hand.

`merge_seatLawsR`: THE SAME WITH NO NUMBER OF THE CLAIM AMONG THE LETTERS (OffRecord.lean): (a)
shrinks to: the layout is a return of `wsLayOf`; 2 lk + 3 ≤ nMsg; 0 < ni; the ties speak of
`frontR`, `BehindR`, `RelFrontR`, `RelBehindR`: so t1 asks of the promise in front the ledger's
sizes and "the ledger has the plan's number of slots" alone.

Paid here, no premises: the law itself at every such B' and at the cap (`merge_goodIn_cap`,
AtSeat.lean), through the wide door (`ownAtTableWide`, Johnson/Desc/Sound/BordersQ.lean); a mark
stays (`seat_mark`); what the strings behind are (`out_behind`); that the piece's yes is the merge's
own decision's yes (`seat_yes`).

Limits. SHOWN AT NO FILLING: t1 to t5 and hD are premises on the table's letters; whether one
filling meets them all is not tried. At the clock `ckP .two` and the witness `Wit Cells Tok MsgT`.
The five facts on the piece come of the tiling: not called here. Of `SeatOf` the first half alone is
spent. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.MergeLaw.OffRecord
import Johnson.Desc.Sound.TiedSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block FileDescription Place Wit Claim)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn ModelPart Meaning Numbers start)
open Johnson.Pack (sigOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeDecide mergeEntries)

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (rc : Cells → ℕ → ℕ → GE) (decT : (ℕ → Option (ℕ × List UInt64)) → S → Option Cells)
  {Pl : K11Caller.Place} (N : K11Caller.Nums Pl) {Fr : Frame}
  (claims : ℕ) (lin : OnBytes.Params.LinShape) (xM xI : Mem) (posM posI : ℕ → Bool × ℕ × ℕ)

/-- **WHAT THE MERGE's AUTHORS OWE AT THE MERGE's PLACE** (`SeatLaws`), at the kind's own block. -/
theorem merge_seatLaws {Pp : Type} (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece (ckP .two) Fr (Pp × S) Claim (Wit Cells Tok MsgT)) (Nn : Numbers)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (P : HeadMergeP)
    -- the law's premises on public numbers
    (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1) (hk0 : 0 < Pl.lay.lk)
    (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg)
    (hunit : ∀ a u, Pl.lay.U[Pl.ui a]? = some u → OnBytes.Road.UnitOK Pl.lay.lk u)
    -- on the reading of the oracles
    (hinM : ∀ j, j < N.ns → InMsg cs (xM.1.l.get xM.2).1 (posM j).1 (posM j).2.1 (posM j).2.2)
    (hinI : ∀ j, j < N.ni → InMsg cs (xI.1.l.get xI.2).1 (posI j).1 (posI j).2.1 (posI j).2.2)
    (hsmp : ∀ (s : S) (a' : HeadOwn), smp { s with rowsOwed := none, here := .head a' } = smp s)
    (hdec : ∀ c (s : S) (a' : HeadOwn),
      decT c { s with rowsOwed := none, here := .head a' } = decT c s)
    -- the facts on the piece
    (he : q.ds.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ q.ds, Fmt.kindOf d.entry.name = some d.kind) (hback : q.back = [])
    (herr : q.err = Err.cap 128 (uLT (ckP .two) q.ds)) (hF : Fenced q.base [xM, xI])
    -- four ties between the merge's own words and the table's; the fifth, what rides, beneath
    (t1 : ∀ (z : Pp) (a : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none →
      frontW N a.1 = true)
    (t2 : ∀ (z : Pp) (a b : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      BehindOk N b.1 → onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b)
    (t3 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      BehindOk N b.1 → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w →
      RelBehind cs G arr smp rc decT N claims lin xM xI posM posI b w)
    (t4 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      BehindOk N b.1 → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w →
      RelFront cs G arr smp rc decT N xM xI posM a w →
      relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps k) a w)
    -- what rides
    (t5 : ∀ (z : Pp) (a b : S × Fr.E.Str) w i, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ Nn Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ Nn Mg (fun s => (z, s)) i a w)
    -- "decodes" rides past the merge's yes
    (hD : ∀ (z : Pp) (a b : S × Fr.E.Str), (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      Mg.decodes (z, a.1) (strsOf Fr a.2) →
      Mg.decodes (z, b.1) (strsOf Fr b.2)) :
    SeatLaws links ps k q Nn Mg (headClaimMergeKind P) := by
  obtain ⟨qb, qbase, qds, qback, qext, qerr⟩ := q
  simp only at he hkd hback herr hF
  subst hback
  subst herr
  have hy : ∀ B' : Block S Claim, SeatOf (headClaimMergeKind P) B' → ∀ (a b : S × Fr.E.Str)
      (τ : Iop.Tr (uLT (ckP .two) qds)),
      (⟨below B', qbase, qds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) qds)⟩ :
        Piece (ckP .two) Fr S Claim (Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      (∃ rs, headMergeDecide P a.1 rs = .ok b.1) ∧
        (∃ τ' : Iop.Tr (uLT (ckP .two) qds), b.2 = behind (ckP .two) Fr qbase qds a.2 τ') ∧
        b.1.failed = a.1.failed := by
    intro B' hB a b τ h
    refine ⟨seat_yes P (⟨below B', qbase, qds, [], fun _ _ w => w,
        Err.cap 128 (uLT (ckP .two) qds)⟩ : Piece (ckP .two) Fr S Claim (Wit Cells Tok MsgT))
        B' hB.1 rfl a b τ h,
      ⟨τ, out_behind (⟨below B', qbase, qds, [], fun _ _ w => w,
        Err.cap 128 (uLT (ckP .two) qds)⟩ : Piece (ckP .two) Fr S Claim (Wit Cells Tok MsgT))
        a b τ h⟩,
      seat_mark P (⟨below B', qbase, qds, [], fun _ _ w => w,
        Err.cap 128 (uLT (ckP .two) qds)⟩ : Piece (ckP .two) Fr S Claim (Wit Cells Tok MsgT))
        B' hB.1 rfl a b τ h⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B' hB z
    refine ownAtTableWide _ _ _ _ _ _ Nn Mg links ps (fun s => (z, s)) k _ _ _ _ _
      (merge_goodIn_cap cs G arr smp rc decT N claims lin xM xI posM posI P hlay h1 hk0 hnum hunit
        qds he hkd hinM hinI hsmp hdec qbase hF B' hB.1)
      (t1 z) ?_ ?_ ?_ ?_ ?_
    · intro a τ b ha hm h ho
      exact t2 z a b ha hm (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 ho
    · intro a τ b w ha hm h ho hw
      exact t3 z a b w ha hm (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 ho hw
    · intro a τ b w ha hm h ho hw hr
      exact t4 z a b w ha hm (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 ho hw hr
    · intro a τ b h hm
      rw [(hy B' hB a b τ h).2.2]
      exact hm
    · intro a τ b h hd
      exact hD z a b (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 hd
  · intro B' hB z a τ b w i ha hm h hb hr ho hi
    exact t5 z a b w i ha hm (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 hb hr ho hi
  · intro B' hB a τ b h hm
    rw [(hy B' hB a b τ h).2.2]
    exact hm
  · intro B' hB z a τ b h hd
    exact hD z a b (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 hd


/-- **THE SAME WITH NO NUMBER OF THE CLAIM AMONG THE LETTERS**: the unit, the slot of the claim's
value and the entry of the index masks' message are read off the record (OffRecord.lean). -/
theorem merge_seatLawsR {Pp : Type} (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece (ckP .two) Fr (Pp × S) Claim (Wit Cells Tok MsgT)) (Nn : Numbers)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (P : HeadMergeP)
    -- the law's premises on public numbers
    {s₀ : OnBytes.Model.WsShape} {p3 : Bool} {lkW : ℕ}
    (h : OnBytes.Model.wsLayOf s₀ p3 lkW = .ok P.lay) (hn : 2 * P.lay.lk + 3 ≤ P.nMsg) (ni : ℕ)
    (hni : 0 < ni)
    -- on the reading of the oracles
    (hinM : ∀ j, j < P.nMsg → InMsg cs (xM.1.l.get xM.2).1 (posM j).1 (posM j).2.1 (posM j).2.2)
    (hinI : ∀ j, j < ni → InMsg cs (xI.1.l.get xI.2).1 (posI j).1 (posI j).2.1 (posI j).2.2)
    (hsmp : ∀ (s : S) (a' : HeadOwn), smp { s with rowsOwed := none, here := .head a' } = smp s)
    (hdec : ∀ c (s : S) (a' : HeadOwn),
      decT c { s with rowsOwed := none, here := .head a' } = decT c s)
    -- the facts on the piece
    (he : q.ds.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ q.ds, Fmt.kindOf d.entry.name = some d.kind) (hback : q.back = [])
    (herr : q.err = Err.cap 128 (uLT (ckP .two) q.ds)) (hF : Fenced q.base [xM, xI])
    -- four ties between the merge's own words and the table's; the fifth, what rides, beneath
    (t1 : ∀ (z : Pp) (a : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none →
      frontR P a.1 = true)
    (t2 : ∀ (z : Pp) (a b : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      BehindR P h hn ni b.1 → onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b)
    (t3 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      BehindR P h hn ni b.1 → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w →
      RelBehindR cs G arr smp rc decT claims lin xM xI posM posI P h hn ni b w)
    (t4 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      BehindR P h hn ni b.1 → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w →
      RelFrontR cs G arr smp rc decT xM xI posM P h hn ni a w →
      relAt (meansQ Nn Mg fun s => (z, s)) (insQ links ps k) a w)
    -- what rides
    (t5 : ∀ (z : Pp) (a b : S × Fr.E.Str) w i, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ Nn Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ Nn Mg (fun s => (z, s)) i a w)
    -- "decodes" rides past the merge's yes
    (hD : ∀ (z : Pp) (a b : S × Fr.E.Str), (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      Mg.decodes (z, a.1) (strsOf Fr a.2) →
      Mg.decodes (z, b.1) (strsOf Fr b.2)) :
    SeatLaws links ps k q Nn Mg (headClaimMergeKind P) := by
  obtain ⟨qb, qbase, qds, qback, qext, qerr⟩ := q
  simp only at he hkd hback herr hF
  subst hback
  subst herr
  have hy : ∀ B' : Block S Claim, SeatOf (headClaimMergeKind P) B' → ∀ (a b : S × Fr.E.Str)
      (τ : Iop.Tr (uLT (ckP .two) qds)),
      (⟨below B', qbase, qds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) qds)⟩ :
        Piece (ckP .two) Fr S Claim (Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      (∃ rs, headMergeDecide P a.1 rs = .ok b.1) ∧
        (∃ τ' : Iop.Tr (uLT (ckP .two) qds), b.2 = behind (ckP .two) Fr qbase qds a.2 τ') ∧
        b.1.failed = a.1.failed := by
    intro B' hB a b τ h
    refine ⟨seat_yes P (⟨below B', qbase, qds, [], fun _ _ w => w,
        Err.cap 128 (uLT (ckP .two) qds)⟩ : Piece (ckP .two) Fr S Claim (Wit Cells Tok MsgT))
        B' hB.1 rfl a b τ h,
      ⟨τ, out_behind (⟨below B', qbase, qds, [], fun _ _ w => w,
        Err.cap 128 (uLT (ckP .two) qds)⟩ : Piece (ckP .two) Fr S Claim (Wit Cells Tok MsgT))
        a b τ h⟩,
      seat_mark P (⟨below B', qbase, qds, [], fun _ _ w => w,
        Err.cap 128 (uLT (ckP .two) qds)⟩ : Piece (ckP .two) Fr S Claim (Wit Cells Tok MsgT))
        B' hB.1 rfl a b τ h⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro B' hB z
    refine ownAtTableWide _ _ _ _ _ _ Nn Mg links ps (fun s => (z, s)) k _ _ _ _ _
      (merge_goodIn_rec cs G arr smp rc decT claims lin xM xI posM posI P h hn ni hni qds he hkd
        hinM hinI hsmp hdec qbase hF B' hB.1)
      (t1 z) ?_ ?_ ?_ ?_ ?_
    · intro a τ b ha hm h ho
      exact t2 z a b ha hm (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 ho
    · intro a τ b w ha hm h ho hw
      exact t3 z a b w ha hm (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 ho hw
    · intro a τ b w ha hm h ho hw hr
      exact t4 z a b w ha hm (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 ho hw hr
    · intro a τ b h hm
      rw [(hy B' hB a b τ h).2.2]
      exact hm
    · intro a τ b h hd
      exact hD z a b (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 hd
  · intro B' hB z a τ b w i ha hm h hb hr ho hi
    exact t5 z a b w i ha hm (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 hb hr ho hi
  · intro B' hB a τ b h hm
    rw [(hy B' hB a b τ h).2.2]
    exact hm
  · intro B' hB z a τ b h hd
    exact hD z a b (hy B' hB a b τ h).1 (hy B' hB a b τ h).2.1 hd

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_seatLaws
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_seatLawsR
