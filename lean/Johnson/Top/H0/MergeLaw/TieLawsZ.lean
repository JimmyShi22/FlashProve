-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/TieLawsZ.lean: what the merge's authors owe at the table of joints, where
the two readers of the verifier's state may hang on what was handed to the chain. One theorem with
its proof.

Why. `merge_seatLawsR` (TieLaws.lean) takes the reader of the stored samples (smp) and the decoder
of the stored table (decT) as functions of the verifier's state alone. In the composed filling of
the table both take what was handed to the chain too. The rule for a place asks its four clauses at
every such z: so the merge's law can be called at the readers at z.

What is said. `merge_seatLawsZ`: `SeatLaws` (Johnson/Desc/Sound/TiedSeat.lean) at the kind's block
`headClaimMergeKind P`, under the premises of `merge_seatLawsR` with smp z and decT z in the place of smp
and decT. The proof is that theorem's, with the law `merge_goodIn_rec` (OffRecord.lean) called at z.

Limits. Those of TieLaws.lean: the five ties and "decodes rides" are premises. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.TieLaws

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
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Cells Tok Pp : Type} (arr : ℕ → ℕ → ℕ)
  (smp : Pp → S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (rc : Cells → ℕ → ℕ → GE) (decT : Pp → (ℕ → Option (ℕ × List UInt64)) → S → Option Cells)
  {Fr : Frame}
  (claims : ℕ) (lin : OnBytes.Params.LinShape) (xM xI : Mem) (posM posI : ℕ → Bool × ℕ × ℕ)

/-- **`merge_seatLawsR` WHERE THE TWO READERS OF THE VERIFIER's STATE MAY HANG ON WHAT WAS HANDED TO
THE CHAIN**: the reader of the stored samples and the decoder of the stored table take z too, as the
composed filling's do. -/
theorem merge_seatLawsZ (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece (ckP .two) Fr (Pp × S) Claim (Wit Cells Tok MsgT)) (Nn : Numbers)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (P : HeadMergeP)
    -- the law's premises on public numbers
    {s₀ : OnBytes.Model.WsShape} {p3 : Bool} {lkW : ℕ}
    (h : OnBytes.Model.wsLayOf s₀ p3 lkW = .ok P.lay) (hn : 2 * P.lay.lk + 3 ≤ P.nMsg) (ni : ℕ)
    (hni : 0 < ni)
    -- on the reading of the oracles
    (hinM : ∀ j, j < P.nMsg → InMsg cs (xM.1.l.get xM.2).1 (posM j).1 (posM j).2.1 (posM j).2.2)
    (hinI : ∀ j, j < ni → InMsg cs (xI.1.l.get xI.2).1 (posI j).1 (posI j).2.1 (posI j).2.2)
    (hsmp : ∀ z (s : S) (a' : HeadOwn),
      smp z { s with rowsOwed := none, here := .head a' } = smp z s)
    (hdec : ∀ z c (s : S) (a' : HeadOwn),
      decT z c { s with rowsOwed := none, here := .head a' } = decT z c s)
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
      RelBehindR cs G arr (smp z) rc (decT z) claims lin xM xI posM posI P h hn ni b w)
    (t4 : ∀ (z : Pp) (a b : S × Fr.E.Str) w, onQ Nn Mg links ps (fun s => (z, s)) k a →
      ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      BehindR P h hn ni b.1 → relAt (meansQ Nn Mg fun s => (z, s)) (outsQ links ps k) b w →
      RelFrontR cs G arr (smp z) rc (decT z) xM xI posM P h hn ni a w →
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
      (merge_goodIn_rec cs G arr (smp z) rc (decT z) claims lin xM xI posM posI P h hn ni hni qds
        he hkd hinM hinI (hsmp z) (hdec z) qbase hF B' hB.1)
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

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_seatLawsZ
