-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/TiesReached.lean: the sub-protocol of the merge of the claims on the
committed table, at its place in the IOP as written in Lean, is tied to the table of joints, in the
form in which each tie has beside the table's condition a condition Rch that every accepting step
hands on. One theorem with its proof.

Why. Three of the merge's ties need facts on the verifier's state that the table's condition does
not say: they hold at the states that the verifier reaches. The form `TiedAtR`
(Johnson/Desc/Sound/ChainOfPromisesR.lean) lets a tie take Rch k at the state in front.

What is said. `merge_tiedAtR`: `TiedAtR Nn Mg links ps id Rch k (q.withMap E)`, for a piece q that
holds, beneath the lift over the public part, the strict reading of a sub-protocol B that narrows
the merge's and whose accepting step bears no mark. By the two rules that are general in the kind
(`tiedAtR_of_seat`, `goodInR_of_each`: Johnson/Top/H0/TiedAtSeatR.lean), the merge's law
(`merge_goodIn_rec`, OffRecord.lean) and the ties `merge_t1_fill`, `merge_t3`, `merge_t4`
(TieThreeFour.lean).

ITS PREMISES.
  The law's, on public numbers and on the reading of the oracle messages: h, hn, hni, hinM, hinI,
    hsmp, hdec. On the piece: he, hkd, hback, herr, hF.
  On the filling: M : `MergeFill`, AT ONE CLAIM (shown at the composed meaning at its own number of
    claims, under premises: that this number is 1 at the output head's segment is a closed fact on
    the planner's numbers, asked by neither theorem: Johnson/Desc/Sound/MgAt/K11.lean).
  On a reached state in front: hFr: the table's condition, Rch k and "no mark" give `MergeFront`
    (EntryFront.lean): four facts. hB: a closed test on the planner's numbers: `pendAllB`
    (PendOfAll.lean). hWa: they give Wa. hWb: with the accepting step they give Wb behind.
  hcb: what the row reads rides back (paid at the composed filling's form of the pins: `merge_hcb`,
    CtxBack.lean).
  t2: THE SECOND TIE, WHOLE: the table's condition behind. t5: what is open and is not the row's
    rides back. hD: "decodes" rides. Each with Rch k in hand where the form grants it.

Limits. t2, t5 and hD are premises: the merge's share of the second tie stands in TieOneTwo.lean and
RowReturns.lean; the public test that the table ties to the run of forms which the row opens is made
by no lemma yet. hFr, hWa and hWb are shown at no Rch.
(Where this and lean/THEOREM.md differ, the page
holds.) At Rch := never the theorem says nothing.
Nothing on soundness.
-/
import Johnson.Top.H0.MergeLaw.TieLawsZ
import Johnson.Top.H0.MergeLaw.CtxBack
import Johnson.Top.H0.MergeLaw.EntryFront
import Johnson.Top.H0.TiedAtSeatR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open OnBytes.Model (WsShape wsLayOf)
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block FileDescription Place Wit Claim)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn ModelPart Item Meaning Numbers start)
open Johnson.Pack (sigOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeDecide mergeEntries)

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Cells Tok Pp : Type} (arr : ℕ → ℕ → ℕ)
  (smp : Pp → S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (rc : Cells → ℕ → ℕ → GE) (decT : Pp → (ℕ → Option (ℕ × List UInt64)) → S → Option Cells)
  {Fr : Frame}
  (lin : OnBytes.Params.LinShape) (xM xI : Mem) (posM posI : ℕ → Bool × ℕ × ℕ)

/-- **THE MERGE's SUB-PROTOCOL AT ITS PLACE IS TIED, IN THE FORM WITH A CONDITION THAT EVERY
ACCEPTING STEP HANDS ON.** -/
theorem merge_tiedAtR (links : List ModelPart) (ps : List Place) (k m : ℕ)
    (q : Piece (ckP .two) Fr (Pp × S) Claim (Wit Cells Tok MsgT)) (P : HeadMergeP)
    (B : Block S Claim) (hS : SeatOf (headClaimMergeKind P) B)
    (hqb : q.b = (below B).lift Prod.snd fun t s => (t.1, s))
    (Nn : Numbers) (Mg : Meaning Pp (Wit Cells Tok MsgT))
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop)
    (E : (Pp × S) × Fr.E.Str → (Pp × S) × Fr.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (hE : ∀ a b w, E a b w = w)
    -- the law's premises on public numbers and on the reading of the oracle messages
    {s₀ : WsShape} {p3 : Bool} {lkW : ℕ} (h : wsLayOf s₀ p3 lkW = .ok P.lay)
    (hn : 2 * P.lay.lk + 3 ≤ P.nMsg) (ni : ℕ) (hni : 0 < ni)
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
    -- the premises on the filling
    (own : List (ℕ × ℕ)) (R : ℕ) (Wa Wb : S → Prop)
    (M : MergeFill cs G arr smp rc decT 1 lin xM xI posM posI P h hn ni own R Wa Wb Nn Mg links ps k
      m)
    -- the facts on a reached state in front
    (hFr : ∀ (z : Pp) (a : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none → MergeFront own xM R ni a.1)
    -- a closed test on the planner's numbers
    (hB : pendAllB P.lay lin = true)
    (hWa : ∀ (z : Pp) (a : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none → Wa a.1)
    (hWb : ∀ (z : Pp) (a b : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none → (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      Wb b.1)
    -- what the row reads rides back
    (hcb : ∀ (z : Pp) (a b : S × Fr.E.Str) w, (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      ∀ i ∈ [Item.pinW, .pin m 0, .pinI], meansQ Nn Mg (fun s => (z, s)) i b w →
        meansQ Nn Mg (fun s => (z, s)) i a w)
    -- the second tie, what rides, and "decodes rides"
    (t2 : ∀ (z : Pp) (a b : S × Fr.E.Str), onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      BehindR P h hn ni b.1 → onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b)
    (t5 : ∀ (z : Pp) (a b : S × Fr.E.Str) w i, onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      onQ Nn Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ Nn Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ Nn Mg (fun s => (z, s)) i a w)
    (hD : ∀ (z : Pp) (a b : S × Fr.E.Str), (∃ rs, headMergeDecide P a.1 rs = .ok b.1) →
      (∃ τ : Iop.Tr (uLT (ckP .two) q.ds), b.2 = behind (ckP .two) Fr q.base q.ds a.2 τ) →
      Mg.decodes (z, a.1) (strsOf Fr a.2) → Mg.decodes (z, b.1) (strsOf Fr b.2)) :
    TiedAtR Nn Mg links ps (fun a => a) Rch k (q.withMap E) := by
  obtain ⟨qb, qbase, qds, qback, qext, qerr⟩ := q
  simp only at he hkd hback herr hF hqb hcb t2 t5 hD
  subst hback
  subst herr
  have hy : ∀ (a b : S × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) qds)),
      (⟨below B, qbase, qds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) qds)⟩ :
        Piece (ckP .two) Fr S Claim (Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      (∃ rs, headMergeDecide P a.1 rs = .ok b.1) ∧
        (∃ τ' : Iop.Tr (uLT (ckP .two) qds), b.2 = behind (ckP .two) Fr qbase qds a.2 τ') ∧
        b.1.failed = a.1.failed := by
    intro a b τ hb
    exact ⟨seat_yes P (⟨below B, qbase, qds, [], fun _ _ w => w,
        Err.cap 128 (uLT (ckP .two) qds)⟩ : Piece (ckP .two) Fr S Claim (Wit Cells Tok MsgT))
        B hS.1 rfl a b τ hb,
      ⟨τ, out_behind (⟨below B, qbase, qds, [], fun _ _ w => w,
        Err.cap 128 (uLT (ckP .two) qds)⟩ : Piece (ckP .two) Fr S Claim (Wit Cells Tok MsgT))
        a b τ hb⟩,
      seat_mark P (⟨below B, qbase, qds, [], fun _ _ w => w,
        Err.cap 128 (uLT (ckP .two) qds)⟩ : Piece (ckP .two) Fr S Claim (Wit Cells Tok MsgT))
        B hS.1 rfl a b τ hb⟩
  have hMark : ∀ a τ b,
      (⟨below B, qbase, qds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) qds)⟩ :
        Piece (ckP .two) Fr S Claim (Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      a.1.failed ≠ none → b.1.failed ≠ none := by
    intro a τ b hb hm
    rw [(hy a b τ hb).2.2]
    exact hm
  refine tiedAtR_of_seat links ps k B _ hqb Nn Mg Rch E hE ?_ ?_ hMark ?_
  · intro z
    refine goodInR_of_each Nn Mg links ps z k (fun a => Rch k ((z, a.1), a.2)) _
      (fun _ _ _ => rfl) ?_ hMark (fun a τ b hb hd => hD z a b (hy a b τ hb).1 (hy a b τ hb).2.1 hd)
    intro a₀ ha hr hm
    refine ⟨_, _, _, _,
      merge_goodIn_rec cs G arr (smp z) rc (decT z) 1 lin xM xI posM posI P h hn ni hni qds he hkd
        hinM hinI (hsmp z) (hdec z) qbase hF B hS.1,
      merge_t1_fill M z a₀ ha hm, ?_⟩
    intro τ b hb ho
    obtain ⟨⟨rs, hyes⟩, hbeh, _⟩ := hy a₀ b τ hb
    have F := hFr z a₀ ha hr hm
    refine ⟨t2 z a₀ b ha hr hm ⟨rs, hyes⟩ hbeh ho, fun w hw => ⟨?_, fun hq => ?_⟩⟩
    · exact merge_t3 M z b w (F.he hyes) (F.maskBehind hyes) (F.hasRow hyes hB)
        (hWb z a₀ b ha hr hm ⟨rs, hyes⟩) ho hw
    · exact merge_t4 M z a₀ b w hm F.mask (hWa z a₀ ha hr hm) hw (hcb z a₀ b w ⟨rs, hyes⟩ hbeh) hq
  · intro z a τ b w i ha hr hm hb hon hall hi hin
    exact t5 z a b w i ha hr hm (hy a b τ hb).1 (hy a b τ hb).2.1 hon hall hi hin
  · intro z a τ b hb hd
    exact hD z a b (hy a b τ hb).1 (hy a b τ hb).2.1 hd

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_tiedAtR
