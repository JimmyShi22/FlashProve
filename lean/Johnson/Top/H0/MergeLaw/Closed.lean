-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Closed.lean: the merge's law at the closed caller: the typed record of the
proved block is no letter any more: it is the record that Johnson/Top/H0/K11Caller/AtSlots.lean
makes
of a place's public data and of the numbers of the slots (`GS`). Definitions, and theorems with
their
proofs.

Against `merge_plain` and `merge_leads` (Plain.lean, AtPiece.lean) three premises inside `MergeSays`
are paid: "the typed target at the drawn element is the reading of the ledger's public part"
(`tg_at`) and the two premises (D1), (D2) of the library's theorem on a sumcheck's row (`D1_at`,
`D2_at`).

Main names:
  `FrontIs`: the condition in front: the typed statement is read off the record (its ledger, its
    claim), and the numbers of the slots are the record's (the slot of the claim's value; the
    ledger's next free slot).
  `ClosedSays`: what the merge's yes says. The values heard, pinned by facts on the two records,
    among them the first of the sumcheck's own slots, the number 2 lk + 2 of the hiding
    polynomial's coefficients (the slots that the run fills late), and its start form; and the
    implication below.
  `merge_closed`: at the written rounds, one statement at a time.
  `merge_closed_leads`: at a piece: for each fixed tuple of entries m, `Reduction.Leads` of the
    piece's reduction, on the statements with `FrontIs`, towards `ClosedSays`.

WHAT STAYS A PREMISE, ONE BY ONE. Inside `ClosedSays`, in front of "the claim on the weights holds":
  (p1) Rd: what rides: a letter of the record.
  (p2) there is a world W with `Fits2`: under each of the sumcheck's own slots lies its mask entry,
       under the slot of the claim's value lies "shown - factor * mask entry";
       `K11Caller.world_at` gives such a world from a later ledger that holds 0 and -1 under the own
       slots and has kept the claim's slot; that a run's ledger is such is not shown.
  (p3) in that world the row form at the sent end value is worth 0: the claim that the kind's run
       hands on, which the batching tests.
  (p4) the summand at the point is the sent value less the mask entry times the last challenge: the
       row on the end value, which the rows on the committed matrix pay.
Outside it: (p5) `FrontIs`; (p6) `MergeDs` of the written rounds, which are letters; (p7) the place
has one claim and the layout's number of column bits is the block's; (p8) the entries m stand
outside the game: no pin is laid here.
BESIDE THESE EIGHT the statements have: hk: the written rounds in the middle are as many as the
typed record's column bits. In `merge_closed` alone: the maps pass, the stretch fits the declared
rounds, and the drawn words are below the prime; `merge_closed_leads` pays these three. In
`merge_closed_leads`: rd, base and ext are letters. Pl and N are letters: they are tied to the
block's parameters P and to the record by four equations alone (N.svA and N.first in `FrontIs`;
Pl.n = 1; the number of column bits). THAT THE PLACE's LAYOUT IS P.lay IS ASKED NOWHERE, though
wo.recs is made of P.lay and the typed claim of Pl: whoever pays (p4) has to bring that tie.

Limits. It is no soundness of the protocol. The error is held against no price. What the typed claim
says in the library's output matrix is Johnson/Top/H0/K11Caller/HeadSays.lean's. Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.AtPiece
import Johnson.Top.H0.K11Caller.AtSlots
import OnBytes.Tie.Pv.Tail.EndClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes (E zeroE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Psc (Weight)
open OnBytes.Model (Reading World wsForkStart)
open OnBytes.Model.Road (Ended)
open VerifiableInference.Desc (Claim roundsFit noDigest fieldPrimeWord)
open VerifiableInference.Desc.Sound (Frame Piece below)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headClaimMergeKind)
open OnBytes.Tie.Pv.Lay.Eng (SumSaid sum_said sumTr sumOut sum_end merge_fits)
open K11Caller (MergeIn GS Fits2 tg_at D1_at D2_at)
open _root_.Run (ckP)

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl)
  (Rd : MergeIn Pl.n → (Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE) → Prop)

/-- The typed statement st is read off the record s, and the numbers of the slots are the record's:
the ledger; the claim; the slot of the claim's value; the ledger's next free slot. -/
def FrontIs (st : MergeIn Pl.n) (s : S) : Prop :=
  ∀ (a : HeadOwn) (claim : OnBytes.Model.WsClaim) (x0 : OnBytes.Model.Head.Heard), s.here = .head a
      → a.claim = some claim → a.x = some x0 →
    st.F = a.F ∧ (∀ i, st.cl i = claim) ∧ N.svA = #[x0.sV] ∧ N.first = a.F.next

/-- **What the merge's yes says at the closed caller.** The values heard, pinned by facts on the two
records; and: if what rides holds, the row form at the sent end value is worth 0 in a world that
gives the sumcheck's own slots their mask entries and the claim's slot «shown - factor * mask entry»
(Fits2), and the summand at the point is the sent value less the mask entry times the last
challenge, then the claim on the weights holds. -/
def ClosedSays (P : HeadMergeP) (m : Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE) (st : MergeIn Pl.n) (s s'
    : S) : Prop :=
  ∃ (a a' : HeadOwn) (claim : OnBytes.Model.WsClaim) (x0 : OnBytes.Model.Head.Heard) (wo :
      OnBytes.Model.WsForkOut)
    (x mu cY beta v T : E) (qs : List (Nat × List E × E)) (hβ : Reading.gl.val beta ≠ 0),
    s.here = .head a ∧ s'.here = .head a' ∧ a.claim = some claim ∧ a.x = some x0 ∧ a'.wo = some wo ∧
    a.F.publicPart (wsForkStart #[x0.sV] (OnBytes.Model.powers x 1)) = some T ∧ wo.p.target = T ∧
        wo.beta = beta ∧
    wo.p.first = a.F.next ∧ wo.p.start = wsForkStart #[x0.sV] (OnBytes.Model.powers x 1) ∧
    wo.p.walk.1.length = 2 * P.lay.lk + 2 ∧
    wo.rm.toList = qs.map (·.2.2) ∧
    wo.recs = (#[claim].zip (OnBytes.Model.powers x 1)).toList.map (fun y =>
      OnBytes.Model.wsRowPart P.lay y.1 (OnBytes.mulE y.2 (OnBytes.Model.wsEpsT P.lay y.1 wo.rm))) ∧
    (∃ Gf : OnBytes.Model.Fork, ({ a.F with next := a.F.next + 1 + 2 * P.lay.lk + 2 } :
        OnBytes.Model.Fork).hideRun wo.sFv #[v] beta =
      some Gf ∧ Gf.shown wo.sFv = some wo.fvp ∧ a'.F = { Gf with planClaimsF := P.nLin }) ∧
    (Rd st m →
      (∃ W : World GE, Fits2 Reading.gl N st m W ∧ (wo.p.rowForm v {}).value Reading.gl W = 0) →
      (GS Reading.gl N Rd).L.f (st, Reading.gl.val x) m ((GS Reading.gl N Rd).L.toSum.Q.outPt (GS
          Reading.gl N Rd).L.toSum.M
          (sumOut Reading.gl (GS Reading.gl N Rd).L.toSum (fun st => pick ((GS Reading.gl N
              Rd).L.toSum.T.par.vars st)) (st, Reading.gl.val x) wo.p.target mu
            wo.p.eps (qs.map fun q => (q.2.1, q.2.2)) [cY] beta hβ fun _ => Reading.gl.val v)) =
        Reading.gl.val v - m (GS Reading.gl N Rd).L.cAt * Reading.gl.val beta →
      ∀ c, (GS Reading.gl N Rd).Cl st m c)

/-- The number of the hiding polynomial's coefficients at k plain rounds of degree 2 and the closing
round. -/
theorem entries_merge (k : ℕ) :
    OnBytes.Psc.hidingEntries (List.replicate k (Weight.plain 3) ++ [Weight.atZero (1 + 1)]) = 2 * k
        + 2 := by
  simp [OnBytes.Psc.hidingEntries, Weight.plain, Weight.atZero, Weight.equality]
  omega

/-- **The merge's law at its written rounds, at the closed caller, one statement at a time.** -/
theorem merge_closed (P : HeadMergeP) (Ex : ExtSpec) {dZ d0 : RDT} {ds : List RDT} {dY dV : RDT}
    (hk : ds.length = (GS Reading.gl N Rd).k) (hkP : (GS Reading.gl N Rd).k = P.lay.lk) (h1 : Pl.n =
        1)
    (H : MergeDs dZ d0 ds dY dV) (m : Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE) (a : MergeIn Pl.n ×
        Ex.Str) (s : S)
    (hfr : FrontIs N a.1 s) :
    Doomed (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV])))
      ((mergeMaps (GS Reading.gl N Rd) Ex dZ d0 ds dY dV hk).err ((GS Reading.gl N Rd).eps (Kc :=
          Unit) ((GS Reading.gl N Rd).L.V1 Ex))) (fun τ =>
      (mergeMaps (GS Reading.gl N Rd) Ex dZ d0 ds dY dV hk).pass τ = true →
      roundsFit (headClaimMergeKind P).rounds ((rvT (ckP .two) _ τ).map noDigest) = true →
      (∀ r ∈ (rvT (ckP .two) _ τ).map noDigest, ∀ x ∈ r.drawn.elems, x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧
          x.2.2 < fieldPrimeWord) →
      ∀ s', headMergeDecide P s ((rvT (ckP .two) _ τ).map noDigest) = .ok s' → ClosedSays N Rd P m
          a.1 s s') := by
  refine merge_carry P (GS Reading.gl N Rd) Ex hk H _ s _ (ClosedSays N Rd P m a.1 s)
    (K11Caller.G_mid (GS Reading.gl N Rd) ((GS Reading.gl N Rd).L.V1 Ex) m a) ?_
  intro τ s' hf hw h hbad
  obtain ⟨h0, a', claim, x0, wo, x, mu, cY, beta, v, T, qs, hβ, e1, e2, e3, e4, e5, e6, e7, e8, hn,
      hq, hrm, hrecs, hE, hled,
    hview⟩ := decide_view P (GS Reading.gl N Rd) Ex hk τ hf hw h
  obtain ⟨fF, _, fsv, ffirst⟩ := hfr h0 claim x0 e1 e3 e4
  refine ⟨h0, a', claim, x0, wo, x, mu, cY, beta, v, T, qs, hβ, e1, e2, e3, e4, e5, e6, e7, e8,
      hE.first, hE.start,
    hE.walkLen.trans (entries_merge P.lay.lk), hrm, hrecs, hled, ?_⟩
  intro hRd hrow hev
  have hpub : a.1.F.publicPart (wsForkStart N.svA (OnBytes.Model.powers x 1)) = some T := by
    rw [fF, fsv]
    exact e6
  have hr : ∀ i : Fin Pl.n, Reading.gl.val ((OnBytes.Model.powers x 1).getD i.val zeroE) =
      Reading.gl.val x ^ (i : ℕ) :=
    fun i => OnBytes.Tie.Pv.Tail.Port.powers_val Reading.gl x 1 i.val (by have := i.isLt; omega)
  have htg := tg_at Reading.gl N Rd a.1 (Reading.gl.val x) (OnBytes.Model.powers x 1) T hpub hr
  obtain ⟨W, hW, hz⟩ := hrow
  have D1 : (GS Reading.gl N Rd).L.toSum.T.par.W (a.1, Reading.gl.val x) m =
      OnBytes.Road.Hd.place W.slot ((GS Reading.gl N Rd).L.toSum.T.par.vars (a.1, Reading.gl.val x))
          wo.p.first := by
    rw [hE.first, ← ffirst]
    exact D1_at Reading.gl N Rd (a.1, Reading.gl.val x) m W hW
  have D2 : (GS Reading.gl N Rd).L.toSum.T.par.inc (a.1, Reading.gl.val x) m =
      Reading.gl.val wo.p.target - wo.p.start.value Reading.gl W := by
    rw [e7, hE.start, ← fsv]
    exact D2_at Reading.gl N Rd (a.1, Reading.gl.val x) m W hW (OnBytes.Model.powers x 1) T hpub hr
  rw [← hkP] at hE hn
  obtain ⟨tRow, tEnd⟩ := tie_of_ended (v := v) (GS Reading.gl N Rd).L hE hn hq (a.1, Reading.gl.val
      x) hβ
  rw [hview] at hbad
  have hout := typed_out (GS Reading.gl N Rd) Ex a.1 a.2 x mu wo.p.eps cY beta v T (qs.map fun q =>
      (q.2.1, q.2.2)) hβ htg
  rw [← e7] at hout
  refine hbad (_, _) (congrArg (Option.map fun xo => (xo, ((GS Reading.gl N Rd).blk ((GS Reading.gl
      N Rd).L.V1 Ex)).imp a.2 _)) hout) hRd ?_ ?_
  · exact ((GS Reading.gl N Rd).L.row_iff _ m).1 ((uholds_conv (GS Reading.gl N Rd).L _ m).2 ((tRow
      Ex a.2 W m D1 D2).1 hz))
  · exact (ev_conv (GS Reading.gl N Rd).L _ m).2 ((tEnd m).2 hev)

variable {F : Frame} {W : Type}

/-- **THE MERGE's LAW AT A PIECE, AT THE CLOSED CALLER, IN THE PLAIN FORM, THE ENTRIES OUTSIDE THE
GAME.** -/
theorem merge_closed_leads (P : HeadMergeP) {dZ d0 : RDT} {ds : List RDT} {dY dV : RDT}
    (hk : ds.length = (GS Reading.gl N Rd).k) (hkP : (GS Reading.gl N Rd).k = P.lay.lk) (h1 : Pl.n =
        1)
    (H : MergeDs dZ d0 ds dY dV) (base : ℕ)
    (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
    (rd : S × F.E.Str → MergeIn Pl.n) (m : Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE) :
    (mergePiece F W P (GS Reading.gl N Rd) dZ d0 ds dY dV hk base ext).ior.red.Leads (fun a =>
        FrontIs N (rd a) a.1)
      (fun a a' => ClosedSays N Rd P m (rd a) a.1 a'.1)
      (mergePiece F W P (GS Reading.gl N Rd) dZ d0 ds dY dV hk base ext).err := by
  intro a ha
  refine Doomed.mono _ _ ?_ (merge_closed N Rd P F.E hk hkP h1 H m (rd a, a.2) a.1 ha)
  intro τ hτ a' ha'
  obtain ⟨hp, hfit, hw, gs, hdec⟩ := piece_yes (headClaimMergeKind P)
    (mergePiece F W P (GS Reading.gl N Rd) dZ d0 ds dY dV hk base ext) rfl rfl a a' τ ha'
  exact hτ (pass_of_passT _ τ hp) (by rw [roundsFit_noDigest]; exact hfit) hw a'.1 hdec

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_closed
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_closed_leads
