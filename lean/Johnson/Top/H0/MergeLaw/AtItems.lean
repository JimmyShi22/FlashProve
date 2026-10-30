-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/AtItems.lean: the merge's law in the three items on the program's records
(Johnson/Top/H0/K11Caller/Items.lean): from "the claim that the merge's sumcheck leaves" and "the
pending row" behind the merge to "the claim on the weights" in front. Definitions, and theorems with
their proofs.

`merge_law` (Johnson/Top/H0/MergeLaw/Front.lean) ends in statements on the typed record `GS`. Here
its
two ends are read on the program's records, at three readings of committed values: cell r c (a cell
of the committed matrix), mask j (entry j of the sub-proof's mask row), idx j (entry j of the
request's index-mask message).

Main names:
  `ItemsSay`: what the merge's yes says: see its docstring: `MergedSays` and `WoSays` give
    `WeightsSays`.
  `merge_items`: from `ClosedSays` at the entries made of the three readings, with `FrontIs`, the
    ledger's sizes and `ClaimsFit`, to `ItemsSay`.
  `merge_law_items`: at any list of written rounds that has the block's own entries: for all readers
    cellOf, maskOf, idxOf of the three off the statement in front: `Reduction.Leads` of the piece's
    reduction towards `ItemsSay`; and the piece's errors are shares of at most 2⁻¹ ^ 128.

How. In front: `weightsSays_iff`. The world: `merged_fits`, from what the run lays and `Later`, as
in
ClosedRun.lean. The row on the end value: `woSays_iff` at the typed output `conv L (sumOut …)`,
whose
five equations are the library's `sum_ini`, `sum_last`, `sum_vals` (OnBytes/Tie/Pv/Lay/SumTie.lean),
`powers_val`, and the pinned form of wo.recs; then `ev_conv` and `sum_end`.

WHAT STAYS A PREMISE OF `merge_law_items`, ONE BY ONE. On public numbers: the place's layout is the
block's; one claim; at least one column bit; N.first + 2 lk + 3 is the plan's number of slots; the
written rounds have the block's entries and their names' kinds. In front: `FrontReads`; the ledger's
three arrays have one entry for each slot; `ClaimsFit`: the claim is on the place's unit, passes the
older test on its sizes, and the unit is in order. Inside `ItemsSay`: the later record stands in the
head's link and still holds what the merge left; its ledger is later than the merge's; the run says
yes; the last ledger is later than the run's; `wsPending` returns; `MergedSays`; `WoSays`. Letters:
the
place, the numbers of the slots, rd, cellOf, maskOf, idxOf, base, ext, the frame, the type of
witnesses. That the three readers give what the statement's oracles decode to, and that a border's
relation says so of its witness (the pin), is not said here. No theorem ties the pending row as
`wsPending` returns it to the row that the link's end lays.

Limits. It is no soundness of the protocol. A bound on each round, not on a sum over rounds. Where
`wsPending` refuses, `ItemsSay` says nothing on the weights. Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.Front
import Johnson.Top.H0.K11Caller.Items
import Johnson.Road.FormsKeysKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes (E zeroE oneE subE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading World Fork wsForkStart WsPending wsPending)
open OnBytes.PscRun (Later Filled)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.Sound (Frame Piece below)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeClaim headClaimMergeKind mergeEntries)
open _root_.Run (ckP)
open scoped ENNReal
open OnBytes.Tie.Pv.Lay.Eng (sumOut sum_end sum_ini sum_last sum_vals)
open K11Caller (MergeIn GS Fits2 noRd entries WeightsSays MergedSays WoSays ClaimsFit
    weightsSays_iff
  woSays_iff merged_fits pointOf zip_ofFn)

theorem getD_snd (qs : List (Nat × List E × E)) (i : ℕ) :
    ((qs.map fun q => (q.2.1, q.2.2)).getD i ([], zeroE)).2 = (qs.map (·.2.2)).getD i zeroE := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases qs[i]? <;> rfl

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl)

/-- **What the merge's yes says in the three items on the program's records**
(Johnson/Top/H0/K11Caller/Items.lean). The record behind stands in the head's link and holds what
the merge left, wo; and at every later record of that link that still holds wo, whose ledger is
later than the merge's, at which the kind's run of claims says yes, and for every ledger Fl later
than the run's: the run hands on one claim, of the form `Psc.rowForm` at the shown end value; and
wherever `wsPending` returns: if that form is worth 0 in the world of Fl at the mask row
(`MergedSays`) and the pending row holds (`WoSays`), then the claim's sum over the cells is what was
shown under its slot less the factor times its mask entry (`WeightsSays`). -/
def ItemsSay (cell : ℕ → ℕ → GE) (mask idx : ℕ → GE) (st : MergeIn Pl.n) (s' : S) : Prop :=
  ∃ (a' : HeadOwn) (wo : OnBytes.Model.WsForkOut), s'.here = .head a' ∧ a'.wo = some wo ∧
    ∀ (n : ℕ) (s₂ s₃ : S) (a₂ a₃ : HeadOwn) (cls : List Claim) (Fl : Fork) (entry : ℕ → ℕ → ℕ → GE),
      s₂.here = .head a₂ → a₂.wo = a'.wo → Later a'.F a₂.F → headMergeClaim n s₂ = .ok (cls, s₃) →
      s₃.here = .head a₃ → Later a₃.F Fl →
      cls = [{ form := wo.p.rowForm wo.fvp {} }] ∧
      ∀ (claims : ℕ) (Sh : OnBytes.Params.LinShape) (w : WsPending), wsPending Pl.lay wo claims Sh =
          .ok w →
        MergedSays Reading.gl wo Fl mask entry → WoSays Reading.gl N wo claims Sh cell idx →
        WeightsSays Reading.gl N st cell mask

/-- **From `ClosedSays` at the three readings' entries to the three items.** -/
theorem merge_items (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1) (hk0 : 0 < Pl.lay.lk)
    (cell : ℕ → ℕ → GE) (mask idx : ℕ → GE) (st : MergeIn Pl.n) {s s' : S}
    (hfr : FrontIs N st s) (hC : ClosedSays N (noRd N) P (entries N cell mask idx) st s s')
    (hz : ∀ a, s.here = .head a → OnBytes.PscRun.Sized a.F) (hfit : ClaimsFit Pl st) :
    ItemsSay N cell mask idx st s' := by
  have hlk : Pl.lay.lk = P.lay.lk := by rw [hlay]
  obtain ⟨a, a', claim, x0, wo, x, mu, cY, beta, v, T, qs, hβ, e1, e2, e3, e4, e5, e6, e7, e8,
      hfirst, hstart, hlen, hrm, hrecs,
    ⟨Gf, hhide, hshown, hF'⟩, himp⟩ := hC
  obtain ⟨fF, fcl, fsv, ffirst⟩ := hfr a claim x0 e1 e3 e4
  have hza := hz a e1
  refine ⟨a', wo, e2, e5, ?_⟩
  intro n s₂ s₃ a₂ a₃ cls Fl entry h₂ hwo hl12 hrun h₃ hl3
  obtain ⟨b, wo₂, G, hb, hbwo, hs3, hcls, hrunF⟩ := claim_inv hrun
  have hab : b = a₂ := by
    rw [h₂] at hb
    exact (Here.head.inj hb).symm
  subst hab
  have hw2 : wo₂ = wo := by
    rw [hwo, e5] at hbwo
    exact (Option.some.inj hbwo).symm
  subst hw2
  have hG : a₃.F = G := by
    rw [hs3] at h₃
    rw [← Here.head.inj h₃]
  rw [hG] at hl3
  have L01 : Later a.F a'.F := by
    rw [hF']
    have k1 : Later a.F { a.F with next := a.F.next + 1 + 2 * P.lay.lk + 2 } :=
      ⟨by show a.F.next ≤ a.F.next + 1 + 2 * P.lay.lk + 2; omega, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩
    exact (k1.trans (OnBytes.PscRun.hideRun_keeps hhide)).trans ⟨Nat.le_refl _, rfl, id, fun _ h =>
        ⟨h, rfl, rfl⟩⟩
  have L02 : Later a.F b.F := L01.trans hl12
  obtain ⟨_, _, r3, _⟩ := OnBytes.PscRun.hideRun_ok b.F G _ _ _ (L02.sized hza) hrunF
  have own : ∀ j, N.first ≤ j → j < N.first + 2 * Pl.lay.lk + 2 →
      Fl.vp.getD j zeroE = zeroE ∧ Fl.mf.getD j zeroE = subE zeroE oneE := by
    intro j j1 j2
    have hi : j - N.first < (Array.replicate wo₂.p.walk.1.length zeroE).size := by
      rw [Array.size_replicate, hlen, ← hlk]
      omega
    obtain ⟨_, _, q3, q4, q5⟩ := r3 (j - N.first) hi
    have ej : wo₂.p.first + (j - N.first) = j := by
      rw [hfirst, ← ffirst]
      omega
    rw [ej] at q3 q4 q5
    obtain ⟨_, k2, k3⟩ := hl3.keep j q3
    exact ⟨by rw [k2, q4, getD_replicate_zero], by rw [k3, q5]⟩
  have hsv : ∀ i : Fin Pl.n, N.sv i = x0.sV := by
    intro i
    have e : N.svA.getD i.val 0 = N.sv i := by simp [K11Caller.Nums.svA, Array.getD, i.isLt]
    have i0 : i.val = 0 := by have := i.isLt; omega
    rw [← e, fsv, i0]
    rfl
  have kept : ∀ i, Fl.vp.getD (N.sv i) zeroE = st.F.vp.getD (N.sv i) zeroE ∧
      Fl.mf.getD (N.sv i) zeroE = st.F.mf.getD (N.sv i) zeroE := by
    intro i
    rw [hsv i, fF]
    obtain ⟨_, k2, k3⟩ := ((L02.trans (OnBytes.PscRun.hideRun_keeps hrunF)).trans hl3).keep x0.sV
        (filled_of_public e6)
    exact ⟨k2, k3⟩
  have hfv : wo₂.fvp = v := fvp_sized hhide hshown ⟨hza.1, hza.2.1, hza.2.2⟩
  refine ⟨hcls, ?_⟩
  intro claims Sh w hpend hmerged hwo'
  have hval : (wo₂.p.rowForm v {}).value Reading.gl (Fl.worldOf Reading.gl mask entry) = 0 := by
    rw [← hfv]
    exact hmerged
  refine (weightsSays_iff N OnBytes.Road.gl_numerals hk0 st hfit cell mask idx).2
    (himp trivial ⟨_, merged_fits Reading.gl N st cell mask idx Fl entry own kept, hval⟩ ?_)
  refine (sum_end Reading.gl (GS Reading.gl N (noRd N)).L.toSum _ (st, Reading.gl.val x)
      wo₂.p.target mu wo₂.p.eps _ [cY] beta hβ
    (fun _ => Reading.gl.val v) (entries N cell mask idx) ()).1 ((ev_conv (GS Reading.gl N (noRd
        N)).L _ _).1 ?_)
  refine (woSays_iff N OnBytes.Road.gl_numerals hk0 _ hfit cell mask idx
    (fun i => (OnBytes.Model.powers x 1).getD i.val zeroE) wo₂ ?_ ?_ ?_ ?_ ?_ hpend).1 hwo'
  · intro i
    exact OnBytes.Tie.Pv.Tail.Port.powers_val Reading.gl x 1 i.val (by have := i.isLt; omega)
  · funext i
    show (GS Reading.gl N (noRd N)).L.toSum.Q.outPt (GS Reading.gl N (noRd N)).L.toSum.M _ i = _
    rw [sum_ini, getD_snd, ← hrm]
    unfold pointOf
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  · rw [hrecs, hlay, zip_ofFn #[claim] (OnBytes.Model.powers x 1) zeroE Pl.n (by rw [h1]; rfl)
      (by rw [h1]; exact OnBytes.Tie.Pv.Tail.Port.powers_size x 1)]
    congr 1
    refine congrArg List.ofFn (funext fun i => ?_)
    have i0 : i.val = 0 := by have := i.isLt; omega
    refine Prod.ext ?_ rfl
    show #[claim].getD i.val default = st.cl i
    rw [i0]
    exact (fcl i).symm
  · show (GS Reading.gl N (noRd N)).L.toSum.Q.outB (GS Reading.gl N (noRd N)).L.toSum.M _ = _
    rw [sum_last, e8]
  · rw [hfv]
    exact congrFun (sum_vals Reading.gl (GS Reading.gl N (noRd N)).L.toSum
      (fun st => pick ((GS Reading.gl N (noRd N)).L.toSum.T.par.vars st)) (st, Reading.gl.val x)
          wo₂.p.target mu wo₂.p.eps
      (qs.map fun q => (q.2.1, q.2.2)) [cY] beta hβ (fun _ => Reading.gl.val v)) ()

variable {F : Frame} {W : Type}

/-- **THE MERGE's LAW AT A PIECE, IN THE THREE ITEMS**, at any list of written rounds that has the
block's own entries; its written counts are shares of at most 2⁻¹ ^ 128. cellOf, maskOf, idxOf:
readers of the committed values off the statement in front: letters. -/
theorem merge_law_items (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1) (hk0 : 0 <
    Pl.lay.lk)
    (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind) :
    ∃ (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT) (hk : ds.length = (GS Reading.gl N (noRd N)).k),
      L = dZ :: d0 :: (ds ++ [dY, dV]) ∧
      ∀ (base : ℕ) (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
        (rd : S × F.E.Str → MergeIn Pl.n) (cellOf : S × F.E.Str → ℕ → ℕ → GE)
        (maskOf idxOf : S × F.E.Str → ℕ → GE),
        (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).ior.red.Leads
          (fun a => FrontReads N (rd a) a.1 ∧ (∀ b, a.1.here = .head b → OnBytes.PscRun.Sized b.F) ∧
            ClaimsFit Pl (rd a))
          (fun a a' => ItemsSay N (cellOf a) (maskOf a) (idxOf a) (rd a) a'.1)
          (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err ∧
        Err.Below (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err
          ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨dZ, d0, ds, dY, dV, hk, hL, hall⟩ := merge_law (F := F) (W := W) N (noRd N) P hlay h1 hnum
      L he hkd
  refine ⟨dZ, d0, ds, dY, dV, hk, hL, fun base ext rd cellOf maskOf idxOf => ?_⟩
  obtain ⟨hleads, hbelow⟩ := hall base ext rd fun a => entries N (cellOf a) (maskOf a) (idxOf a)
  refine ⟨hleads.conseq (fun a h => ⟨h.1, h.2.1⟩) ?_, hbelow⟩
  intro a τ a' ha hout hq
  obtain ⟨_, _, _, gs, hdec⟩ := piece_yes (headClaimMergeKind P)
    (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext) rfl rfl a a' τ hout
  exact merge_items N P hlay h1 hk0 _ _ _ (rd a) (frontIs_of_yes N hnum ha.1 hdec) hq.1 ha.2.1
      ha.2.2

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_law_items
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_items
