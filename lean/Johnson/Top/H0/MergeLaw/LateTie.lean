-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/LateTie.lean: the tie between "merged" at one record (`MergedHere`,
Johnson/Top/H0/MergeLaw/Here.lean) and the table of joints' own filling of "forms" (`formsQ`,
Johnson/Desc/Sound/FormsQ.lean). Theorems with their proofs.

Why. That filling reads a run's forms and its LATE slots off the run itself, called at the border's
record: late: free in the record's ledger and filled in the ledger that the run returns
(`lateOf`, Johnson/Desc/First/Batch/ReaderOf.lean). Its world reads a late slot by what the run will
lay, every other slot by the record's ledger (`slotW`). The merge's law spends "a world that fits".
The two meet because the merge's run lays 0 and the factor -1 under each slot of the sumcheck's
window.

Main names:
  `mem_lateOf`, `lateAt_some`, `lateAt_none`: which slots are late, and with what.
  `late_fits`: THE TIE: where the run says yes at a record that holds what the merge has left, the
    world `slotW` at `lateOf` fits.
  `mergedHere_of_formsQ`: `formsQ` at the readers that are the runs themselves, at a piece and a
    name under which the merge's run is stated, gives `MergedHere` at the mask row that the
    filling reads.
  `merged_at_table`: the same with its premises on the record paid by `BehindOk`.

Limits. One way alone: from the table's sentence to ours. hst (the blocks state the merge's run at
that piece under that name) is a premise on a letter. Nothing on "wo" or "weights". No member.
Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.MergeLaw.Here
import Johnson.Top.H0.MergeLaw.RunFills
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.First.Batch.ReaderOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes (E zeroE oneE subE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading World Fork WsForkOut)
open OnBytes.PscRun (Later Filled Sized)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.K9 (lateAt lateOf readerOf Readers RunOf segAt?)
open VerifiableInference.Desc.Sound (slotW slotW_late slotW_ledger formsQ worldOwn dataQ MsgQ)
open VerifiableInference.Desc.First.Close (leftHead)
open Johnson.Desc.First.Walk.Law (leftOf leftOf_of_head)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open K11Caller (MergeIn Fits2 entries maskOf_entries)

/-- What stands in the list of late slots. -/
theorem mem_lateOf {F G : Fork} {x : ℕ × E × E} (h : x ∈ lateOf F G) :
    ¬ Filled F x.1 ∧ Filled G x.1 ∧ x.2 = (G.vp.getD x.1 zeroE, G.mf.getD x.1 zeroE) := by
  unfold lateOf at h
  obtain ⟨j, _, hx⟩ := List.mem_filterMap.1 h
  by_cases hc : (!(F.gotF.getD j false) && G.gotF.getD j false) = true
  · rw [if_pos hc] at hx
    obtain rfl := Option.some.inj hx
    obtain ⟨c1, c2⟩ := Eq.mp (Bool.and_eq_true _ _) hc
    exact ⟨fun hf => by
      unfold Filled at hf
      rw [hf] at c1
      exact absurd c1 (by simp), c2, rfl⟩
  · rw [if_neg hc] at hx
    exact nomatch hx

/-- A slot that is free in F and filled in G is late, with G's pair. -/
theorem lateAt_some {F G : Fork} {j : ℕ} (hj : j < G.ns) (h0 : ¬ Filled F j) (h1 : Filled G j) :
    lateAt (lateOf F G) j = some (G.vp.getD j zeroE, G.mf.getD j zeroE) := by
  have hm : (j, G.vp.getD j zeroE, G.mf.getD j zeroE) ∈ lateOf F G := by
    unfold lateOf
    refine List.mem_filterMap.2 ⟨j, List.mem_range.2 hj, ?_⟩
    have c1 : F.gotF.getD j false = false := by
      unfold Filled at h0
      simpa using h0
    unfold Filled at h1
    rw [c1, h1]
    rfl
  unfold lateAt
  cases e : (lateOf F G).find? fun x => x.1 == j with
  | none =>
    have := List.find?_eq_none.1 e _ hm
    exact absurd this (by simp)
  | some x =>
    have hx : x.1 = j := by simpa using List.find?_some e
    obtain ⟨_, _, h3⟩ := mem_lateOf (List.mem_of_find?_eq_some e)
    show some x.2 = _
    rw [h3, hx]

/-- A slot that is filled in F is not late. -/
theorem lateAt_none {F G : Fork} {j : ℕ} (h : Filled F j) : lateAt (lateOf F G) j = none := by
  unfold lateAt
  cases e : (lateOf F G).find? fun x => x.1 == j with
  | none => rfl
  | some x =>
    have hx : x.1 = j := by simpa using List.find?_some e
    obtain ⟨h0, _, _⟩ := mem_lateOf (List.mem_of_find?_eq_some e)
    rw [hx] at h0
    exact absurd h h0

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl)

/-- **THE TIE.** At a record of the head's part that holds what the merge has left, whose ledger has
its sizes: let the kind's run of claims say yes there. Then the world that reads a slot by what the
run will lay where the slot is late, and by the record's own ledger elsewhere (`slotW` at `lateOf`),
FITS: the sumcheck's own slots read as their mask entries, the slot of the claim's value as what was
shown less the factor times its mask entry. -/
theorem late_fits {n : ℕ} {s s₃ : S} {cls : List Claim} {a a₃ : HeadOwn} {wo : WsForkOut}
    (hrun : headMergeClaim n s = .ok (cls, s₃)) (e1 : s.here = .head a) (e3 : s₃.here = .head a₃)
    (hwo : a.wo = some wo) (hz : Sized a.F) (hfirst : wo.p.first = N.first)
    (hlen : wo.p.walk.1.length = 2 * Pl.lay.lk + 2) (hsv : ∀ i, Filled a.F (N.sv i))
    (cell : ℕ → ℕ → GE) (mask idx : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) :
    Fits2 Reading.gl N (frontIn Pl.n s) (entries N cell mask idx)
      ⟨slotW a.F (lateOf a.F a₃.F) mask, entry⟩ := by
  obtain ⟨b, wo₂, G, hb, hbwo, hs3, _, hrunF⟩ := claim_inv hrun
  have hab : b = a := by
    rw [e1] at hb
    exact (Here.head.inj hb).symm
  subst hab
  have hw2 : wo₂ = wo := by
    rw [hwo] at hbwo
    exact (Option.some.inj hbwo).symm
  subst hw2
  have hG : a₃.F = G := by
    rw [hs3] at e3
    rw [← Here.head.inj e3]
  obtain ⟨hsame, _, r3, _⟩ := OnBytes.PscRun.hideRun_ok b.F G _ _ _ hz hrunF
  have hns : G.ns = b.F.ns := by
    unfold OnBytes.PscRun.Same at hsame
    rw [hsame]
  have eF : (frontIn Pl.n s).F = b.F := by
    unfold frontIn
    rw [e1]
  refine ⟨fun j j1 j2 => ?_, fun i => ?_⟩
  · have hi : j - N.first < (Array.replicate wo₂.p.walk.1.length zeroE).size := by
      rw [Array.size_replicate, hlen]
      omega
    obtain ⟨q1, q2, q3, q4, q5⟩ := r3 (j - N.first) hi
    have ej : wo₂.p.first + (j - N.first) = j := by
      rw [hfirst]
      omega
    rw [ej] at q1 q2 q3 q4 q5
    rw [maskOf_entries N cell mask idx (by have := N.room; omega)]
    show slotW b.F (lateOf b.F a₃.F) mask j = mask j
    rw [hG, slotW_late _ _ _ _ _ (lateAt_some (by rw [hns]; exact q1) q2 q3), q4, q5,
      getD_replicate_zero, Reading.gl.sub, Reading.gl.zero, Reading.gl.one]
    ring
  · rw [maskOf_entries N cell mask idx (N.hsv i), eF]
    show slotW b.F (lateOf b.F a₃.F) mask (N.sv i) = _
    rw [slotW_ledger _ _ _ _ (lateAt_none (hsv i))]

/-- **FROM THE TABLE's OWN SENTENCE TO "merged" AT ONE RECORD.** `formsQ` (the table's filling of
"forms", Johnson/Desc/Sound/FormsQ.lean) at the readers that are the runs themselves, at a piece and
a name under which the blocks state the merge's run: at a record of the head's part that holds what
the merge has left: it gives `MergedHere` at the mask row that the filling reads off the witness's
tables. -/
theorem mergedHere_of_formsQ (states : ℕ → List (RunOf S)) (own : List (ℕ × ℕ)) (piece : ℕ)
    (run name : String)
    (hst : ((states piece).find? fun r => r.1 == run) = some (name, headMergeClaim))
    {s : S} {a : HeadOwn} {wo : WsForkOut} (e1 : s.here = .head a) (hwo : a.wo = some wo)
    (hz : Sized a.F) (hfirst : wo.p.first = N.first)
    (hlen : wo.p.walk.1.length = 2 * Pl.lay.lk + 2) (hsv : ∀ i, Filled a.F (N.sv i))
    (rd : ℕ × ℕ → MsgQ) (cell : ℕ → ℕ → GE) (idx : ℕ → GE)
    (h : formsQ (Readers.ofStates states) own piece run s rd) :
    ∃ a9, segAt? s = some a9 ∧ MergedHere N cell (dataQ own a9 rd).mask idx s := by
  obtain ⟨a9, R, ha9, hR, _, hf⟩ := h
  refine ⟨a9, ha9, ?_⟩
  have hR' : readerOf states piece run s = some R := hR
  unfold readerOf at hR'
  rw [hst] at hR'
  simp only [Option.bind_some] at hR'
  cases hrun : headMergeClaim 0 s with
  | error e => simp [hrun] at hR'
  | ok z =>
    obtain ⟨cls, s₃⟩ := z
    obtain ⟨b, wo₂, G, hb, hbwo, hs3, hcls, hrunF⟩ := claim_inv hrun
    have hab : b = a := by
      rw [e1] at hb
      exact (Here.head.inj hb).symm
    subst hab
    have hw2 : wo₂ = wo := by
      rw [hwo] at hbwo
      exact (Option.some.inj hbwo).symm
    subst hw2
    cases hF : s.fork? with
    | none => simp [hrun, hF] at hR'
    | some F0 =>
      have hop : b.opened = true ∧ F0 = b.F := by
        unfold S.fork? at hF
        rw [e1] at hF
        have hF' : (if b.opened = true then some b.F else none) = some F0 := hF
        by_cases ho : b.opened = true
        · rw [if_pos ho] at hF'
          exact ⟨ho, (Option.some.inj hF').symm⟩
        · rw [if_neg ho] at hF'
          exact nomatch hF'
      obtain ⟨ho, rfl⟩ := hop
      have hG : s₃.fork? = some G := by
        rw [hs3]
        unfold S.fork?
        show (if b.opened = true then some G else none) = some G
        rw [if_pos ho]
      simp only [hrun, hF, hG, Option.bind_some] at hR'
      split at hR'
      · obtain rfl := Option.some.inj hR'
        have e9 : a9.F = b.F := by
          unfold segAt? at ha9
          simp only [Option.bind_eq_bind, Option.pure_def] at ha9
          obtain ⟨L, _, h2⟩ := Option.bind_eq_some_iff.1 ha9
          obtain ⟨F1, hF1, h3⟩ := Option.bind_eq_some_iff.1 h2
          obtain ⟨tl, _, h4⟩ := Option.bind_eq_some_iff.1 h3
          rw [← Option.some.inj h4]
          show F1 = b.F
          rw [hF] at hF1
          exact (Option.some.inj hF1).symm
        have hv := (hf (wo₂.p.rowForm wo₂.fvp {}) (by rw [hcls]; simp)).2
        have hl : leftOf s = some wo₂ := leftOf_of_head (by
          unfold leftHead
          rw [e1]
          exact hwo)
        refine ⟨wo₂, _, hl, ?_, hv⟩
        have hfit := late_fits N (a₃ := { b with F := G }) hrun e1 (by rw [hs3]) hwo hz hfirst hlen
          hsv cell (dataQ own a9 rd).mask idx
          (worldOwn a9 (lateOf b.F G) (dataQ own a9 rd)).entry
        unfold worldOwn
        rw [e9]
        exact hfit
      · exact nomatch hR'

/-- **The same behind the merge's yes**: its six premises on the record are among what the yes
leaves for certain (`BehindOk`, Johnson/Top/H0/MergeLaw/Here.lean). -/
theorem merged_at_table (states : ℕ → List (RunOf S)) (own : List (ℕ × ℕ)) (piece : ℕ)
    (run name : String)
    (hst : ((states piece).find? fun r => r.1 == run) = some (name, headMergeClaim))
    {s : S} (hb : BehindOk N s) (rd : ℕ × ℕ → MsgQ) (cell : ℕ → ℕ → GE) (idx : ℕ → GE)
    (h : formsQ (Readers.ofStates states) own piece run s rd) :
    ∃ a9, segAt? s = some a9 ∧ MergedHere N cell (dataQ own a9 rd).mask idx s := by
  obtain ⟨a', wo, e1, e2, hz, hf, hl, hs, _⟩ := hb
  exact mergedHere_of_formsQ N states own piece run name hst e1 e2 hz hf hl hs rd cell idx h

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merged_at_table
#print axioms VerifiableInference.Desc.First.MergeLaw.mergedHere_of_formsQ
#print axioms VerifiableInference.Desc.First.MergeLaw.late_fits
