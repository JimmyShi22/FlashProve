-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Here.lean: the merge's law in three sentences, each of which reads ONE
record. Definitions, and theorems with their proofs.

Why. The head statement `merge_head` (Johnson/Top/H0/MergeLaw/HeadLaw.lean [not in this library])
says "merged" and "wo" of LATER records: the record at which the kind's run of claims is called, a
later ledger, the record in front of the link's end. The table of joints
(Johnson/Desc/First/Borders.lean) gives an item a meaning that reads one statement and the witness:
no filling of such a letter can speak of later records. So here the three sentences are functions of
the record at the border.

How the two hang together. They are ONE law at two storeys, both got from `merge_law`
(Johnson/Top/H0/MergeLaw/Front.lean), whose `ClosedSays` (Closed.lean) asks "the form is worth 0 in
a world that fits". Here that premise is kept as it is. `closed_run` and `merge_items` pay it from
"the run's one claim is worth 0 in the world of a ledger later than the run's": that is
`merge_head`'s storey.

Main names:
  `MergedHere`: what the merge has left in the record, wo: the form `wo.p.rowForm wo.fvp {}` is
    worth 0 in a world that fits (`Fits2`, Johnson/Top/H0/K11Caller/AtSlots.lean) at the record's
    own ledger. `mergedHere_all`: at a record with `BehindOk` every fitting world gives the form
    the value 0 then (by `rowForm_same`, OneWorld.lean, whose three premises `BehindOk` holds).
  `WoHere`: the frame's reader gives a row at the record; the index masks' ledger's next entry is
    N.c; the row holds in the pile's sense (`Holds`, Johnson/Desc/K13/Law/Means.lean).
  `WeightsHere`: `WeightsSays` at the typed statement read off the record.
  `BehindOk`: what the yes leaves for certain in the record behind.
  `merge_items_here`, `behind_ok`, `here_say`: from `ClosedSays` to these.
  `merge_table_here`: on `frontB`'s yes the prover has lost, round by round at the piece's own list
    of errors, towards: whatever the verifier puts out: `BehindOk` behind, and "merged" and "wo"
    behind give "weights" in front (`HereSay`); each error at most a share of 2⁻¹ ^ 128.
  `frontW`, `frontB_of_W`, `merge_table_hereW`: the same at a weaker test in front: the ledger's
    sizes; and, WHERE the claim and what the head heard are laid, the slot's number and the unit.
    Where `frontB` fails the block never says yes.

Limits. cellOf, maskOf, idxOf are functions of the statement in front: letters (pinned in
AtTable.lean). claims and lin are bound by "for all" and tied to no plan. That N.c is the ledger's
next entry stands INSIDE `WoHere`: nobody pays it yet. `MergedHere` follows from the table's own
sentence on a run's forms (LateTie.lean); no record and witness at which `MergedHere` or `WoHere`
holds is shown. A bound a round: not on a sum over rounds, and not on a prover's chance. Nothing on
hiding.

-/
import Johnson.Top.H0.MergeLaw.RowHolds
import Johnson.Top.H0.MergeLaw.OneWorld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes (E zeroE oneE subE TensorRow)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading World Fork wsForkStart WsPending wsPending WsForkOut)
open OnBytes.PscRun (Later Filled)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.Pend (takeEntry)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeClaim headClaimMergeKind mergeEntries)
open VerifiableInference.Desc.First.Close (leftHead)
open Johnson.Desc.First.Walk.Law (leftOf ledgerAt leftOf_of_head)
open VerifiableInference.Desc.K13.Law (Wit Holds lowBits)
open _root_.Run (ckP)
open scoped ENNReal
open OnBytes.Tie.Pv.Lay.Eng (sumOut sum_end sum_ini sum_last sum_vals)
open K11Caller (MergeIn GS Fits2 noRd entries WeightsSays WoSays ClaimsFit weightsSays_iff
  woSays_iff pointOf zip_ofFn cellsIn)

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl)

/-- **"merged", at one record**: the form that the merge's sumcheck has left, at the shown end
value, is worth 0 in a world that fits: the sumcheck's own slots read as their mask entries, the
slot
of the claim's value as what was shown less the factor times its mask entry, at the record's own
ledger. -/
def MergedHere (cell : ℕ → ℕ → GE) (mask idx : ℕ → GE) (s : S) : Prop :=
  ∃ (wo : WsForkOut) (Wd : World GE), leftOf s = some wo ∧
    Fits2 Reading.gl N (frontIn Pl.n s) (entries N cell mask idx) Wd ∧
    (wo.p.rowForm wo.fvp {}).value Reading.gl Wd = 0

/-- **"weights", at one record.** -/
def WeightsHere (cell : ℕ → ℕ → GE) (mask : ℕ → GE) (s : S) : Prop :=
  WeightsSays Reading.gl N (frontIn Pl.n s) cell mask

/-- A world fits at two typed statements alike, where their ledgers have one pair under each claim's
slot. -/
theorem fits2_congr {st st' : MergeIn Pl.n} {m : Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE}
    {Wd : World GE}
    (h : ∀ a, st'.F.vp.getD (N.sv a) zeroE = st.F.vp.getD (N.sv a) zeroE ∧
      st'.F.mf.getD (N.sv a) zeroE = st.F.mf.getD (N.sv a) zeroE)
    (F : Fits2 Reading.gl N st' m Wd) : Fits2 Reading.gl N st m Wd :=
  ⟨F.w1, fun a => by rw [F.w2 a, (h a).1, (h a).2]⟩

/-- **From `ClosedSays` to the items at the two records alone**: no run, no later ledger. -/
theorem merge_items_here (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
    (hk0 : 0 < Pl.lay.lk) (cell : ℕ → ℕ → GE) (mask idx : ℕ → GE) (st : MergeIn Pl.n) {s s' : S}
    (hfr : FrontIs N st s) (hC : ClosedSays N (noRd N) P (entries N cell mask idx) st s s')
    (hz : ∀ a, s.here = .head a → OnBytes.PscRun.Sized a.F) (hfit : ClaimsFit Pl st) :
    ∃ (a' : HeadOwn) (wo : WsForkOut), s'.here = .head a' ∧ a'.wo = some wo ∧
      (∀ i, a'.F.vp.getD (N.sv i) zeroE = st.F.vp.getD (N.sv i) zeroE ∧
        a'.F.mf.getD (N.sv i) zeroE = st.F.mf.getD (N.sv i) zeroE) ∧
      ∀ (claims : ℕ) (Sh : OnBytes.Params.LinShape) (w : WsPending),
        wsPending Pl.lay wo claims Sh = .ok w →
        (∃ Wd : World GE, Fits2 Reading.gl N st (entries N cell mask idx) Wd ∧
          (wo.p.rowForm wo.fvp {}).value Reading.gl Wd = 0) →
        WoSays Reading.gl N wo claims Sh cell idx → WeightsSays Reading.gl N st cell mask := by
  obtain ⟨a, a', claim, x0, wo, x, mu, cY, beta, v, T, qs, hβ, e1, e2, e3, e4, e5, e6, e7, e8,
      hfirst, hstart, hlen, hrm, hrecs,
    ⟨Gf, hhide, hshown, hF'⟩, himp⟩ := hC
  obtain ⟨fF, fcl, fsv, ffirst⟩ := hfr a claim x0 e1 e3 e4
  have hza := hz a e1
  have L01 : Later a.F a'.F := by
    rw [hF']
    have k1 : Later a.F { a.F with next := a.F.next + 1 + 2 * P.lay.lk + 2 } :=
      ⟨by show a.F.next ≤ a.F.next + 1 + 2 * P.lay.lk + 2; omega, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩
    exact (k1.trans (OnBytes.PscRun.hideRun_keeps hhide)).trans ⟨Nat.le_refl _, rfl, id, fun _ h =>
        ⟨h, rfl, rfl⟩⟩
  have hsv : ∀ i : Fin Pl.n, N.sv i = x0.sV := by
    intro i
    have e : N.svA.getD i.val 0 = N.sv i := by simp [K11Caller.Nums.svA, Array.getD, i.isLt]
    have i0 : i.val = 0 := by have := i.isLt; omega
    rw [← e, fsv, i0]
    rfl
  have hfv : wo.fvp = v := fvp_sized hhide hshown ⟨hza.1, hza.2.1, hza.2.2⟩
  refine ⟨a', wo, e2, e5, ?_, ?_⟩
  · intro i
    rw [hsv i, fF]
    obtain ⟨_, k2, k3⟩ := L01.keep x0.sV (filled_of_public e6)
    exact ⟨k2, k3⟩
  intro claims Sh w hpend hmerged hwo'
  obtain ⟨Wd, hWd, hval0⟩ := hmerged
  have hval : (wo.p.rowForm v {}).value Reading.gl Wd = 0 := by
    rw [← hfv]
    exact hval0
  refine (weightsSays_iff N OnBytes.Road.gl_numerals hk0 st hfit cell mask idx).2
    (himp trivial ⟨Wd, hWd, hval⟩ ?_)
  refine (sum_end Reading.gl (GS Reading.gl N (noRd N)).L.toSum _ (st, Reading.gl.val x)
      wo.p.target mu wo.p.eps _ [cY] beta hβ
    (fun _ => Reading.gl.val v) (entries N cell mask idx) ()).1 ((ev_conv (GS Reading.gl N (noRd
        N)).L _ _).1 ?_)
  refine (woSays_iff N OnBytes.Road.gl_numerals hk0 _ hfit cell mask idx
    (fun i => (OnBytes.Model.powers x 1).getD i.val zeroE) wo ?_ ?_ ?_ ?_ ?_ hpend).1 hwo'
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
          wo.p.target mu wo.p.eps
      (qs.map fun q => (q.2.1, q.2.2)) [cY] beta hβ (fun _ => Reading.gl.val v)) ()

/-- **What the merge's yes leaves for certain in the record behind**: it stands in the head's part
and holds what the merge has left; the ledger has its sizes; the sumcheck's window begins at the
place's number and has 2 lk + 2 slots; the slot of each claim's value is filled; the sumcheck's
start form is the merge's, over the slots of the claims' values. -/
def BehindOk (s' : S) : Prop :=
  ∃ (a' : HeadOwn) (wo : WsForkOut), s'.here = .head a' ∧ a'.wo = some wo ∧
    OnBytes.PscRun.Sized a'.F ∧ wo.p.first = N.first ∧
    wo.p.walk.1.length = 2 * Pl.lay.lk + 2 ∧ (∀ i, Filled a'.F (N.sv i)) ∧
    ∃ rho, wo.p.start = wsForkStart N.svA rho

theorem behind_ok (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
    (m : Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE) (st : MergeIn Pl.n) {s s' : S}
    (hfr : FrontIs N st s) (hC : ClosedSays N (noRd N) P m st s s')
    (hz : ∀ a, s.here = .head a → OnBytes.PscRun.Sized a.F) : BehindOk N s' := by
  obtain ⟨a, a', claim, x0, wo, x, mu, cY, beta, v, T, qs, hβ, e1, e2, e3, e4, e5, e6, e7, e8,
      hfirst, hstart, hlen, hrm, hrecs,
    ⟨Gf, hhide, hshown, hF'⟩, himp⟩ := hC
  obtain ⟨fF, fcl, fsv, ffirst⟩ := hfr a claim x0 e1 e3 e4
  have L01 : Later a.F a'.F := by
    rw [hF']
    have k1 : Later a.F { a.F with next := a.F.next + 1 + 2 * P.lay.lk + 2 } :=
      ⟨by show a.F.next ≤ a.F.next + 1 + 2 * P.lay.lk + 2; omega, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩
    exact (k1.trans (OnBytes.PscRun.hideRun_keeps hhide)).trans ⟨Nat.le_refl _, rfl, id, fun _ h =>
        ⟨h, rfl, rfl⟩⟩
  have hsv : ∀ i : Fin Pl.n, N.sv i = x0.sV := by
    intro i
    have e : N.svA.getD i.val 0 = N.sv i := by simp [K11Caller.Nums.svA, Array.getD, i.isLt]
    have i0 : i.val = 0 := by have := i.isLt; omega
    rw [← e, fsv, i0]
    rfl
  refine ⟨a', wo, e2, e5, L01.sized (hz a e1), by rw [hfirst, ffirst], by rw [hlen, hlay], ?_,
    ⟨_, by rw [hstart, fsv]⟩⟩
  intro i
  rw [hsv i]
  exact (L01.keep x0.sV (filled_of_public e6)).1

/-- **Behind a yes "merged" does not hang on the choice of the world**: every world that fits gives
the form the value 0. -/
theorem mergedHere_all {cell : ℕ → ℕ → GE} {mask idx : ℕ → GE} {s : S} (hb : BehindOk N s)
    (h : MergedHere N cell mask idx s) (wo : WsForkOut) (hl : leftOf s = some wo) (Wd : World GE)
    (hW : Fits2 Reading.gl N (frontIn Pl.n s) (entries N cell mask idx) Wd) :
    (wo.p.rowForm wo.fvp {}).value Reading.gl Wd = 0 := by
  obtain ⟨a', wo₁, e1, e2, _, hf, hlen, _, rho, hst⟩ := hb
  obtain ⟨wo₂, Wd₂, hl₂, hW₂, hv⟩ := h
  have hl₁ : leftOf s = some wo₁ := leftOf_of_head (by
    unfold leftHead
    rw [e1]
    exact e2)
  have ea : wo = wo₁ := by
    rw [hl₁] at hl
    exact (Option.some.inj hl).symm
  have eb : wo₂ = wo₁ := by
    rw [hl₁] at hl₂
    exact (Option.some.inj hl₂).symm
  subst ea
  subst eb
  rw [rowForm_same N hW hW₂ wo₂.p rho hf hlen hst wo₂.fvp]
  exact hv

/-- **"wo", at one record**: the frame's reader gives a row there, at the plan's number of claims
and shape; the entry that the index masks' ledger gives next is the number N.c; and the row holds,
in
the pile's sense, of a matrix witness whose matrix is the cells and whose mask entries of the index
masks' message are idx. -/
def WoHere (claims : ℕ) (lin : OnBytes.Params.LinShape) (cell : ℕ → ℕ → GE) (idx : ℕ → GE)
    (s : S) : Prop :=
  ∃ (r : TensorRow) (wK : Wit GE Pl.lay.m0 Pl.lay.lk),
    Johnson.Desc.First.Walk.Law.rowAt Pl.lay claims lin s = some r ∧
    (∀ l c l', ledgerAt s = some l → takeEntry l = some (c, l') → N.c = c) ∧
    (∀ (i : Fin Pl.lay.m0) (C : ℕ), C < 2 ^ Pl.lay.lk → wK.mat i (lowBits Pl.lay.lk C) = cell i C) ∧
    (∀ c, wK.mask ⟨s.out.indexMasks, c⟩ = idx c) ∧ Holds Reading.gl wK r

/-- **What the merge's yes says, at its two records alone**: "merged" and "wo" at the record behind
give "weights" at the record in front. -/
def HereSay (claims : ℕ) (lin : OnBytes.Params.LinShape) (cell : ℕ → ℕ → GE) (mask idx : ℕ → GE)
    (s s' : S) : Prop :=
  MergedHere N cell mask idx s' → WoHere N claims lin cell idx s' → WeightsHere N cell mask s

theorem here_say (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1) (hk0 : 0 < Pl.lay.lk)
    (claims : ℕ) (lin : OnBytes.Params.LinShape) (cell : ℕ → ℕ → GE) (mask idx : ℕ → GE) {s s' : S}
    (hfr : FrontIs N (frontIn Pl.n s) s)
    (hC : ClosedSays N (noRd N) P (entries N cell mask idx) (frontIn Pl.n s) s s')
    (hz : ∀ a, s.here = .head a → OnBytes.PscRun.Sized a.F)
    (hfit : ClaimsFit Pl (frontIn Pl.n s)) : HereSay N claims lin cell mask idx s s' := by
  obtain ⟨a', wo, e2, e5, hkeep, himp⟩ :=
    merge_items_here N P hlay h1 hk0 cell mask idx (frontIn Pl.n s) hfr hC hz hfit
  have hl : leftOf s' = some wo := leftOf_of_head (by
    unfold leftHead
    rw [e2]
    exact e5)
  intro hm hw
  obtain ⟨wo', Wd, hl', hfits, hval⟩ := hm
  have ew : wo' = wo := by
    rw [hl] at hl'
    exact (Option.some.inj hl').symm
  subst ew
  obtain ⟨r, wK, hr, hc, hmat, hmask, hH⟩ := hw
  obtain ⟨w0, w, l, c, l', b1, b2, _, _, b5, b6, _, _⟩ := row_tie (left := leftOf) hr
  have e0 : w0 = wo' := by
    rw [hl] at b1
    exact (Option.some.inj b1).symm
  subst e0
  obtain ⟨z1, z2⟩ := pending_sizes b2
  have eF : (frontIn Pl.n s').F = a'.F := by
    unfold frontIn
    rw [e2]
  refine himp claims lin w b2 ⟨Wd, fits2_congr N (fun i => by rw [eF]; exact hkeep i) hfits, hval⟩
    (woSays_of_row N (left := leftOf) cell idx hr hl hc
      ((rowSays_iff_holds (cellsIn Pl cell) idx r wK ?_ z2 ?_ ?_ ?_).2 hH))
  · rw [b5]
    show w.psi.length = Pl.lay.lk
    rw [b6, List.length_reverse, Array.length_toList, z1]
  · intro j hj C
    unfold cellsIn K11Caller.Wof
    rw [dif_neg (by omega)]
  · intro i C hC'
    rw [hmat i C hC']
    unfold cellsIn K11Caller.Wof
    rw [dif_pos ⟨i.isLt, hC'⟩]
  · intro t ht
    rw [b5] at ht
    have e : t = (⟨s'.out.indexMasks, c⟩, w.beta) := by simpa using ht
    rw [e]
    exact hmask c

variable {F : Frame} {W : Type}

/-- **THE MERGE's LAW AT A PIECE, IN THREE SENTENCES EACH OF WHICH READS ONE RECORD.** -/
theorem merge_table_here (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
    (hk0 : 0 < Pl.lay.lk) (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg)
    (hunit : ∀ a u, Pl.lay.U[Pl.ui a]? = some u → OnBytes.Road.UnitOK Pl.lay.lk u) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind) (claims : ℕ)
    (lin : OnBytes.Params.LinShape) :
    ∃ (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT) (hk : ds.length = (GS Reading.gl N (noRd N)).k),
      L = dZ :: d0 :: (ds ++ [dY, dV]) ∧
      ∀ (base : ℕ) (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
        (cellOf : S × F.E.Str → ℕ → ℕ → GE) (maskOf idxOf : S × F.E.Str → ℕ → GE),
        (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).ior.red.Leads
          (fun a => frontB N a.1 = true)
          (fun a a' => BehindOk N a'.1 ∧
            HereSay N claims lin (cellOf a) (maskOf a) (idxOf a) a.1 a'.1)
          (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err ∧
        Err.Below (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err
          ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨dZ, d0, ds, dY, dV, hk, hL, hall⟩ := merge_law (F := F) (W := W) N (noRd N) P hlay h1 hnum
      L he hkd
  refine ⟨dZ, d0, ds, dY, dV, hk, hL, fun base ext cellOf maskOf idxOf => ?_⟩
  obtain ⟨hleads, hbelow⟩ := hall base ext (fun a => frontIn Pl.n a.1)
    fun a => entries N (cellOf a) (maskOf a) (idxOf a)
  refine ⟨hleads.conseq (fun a h => ⟨(front_of_B N h).1, (front_of_B N h).2.1⟩) ?_, hbelow⟩
  intro a τ a' ha hout hq
  obtain ⟨hf1, hf2, hf3⟩ := front_of_B N ha
  obtain ⟨_, _, _, gs, hdec⟩ := piece_yes (headClaimMergeKind P)
    (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext) rfl rfl a a' τ hout
  obtain ⟨b, _, claim, x0, _, _, _, _, _, _, _, _, _, e1, _, e3, e4, _⟩ := hq.1
  obtain ⟨_, fcl, _⟩ := hf1 b claim x0 e1 e3 e4
  have hfit : ClaimsFit Pl (frontIn Pl.n a.1) := ⟨hf3, fun i => by
    rw [fcl i, hlay]
    exact shape_of_yes hdec b claim e1 e3, hunit⟩
  exact ⟨behind_ok N P hlay h1 _ _ (frontIs_of_yes N hnum hf1 hdec) hq.1 hf2,
    here_say N P hlay h1 hk0 claims lin _ _ _ (frontIs_of_yes N hnum hf1 hdec) hq.1 hf2 hfit⟩

/-- **The condition in front, as little as the proof spends**: a test on the record: where it stands
in the head's part: the ledger's three arrays have one entry a slot; and where the claim and what
the
head heard are laid: the slot of the claim's value is the place's number, and the claim is on the
place's unit. Elsewhere, and where one of the two is not laid: yes. -/
def frontW (s : S) : Bool :=
  match s.here with
  | .head a =>
    a.F.vp.size == a.F.ns && a.F.mf.size == a.F.ns && a.F.gotF.size == a.F.ns &&
      match a.claim, a.x with
      | some claim, some x0 =>
        N.svA == #[x0.sV] && (List.finRange Pl.n).all fun i => claim.ui == Pl.ui i
      | _, _ => true
  | _ => true

/-- Where the block's decision says yes, the weaker test gives the stronger. -/
theorem frontB_of_W {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView}
    (h : Johnson.Desc.First.ForkMerge.headMergeDecide P s rs = .ok s') (hw : frontW N s = true) :
    frontB N s = true := by
  obtain ⟨a, _, _, _, claim, x, _, e1, _, e3, e4, _⟩ := decide_inv h
  unfold frontW at hw
  unfold frontB
  rw [e1] at hw ⊢
  simp only [e3, e4, Bool.and_eq_true] at hw ⊢
  obtain ⟨⟨⟨h2, h3⟩, h4⟩, h1, h5⟩ := hw
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

/-- **THE SAME LAW AT THE WEAKER CONDITION**: where the stronger fails the block never says yes. -/
theorem merge_table_hereW (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
    (hk0 : 0 < Pl.lay.lk) (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg)
    (hunit : ∀ a u, Pl.lay.U[Pl.ui a]? = some u → OnBytes.Road.UnitOK Pl.lay.lk u) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind) (claims : ℕ)
    (lin : OnBytes.Params.LinShape) :
    ∃ (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT) (hk : ds.length = (GS Reading.gl N (noRd N)).k),
      L = dZ :: d0 :: (ds ++ [dY, dV]) ∧
      ∀ (base : ℕ) (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
        (cellOf : S × F.E.Str → ℕ → ℕ → GE) (maskOf idxOf : S × F.E.Str → ℕ → GE),
        (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).ior.red.Leads
          (fun a => frontW N a.1 = true)
          (fun a a' => BehindOk N a'.1 ∧
            HereSay N claims lin (cellOf a) (maskOf a) (idxOf a) a.1 a'.1)
          (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err ∧
        Err.Below (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err
          ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨dZ, d0, ds, dY, dV, hk, hL, hall⟩ :=
    merge_table_here (F := F) (W := W) N P hlay h1 hk0 hnum hunit L he hkd claims lin
  refine ⟨dZ, d0, ds, dY, dV, hk, hL, fun base ext cellOf maskOf idxOf => ?_⟩
  obtain ⟨hleads, hbelow⟩ := hall base ext cellOf maskOf idxOf
  refine ⟨fun a ha => ?_, hbelow⟩
  by_cases hB : frontB N a.1 = true
  · exact hleads a hB
  · refine Doomed.of_forall _ _ fun τ b hb => ?_
    obtain ⟨_, _, _, gs, hdec⟩ := piece_yes (headClaimMergeKind P)
      (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext) rfl rfl a b τ hb
    exact absurd (frontB_of_W N hdec ha) hB

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.mergedHere_all
#print axioms VerifiableInference.Desc.First.MergeLaw.behind_ok
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_table_hereW
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_table_here
#print axioms VerifiableInference.Desc.First.MergeLaw.here_say
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_items_here
