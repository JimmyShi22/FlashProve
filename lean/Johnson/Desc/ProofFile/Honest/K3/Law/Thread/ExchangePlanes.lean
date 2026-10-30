-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangePlanes.lean: the honest side of the kind
"lookup" (K3): what the lookup's row owes behind its sub-protocol: the item on the planes of the
library's row out. Definitions with code, and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the item on the planes is `K3OutPlanes`
(Johnson/Top/H/K3RowOut.lean). It speaks of three numbers made of rounds and of a reading ν of
places. `Left` (Honest/K3/Law/LookLeftOf.lean) says what the lookup leaves. `Dict`
(Honest/K3/Law/Thread/ExchangeRows.lean) is `MasksAre` (Honest/K3/Law/Statements.lean) at the mask
entries of the reading ν.

What is shown.
  `bare`, `bare_fits`: the seat: a pair of a ledger and a heard structure.
  `constE`, `constE_value`, `readersAt`: a form that is a constant with a given reading; the
    readers.
  `leavesRow_both`: where the leaves' own slots are still owed, the part's own late row and the
    seated text of it return, with one ledger behind.
  `paid_later`: marking a debt as paid leaves a later ledger.
  `outPlanes_of_left`: the item at the ledger F'. Conditional on `Left` at `planesOf D`, on `Dict`,
    on the bits of D being the reading of their places, and, at the ledger F' at which the item is
    asked: its arrays' sizes, the leaves' own slots still owed, the planes' debt not yet marked.

Hypotheses that remain, in `outPlanes_of_left`.
  `hLeft`: `Left` at `planesOf D` (Honest/K3/Law/SpecLawful.lean).
  `hD`: `Dict`, that is `MasksAre`.
  `hbit`, `h0`: the bits of D are what ν reads at their places; ν reads 0 at the place zero.
  `hS'`, `hL`, `ho`, `hu`: at F': its arrays have their size; it is later than the ledger behind the
    hearing; the leaves' own slots are still owed; the planes' debt is not yet marked.
  `hok`, `hpo`, `hv`: the library's test on the shape; 5 ≤ lm ≤ kT + 5; v < 64. These are public.
  `hz0`, `hz1`: the sizes of the two points. They follow from what was heard being the run's: the
    points are lists of mu + d challenges. `zb_sizes` (Honest/K3/Law/Thread/Out.lean) has the two
    sizes, as kT + cK + 5, from `hh` alone.
  `hf`, `hDN`, `hS`, `hroom`, `hh`, `hg`: the course's face is the shape's; the numbers of D; the
    ledger in front has its sizes and room for the lookup's slots; the hearing returns; the
    program's structure of what was heard.
The tie of the bits (`hbit`) and the dictionary (`hD`) are asked of one reading ν: the first reads
cells, the second mask entries. Honest/K3/Law/Thread/ExchangeReading.lean carries a tie that was
shown at one mask row to any other.

How the proof goes. The library shows the item (`K3PlanesPaid`, Johnson/Top/H/K3LeftStatement.lean,
proved at every seat that fits: `k3PaidAtSeat`, Johnson/Top/H/K3OutPaid.lean) from an acceptance by
the run of claims "planes" whose three claims are worth 0 in one world, and from three clauses on
the forms that the caller's readers hand in. The item itself names no caller. So the run is made
here at a seat of this file's own, a ledger and a heard structure and no more, with readers that
hand in constant forms: for each column the very number that the clause asks. The clauses then hold
by reading a constant; that the three claims are worth 0 is `Left`, through
Honest/K3/Law/SeatedWorth.lean and Honest/K3/Law/ReadersSayCount.lean.

Users. Honest/K3/Law/Thread/LookAsksOf.lean [not in this library] calls `outPlanes_of_left`.

Limits. The item is shown at ledgers at which the claims on the planes are not yet made. No instance
of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeRows
import Johnson.Desc.ProofFile.Honest.K3.Law.ReadersSayCount
import Johnson.Desc.ProofFile.Honest.K3.Law.SeatedAll
import Johnson.Top.H.K3OutPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork Aff Reading World)
open OnBytes.Model.Forest (Shape)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Sized Later)
open OnBytes.K.Kc (Fl)
open OnBytes.HonestTrace.Look (Data)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV Seat Readers faceOf hearV toHeard toHeardG toPsc planesRun
  unpaid leafVars)
open VerifiableInference.Desc.First.Look
  (leavesRowOwn planeClaimsOwn planesAtF planesOk planesAddedF)
open VerifiableInference.OnPublicFiles (K3OutPlanes K3RanAt SeatFits k3PaidAtSeat laterFo_of_psc)
open ProofFile.Honest.K3.Law.Spec (planesOf ColsSay PinsSay readersSay_of)

/-! ## 1 A seat of this file's own -/

/-- **The seat**: a ledger and a heard structure. -/
def bare : Seat (Fork × OnBytes.Model.Forest.Heard) Aff where
  fork := fun s => some s.1
  owed := fun _ => default
  put := fun _ g F => (F, g)
  mark := fun s F => (F, s.2)
  heard := fun s => some s.2
  claim := id

theorem bare_fits : SeatFits bare id := ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ => rfl⟩

/-- A form that is a constant with the reading x. -/
def constE (x : KE) : Aff := Aff.ofConst (down x)

theorem constE_value (x : KE) (Wd : World GE) : (constE x).value Reading.gl Wd = x := by
  unfold constE
  rw [Aff.value_ofConst]
  exact up_down x

/-- **The readers**: for each column the number that the library's clause asks, as a constant. -/
def readersAt (h : Shape) (lm : Nat) (g : OnBytes.Model.Forest.Heard) (ν : _root_.Fo.Pl → GE) :
    (Nat → Nat → Option Aff) × (Nat → Option Aff) :=
  (fun e col => some (constE (_root_.Fo.colsK h lm (_root_.Fo.rdA Reading.gl (g.zb e)) ν col)),
    fun col => some (constE (Cb.Fo.Pin.pinColK lm ν col)))

/-! ## 2 The late row -/

/-- **Where the leaves' own slots are still owed, the part's own late row and the seated text of it
return, with one ledger behind.** Conditional on the return of `hearV` and on the slots being owed
at F'. -/
theorem leavesRow_both (f : LFace) {F G F' : Fork} {x : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hroom : F.next + f.slots ≤ F.ns) (hh : hearV f F x = some (g, G)) (hS' : Sized F')
    (hL : Later G F')
    (ho : OnBytes.PscRun.SlotsOwed F' (F.next + firstSlot f .leaves) (Stage.own f .leaves)) :
    ∃ y G', MaskedSum.row g.leaves oneE {} F' = some (y, G') ∧ Later F' G' ∧
      ∀ (S1 : E) (kept1 : Aff) (t : OnBytes.K.Kc.Tape),
        leavesRowOwn (toPsc g.leaves) S1 kept1 F' t =
          some ((toPsc g.leaves).rowForm S1 kept1, G', t) := by
  obtain ⟨hok, hm⟩ := hearV_messages hh
  have hp := two_le_planes_of_ok f hok
  obtain ⟨C, z, F₀, G₀, rs₀, h0, _, hn⟩ := leaves_heard f hS hm
  have hF0 := leaves_first f hp hn
  have hown : Stage.own f .leaves = 1 + f.mu + 2 * f.d := slots_leaves f
  have hall : MaskedSum.ownSlots
      ({ lead := 0, vs := leafVars f z, ends := none } : MaskedSum.Call).all =
      1 + f.mu + 2 * f.d := own_leafVars f z
  have hns : F'.ns = F.ns := hL.ns.trans (hearV_later hh).ns
  have hr := MaskedSum.row_returns_later h0 hS' (by rw [hall, hns]; omega)
    (fun j a b => ho.2 j (by omega) (by rw [hall] at b; omega)) oneE {}
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hr
  have hy' : MaskedSum.row g.leaves oneE {} F' = some (y.1, y.2) := hy
  exact ⟨y.1, y.2, hy', MaskedSum.row_keeps hy', fun _ _ t => leavesRowOwn_of_row t h0 hy'⟩

/-- Marking a debt as paid leaves a later ledger. -/
theorem paid_later (F : Fork) (i : Nat) : Later F (F.paid i) :=
  ⟨Nat.le_refl _, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩

/-! ## 3 The item -/

/-- **The item on the planes of the row out.** Conditional on `Left` at `planesOf D`, on `Dict`, on
the bits of D being the reading of their places, and, at the ledger F' at which the item is asked:
sizes, the leaves' own slots still owed, the planes' debt not yet marked. No instance of these
hypotheses is exhibited in this file. -/
theorem outPlanes_of_left {W : Type} (R : Course W) (h : Shape) (hf : R.f = faceOf h)
    (keys : Nat → Array E → GE) (D : Data _root_.Fo.Pl KE) (lm jLK : Nat) (θ : KE)
    (hDN : D.N = _root_.Fo.numsF h lm jLK θ) {F G F' : Fork} {x : List Fmt.RoundView} {gV : HeardV}
    {g : OnBytes.Model.Forest.Heard} (hS : Sized F) (hroom : F.next + (faceOf h).slots ≤ F.ns)
    (hh : hearV (faceOf h) F x = some (gV, G)) (hg : toHeard h (toHeardG gV) = some g)
    (hLeft : Left R (planesOf D) keys gV G) (hok : FoNums.ok h = true) (hpo : planesOk h lm = true)
    (hv : h.v < 64) (hz0 : gV.zb0.size = 5 + h.d) (hz1 : gV.zb1.size = 5 + h.d) (hS' : Sized F')
    (hL : Later G F')
    (ho : OnBytes.PscRun.SlotsOwed F' (F.next + firstSlot (faceOf h) .leaves)
      (Stage.own (faceOf h) .leaves))
    (hu : unpaid F' g.owedPlanes = true) (first : Nat) (ν : _root_.Fo.Pl → GE) (h0 : ν .zero = 0)
    (hbit : ∀ u j, u < 2 ^ D.N.d → j < 2 ^ D.N.w → D.bits u j = ν (D.N.bAt u j)) (hD : Dict R ν) :
    K3OutPlanes h lm first ν Reading.gl g F' := by
  obtain ⟨hsh, hlv, _, _⟩ := toHeard_fields hg
  obtain ⟨hzb0, hzb1⟩ := Spec.toHeard_zb hg
  have h5 : 5 ≤ lm ∧ lm ≤ h.kT + 5 := by
    simpa [planesOk] using hpo
  have hNC : h.NC ≤ 2 ^ h.cK := (Cb.Fo.ok_parts hok).1.2.2.1
  have hpub : h.pub.size = h.NT := (Cb.Fo.ok_parts hok).1.2.2.2.2.2.1
  obtain ⟨y, G', hrow, hl', hseat⟩ := leavesRow_both (faceOf h) hS hroom hh hS' hL ho
  -- the three folds
  obtain ⟨a0, ha0⟩ := planesAtF_returns g lm 0 (readersAt h lm g ν).1 (fun _ _ => rfl) F' []
  obtain ⟨a1, ha1⟩ := planesAtF_returns g lm 1 (readersAt h lm g ν).1 (fun _ _ => rfl) F' []
  obtain ⟨c, hc⟩ : ∃ c, countFold g lm (fun col => Fl.need ((readersAt h lm g ν).2 col)) F' [] =
      some (c, F', []) :=
    fl_foldlM_same _ F' [] _ _ fun s col _ => ⟨s + constE (Cb.Fo.Pin.pinColK lm ν col), rfl⟩
  have hcl := planeClaimsOwn_is g lm (fun e col => Fl.need ((readersAt h lm g ν).1 e col))
    (fun col => Fl.need ((readersAt h lm g ν).2 col)) (G := G') (by rw [hsh]; exact hpo) ha0 ha1 hc
    (by rw [hlv]; exact hseat _ _ _)
  -- the run at this file's own seat
  have hrun : planesRun bare lm (fun _ => some (readersAt h lm g ν)) 0 (F', g) =
      .ok ([g.leaves.rowForm oneE (Aff.scale a0 g.leavesA), Aff.slot g.sBit - a1, c],
        (G'.paid g.owedPlanes, g)) := by
    have hall : (do
        let fs ← planeClaimsOwn g lm (fun e col => Fl.need ((readersAt h lm g ν).1 e col))
          fun col => Fl.need ((readersAt h lm g ν).2 col)
        planesAddedF g
        pure fs : Fl (Array Aff)) F' [] =
        some (#[g.leaves.rowForm oneE (Aff.scale a0 g.leavesA), Aff.slot g.sBit - a1, c],
          G'.paid g.owedPlanes, []) := by
      rw [fl_bind_some hcl]
      rfl
    unfold planesRun
    simp only [bare, hu, VerifiableInference.Desc.named, VerifiableInference.Desc.need, bind,
      Except.bind, if_true, pure, Except.pure]
    have hall' := hall
    simp only [bind, pure] at hall'
    rw [hall']
    rfl
  -- the world
  have hRS := readersSay_of h lm jLK θ ν h0 hNC h5.1 h5.2 hv gV g hg hz0 hz1 (readersAt h lm g ν).1
    (readersAt h lm g ν).2
    ((G'.paid g.owedPlanes).worldOf Reading.gl (fun j => ν (.mask j)) fun _ _ _ => 0)
    (fun col _ => by
      show (constE _).value _ _ = _
      rw [constE_value, hzb0]
      rfl)
    (fun col _ => by
      show (constE _).value _ _ = _
      rw [constE_value, hzb1]
      rfl)
    (fun col _ => constE_value _ _) D hDN hbit ha0 ha1 hc
  obtain ⟨w0, w1, w2⟩ := seated_zero R h hf (planesOf D) keys gV G hLeft g hg hpub hS' hL hrow a0 a1
    c
    (G'.paid g.owedPlanes) _ (fun _ _ _ => 0) (paid_later G' _) hD (by rw [hf]; exact hRS)
  have key := (k3PaidAtSeat _ _ bare id bare_fits lm (fun _ => some (readersAt h lm g ν))
    (fun _ => none)).2.1 GE Reading.gl g F' first (F', g) _ (G'.paid g.owedPlanes)
    (G'.paid g.owedPlanes) ν (fun _ _ _ => 0) (by rw [hsh]; exact hok)
    ⟨rfl, ⟨F', rfl, laterFo_of_psc (Later.refl F'), hS'⟩, ⟨0, _, hrun, rfl⟩⟩
    (laterFo_of_psc (Later.refl _))
    (by
      intro cl hcl'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl'
      rcases hcl' with rfl | rfl | rfl
      · exact w0
      · exact w1
      · exact w2)
    (fun col _ => by
      show (constE _).value _ _ = _
      rw [constE_value, hsh]
      rfl)
    (fun col _ => by
      show (constE _).value _ _ = _
      rw [constE_value, hsh]
      rfl)
    (fun col _ => constE_value _ _)
  rw [hsh] at key
  exact key

#print axioms ProofFile.Honest.K3.Law.Exchange.outPlanes_of_left
#print axioms ProofFile.Honest.K3.Law.Exchange.bare_fits
#print axioms ProofFile.Honest.K3.Law.Exchange.constE_value
#print axioms ProofFile.Honest.K3.Law.Exchange.leavesRow_both
#print axioms ProofFile.Honest.K3.Law.Exchange.paid_later

end ProofFile.Honest.K3.Law.Exchange
