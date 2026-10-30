-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawRow.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS ROW OF THE TABLE OF
JOINTS, IN PLAIN ITEMS OVER THE CARRIED RECORD'S OWN READERS, PROVED IN THE PLAIN FORM.

The table of joints of the first chain gives the block of the draw one row: IN FRONT "every cell is
small" and "the tie"; BEHIND "the forms of the run «small» are worth 0" and "the digits are in their
tables". The laws run backward: what stands in front holds IF what stands behind holds, but for the
round's lost verifier messages. Here the four items are said with no typed size, of a table of
cells A w (array, row, column), in the words of the record of the smallness test that lies in the
carried record:
  `TieAt` (Johnson/Desc/First/K8/LawTie.lean): "every cell is small", the packing, and the tie.
  `SmallAt A s w`: a link is open, and EVERY SINGLE EQUATION OF THE LIST `rowsTail`
    (OnBytes/Tie/Pv/Tail/EndRows.lean), at the link's record and its own closed list of tables, is 0
    at A w: a tie for each matrix, packed row and combination; a read for each table's segment and
    combination. THIS IS THE READER OF THE RUN'S FORMS OFF THE RECORD. The list bears exponents that
    start at a number pc; 0 is written here. `small_any`: THAT NUMBER DOES NOT MATTER: the rows are
    0 at one pc if and only if at every other. `small_iff_ledger`: at the cells of committed entries
    it is, at every pc, "every form of the library's `rowsLedger` holds on these entries": the form
    in which the second half's law (`K08Out`) takes it, at the plan's number of claims.
  `DigitsAt A s w`: a link is open, and the cells of the digits' array, at the verifier's columns,
    are in the two digits' tables.
  `PinsAt`: member by member the library's decoder with the sample gives the witness's message.
  `Extra s`: two conditions more on the record in the state: the shapes fit the matrices; every
    table lies on the third vector of reads.
  `k08_row`: **THE ROW**: between the conditions (`lay_onA` with `Extra`, in front and behind):
    pins, `SmallAt` and `DigitsAt` behind give pins and `TieAt` in front: `KeepsW`
    (Johnson/Desc/Plain/World.lean) at the piece's own error. `k08_row_place`: the same at the
    public record `recP tlL p`, which is made of the place's numbers.
WHAT IS USED FOR CERTAIN OF A YES, AND SO IS NO PREMISE: a link is open · the record behind is the
record in front with the list of the typed challenge and the running sums as first columns · THE
RECORD HAS THE PLACE'S NUMBERS: matrices, rows, columns, combinations, shapes of tables (tests (d),
(e), (f), (t): `placeRec_of_yes`, Johnson/Desc/First/K8/LawPlace.lean).
Statement and proof; nothing is counted anew: `lay_keepsW`, `lay_relB_of_rows`
(Johnson/Desc/First/K8/LawLay.lean), `tie_of_relA`.
Limits. The letters of LawLay.lean stand: J, Y, entE, entW with `hE` · smpOf · l, seat', arr.
PREMISES: the public record tl0 has the place's numbers (`PlaceRec p tl0`: `recP tlL p` is such a
record, at the layout of a link's planned record tlL) · the error · each matrix has its symbol array
and the vector of reads its array in tl0's lists. THE ITEMS BEHIND ARE READ AT THE BORDER RIGHT
BEHIND THE DRAW: that they hold there if they hold at the front of the batching (the lookup on the
digits stands between and turns the record) is the riding's, not shown here. Non-emptiness at the
real sizes is not shown. Nothing says that what stands at a border holds.
`SmallAt`, `small_any`, `small_iff_ledger`, `DigitsAt` and `Extra` are defined and proved in
Johnson/Desc/First/K8/LawItems.lean.

-/
import Johnson.Desc.First.K8.LawPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Cb Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Maker OnBytes.Road.Rows OnBytes.Tie.Pv.Tail
  OnBytes.Tie.Pv.Tail.Port KObj Johnson.Pack VerifiableInference.OnPublicFiles
  VerifiableInference.Desc.Sound

section
variable {J : Type} [Fintype J] (Y : Lay J) (tl0 : HTailF2) (cs : OnBytes.Codes)
  (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  {Cells Tok : Type} (entE : (sigOf cs l).Msg → J → Cb.Gl.E)
  (entW : Wit Cells Tok MsgT → J → Cb.Gl.E) {Xi : Type} (G : FileDescription Xi)
  (smpOf : S → (sigOf cs l).Smp)
  (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
  (Cl : Type) (F : Frame) (p : Par) (base e : ℕ) (hseat : ∀ i, (seat' i).1 < base)

/-- The pins. -/
def PinsAt (a : S × F.E.Str) (w : Wit Cells Tok MsgT) : Prop :=
  ∀ i, (sigOf cs l).decs (smpOf a.1) (wordsOf G cs l seat' (strsOf F a.2)) i =
    some (msgsOf cs l seat' arr w i)

local notation "LR" => layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat

/-- **THE ROW of the block of the draw, in plain items.** -/
theorem k08_row
    (hE : ∀ w j, early tl0 (Y.addr j) = true → entE (msgsOf cs l seat' arr w) j = entW w j)
    (hgt : tl0.NM ≤ tl0.gtTree.size) (hu : ∃ t, tl0.ix.U[2]? = some (some t))
    (hP : PlaceRec p tl0)
    (he : (Fintype.card (Dr (OnBytes.Tie.Pv.Tail.sizeOf tl0).size) /
      2 ^ (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e) :
    (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).ior.red.KeepsW
      (fun a => (LR).onA a ∧ Extra a.1) (fun b => (LR).onB b ∧ Extra b.1)
      (fun a w => PinsAt cs l seat' arr G smpOf F a w ∧
        TieAt (fun w a r c => Y.cellAt (entW w) a r c) a.1 w)
      (fun b w => PinsAt cs l seat' arr G smpOf F b w ∧
        SmallAt (fun w a r c => Y.cellAt (entW w) a r c) b.1 w ∧
        DigitsAt (fun w a r c => Y.cellAt (entW w) a r c) b.1 w)
      (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).err := by
  have hf := fits_of_place hP
  refine Iop.Reduction.Leads.conseq
    (lay_keepsW Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat hf he)
    (fun _ h => h.1) fun a τ b ha hout hq => ?_
  obtain ⟨m, c, ⟨⟩⟩ := τ
  obtain ⟨_, ⟨cols, k, hstep⟩, _⟩ := piece_out atS p base e a b m c hout
  obtain ⟨_, _, _, c4, c5, _, _, _, hl, _⟩ :=
    (hear_law_view (Cl := Cl) hf atS m c F.ft a.1 b.1 k cols).1 hstep
  obtain ⟨tl, ht, hb⟩ := atS_lay a.1 b.1 _ _ hl
  have hd : tl.NM = p.ks.length := by simpa [atS, ht] using c4
  have hk : tl.mats.toList.map (·.k) = p.ks := by simpa [atS, ht] using c5
  have hnm : tl.NM = tl.mats.size := by rw [hd, ← hk]; simp
  rw [firstColumns_of_tests tl p hk] at hb
  have htb : b.1.tl? = some { tl with
      cfF := listOf (matrixOf hf c)
      cfFirst := tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0] } := by
    rw [hb]
    exact putTl_tl a.1 tl _ ht
  have hz : SameSize tl tl0 :=
    sameSize_of_place (placeRec_of_yes (Cl := Cl) p tl F.ft a.1 b.1 k _ cols ht hstep) hP
  have hpa : SameLay (recOf tl0 a.1) tl0 :=
    ((lay_onA Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat a).1 ha.1).2
  have hpb : SameLay (recOf tl0 b.1) tl0 := by
    rw [hb, recOf_put tl0 a.1 tl _ _ ht]
    exact hpa
  obtain ⟨hfit, htree⟩ := ha.2 tl ht
  refine ⟨⟨hq.1, fun t' ht' => ?_⟩, fun w hw => ?_⟩
  · obtain rfl := Option.some.inj (htb.symm.trans ht')
    exact ⟨hfit.of_same rfl rfl rfl, htree⟩
  · obtain ⟨hpin, ⟨t1, e1, hrows⟩, ⟨t2, e2, hdg⟩⟩ := hw
    obtain rfl := Option.some.inj (htb.symm.trans e1)
    obtain rfl := Option.some.inj (htb.symm.trans e2)
    have hx : recOf tl0 a.1 = blank tl := by
      unfold recOf
      rw [ht]
      rfl
    have hp : SamePub tl tl0 := by
      have h0 := hpa
      rw [hx] at h0
      exact { toSameSize := hz, toSameLay := ⟨h0.gt, h0.ix, h0.mz, h0.off⟩ }
    have hB := lay_relB_of_rows Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat hE b
      w _ htb hpb ⟨hz.nm, hz.m, hz.k, hz.tau, hz.tabs⟩ hgt hu hnm rfl (matrixOf hf c) rfl hpin 0
      (hfit.of_same rfl rfl rfl) htree
      (fun μ u i => by
        have h1 := hdg μ.val (by show μ.val < tl.NM; rw [hp.nm]; exact μ.isLt) u.val
          (by show u.val < tl.tau; rw [hp.tau]; exact u.isLt) i.val
          (by show i.val < (tl.mats.getD μ.val {}).m; rw [hp.m]; exact i.isLt)
        have z0 : tl.zzCol μ.val 0 0 = tl0.zzCol μ.val 0 0 := zzCol_same hp _ _ _
        have z1 : tl.zzCol μ.val 1 0 = tl0.zzCol μ.val 1 0 := zzCol_same hp _ _ _
        have h2 : Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.lo
              (Y.cellAt (entW w) tl.ix.ZZ u.val ((tl.zzCol μ.val 0 0).getD 0 + i.val)) ∧
            Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl0).size.hi
              (Y.cellAt (entW w) tl.ix.ZZ u.val ((tl.zzCol μ.val 1 0).getD 0 + i.val)) := h1
        rw [hp.ix, z0, z1] at h2
        exact h2) hrows
    have hA := hq.2 w hB
    exact ⟨hA.1, tie_of_relA Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat hE hgt hu
      a w tl ht hpa hz hA⟩

/-- **THE ROW AT A PUBLIC RECORD THAT IS MADE OF THE PLACE'S NUMBERS**, at the layout of a link's
planned record tlL: no premise on sizes is left but one test on the plan: the place lists as many
numbers of rows as of columns. -/
theorem k08_row_place (tlL : HTailF2) (hlen : p.ms.length = p.ks.length)
    (hE : ∀ w j, early (recP tlL p) (Y.addr j) = true →
      entE (msgsOf cs l seat' arr w) j = entW w j)
    (hgt : p.ks.length ≤ tlL.gtTree.size) (hu : ∃ t, tlL.ix.U[2]? = some (some t))
    (he : (Fintype.card (Dr (OnBytes.Tie.Pv.Tail.sizeOf (recP tlL p)).size) /
      2 ^ (OnBytes.Tie.Pv.Tail.sizeOf (recP tlL p)).size.tau) *
      (Run.bsRound .two (rdt p).entry (rdt p).kind).w ≤ e) :
    (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).ior.red.KeepsW
      (fun a => (layReads Y (recP tlL p) cs l seat' arr entE entW G smpOf hs Cl F p base e
        hseat).onA a ∧ Extra a.1)
      (fun b => (layReads Y (recP tlL p) cs l seat' arr entE entW G smpOf hs Cl F p base e
        hseat).onB b ∧ Extra b.1)
      (fun a w => PinsAt cs l seat' arr G smpOf F a w ∧
        TieAt (fun w a r c => Y.cellAt (entW w) a r c) a.1 w)
      (fun b w => PinsAt cs l seat' arr G smpOf F b w ∧
        SmallAt (fun w a r c => Y.cellAt (entW w) a r c) b.1 w ∧
        DigitsAt (fun w a r c => Y.cellAt (entW w) a r c) b.1 w)
      (piece (Cl := Cl) (W := Wit Cells Tok MsgT) (F := F) atS p base e).err :=
  k08_row Y (recP tlL p) cs l seat' arr entE entW G smpOf hs Cl F p base e hseat hE hgt hu
    (placeRec_recP tlL p hlen) he

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.k08_row
#print axioms VerifiableInference.Desc.First.K8.k08_row_place
