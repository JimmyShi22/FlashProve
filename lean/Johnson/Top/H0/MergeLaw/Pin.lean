-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Pin.lean: the merge's law of every pinned witness. Of the three readers of
committed values two are the library's decoder with a sample; the cells are read off the
letter decT, at which the witness is pinned. Definitions, and theorems with their proofs.

In `merge_table_row` (Johnson/Top/H0/MergeLaw/WoRow.lean) the cells, the sub-proof's mask row and
the index masks are read off the statement in front by three free functions: the law is true of
every choice, also of readers that have nothing to do with the oracles. Here the mask row and the
index masks are laid by the decoder with a sample at a member of a sending (`decAt`,
Johnson/Desc/Sound/World.lean). THE CELLS ARE NOT YET SO: they are read by rc of what decT gives,
and decT, "the stored table's decoder", is itself a free letter, bound by one condition alone (L2,
L3): the law holds of every such function. The conclusion speaks of every witness that is pinned
BEHIND the block, at that witness's own readings.

Main names:
  `vecOf`, `vecBy`, `vecAt`: a vector of n entries read off a table at the places that pos names (0
    from n on): off the witness's table of a member (`memTab`); off what the member decodes to at a
    statement.
  `vec_of_pin`: at a pinned witness the two are one function, where the places named lie inside the
    member's ranges. By `dec_of_pin` and `tab_of_pin`. `cellAt`, `cell_of_pin`: the like for the
    cells.
  `flat`: the flat numbering of a table's entries, row first.
  `Pinned`: the three pins: the cells (`pinWOf`, MeaningSig.lean), the member xM, the member xI
    (`PinAt`, MsgSig.lean).
  `merge_table_pinned`: `Reduction.Leads` of the merge's piece, on `frontB`'s yes, towards: for
  every
    witness w with `Pinned` at the statement BEHIND the block: `ItemsRow` at w's own cells, mask row
    and index masks. The pins are brought in front of the block by `rides` (SendLaw.lean).
  `piece_local`, `merge_table_pins`: the same with two of its premises paid (`SmpStays`; "the stored
    table decodes alike in front and behind"): out of `isLocal` (Law.lean), `out_behind` and the
    strings' own make.

WHAT STAYS A LETTER OR A PREMISE OF `merge_table_pins`, beside what WoRow.lean's head lists.
(L1) WHICH MEMBER BEARS WHICH VECTOR, AND WHERE AN ENTRY STANDS IN ITS TABLE: xM, xI, posM, posI are
letters, under "the places of the entries below N.ns | N.ni lie inside the member's ranges". What
the
report on these steps says, by reading; no theorem backs it, and none of it is laid here:
  slot j of the head's ledger: the mask table of the first of the open segment's messages that has
  mask rows (`maskOracle`, Johnson/Desc/First/Batch/Law/AsRow.lean), at `flat true R`, R that
  table's
  row bits;
  entry c of the index masks' message: the mask table of the first message "at the start", sent in
  the first chain's first sending, at `flat true k`, k the ceiling of the logarithm of its mask rows
  (OnBytes/Iop/Send.lean, Ground.lean: `groupIndex`); that the ledger's own logRows, by which
  `takeEntry` steps, is that k has no lemma.
(L2) The type Cells, its reader rc and the stored table's decoder decT are letters.
(L3) cs, G, arr and the samples' reader smp are letters of Johnson/Desc/Sound/. Of smp and decT it
is asked that they do not read "what is owed" and the open link's part of the record. `Fenced`: the
two members' trees' numbers lie below the piece's base: a premise on numbers.
(L4) That a border's relation holds the three pins, so that a rule of composition can spend this
law, is not said here.

IS IT EMPTY? Not tried. `Fenced` holds at every base above the two trees' numbers, and the two
conditions on smp and decT hold of all readers of the record's other fields. Whether the readers
that
will be laid for smp and decT are such, and whether the two trees' numbers lie below the base of the
merge's piece at a real plan, is not shown. No member with `frontB`'s yes, a yes of the piece and a
pinned witness is shown.

Limits. It is no soundness of the protocol. A pin fixes a message inside the member's ranges alone.
Whether a member decodes, and whether what it decodes to is the one candidate, is the promise's
matter (no collision): not touched. Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.WoRow
import Johnson.Desc.Sound.SendLaw
import Johnson.Desc.Sound.MeaningSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes (E zeroE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading)
open VerifiableInference.Desc (FileDescription Wit Strs)
open VerifiableInference.Desc.Sound (Frame Piece below Mem MsgT InMsg memTab decAt PinAt pinWOf
  tab_of_pin dec_of_pin rides Fenced SmpStays strsOf Sending out_behind)
open Johnson.Pack (sigOf)
open Johnson.Desc.First.ForkMerge (HeadMergeP mergeEntries headClaimMergeKind)
open K11Caller (MergeIn GS noRd)
open _root_.Run (ckP)
open scoped ENNReal

variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- A vector read off a table: entry j, for j below n, is the table's value at the place that pos
names; 0 from n on. -/
def vecOf (n : ℕ) (pos : ℕ → Bool × ℕ × ℕ) (t : MsgT) : ℕ → GE := fun j =>
  if j < n then t (pos j).1 (pos j).2.1 (pos j).2.2 else 0

/-- The vector off the witness, at a member. -/
def vecBy (n : ℕ) (pos : ℕ → Bool × ℕ × ℕ) (x : Mem) (w : Wit Cells Tok MsgT) : ℕ → GE :=
  vecOf n pos (memTab cs arr w x)

/-- The vector off the statement: of what the member decodes to; the zero table where it does not
decode. -/
def vecAt (n : ℕ) (pos : ℕ → Bool × ℕ × ℕ) (x : Mem) (a : S) (y : Strs) : ℕ → GE :=
  vecOf n pos ((decAt cs G smp x.1 x.2 a y).getD fun _ _ _ => 0)

/-- **A pinned witness's vector is the statement's**, where the places named lie inside the member's
ranges. -/
theorem vec_of_pin (n : ℕ) (pos : ℕ → Bool × ℕ × ℕ) (x : Mem)
    (hin : ∀ j, j < n → InMsg cs (x.1.l.get x.2).1 (pos j).1 (pos j).2.1 (pos j).2.2)
    (a : S) (y : Strs) (w : Wit Cells Tok MsgT)
    (hp : PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w) :
    vecBy cs arr n pos x w = vecAt cs G smp n pos x a y := by
  funext j
  unfold vecBy vecAt vecOf
  by_cases hj : j < n
  · rw [if_pos hj, if_pos hj, dec_of_pin cs G arr smp x.1 x.2 a y w hp]
    exact tab_of_pin cs G arr smp x.1 x.2 a y w _ (dec_of_pin cs G arr smp x.1 x.2 a y w hp) hp _ _
        _
      (hin j hj)
  · rw [if_neg hj, if_neg hj]

/-- The flat numbering of a table's entries, row first: entry J of a table with 2 ^ R rows (some of
them idle) stands in row J % 2 ^ R at place J / 2 ^ R. b: the mask table or the main table. -/
def flat (b : Bool) (R : ℕ) : ℕ → Bool × ℕ × ℕ := fun J => (b, J % 2 ^ R, J / 2 ^ R)

variable (rc : Cells → ℕ → ℕ → GE)
  (decT : (ℕ → Option (ℕ × List UInt64)) → S → Option Cells)

/-- The cells off the statement: of what the stored table decodes to; zeros where it does not. -/
def cellAt (a : S) (y : Strs) : ℕ → ℕ → GE :=
  match decT y.cell a with
  | some c => rc c
  | none => fun _ _ => 0

theorem cell_of_pin (a : S) (y : Strs) (w : Wit Cells Tok MsgT) (h : pinWOf decT a y w) :
    rc w.cells = cellAt rc decT a y := by
  unfold cellAt
  rw [show decT y.cell a = some w.cells from h]

/-- **The three pins**: the cells, the member that bears the sub-proof's mask row, the member that
bears the index masks. -/
def Pinned (xM xI : Mem) (a : S) (y : Strs) (w : Wit Cells Tok MsgT) : Prop :=
  pinWOf decT a y w ∧ PinAt G cs xM.1.l xM.1.seat (fun z => smp z xM.1) arr xM.2 a y w ∧
    PinAt G cs xI.1.l xI.1.seat (fun z => smp z xI.1) arr xI.2 a y w

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl) {F : Frame} {W : Type}

/-- **THE MERGE's LAW AT A PIECE, OF EVERY PINNED WITNESS.** -/
theorem merge_table_pinned (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
    (hk0 : 0 < Pl.lay.lk) (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg)
    (hunit : ∀ a u, Pl.lay.U[Pl.ui a]? = some u → OnBytes.Road.UnitOK Pl.lay.lk u) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind)
    (xM xI : Mem) (posM posI : ℕ → Bool × ℕ × ℕ)
    (hinM : ∀ j, j < N.ns → InMsg cs (xM.1.l.get xM.2).1 (posM j).1 (posM j).2.1 (posM j).2.2)
    (hinI : ∀ j, j < N.ni → InMsg cs (xI.1.l.get xI.2).1 (posI j).1 (posI j).2.1 (posI j).2.2) :
    ∃ (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT) (hk : ds.length = (GS Reading.gl N (noRd N)).k),
      L = dZ :: d0 :: (ds ++ [dY, dV]) ∧
      ∀ (base : ℕ) (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W),
        Fenced base [xM, xI] →
        SmpStays cs smp (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext)
          [xM, xI] →
        (∀ a τ b,
          (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).ior.red.out a τ =
            some b → decT (strsOf F b.2).cell b.1 = decT (strsOf F a.2).cell a.1) →
        (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).ior.red.Leads
          (fun a => frontB N a.1 = true)
          (fun a a' => ∀ w : Wit Cells Tok MsgT,
            Pinned cs G arr smp decT xM xI a'.1 (strsOf F a'.2) w →
            ItemsRow N (rc w.cells) (vecBy cs arr N.ns posM xM w) (vecBy cs arr N.ni posI xI w)
              (frontIn Pl.n a.1) a'.1)
          (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err ∧
        Err.Below (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err
          ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨dZ, d0, ds, dY, dV, hk, hL, hall⟩ :=
    merge_table_row (F := F) (W := W) N P hlay h1 hk0 hnum hunit L he hkd
  refine ⟨dZ, d0, ds, dY, dV, hk, hL, fun base ext hF hS hT => ?_⟩
  obtain ⟨hleads, hbelow⟩ := hall base ext (fun a => cellAt rc decT a.1 (strsOf F a.2))
    (fun a => vecAt cs G smp N.ns posM xM a.1 (strsOf F a.2))
    (fun a => vecAt cs G smp N.ni posI xI a.1 (strsOf F a.2))
  refine ⟨hleads.conseq (fun _ h => h) ?_, hbelow⟩
  intro a τ a' _ hout hq w hw
  obtain ⟨pw, pm, pi⟩ := hw
  have pm' := ((rides cs G arr smp _ [xM, xI] hF hS a a' τ hout xM (by simp)).1 w).1 pm
  have pi' := ((rides cs G arr smp _ [xM, xI] hF hS a a' τ hout xI (by simp)).1 w).1 pi
  have pw' : pinWOf decT a.1 (strsOf F a.2) w := by
    unfold pinWOf at pw ⊢
    rw [← hT a τ a' hout]
    exact pw
  rw [cell_of_pin rc decT a.1 (strsOf F a.2) w pw',
    vec_of_pin cs G arr smp N.ns posM xM hinM a.1 (strsOf F a.2) w pm',
    vec_of_pin cs G arr smp N.ni posI xI hinI a.1 (strsOf F a.2) w pi']
  exact hq

/-- Where the merge's piece puts out, the record behind is the record in front but for "nothing is
owed" and the head's part. -/
theorem piece_local (P : HeadMergeP) (Gw : WeightsL GE) {dZ d0 : RDT} {ds : List RDT} {dY dV : RDT}
    (hk : ds.length = Gw.k) (base : ℕ)
    (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W)
    (a b : S × F.E.Str) (τ : Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))))
    (h : (mergePiece F W P Gw dZ d0 ds dY dV hk base ext).ior.red.out a τ = some b) :
    ∃ a' : HeadOwn, b.1 = { a.1 with rowsOwed := none, here := .head a' } := by
  obtain ⟨_, _, _, gs, hdec⟩ := piece_yes (headClaimMergeKind P)
    (mergePiece F W P Gw dZ d0 ds dY dV hk base ext) rfl rfl a b τ h
  obtain ⟨_, a', _, _, e, _⟩ := isLocal P _ _ _ hdec
  exact ⟨a', e⟩

/-- **THE SAME, THE TWO FRAME FACTS PAID**: the samples' reader and the stored table's decoder are
asked not to read what the merge turns: "what is owed" and the open link's part. -/
theorem merge_table_pins (P : HeadMergeP) (hlay : Pl.lay = P.lay) (h1 : Pl.n = 1)
    (hk0 : 0 < Pl.lay.lk) (hnum : N.first + 1 + 2 * P.lay.lk + 2 = P.nMsg)
    (hunit : ∀ a u, Pl.lay.U[Pl.ui a]? = some u → OnBytes.Road.UnitOK Pl.lay.lk u) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries P.lay.lk 1 P.work)
    (hkd : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind)
    (xM xI : Mem) (posM posI : ℕ → Bool × ℕ × ℕ)
    (hinM : ∀ j, j < N.ns → InMsg cs (xM.1.l.get xM.2).1 (posM j).1 (posM j).2.1 (posM j).2.2)
    (hinI : ∀ j, j < N.ni → InMsg cs (xI.1.l.get xI.2).1 (posI j).1 (posI j).2.1 (posI j).2.2)
    (hsmp : ∀ (s : S) (a' : HeadOwn), smp { s with rowsOwed := none, here := .head a' } = smp s)
    (hdec : ∀ c (s : S) (a' : HeadOwn),
      decT c { s with rowsOwed := none, here := .head a' } = decT c s) :
    ∃ (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT) (hk : ds.length = (GS Reading.gl N (noRd N)).k),
      L = dZ :: d0 :: (ds ++ [dY, dV]) ∧
      ∀ (base : ℕ) (ext : S × F.E.Str → Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) → W → W),
        Fenced base [xM, xI] →
        (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).ior.red.Leads
          (fun a => frontB N a.1 = true)
          (fun a a' => ∀ w : Wit Cells Tok MsgT,
            Pinned cs G arr smp decT xM xI a'.1 (strsOf F a'.2) w →
            ItemsRow N (rc w.cells) (vecBy cs arr N.ns posM xM w) (vecBy cs arr N.ni posI xI w)
              (frontIn Pl.n a.1) a'.1)
          (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err ∧
        Err.Below (mergePiece F W P (GS Reading.gl N (noRd N)) dZ d0 ds dY dV hk base ext).err
          ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨dZ, d0, ds, dY, dV, hk, hL, hall⟩ :=
    merge_table_pinned (F := F) (W := W) cs G arr smp rc decT N P hlay h1 hk0 hnum hunit L he hkd
      xM xI posM posI hinM hinI
  refine ⟨dZ, d0, ds, dY, dV, hk, hL, fun base ext hF => hall base ext hF ?_ ?_⟩
  · intro a τ b hout x _
    obtain ⟨a', e⟩ := piece_local P _ hk base ext a b τ hout
    rw [e, hsmp]
  · intro a τ b hout
    obtain ⟨a', e⟩ := piece_local P _ hk base ext a b τ hout
    rw [e, hdec, out_behind _ a b τ hout]
    rfl

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_table_pins
#print axioms VerifiableInference.Desc.First.MergeLaw.vec_of_pin
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_table_pinned
