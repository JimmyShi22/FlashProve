-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigRows.lean: the lookup on the digits of a link's smallness test: WHO CAN
PAY THE PREMISE ON THE ROWS (DigRows, Johnson/Top/H/K3OutRows.lean) OF THE PAYER INTO THE ROW OUT,
AT THE CLOSED CALLER (Johnson/Desc/First/Look/K3Caller.lean). Definitions and small statements with
their proofs. It imports nothing of the rule of composition. NO SOUNDNESS IS CLAIMED.

Why. k3Out_of_rows asks DigRows at the cells that a caller's reading msg₀ gives. The closed caller's
msg₀ reads the link's own messages; at the cells of an array that an earlier link sent it is 0.
Whoever makes the world has cells of its own for all the link's arrays. DigRows reads cells of the
counts' array BZ and of the pieces of the digits' array ZZ alone; there the closed caller's msg₀ is
what the messages hold at the cell's seat.

Main names.
  digB_rad: the one Bool on public data (digB) does not read the radius.
  reads_bz, reads_zz: every cell that DigRows reads (BZ: 32 rows, bzColumns columns; each piece's
    rows and columns on ZZ, under p.c0 = q * mz) is among the addresses of ReadsDig.
  dig_cell_bz, dig_cell_zz: so, under DigOK, msg₀ there is what the messages hold at the cell's
    seat: no fall to 0.
  SameLay tl tlS: two records of a smallness test have one layout of the digits' lookup ·
    sameLay_of_fields: the layout reads f9, ix, mz, z1, z2 alone · sameLay_put.
  put_tl, put_sameLay: what the digits' seat lays behind a hearing, read back by the record's own
    reader; it keeps the layout.
  digRows_congr: DigRows passes from cells to cells that agree AT THE CELLS THAT ARE READ; no «for
    all» ranges over a cell outside these.
  SameDig tl tlS: six equations (f9, ix, mz, tau, z1, z2) · SameDig.lay · SameDig.tailOK: the
    library's test TailOK passes from the plan's record to the carried one · sameDig_put ·
    digRows_rec: DigRows at the carried record is DigRows at the plan's.
  digRows_at_caller: under DigOK and SameDig: DigRows at any cells that, where they are read, are
    what the messages m hold at the cell's seat (digVal) gives DigRows at the caller's msg₀ of m.
  digRows_some, digRows_pins, digRows_not_all: DigRows is neither empty nor met by all entries.
Limits. That a world's cells are what the committed messages hold is owed by whoever makes the
world; SO IS THE SAME OF ITS MASKS: nothing here passes from a world with masks of its own to the
world whose masks are the caller's msg₀ at mkOf. SameDig.f9 is an equation of records: a test that
compares some fields of the two records does not give it. put_tl is at a record in which a
sub-proof is open. The public premises of digRows_some are shown at no value here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3OutRows
import Johnson.Desc.First.Look.K3CallerTests
import Johnson.Desc.First.Look.K3SeatLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open OnBytes.Road.Rows (Addr)

theorem getFst {l l' : List (OracleShape × Nat)} (h : l.map (·.1) = l'.map (·.1)) (k : Nat) :
    (l[k]?).map (·.1) = (l'[k]?).map (·.1) := by
  rw [← List.getElem?_map, ← List.getElem?_map, h]

/-- A test that reads of a member its shape alone. -/
theorem onFst {l l' : List (OracleShape × Nat)} (h : l.map (·.1) = l'.map (·.1)) (k : Nat)
    (f : OracleShape → Bool) :
    (match l[k]? with
      | some o => f o.1
      | none => false) =
    (match l'[k]? with
      | some o => f o.1
      | none => false) := by
  have e := getFst h k
  cases h1 : l[k]? with
  | none =>
    cases h2 : l'[k]? with
    | none => rfl
    | some o' =>
      rw [h1, h2] at e
      cases e
  | some o =>
    cases h2 : l'[k]? with
    | none =>
      rw [h1, h2] at e
      cases e
    | some o' =>
      rw [h1, h2] at e
      have e' : o.1 = o'.1 := Option.some.inj e
      show f o.1 = f o'.1
      rw [e']

theorem arrB_congr (S : Road.Rows.Shape) (D : Sent) {l l' : List (OracleShape × Nat)}
    (h : l.map (·.1) = l'.map (·.1)) (i t : Nat) : arrB S D l i t = arrB S D l' i t := by
  unfold arrB
  split
  · rename_i T bn _ _
    congr 1
    split
    · rename_i a _
      exact onFst h a.message fun o =>
        blocksB a.blocks T.R T.K o.mainRows (Johnson.Pack.pMain D.codes o).ell
    · rfl
  · rfl

theorem maskB_congr (D : Sent) {l l' : List (OracleShape × Nat)}
    (h : l.map (·.1) = l'.map (·.1)) (i upTo : Nat) : maskB D l i upTo = maskB D l' i upTo := by
  unfold maskB
  split
  · rename_i m _
    exact onFst h m fun o =>
      decide (0 < o.maskRows) && decide (upTo ≤ (Johnson.Pack.pMask D.codes o).ell)
  · rfl

theorem digList_fst (x : Place) (D : Sent) (rad rad' : OracleShape → Nat) :
    (digList x D rad).map (·.1) = (digList x D rad').map (·.1) := by
  unfold digList sigList
  simp only [List.map_map]
  rfl

/-- **The one Bool does not read the radius.** -/
theorem digB_rad (set : Params.Setting) (x : Place) (tl : HTailF2) (D : Sent)
    (rad rad' : OracleShape → Nat) (pp : Nat) :
    digB set x tl D rad pp = digB set x tl D rad' pp := by
  have h := digList_fst x D rad rad'
  have hall : (digList x D rad).all (fun o => o.1.answers == 1) =
      (digList x D rad').all (fun o => o.1.answers == 1) := by
    have e : ∀ l : List (OracleShape × Nat), l.all (fun o => o.1.answers == 1) =
        (l.map (·.1)).all fun o => o.answers == 1 := fun l => by
      rw [List.all_map]
      rfl
    rw [e, e, h]
  unfold digB digAddrB
  rw [hall, arrB_congr _ D h, arrB_congr _ D h, maskB_congr D h]

/-! ## What the payer's law of the rows reads lies among the addresses that resolve -/

/-- Every cell of the counts' array BZ (32 rows, bzColumns columns) is among the addresses that the
lookup reads. -/
theorem reads_bz (tl : HTailF2) (first : Nat) (hfull : 2 ^ tl.f9.cK = tl.f9.NC) {r i : Nat}
    (hr : r < 32) (hi : i < tl.bzColumns) : ReadsDig tl first (.cell tl.ix.BZ r i) := by
  have hb : tl.bzColumns = 2 ^ tl.f9.kT * 2 ^ tl.f9.cK := by
    unfold HTailF2.bzColumns
    rw [pow_add]
  have hpos : 0 < tl.bzColumns := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  have hc0 : 0 < 2 ^ tl.f9.cK := by positivity
  generalize hN : i + tl.bzColumns * r = N
  have hlt : N < tl.bzColumns * 32 := by
    rw [← hN]
    calc i + tl.bzColumns * r < tl.bzColumns + tl.bzColumns * r := Nat.add_lt_add_right hi _
      _ = tl.bzColumns * (r + 1) := by ring
      _ ≤ tl.bzColumns * 32 := Nat.mul_le_mul_left _ hr
  have hY : N / 32 < 2 ^ tl.f9.kT * 2 ^ tl.f9.cK := by
    rw [← hb]
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hlt)
  have ht : N / 32 / 2 ^ tl.f9.cK < 2 ^ tl.f9.kT :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hY)
  have hc : N / 32 % 2 ^ tl.f9.cK < tl.f9.NC := by
    rw [← hfull]
    exact Nat.mod_lt _ hc0
  have hj : N % 32 < FoNums.planes := Nat.mod_lt _ (by decide)
  have h := ReadsDig.bit (tl := tl) (first := first) _ _ _ ht hc hj
  have e1 :
      (N / 32 / 2 ^ tl.f9.cK * 2 ^ tl.f9.cK + N / 32 % 2 ^ tl.f9.cK) * 2 ^ 5 + N % 32 = N := by
    rw [Nat.div_add_mod']
    exact Nat.div_add_mod' N 32
  have e2 : N / tl.bzColumns = r := by
    rw [← hN, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hi, Nat.zero_add]
  have e3 : N % tl.bzColumns = i := by
    rw [← hN, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have e : addrOf (DgP.bcP tl (N / 32 / 2 ^ tl.f9.cK) (N / 32 % 2 ^ tl.f9.cK) (N % 32)) =
      .cell tl.ix.BZ r i := by
    show Addr.cell tl.ix.BZ
      (((N / 32 / 2 ^ tl.f9.cK * 2 ^ tl.f9.cK + N / 32 % 2 ^ tl.f9.cK) * 2 ^ 5 + N % 32) /
        tl.bzColumns)
      (((N / 32 / 2 ^ tl.f9.cK * 2 ^ tl.f9.cK + N / 32 % 2 ^ tl.f9.cK) * 2 ^ 5 + N % 32) %
        tl.bzColumns) = _
    rw [e1, e2, e3]
  rw [e] at h
  exact h

/-- Every cell of a piece of the digits' array ZZ is among the addresses that the lookup reads. -/
theorem reads_zz (tl : HTailF2) (first : Nat) (hT : DgP.TailOK tl) {q : Nat} (hq : q < 2)
    {p : OnBytes.Model.Piece} (hp : p ∈ DgP.piecesL tl q) (hc0 : p.c0 = q * tl.mz) {r i : Nat}
    (hr : r < p.Rp) (hi : i < p.Cp) : ReadsDig tl first (.cell tl.ix.ZZ (p.r0 + r) (p.c0 + i)) := by
  obtain ⟨h1, -, -, -, h5⟩ := hT.pc q (by rw [hT.nc]; exact hq) p hp
  have hi' : i < tl.mz := h1 ▸ hi
  have hr' : p.r0 + r < tl.tau := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hr _) h5
  rw [hc0]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq0 | rfl
  · obtain rfl : q = 0 := Nat.lt_one_iff.1 hq0
    rw [Nat.zero_mul, Nat.zero_add]
    exact ReadsDig.low (⟨i, hi'⟩, ⟨p.r0 + r, hr'⟩)
  · rw [Nat.one_mul]
    exact ReadsDig.high (⟨i, hi'⟩, ⟨p.r0 + r, hr'⟩)

/-- **At every cell that the payer's law of the rows (DigRows) reads, the caller's msg₀ is what the
committed messages hold at that cell's seat**: the counts' array. -/
theorem dig_cell_bz {set : Params.Setting} {x : Place} {tl : HTailF2} {D : Sent}
    {rad : OracleShape → Nat} {pp : Nat} (H : DigOK set x tl D rad pp)
    (hfull : 2 ^ tl.f9.cK = tl.f9.NC) (m : (digSg x D rad).Msg) {r i : Nat} (hr : r < 32)
    (hi : i < tl.bzColumns) :
    digVal x D rad m (.cell tl.ix.BZ r i) =
      some (digMsg x D rad m (enOf x.arrays (tl.ix.BZ, r, i))) :=
  msgAt_val _ _ _ H.resolves (reads_bz tl x.F.next hfull hr hi) m

/-- The same at a piece of the digits' array. -/
theorem dig_cell_zz {set : Params.Setting} {x : Place} {tl : HTailF2} {D : Sent}
    {rad : OracleShape → Nat} {pp : Nat} (H : DigOK set x tl D rad pp)
    (m : (digSg x D rad).Msg) {q : Nat} (hq : q < 2) {p : OnBytes.Model.Piece}
    (hp : p ∈ DgP.piecesL tl q) (hc0 : p.c0 = q * tl.mz) {r i : Nat} (hr : r < p.Rp)
    (hi : i < p.Cp) :
    digVal x D rad m (.cell tl.ix.ZZ (p.r0 + r) (p.c0 + i)) =
      some (digMsg x D rad m (enOf x.arrays (tl.ix.ZZ, p.r0 + r, p.c0 + i))) :=
  msgAt_val _ _ _ H.resolves (reads_zz tl x.F.next (DgP.shape2_parts H.tail).2.1 hq hp hc0 hr hi) m

end VerifiableInference.Desc.First.Look

noncomputable section

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First VerifiableInference.Desc.First.Look

/-- **Two records of a smallness test have one layout of the digits' lookup.** -/
structure SameLay (tl tlS : HTailF2) : Prop where
  f9 : tlS.f9 = tl.f9
  pl : ∀ (J₀ : Type) (en : Ent3 → J₀), plV tlS en = plV tl en
  lay : ∀ (J₀ : Type) (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ),
    digL5 Cb.Gl.E tlS en mk jLK Unit = digL5 Cb.Gl.E tl en mk jLK Unit

theorem sameLay_refl (tl : HTailF2) : SameLay tl tl :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- **The layout reads five fields of the record**: the lookup's shape, the arrays' numbers, the
columns of digits a plane, and the two calls' records. -/
theorem sameLay_of_fields {tl tlS : HTailF2} (h1 : tlS.f9 = tl.f9) (h2 : tlS.ix = tl.ix)
    (h3 : tlS.mz = tl.mz) (h4 : tlS.z1 = tl.z1) (h5 : tlS.z2 = tl.z2) : SameLay tl tlS := by
  cases tl
  cases tlS
  dsimp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  exact ⟨rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- What the digits' seat lays behind the hearing keeps the layout. -/
theorem sameLay_put (tl : HTailF2) (n a b : ℕ) (g : Heard) :
    SameLay tl { tl with foldDrawn := n, slotA := a, slotB := b, heard := some g } :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- **What the digits' seat lays, read back.** -/
theorem put_tl {Cl : Type} (claim : Aff → Cl) (s : Desc.First.S) (g : Heard) (Gk : Fork)
    (tl : HTailF2) (F : Fork) (h1 : s.tl? = some tl) (h2 : s.fork? = some F) :
    ((Desc.K3.seatDigits claim).put s g Gk).tl? =
      some { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := Gk.next, heard := some g } := by
  simp only [Desc.K3.seatDigits, h1, h2]
  cases hh : s.here with
  | between => simp [S.tl?, hh] at h1
  | fin _ => simp [S.tl?, hh] at h1
  | mem _ => simp [S.tl?, hh] at h1
  | lay a => simp [S.tl?, S.putTl, S.putFork, hh]
  | att a => simp [S.tl?, S.putTl, S.putFork, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.tl?, hh, ho] at h1
    | true => simp [S.tl?, S.putTl, S.putFork, hh, ho]

/-- **So the seat's own step keeps the lookup's layout.** -/
theorem put_sameLay {Cl : Type} (claim : Aff → Cl) (s : Desc.First.S) (g : Heard) (Gk : Fork)
    (tl : HTailF2) (F : Fork) (h1 : s.tl? = some tl) (h2 : s.fork? = some F) :
    ∃ tl', ((Desc.K3.seatDigits claim).put s g Gk).tl? = some tl' ∧ SameLay tl tl' :=
  ⟨_, put_tl claim s g Gk tl F h1 h2, sameLay_put tl _ _ _ g⟩

section
variable {K : Type} [Field K] (ρ : Reading K)

/-- **DigRows reads its cells at the counts' array and at the pieces alone.** -/
theorem digRows_congr (tl : HTailF2) (g : Heard) (entry : ℕ → ℕ → ℕ → K) {cell cell' : Ent3 → K}
    (hb : ∀ r < 32, ∀ i < tl.bzColumns, cell (tl.ix.BZ, r, i) = cell' (tl.ix.BZ, r, i))
    (hz : ∀ q < 2, ∀ p ∈ piecesL tl q, ∀ r < p.Rp, ∀ i < p.Cp,
      cell (tl.ix.ZZ, p.r0 + r, p.c0 + i) = cell' (tl.ix.ZZ, p.r0 + r, p.c0 + i))
    (h : DigRows ρ tl g entry cell) : DigRows ρ tl g entry cell' := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun q hq p hp i hi => ?_⟩
  · refine (h.bz0 i hi).trans (Finset.sum_congr rfl fun r hr => ?_)
    have e := hb r (Finset.mem_range.1 hr) i hi
    simp only [e]
  · refine (h.bz1 i hi).trans (Finset.sum_congr rfl fun r hr => ?_)
    have e := hb r (Finset.mem_range.1 hr) i hi
    simp only [e]
  · refine (h.bz2 i hi).trans (Finset.sum_congr rfl fun r hr => ?_)
    have e := hb r (Finset.mem_range.1 hr) i hi
    simp only [e]
  · refine (h.piece q hq p hp i hi).trans (Finset.sum_congr rfl fun r hr => ?_)
    have e := hz q hq p hp r (Finset.mem_range.1 hr) i hi
    simp only [e]

end

/-- **Two records of a smallness test agree in the six fields that the digits' lookup and the
library's test on the record (TailOK) read.** -/
structure SameDig (tl tlS : HTailF2) : Prop where
  f9 : tlS.f9 = tl.f9
  ix : tlS.ix = tl.ix
  mz : tlS.mz = tl.mz
  tau : tlS.tau = tl.tau
  z1 : tlS.z1 = tl.z1
  z2 : tlS.z2 = tl.z2

theorem SameDig.lay {tl tlS : HTailF2} (h : SameDig tl tlS) : SameLay tl tlS :=
  sameLay_of_fields h.f9 h.ix h.mz h.z1 h.z2

theorem SameDig.zOf {tl tlS : HTailF2} (h : SameDig tl tlS) (q : ℕ) : tlS.zOf q = tl.zOf q := by
  unfold HTailF2.zOf
  rw [h.z1, h.z2]

theorem SameDig.pieces {tl tlS : HTailF2} (h : SameDig tl tlS) (q : ℕ) :
    piecesL tlS q = piecesL tl q := by
  unfold piecesL
  rw [h.zOf]

theorem SameDig.bz {tl tlS : HTailF2} (h : SameDig tl tlS) : tlS.bzColumns = tl.bzColumns := by
  unfold HTailF2.bzColumns
  rw [h.f9]

/-- **The library's test on the record passes from the plan's record to the carried one.** -/
theorem SameDig.tailOK {tl tlS : HTailF2} (h : SameDig tl tlS) (k : TailOK tl) : TailOK tlS := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases tl
  cases tlS
  dsimp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4 h5 h6
  exact ⟨k.port, k.nc, k.pc, k.rows, k.one, k.cnt⟩

/-- What the digits' seat lays behind the hearing keeps the six. -/
theorem sameDig_put (tl : HTailF2) (n a b : ℕ) (g : Heard) :
    SameDig tl { tl with foldDrawn := n, slotA := a, slotB := b, heard := some g } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

section
variable {K : Type} [Field K] (ρ : Reading K)

/-- **DigRows at the carried record is DigRows at the plan's.** -/
theorem digRows_rec {tl tlS : HTailF2} (h : SameDig tl tlS) (g : Heard) (entry : ℕ → ℕ → ℕ → K)
    (cell : Ent3 → K) : DigRows ρ tlS g entry cell ↔ DigRows ρ tl g entry cell := by
  constructor
  · intro k
    obtain ⟨k0, k1, k2, k3⟩ := k
    rw [h.ix, h.bz] at k0 k1 k2
    refine ⟨k0, k1, k2, fun q hq p hp i hi => ?_⟩
    have e := k3 q hq p (by rw [h.pieces]; exact hp) i hi
    rw [h.zOf, h.ix] at e
    exact e
  · intro k
    obtain ⟨k0, k1, k2, k3⟩ := k
    rw [← h.ix, ← h.bz] at k0 k1 k2
    refine ⟨k0, k1, k2, fun q hq p hp i hi => ?_⟩
    have e := k3 q hq p (by rw [← h.pieces]; exact hp) i hi
    rw [← h.zOf, ← h.ix] at e
    exact e

end

/-- **DigRows at the closed caller, from DigRows at any cells that are, where they are read, what
the messages hold at the cell's seat.** -/
theorem digRows_at_caller {set : Params.Setting} {x : Desc.First.Look.Place} {tl tlS : HTailF2}
    {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {pp : ℕ} (H : DigOK set x tl D rad pp)
    (hfull : 2 ^ tl.f9.cK = tl.f9.NC) (h5 : SameDig tl tlS) (g : Heard)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hc0 : ∀ q < 2, ∀ p ∈ piecesL tlS q, p.c0 = q * tlS.mz)
    (m : (digSg x D rad).Msg) (cell : Ent3 → Cb.Gl.E)
    (hb : ∀ r < 32, ∀ i < tl.bzColumns,
      digVal x D rad m (.cell tl.ix.BZ r i) = some (cell (tl.ix.BZ, r, i)))
    (hz : ∀ q < 2, ∀ p ∈ piecesL tl q, ∀ r < p.Rp, ∀ i < p.Cp,
      digVal x D rad m (.cell tl.ix.ZZ (p.r0 + r) (p.c0 + i)) =
        some (cell (tl.ix.ZZ, p.r0 + r, p.c0 + i)))
    (h : DigRows Reading.gl tlS g entry cell) :
    DigRows Reading.gl tlS g entry fun e => digMsg x D rad m (enOf x.arrays e) := by
  refine (digRows_rec Reading.gl h5 g entry _).2 ?_
  refine digRows_congr Reading.gl tl g entry (fun r hr i hi => ?_)
    (fun q hq p hp r hr i hi => ?_) ((digRows_rec Reading.gl h5 g entry cell).1 h)
  · exact Option.some.inj ((hb r hr i hi).symm.trans (dig_cell_bz H hfull m hr hi))
  · have hc : p.c0 = q * tl.mz := by
      rw [← h5.mz]
      exact hc0 q hq p (by rw [h5.pieces]; exact hp)
    exact Option.some.inj ((hz q hq p hp r hr i hi).symm.trans (dig_cell_zz H m hq hp hc hr hi))

section
variable {K : Type} [Field K] (ρ : Reading K)

/-- **DigRows is met by some entries, at any cells.** -/
theorem digRows_some (tl tlX : HTailF2) (hX : SameZ tl tlX) (g : Heard)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (Fc : Fork) (T : CoefOK tlX Fc)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R)
    (cell : Ent3 → K) : ∃ entry, DigRows ρ tl g entry cell := by
  obtain ⟨W, -, hW⟩ := rowsLaw_some ρ (coefAll tlX g Fc) (fun _ => 0)
    (fun t r i => cell (t, r, i))
  exact ⟨W.entry, digRows_of_law ρ tl tlX hX g hP Fc T hRw W cell hW⟩

/-- **DigRows pins the counts' array's three virtual rows.** -/
theorem digRows_pins {tl : HTailF2} {g : Heard} {e₁ e₂ : ℕ → ℕ → ℕ → K} {cell : Ent3 → K}
    (h₁ : DigRows ρ tl g e₁ cell) (h₂ : DigRows ρ tl g e₂ cell) (i : ℕ) (hi : i < tl.bzColumns) :
    e₁ tl.ix.BZ 0 i = e₂ tl.ix.BZ 0 i ∧ e₁ tl.ix.BZ 1 i = e₂ tl.ix.BZ 1 i ∧
      e₁ tl.ix.BZ 2 i = e₂ tl.ix.BZ 2 i :=
  ⟨virtRow_pins h₁.bz0 h₂.bz0 i hi, virtRow_pins h₁.bz1 h₂.bz1 i hi,
    virtRow_pins h₁.bz2 h₂.bz2 i hi⟩

/-- **DigRows is not met by all entries.** -/
theorem digRows_not_all (tl : HTailF2) (g : Heard) (cell : Ent3 → K) :
    ∃ entry, ¬ DigRows ρ tl g entry cell := by
  refine ⟨fun _ _ _ => (∑ r ∈ range 32, (1 : K) * cell (tl.ix.BZ, r, 0)) + 1, fun h => ?_⟩
  have hpos : 0 < tl.bzColumns := by
    unfold HTailF2.bzColumns
    positivity
  have e : (∑ r ∈ range 32, (1 : K) * cell (tl.ix.BZ, r, 0)) + 1 =
      ∑ r ∈ range 32, (1 : K) * cell (tl.ix.BZ, r, 0) := h.bz2 0 hpos
  exact one_ne_zero (add_left_cancel (e.trans (add_zero _).symm))

end

#print axioms VerifiableInference.Desc.First.Look.digB_rad
#print axioms VerifiableInference.Desc.First.Look.reads_bz
#print axioms VerifiableInference.Desc.First.Look.reads_zz
#print axioms VerifiableInference.Desc.First.Look.dig_cell_bz
#print axioms VerifiableInference.Desc.First.Look.dig_cell_zz
#print axioms sameLay_of_fields
#print axioms sameLay_put
#print axioms put_tl
#print axioms put_sameLay
#print axioms digRows_congr
#print axioms SameDig.lay
#print axioms SameDig.tailOK
#print axioms sameDig_put
#print axioms digRows_rec
#print axioms digRows_at_caller
#print axioms digRows_some
#print axioms digRows_pins
#print axioms digRows_not_all

end VerifiableInference.OnPublicFiles
