-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Placed.lean: that the two messages of (fold) have their tables: from the public
shape's conditions and the messages' shapes in the statement.

Main names: Seated (the statement has the codes, the two messages are two and have the shapes that
the public shape names, and u's layout is that shape's), Seated.grows (a statement that grows keeps
it), placed_of_seated (with the public shape's conditions it gives Placed), vectorRoom_le,
ceilLog2_le, recvP_inv, recvP_first, seated_behind.

What is not claimed. seated_behind shows Seated behind two receivings of oracle messages, with
statements that only grow between and behind them as premises. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.Means
import Johnson.Desc.Grows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Grows)

/-- The statement has the codes; the two messages of (fold) are two and have the shapes that the
public shape names; u's layout is that of its shape. -/
structure Seated (T : Statement) (codes : Codes) (S : LinShape) (l : Lin) : Prop where
  sameCodes : T.codes = codes
  two : l.oOmega ≠ l.oU.oracle
  omega : ∃ x, T.oracles[l.oOmega]? = some x ∧ x.shape = S.omega
  u : ∃ x, T.oracles[l.oU.oracle]? = some x ∧ x.shape = S.fold.u
  lay : l.oU.lay = vectorLay codes S.fold.u S.fold.rowsHigh

/-- A statement that grows keeps it. -/
theorem Seated.grows {T T' : Statement} {codes : Codes} {S : LinShape} {l : Lin}
    (h : Seated T codes S l) (g : Grows T T') : Seated T' codes S l := by
  obtain ⟨x, hx, sx⟩ := h.omega
  obtain ⟨y, hy, sy⟩ := h.u
  obtain ⟨x', hx', gx⟩ := g.2.2 _ x hx
  obtain ⟨y', hy', gy⟩ := g.2.2 _ y hy
  exact ⟨g.1.trans h.sameCodes, h.two, ⟨x', hx', gx.1.trans sx⟩, ⟨y', hy', gy.1.trans sy⟩, h.lay⟩

/-- A number that is at most 2 ^ k is indexed by k bits. -/
theorem ceilLog2_le (n k : Nat) (h : n ≤ 2 ^ k) : ceilLog2 n ≤ k := by
  unfold ceilLog2
  split_ifs with h1
  · exact Nat.zero_le _
  · have : (n - 1).log2 < k := (Nat.log2_lt (by omega)).2 (by omega)
    omega

/-- A fold whose step never goes up ends at most where it began. -/
theorem foldl_le_init {α : Type} (f : Nat → α → Nat) (hf : ∀ m a, f m a ≤ m) (l : List α)
    (m : Nat) : l.foldl f m ≤ m := by
  induction l generalizing m with
  | nil => exact Nat.le_refl _
  | cons a l ih => exact Nat.le_trans (ih _) (hf m a)

/-- The room for a vector in a message is within the message's main table. -/
theorem vectorRoom_le (codes : Codes) (s : OracleShape) (rowsHigh : Bool) :
    vectorRoom codes s rowsHigh ≤ 2 ^ (vectorLay codes s rowsHigh).bits := by
  have hroom : s.mainRows * 2 ^ (vectorLay codes s rowsHigh).placeBits ≤
      2 ^ (vectorLay codes s rowsHigh).bits := by
    rw [VectorLay.bits, Nat.pow_add]
    exact Nat.mul_le_mul_right _ (le_two_pow_ceilLog2 _)
  unfold vectorRoom
  dsimp only
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact hroom
  · split
    · exact Nat.zero_le _
    · refine Nat.le_trans (foldl_le_init _ (fun m a => ?_) _ _) hroom
      split_ifs
      · exact Nat.min_le_left _ _
      · exact Nat.le_refl _

/-- A number is at most the next multiple of s. -/
theorem le_roundUp (a s : Nat) (hs : 0 < s) : a ≤ (a + s - 1) / s * s := by
  have h1 := Nat.div_add_mod (a + s - 1) s
  have h2 := Nat.mod_lt (a + s - 1) hs
  rw [Nat.mul_comm] at h1
  omega

/-- A table's number of index bits, from the message's shape. -/
theorem tableBits_main (T : Statement) (o : Nat) (x : Oracle) (hx : T.oracles[o]? = some x)
    (h0 : x.shape.mainRows ≠ 0) (rowsHigh : Bool) :
    T.has o .main = true ∧ T.tableBits o .main = (vectorLay T.codes x.shape rowsHigh).bits := by
  constructor
  · simp [Statement.has, hx, OracleShape.rows]; omega
  · simp [Statement.tableBits, Statement.rowBits, Statement.placeBits, hx, OracleShape.rows, h0,
      vectorLay, VectorLay.bits]

/-- **The two messages of (fold) have their tables.** -/
theorem placed_of_seated {T : Statement} {codes : Codes} {S : LinShape} {l : Lin}
    (h : Seated T codes S l) (hok : linOk codes S = true) :
    Placed T S l (linLayOmega codes S) := by
  obtain ⟨x, hx, sx⟩ := h.omega
  obtain ⟨y, hy, sy⟩ := h.u
  simp only [linOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hS : S.ok = true := by tauto
  have hF : foldeqOk codes S.fold = true := by tauto
  have h5 : S.matrixRows ≤ vectorRoom codes S.omega S.omegaRowsHigh := by tauto
  simp only [LinShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hS
  have a2 : 1 ≤ S.matrixRows := by tauto
  have a6 : S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain := by tauto
  have a7 : LinShape.vectorMessageOk S.omega = true := by tauto
  simp only [LinShape.vectorMessageOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at a7
  have b1 : S.omega.mainRows ≠ 0 := by tauto
  simp only [foldeqOk, FoldeqShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hF
  have c1 : 0 < S.fold.u.mainRows := by tauto
  have c2 : S.fold.entries ≤ vectorRoom codes S.fold.u S.fold.rowsHigh := by tauto
  have tO := tableBits_main T _ x hx (by rw [sx]; exact b1) S.omegaRowsHigh
  have tU := tableBits_main T _ y hy (by rw [sy]; omega) S.fold.rowsHigh
  rw [sx, h.sameCodes] at tO
  rw [sy, h.sameCodes] at tU
  have hU : S.matrixRows * 2 ^ S.kLo ≤ 2 ^ l.oU.lay.bits := by
    rw [h.lay]
    refine Nat.le_trans ?_ (vectorRoom_le codes S.fold.u S.fold.rowsHigh)
    refine Nat.le_trans ?_ c2
    have e1 : S.fold.index.plain ≤ S.fold.index.code.ell := Nat.sub_le _ _
    have e2 : S.fold.index.code.ell ≤ S.fold.tailFirst := by
      exact le_roundUp _ _ (Nat.two_pow_pos _)
    unfold FoldeqShape.entries
    omega
  refine ⟨h.two, tO.1, tU.1, tO.2, by rw [tU.2, h.lay], ?_, ?_⟩
  · exact ceilLog2_le _ _ (Nat.le_trans h5 (vectorRoom_le _ _ _))
  · have k1 : 2 ^ S.kLo ≤ 2 ^ l.oU.lay.bits :=
      Nat.le_trans (Nat.le_mul_of_pos_left _ a2) hU
    have k2 : S.kLo ≤ l.oU.lay.bits := (Nat.pow_le_pow_iff_right (by decide)).1 k1
    have k3 : S.matrixRows ≤ 2 ^ (l.oU.lay.bits - S.kLo) := by
      refine Nat.le_of_mul_le_mul_right ?_ (Nat.two_pow_pos S.kLo)
      rw [← Nat.pow_add, Nat.sub_add_cancel k2]
      exact hU
    have k4 := ceilLog2_le _ _ k3
    unfold LinShape.kRow
    omega

/-- What the receiving of a prover's oracle messages does to the statement, and their numbers. -/
theorem recvP_inv (ft : Nat) (d d1 : St) (sent : Array OracleNotice) (ids : Array Nat)
    (h : VerifiableInference.Desc.Ground.recvP ft d sent = some (ids, d1)) :
    d1.st = stSent d.st sent ∧ ids = (Array.range sent.size).map (· + d.st.oracles.size) := by
  unfold VerifiableInference.Desc.Ground.recvP at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨lay, _, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · cases h

/-- The first of the messages received: its number, and its shape in the statement. -/
theorem recvP_first (ft : Nat) (d d1 : St) (sent : Array OracleNotice) (ids : Array Nat)
    (h : VerifiableInference.Desc.Ground.recvP ft d sent = some (ids, d1)) (n : OracleNotice)
    (hn : sent[0]? = some n) (o : Nat) (ho : ids[0]? = some o) :
    o = d.st.oracles.size ∧ ∃ x, d1.st.oracles[o]? = some x ∧ x.shape = n.shape := by
  obtain ⟨h1, h2⟩ := recvP_inv ft d d1 sent ids h
  have hs : 0 < sent.size := (Array.getElem?_eq_some_iff.1 hn).1
  have e : o = d.st.oracles.size := by
    rw [h2] at ho
    simp [hs] at ho
    omega
  refine ⟨e, { shape := n.shape }, ?_, rfl⟩
  have := stSent_new d.st sent 0
  rw [Nat.add_zero, hn] at this
  rw [h1, e, this]
  rfl

/-- **Behind the two sendings the two messages are seated**: said of the two receivings of oracle
messages and of statements that only grow between and behind them. -/
theorem seated_behind (codes : Codes) (S : LinShape) (l : Lin) (T : Statement)
    (dU dU1 dO dO1 : St) (ftU ftO : Nat) (sentU sentO : Array OracleNotice) (idsU idsO : Array Nat)
    (nU nO : OracleNotice) (hc : dU.st.codes = codes)
    (hU : VerifiableInference.Desc.Ground.recvP ftU dU sentU = some (idsU, dU1))
    (sU : sentU[0]? = some nU) (shU : nU.shape = S.fold.u) (lU : idsU[0]? = some l.oU.oracle)
    (g1 : Grows dU1.st dO.st)
    (hO : VerifiableInference.Desc.Ground.recvP ftO dO sentO = some (idsO, dO1))
    (sO : sentO[0]? = some nO) (shO : nO.shape = S.omega) (lO : idsO[0]? = some l.oOmega)
    (g2 : Grows dO1.st T) (hl : l.oU.lay = vectorLay codes S.fold.u S.fold.rowsHigh) :
    Seated T codes S l := by
  obtain ⟨eU, x, hx, sx⟩ := recvP_first ftU dU dU1 sentU idsU hU nU sU _ lU
  obtain ⟨eO, y, hy, sy⟩ := recvP_first ftO dO dO1 sentO idsO hO nO sO _ lO
  have gU : Grows dU.st dU1.st := by
    rw [(recvP_inv ftU dU dU1 sentU idsU hU).1]
    exact VerifiableInference.Desc.grows_stSent _ _
  have gO : Grows dO.st dO1.st := by
    rw [(recvP_inv ftO dO dO1 sentO idsO hO).1]
    exact VerifiableInference.Desc.grows_stSent _ _
  obtain ⟨x1, hx1, gx1⟩ := g1.2.2 _ x hx
  obtain ⟨x2, hx2, gx2⟩ := (gO.trans g2).2.2 _ x1 hx1
  obtain ⟨y2, hy2, gy2⟩ := g2.2.2 _ y hy
  have hlt : l.oU.oracle < dO.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx1).1
  refine ⟨?_, by omega, ⟨y2, hy2, (gy2.1.trans sy).trans shO⟩,
    ⟨x2, hx2, ((gx2.1.trans gx1.1).trans sx).trans shU⟩, hl⟩
  exact (((gU.trans g1).trans gO).trans g2).1.trans hc

end Desc.K14.Law
