--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/SendHeld.lean: the tables that an honest prover lays at the linear claim's
two shared sendings (Johnson/Desc/K14/Honest/SendMoves.lean) hold, at the indices that the
verifier's constraints read, the folded row, omega_col and the mask's entry.

  padCoin_none, vecMain_at   off the pad, the main rows hold the vector's entry
  vecMain_on_pad  at a place of the pad in the main table they hold a random value of the pad, not
                  the vector's filler 0
  vecMain_pad_at, ownPadPlaces_main, word_pad   so the table of a message without a mask row holds
                  the random value number i of its pad at the place of the pad of OOD answer number
                  i, at the end of its last main row. These are the indices at which the statement
                  notes the pad; that the message's sample rows have their pads there is pad_places
                  (Johnson/Desc/K1/Law/PadTie.lean), where every code's length is a power of two
  word_vec        the first n entries of the vector stand at their indices of the main table, for n
                  within the room that the message's shape has for a vector
  chainWords_u, chainWords_o   the tables of the two sendings' messages, by number
  u_chain, isFold_chain   o_u's table holds uHon at the places of a row: so it holds the rows' fold
                  (IsFold: Johnson/Desc/K14/Honest/Values.lean)
  omega_chain, col_chain   o_omega's table holds omegaHon on the matrix's rows: so it holds what
                  o_u's table gives at psi_lo, row by row of the matrix
  kappa_chain     o_sp's mask table holds kappaOf at an index in a real row
  mu_chain        so muSent is omega_col, as o_omega's table holds it, at z_fd, plus that entry
  isFold_weights  the fold reads the weights of the table's rows alone
  u_held, isFold_of_eq, isFold_held   the like for o_u between the two sendings, when the messages
                  of "send o_omega" are not yet laid

The room: Johnson/Desc/Own/RoomPlaces.lean (room_rows, room_off_pad, entryAt_index). The tables by
index: Johnson/Prover/Send/Held.lean.

What is assumed, as premises. The public test linFits on the codes and the shape
(Johnson/Desc/Own/Lin.lean), which "LIN point" asks. The two places announce the shapes S.fold.u,
then S.omega and S.sharedSplit. The verifier's state notes for o_u, o_omega and o_sp the numbers and
layouts that the sendings give them. The messages of "send o_omega" get numbers behind those of
"send o_u".
What is not claimed. That an index named here is a place below its code's message length: of a
vector's entries room_places (Johnson/Desc/Own/RoomPlaces.lean) says it where that length is a power
of two; no theorem here asks or calls it (see the head of Johnson/Desc/K14/Honest/SendMoves.lean).
Nothing on a decision of the verifier, on the OOD answers or on the written columns. Nothing on how
the random values are distributed. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K14.Honest.SendMoves
import Johnson.Desc.K14.Honest.Values
import Johnson.Prover.Send.Held
import Johnson.Desc.Own.RoomPlaces
import Johnson.Desc.Own.RoomAtU
import Johnson.Desc.Own.LinMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words)
open Johnson.Prover.Send (Rows held shapeAt held_old held_new word_main)
open Desc.K14.Law

/-! ## A message that carries a vector -/

/-- An index that is no place of the pad in the main table. -/
theorem padCoin_none (places : List PadPlace) (pad : ℕ → Cb.Gl.E) (t : ℕ)
    (h : ∀ p ∈ places, p.part = .main → t ≠ p.index) : padCoin places pad t = none := by
  have e : places.find? (fun p => p.part == .main && p.index == t) = none :=
    List.find?_eq_none.2 fun p hp hc => by
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact h p hp hc.1 hc.2.symm
  unfold padCoin
  rw [e, Option.map_none]

/-- Off the pad, the main rows hold the vector's entry that the layout has at the index. -/
theorem vecMain_at (lay : VectorLay) (places : List PadPlace) (data pad : ℕ → Cb.Gl.E) (i : ℕ)
    (h : ∀ p ∈ places, p.part = .main → i ≠ p.index) :
    vecMain lay places data pad (i % 2 ^ lay.rowBits) (i / 2 ^ lay.rowBits) =
      data (lay.entryAt i) := by
  unfold vecMain
  rw [Nat.mod_add_div', padCoin_none places pad i h, Option.getD_none]

/-- **At a place of the pad in the main table the main rows hold a random value of the pad.** -/
theorem vecMain_on_pad (lay : VectorLay) (places : List PadPlace) (data pad : ℕ → Cb.Gl.E)
    (p : PadPlace) (hp : p ∈ places) (hm : p.part = .main) :
    ∃ q ∈ places, q.part = .main ∧ q.index = p.index ∧
      vecMain lay places data pad (p.index % 2 ^ lay.rowBits) (p.index / 2 ^ lay.rowBits) =
        pad q.answer := by
  cases e : places.find? (fun q => q.part == .main && q.index == p.index) with
  | none =>
    have h := List.find?_eq_none.1 e p hp
    simp only [hm, beq_self_eq_true, Bool.and_self, not_true_eq_false] at h
  | some q =>
    have hq := List.find?_some e
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    refine ⟨q, List.mem_of_find?_eq_some e, hq.1, hq.2, ?_⟩
    unfold vecMain padCoin
    rw [Nat.mod_add_div', e, Option.map_some, Option.getD_some]

/-- The same at a row and a place of the row, given apart. -/
theorem vecMain_pad_at (lay : VectorLay) (places : List PadPlace) (data pad : ℕ → Cb.Gl.E)
    (r j : ℕ) (p : PadPlace) (hp : p ∈ places) (hm : p.part = .main)
    (hi : p.index = r + j * 2 ^ lay.rowBits) :
    ∃ q ∈ places, q.part = .main ∧ q.index = p.index ∧
      vecMain lay places data pad r j = pad q.answer := by
  cases e : places.find? (fun q => q.part == .main && q.index == p.index) with
  | none =>
    have h := List.find?_eq_none.1 e p hp
    simp only [hm, beq_self_eq_true, Bool.and_self, not_true_eq_false] at h
  | some q =>
    have hq := List.find?_some e
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    refine ⟨q, List.mem_of_find?_eq_some e, hq.1, hq.2, ?_⟩
    unfold vecMain padCoin
    rw [← hi, e, Option.map_some, Option.getD_some]

/-- The places of the pad of a message without a mask row whose main rows are over the extension
field: one for each OOD answer, at the end of the last main row. -/
theorem ownPadPlaces_main (codes : Codes) (s : OracleShape) (hz : s.maskRows = 0)
    (hm : 0 < s.mainRows) (hdeg : s.mainDeg = 3)
    (hlen : s.answers ≤ (codes.base.getD s.code default).ell) :
    ownPadPlaces codes s = (List.range s.answers).map fun i =>
      { part := .main
        index := (s.mainRows - 1) +
          ((codes.base.getD s.code default).ell - s.answers + i) * 2 ^ ceilLog2 s.mainRows
        answer := i, basis := thetaE 0 } := by
  by_cases h0 : s.answers = 0
  · simp [ownPadPlaces, h0]
  · have hb : (s.answers == 0) = false := by simpa using h0
    have hnot : ¬ (codes.base.getD s.code default).ell < s.answers := Nat.not_lt.2 hlen
    simp [ownPadPlaces, VerifiableInference.Desc.Own.padMade, Send.cube, hb, hz, hm, hdeg,
      List.range_succ]
    rw [if_neg (by simpa using hnot), Option.getD_some]
    generalize List.range s.answers = L
    induction L with
    | nil => rfl
    | cons a l ih =>
      rw [List.flatMap_cons, ih]
      rfl

/-- **The table of such a message holds, at the place of the pad of OOD answer number i, the random
value number i of its pad.** -/
theorem word_pad (codes : Codes) (s : OracleShape) (rowsHigh : Bool) (data : ℕ → Cb.Gl.E)
    (c : MsgCoins) (hz : s.maskRows = 0) (hm : 0 < s.mainRows) (hdeg : s.mainDeg = 3)
    (hlen : s.answers ≤ (codes.base.getD s.code default).ell) (i : ℕ) (hi : i < s.answers) :
    (vecRows codes s rowsHigh data c).word s .main ((s.mainRows - 1) +
        ((codes.base.getD s.code default).ell - s.answers + i) * 2 ^ ceilLog2 s.mainRows) =
      c.pad i := by
  have hP := ownPadPlaces_main codes s hz hm hdeg hlen
  have hrow : s.mainRows - 1 < s.mainRows := by omega
  have hw := word_main (vecRows codes s rowsHigh data c) s (s.mainRows - 1)
    ((codes.base.getD s.code default).ell - s.answers + i) hrow
  have hd : (s.mainDeg == 3) = true := by
    rw [hdeg]
    rfl
  have hmem : (⟨.main, (s.mainRows - 1) +
      ((codes.base.getD s.code default).ell - s.answers + i) * 2 ^ ceilLog2 s.mainRows, i,
      thetaE 0⟩ : PadPlace) ∈ ownPadPlaces codes s := by
    rw [hP]
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  obtain ⟨q, hq, _, hqi, hv⟩ := vecMain_pad_at (vectorLay codes s rowsHigh) (ownPadPlaces codes s)
    data c.pad (s.mainRows - 1) ((codes.base.getD s.code default).ell - s.answers + i) _ hmem rfl
    rfl
  rw [hP] at hq
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hq
  have hpos : 0 < 2 ^ ceilLog2 s.mainRows := Nat.two_pow_pos _
  have hji : j = i := by
    have e1 := Nat.add_left_cancel hqi
    have e2 := Nat.eq_of_mul_eq_mul_right hpos e1
    omega
  refine Eq.trans hw ?_
  unfold Rows.main
  rw [if_pos hd]
  refine Eq.trans hv ?_
  rw [hji]

/-- **The vector's first n entries stand at their indices of the main table**, for n within the room
that the shape has for a vector. -/
theorem word_vec (codes : Codes) (s : OracleShape) (rowsHigh : Bool) (data : ℕ → Cb.Gl.E)
    (c : MsgCoins) (hdeg : s.mainDeg = 3) (n : ℕ) (h1 : 1 ≤ n)
    (hn : n ≤ VerifiableInference.Desc.Own.roomOf codes s rowsHigh) (j : ℕ) (hj : j < n) :
    (vecRows codes s rowsHigh data c).word s .main ((vectorLay codes s rowsHigh).index j) =
      data j := by
  have hrow := VerifiableInference.Desc.Own.room_rows codes s rowsHigh n h1 hn j hj
  have htab := VerifiableInference.Desc.Own.room_in_table codes s rowsHigh n h1 hn j hj
  have hoff : ∀ p ∈ ownPadPlaces codes s, p.part = .main →
      (vectorLay codes s rowsHigh).index j ≠ p.index := fun p hp hm =>
    VerifiableInference.Desc.Own.room_off_pad codes s rowsHigh n h1 hn j hj p hp hm
  have hw := word_main (vecRows codes s rowsHigh data c) s
    ((vectorLay codes s rowsHigh).index j % 2 ^ VerifiableInference.Desc.K1.clog s.mainRows)
    ((vectorLay codes s rowsHigh).index j / 2 ^ VerifiableInference.Desc.K1.clog s.mainRows) hrow
  rw [Nat.mod_add_div'] at hw
  have hd : (s.mainDeg == 3) = true := by
    rw [hdeg]
    rfl
  have e := vecMain_at (vectorLay codes s rowsHigh) (ownPadPlaces codes s) data c.pad
    ((vectorLay codes s rowsHigh).index j) hoff
  rw [VerifiableInference.Desc.Own.entryAt_index _ j htab] at e
  rw [hw]
  unfold Rows.main
  rw [if_pos hd]
  exact e

/-! ## The two sendings' tables, by number -/

/-- The tables of the messages of "send o_u". -/
theorem chainWords_u (w₀ : Words Cb.Gl.E) (first next : ℕ)
    (PU PO : VerifiableInference.Desc.K1.Par)
    (VU VO : ℕ → Rows) (hle : first + PU.sent.size ≤ next) (k : ℕ) (hk : k < PU.sent.size)
    (part : Part) (i : ℕ) :
    chainWords w₀ first next PU PO VU VO (first + k) part i =
      (VU k).word (shapeAt PU k) part i := by
  have h : ¬ (next ≤ first + k ∧ first + k < next + PO.sent.size) := fun e => by omega
  unfold chainWords
  rw [held_old _ _ PO VO _ part i h, held_new w₀ first PU VU k hk]

/-- The tables of the messages of "send o_omega". -/
theorem chainWords_o (w₀ : Words Cb.Gl.E) (first next : ℕ)
    (PU PO : VerifiableInference.Desc.K1.Par)
    (VU VO : ℕ → Rows) (k : ℕ) (hk : k < PO.sent.size) (part : Part) (i : ℕ) :
    chainWords w₀ first next PU PO VU VO (next + k) part i =
      (VO k).word (shapeAt PO k) part i := by
  unfold chainWords
  rw [held_new _ _ PO VO k hk]

/-! ## What the verifier's constraints read -/

/-- o_u's table holds the folded row at the places that a row takes. -/
theorem u_chain (w₀ : Words Cb.Gl.E) (first next : ℕ)
    (PU PO : VerifiableInference.Desc.K1.Par)
    (VO : ℕ → Rows) (codes : Codes) (S : LinShape) (w : ℕ → Cb.Gl.E) (Rw : ℕ → ℕ → Cb.Gl.E)
    (cU cMask : MsgCoins) (l : Lin)
    (hfit : VerifiableInference.Desc.Own.linFits codes S = true)
    (hle : first + PU.sent.size ≤ next) (hsz : 0 < PU.sent.size) (hsh : shapeAt PU 0 = S.fold.u)
    (hl : l.oU = ⟨first, vectorLay codes S.fold.u S.fold.rowsHigh⟩) (k : ℕ)
    (hk : k < S.fold.entries) :
    uOf l (chainWords w₀ first next PU PO (sendsU codes S w Rw cU cMask) VO) k =
      uHon S.fold w Rw k := by
  obtain ⟨_, hf, _⟩ := (VerifiableInference.Desc.Own.linFits_iff codes S).1 hfit
  obtain ⟨hs, _, hr⟩ := hf
  have e := chainWords_u w₀ first next PU PO (sendsU codes S w Rw cU cMask) VO hle 0 hsz .main
    ((vectorLay codes S.fold.u S.fold.rowsHigh).index k)
  rw [Nat.add_zero, hsh] at e
  unfold uOf
  rw [hl]
  refine Eq.trans e ?_
  exact word_vec codes S.fold.u S.fold.rowsHigh (uHon S.fold w Rw) cU hs.2.2.2.1 S.fold.entries
    (VerifiableInference.Desc.Own.entries_pos S.fold hs.1.1.2.2.1) hr k hk

/-- **So o_u's table holds the rows' fold.** -/
theorem isFold_chain (w₀ : Words Cb.Gl.E) (first next : ℕ)
    (PU PO : VerifiableInference.Desc.K1.Par)
    (VO : ℕ → Rows) (codes : Codes) (S : LinShape) (w : ℕ → Cb.Gl.E) (Rw : ℕ → ℕ → Cb.Gl.E)
    (cU cMask : MsgCoins) (l : Lin)
    (hfit : VerifiableInference.Desc.Own.linFits codes S = true)
    (hle : first + PU.sent.size ≤ next) (hsz : 0 < PU.sent.size) (hsh : shapeAt PU 0 = S.fold.u)
    (hl : l.oU = ⟨first, vectorLay codes S.fold.u S.fold.rowsHigh⟩) :
    IsFold S.fold w Rw
      (uOf l (chainWords w₀ first next PU PO (sendsU codes S w Rw cU cMask) VO)) := by
  have h0 := ell_le_tailFirst S.fold
  have key := u_chain w₀ first next PU PO VO codes S w Rw cU cMask l hfit hle hsz hsh hl
  refine ⟨fun k hk => ?_, fun j hj => ?_⟩
  · have hk' : k < S.fold.entries := by
      unfold FoldeqShape.entries
      omega
    rw [key k hk', (uHon_isFold S.fold w Rw).onMsg k hk]
  · have hk' : S.fold.tailFirst + j < S.fold.entries := by
      unfold FoldeqShape.entries
      omega
    rw [key _ hk', (uHon_isFold S.fold w Rw).onTail j hj]

/-- o_omega's table holds omega_col on the matrix's rows. -/
theorem omega_chain (w₀ : Words Cb.Gl.E) (first next : ℕ)
    (PU PO : VerifiableInference.Desc.K1.Par)
    (VU : ℕ → Rows) (codes : Codes) (S : LinShape) (psiLo : List Cb.Gl.E) (u : ℕ → Cb.Gl.E)
    (cOmega cSp : MsgCoins) (l : Lin)
    (hfit : VerifiableInference.Desc.Own.linFits codes S = true) (hsz : 0 < PO.sent.size)
    (hsh : shapeAt PO 0 = S.omega) (hl : l.oOmega = next) (j : ℕ)
    (hj : j < S.matrixRows) :
    omegaOf l (linLayOmega codes S)
        (chainWords w₀ first next PU PO VU (sendsOmega codes S psiLo u cOmega cSp)) j =
      omegaHon S psiLo u j := by
  obtain ⟨hs, _, _, _, _, _, hr, _⟩ := (VerifiableInference.Desc.Own.linFits_iff codes S).1 hfit
  have e := chainWords_o w₀ first next PU PO VU (sendsOmega codes S psiLo u cOmega cSp) 0 hsz .main
    ((linLayOmega codes S).index j)
  rw [Nat.add_zero, hsh] at e
  unfold omegaOf
  rw [hl]
  refine Eq.trans e ?_
  exact word_vec codes S.omega S.omegaRowsHigh (omegaHon S psiLo u) cOmega hs.2.2.2.2.2.2.1.2.2.1
    S.matrixRows hs.2.1 hr j hj

/-- **So o_omega's table holds what o_u's table gives at psi_lo**, row by row of the matrix. -/
theorem col_chain (w₀ : Words Cb.Gl.E) (first next : ℕ)
    (PU PO : VerifiableInference.Desc.K1.Par)
    (codes : Codes) (S : LinShape) (psiLo : List Cb.Gl.E) (w : ℕ → Cb.Gl.E) (Rw : ℕ → ℕ → Cb.Gl.E)
    (cU cMask cOmega cSp : MsgCoins) (l : Lin)
    (hfit : VerifiableInference.Desc.Own.linFits codes S = true)
    (hle : first + PU.sent.size ≤ next) (hszU : 0 < PU.sent.size) (hshU : shapeAt PU 0 = S.fold.u)
    (hlU : l.oU = ⟨first, vectorLay codes S.fold.u S.fold.rowsHigh⟩) (hszO : 0 < PO.sent.size)
    (hshO : shapeAt PO 0 = S.omega) (hlO : l.oOmega = next) (j : ℕ)
    (hj : j < S.matrixRows) :
    omegaOf l (linLayOmega codes S)
        (chainWords w₀ first next PU PO (sendsU codes S w Rw cU cMask)
          (sendsOmega codes S psiLo (uHon S.fold w Rw) cOmega cSp)) j =
      ∑ t ∈ Finset.range (2 ^ S.kLo), eqK psiLo t *
        uOf l (chainWords w₀ first next PU PO (sendsU codes S w Rw cU cMask)
          (sendsOmega codes S psiLo (uHon S.fold w Rw) cOmega cSp)) (t + 2 ^ S.kLo * j) := by
  obtain ⟨hs, _⟩ := (VerifiableInference.Desc.Own.linFits_iff codes S).1 hfit
  have hroom : S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain := hs.2.2.2.2.2.1
  have h0 := ell_le_tailFirst S.fold
  have hpl : S.fold.index.plain ≤ S.fold.index.code.ell := Nat.sub_le _ _
  rw [omega_chain w₀ first next PU PO _ codes S psiLo _ cOmega cSp l hfit hszO hshO hlO j hj,
    omegaHon_row S psiLo _ j hj]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  have h1 : 2 ^ S.kLo * (j + 1) ≤ 2 ^ S.kLo * S.matrixRows := Nat.mul_le_mul_left _ hj
  have h2 : 2 ^ S.kLo * (j + 1) = 2 ^ S.kLo * j + 2 ^ S.kLo := Nat.mul_succ _ _
  have h3 : 2 ^ S.kLo * S.matrixRows = S.matrixRows * 2 ^ S.kLo := Nat.mul_comm _ _
  have hk : t + 2 ^ S.kLo * j < S.fold.entries := by
    unfold FoldeqShape.entries
    omega
  rw [u_chain w₀ first next PU PO _ codes S w Rw cU cMask l hfit hle hszU hshU hlU _ hk]

/-- o_sp's mask table holds kappaOf at an index in a real row. -/
theorem kappa_chain (w₀ : Words Cb.Gl.E) (first next : ℕ)
    (PU PO : VerifiableInference.Desc.K1.Par)
    (VU : ℕ → Rows) (codes : Codes) (S : LinShape) (psiLo : List Cb.Gl.E) (u : ℕ → Cb.Gl.E)
    (cOmega cSp : MsgCoins) (hsz : 1 < PO.sent.size) (hsh : shapeAt PO 1 = S.sharedSplit)
    (kappa : ℕ) (hk : kappa % 2 ^ ceilLog2 S.sharedSplit.maskRows < S.sharedSplit.maskRows) :
    chainWords w₀ first next PU PO VU (sendsOmega codes S psiLo u cOmega cSp)
        (next + 1) .mask kappa =
      kappaOf cSp S.sharedSplit.maskRows kappa := by
  rw [chainWords_o w₀ first next PU PO VU _ 1 hsz .mask kappa, hsh]
  show (if kappa % 2 ^ VerifiableInference.Desc.K1.clog S.sharedSplit.maskRows <
      S.sharedSplit.maskRows then _ else _) = _
  have hk' : kappa % 2 ^ VerifiableInference.Desc.K1.clog S.sharedSplit.maskRows <
      S.sharedSplit.maskRows := hk
  rw [if_pos hk']
  rfl

/-- **So the scalar muSent is omega_col, as o_omega's table holds it, at z_fd, plus the entry that
o_sp's table holds.** -/
theorem mu_chain (w₀ : Words Cb.Gl.E) (first next : ℕ)
    (PU PO : VerifiableInference.Desc.K1.Par)
    (VU : ℕ → Rows) (codes : Codes) (S : LinShape) (psiLo z : List Cb.Gl.E) (u : ℕ → Cb.Gl.E)
    (cOmega cSp : MsgCoins) (l : Lin)
    (hfit : VerifiableInference.Desc.Own.linFits codes S = true) (hsz : 1 < PO.sent.size)
    (hsh0 : shapeAt PO 0 = S.omega) (hsh1 : shapeAt PO 1 = S.sharedSplit)
    (hlO : l.oOmega = next) (hlS : l.oSp = next + 1) (kappa : ℕ)
    (hk : kappa % 2 ^ ceilLog2 S.sharedSplit.maskRows < S.sharedSplit.maskRows) :
    (∑ j ∈ Finset.range S.matrixRows, eqK z j * omegaOf l (linLayOmega codes S)
        (chainWords w₀ first next PU PO VU (sendsOmega codes S psiLo u cOmega cSp)) j) +
      chainWords w₀ first next PU PO VU (sendsOmega codes S psiLo u cOmega cSp) l.oSp .mask kappa =
    muSent S psiLo z u cSp kappa := by
  have h0 : 0 < PO.sent.size := Nat.lt_trans Nat.zero_lt_one hsz
  rw [hlS, kappa_chain w₀ first next PU PO VU codes S psiLo u cOmega cSp hsz hsh1 kappa hk]
  unfold muSent muHon
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [omega_chain w₀ first next PU PO VU codes S psiLo u cOmega cSp l hfit h0 hsh0 hlO j
    (Finset.mem_range.1 hj)]

/-! ## Between the two sendings -/

/-- Behind "send o_u" alone, o_u's table holds the folded row at the places that a row takes. -/
theorem u_held (w₀ : Words Cb.Gl.E) (first : ℕ) (PU : VerifiableInference.Desc.K1.Par)
    (codes : Codes) (S : LinShape) (w : ℕ → Cb.Gl.E) (Rw : ℕ → ℕ → Cb.Gl.E)
    (cU cMask : MsgCoins) (l : Lin)
    (hfit : VerifiableInference.Desc.Own.linFits codes S = true) (hsz : 0 < PU.sent.size)
    (hsh : shapeAt PU 0 = S.fold.u)
    (hl : l.oU = ⟨first, vectorLay codes S.fold.u S.fold.rowsHigh⟩) (k : ℕ)
    (hk : k < S.fold.entries) :
    uOf l (held w₀ first PU (sendsU codes S w Rw cU cMask)) k = uHon S.fold w Rw k := by
  obtain ⟨_, hf, _⟩ := (VerifiableInference.Desc.Own.linFits_iff codes S).1 hfit
  obtain ⟨hs, _, hr⟩ := hf
  have e := held_new w₀ first PU (sendsU codes S w Rw cU cMask) 0 hsz .main
    ((vectorLay codes S.fold.u S.fold.rowsHigh).index k)
  rw [Nat.add_zero, hsh] at e
  unfold uOf
  rw [hl]
  refine Eq.trans e ?_
  exact word_vec codes S.fold.u S.fold.rowsHigh (uHon S.fold w Rw) cU hs.2.2.2.1 S.fold.entries
    (VerifiableInference.Desc.Own.entries_pos S.fold hs.1.1.2.2.1) hr k hk

/-- A vector that is the folded row at the places that a row takes holds the rows' fold. -/
theorem isFold_of_eq (S : FoldeqShape) (w u : ℕ → Cb.Gl.E) (Rw : ℕ → ℕ → Cb.Gl.E)
    (key : ∀ k < S.entries, u k = uHon S w Rw k) : IsFold S w Rw u := by
  have h0 := ell_le_tailFirst S
  refine ⟨fun k hk => ?_, fun j hj => ?_⟩
  · have hk' : k < S.entries := by
      unfold FoldeqShape.entries
      omega
    rw [key k hk', (uHon_isFold S w Rw).onMsg k hk]
  · have hk' : S.tailFirst + j < S.entries := by
      unfold FoldeqShape.entries
      omega
    rw [key _ hk', (uHon_isFold S w Rw).onTail j hj]

/-- The rows' fold reads the weights of the table's rows alone. -/
theorem isFold_weights (S : FoldeqShape) (w w' u : ℕ → Cb.Gl.E) (Rw : ℕ → ℕ → Cb.Gl.E)
    (hw : ∀ r < S.index.rows, w r = w' r) (h : IsFold S w Rw u) : IsFold S w' Rw u := by
  have e : ∀ k, foldRows S.index.rows w Rw k = foldRows S.index.rows w' Rw k := fun k =>
    Finset.sum_congr rfl fun r hr => by rw [hw r (Finset.mem_range.1 hr)]
  exact ⟨fun k hk => (h.onMsg k hk).trans (e k), fun j hj => (h.onTail j hj).trans (e _)⟩

/-- **Behind "send o_u" alone, o_u's table holds the rows' fold.** -/
theorem isFold_held (w₀ : Words Cb.Gl.E) (first : ℕ) (PU : VerifiableInference.Desc.K1.Par)
    (codes : Codes) (S : LinShape) (w : ℕ → Cb.Gl.E) (Rw : ℕ → ℕ → Cb.Gl.E)
    (cU cMask : MsgCoins) (l : Lin)
    (hfit : VerifiableInference.Desc.Own.linFits codes S = true) (hsz : 0 < PU.sent.size)
    (hsh : shapeAt PU 0 = S.fold.u)
    (hl : l.oU = ⟨first, vectorLay codes S.fold.u S.fold.rowsHigh⟩) :
    IsFold S.fold w Rw (uOf l (held w₀ first PU (sendsU codes S w Rw cU cMask))) :=
  isFold_of_eq S.fold w _ Rw (u_held w₀ first PU codes S w Rw cU cMask l hfit hsz hsh hl)

end Desc.K14.Honest

#print axioms Desc.K14.Honest.padCoin_none
#print axioms Desc.K14.Honest.vecMain_at
#print axioms Desc.K14.Honest.vecMain_on_pad
#print axioms Desc.K14.Honest.vecMain_pad_at
#print axioms Desc.K14.Honest.ownPadPlaces_main
#print axioms Desc.K14.Honest.word_pad
#print axioms Desc.K14.Honest.word_vec
#print axioms Desc.K14.Honest.chainWords_u
#print axioms Desc.K14.Honest.chainWords_o
#print axioms Desc.K14.Honest.u_chain
#print axioms Desc.K14.Honest.isFold_chain
#print axioms Desc.K14.Honest.omega_chain
#print axioms Desc.K14.Honest.col_chain
#print axioms Desc.K14.Honest.kappa_chain
#print axioms Desc.K14.Honest.mu_chain
#print axioms Desc.K14.Honest.u_held
#print axioms Desc.K14.Honest.isFold_of_eq
#print axioms Desc.K14.Honest.isFold_weights
#print axioms Desc.K14.Honest.isFold_held
