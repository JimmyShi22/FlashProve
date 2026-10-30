-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxViewSto.lean: the stored tables' half of "the typed view of an entry's chain is
the strict reader's view", at the typed string that `assembleS` makes
(OnBytes/TypedOracleCompiler/Slice/EntryTyping.lean). For proofs only; the program does not import this file.



`viewX_cols` (OnBytes/TypedOracleCompiler/Run/ViewERead.lean) asks of the external string y: at every place that the
reader lists in an opening of a stored table, y holds the place and the listed column (its
hypothesis `hy`). The lax verifier builds y of the symbols in the typed string's external openings;
`assembleS` makes these by `extE`, a look-up in the table tx of all stored openings' rows, keyed by
which table it is (`whichOf`) and the place. Here `hy` is shown at that y.

Main theorems.
 `op_mem`          opening k of the stored openings of round i, as the reader hands them out, is a
                  member of `opsOf 1 o`, with the numbers i and k.
 `hy_extE`         `viewX_cols`' hypothesis `hy` at y := the wiring's string of `extE D.a cfg tx`.
 `flat_pos`        in a list of lists whose members have unlike marks, a mark names one place.
 `op_of_mem`       a member of `opsOf 1 o` is an opening of some round, with its numbers.
 `agree_tx`        `Agree tx`, if each stored table is opened at most once and the own trees' forms
                  do not say "stored".
 `hy_once`         so `hy` without `Agree` among what is asked.
 `hcar_extE`       every symbol of that y at a wanted place carries its place (`symbolsCarryTheirPositions`), if every
                  position that is read in a stored table is listed in a stored opening (`ListedX`).
 `hfull_read`      no part of the draws is shortened (`everyOpeningHasItsDraws`), from what one yes of the strict
                  reader says (OnBytes/K/OpenedRead.lean's `read_parts`).
 `xWanted_lt`      a wanted place of a stored table lies within the tables.
 `hown_of`         the forms of the own openings as read do not say "stored": from the reader's
                  trace and `TabGood` of the description's openings.
 `sto_half`        all three at the string π that `assembleS` makes of o, in the letters of the
                  record `LaxDebts` (OnBytes/K/Left/Lax.lean).
 `viewX_statement`  the strict reader's view does not read the statement in the description.

Asked: the rounds as read are the stripped rounds with the stored openings in front (`ho`); each
stored opening has `StoredFact` (`hS`); all tables have the depth D.a (`hD`) and forms that say
"stored" (`hst`); tx is `assembleS`' table; two rows of tx under one key have one column (`Agree`).

`honce`, "each stored table is opened at most once", is a test on the description alone: the marks
"is it item 1" of all stored openings are unlike, so there are at most two, one for each table. It
is false at any description that opens a table twice. It is shown at no description here.
stm: the statement under which the reader has read: a letter. The description's own statement is
not read: "the description is in order" (`hSok`) is asked with stm put in.

What is not claimed. `Agree tx` where a stored table is opened twice. The own trees' half (`hcol`).
Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Run.ViewERead3
import OnBytes.TypedOracleCompiler.Run.StoredMain
import OnBytes.TypedOracleCompiler.Slice.EntryTyping
import OnBytes.TypedOracleCompiler.Slice.EntryOpened

set_option autoImplicit false

namespace OnBytes.K.Left

open _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Slice (OpAt opsOf tabOf whichOf extE ListedX ext_opened assembleS assembleS_some
  PSXE wqXE)
open TypedOracleCompiler.Run.PQ (XD Agree lookup_agree tabOf_mem agree_of_once symbolsCarryTheirPositions xWanted drawnSL uL
  specX_parts specX_len specX_shape forall2_and_left wantedXL wantedX okX SOf RD)
open OnBytes.Tie (roundWithStoredOpenings StoredFact)
open _root_.Run (HId OpenB)
open _root_.Run.PQ (SgX xPos weX everyOpeningHasItsDraws XO storedKey xsAt View)

/-- A member of a zip, by its number. -/
theorem mem_zip_idx {α β : Type} : ∀ (l : List α) (m : List β) (x : α × β), x ∈ l.zip m →
    ∃ i : ℕ, l[i]? = some x.1 ∧ m[i]? = some x.2
  | [], _, x, h => by simp at h
  | _ :: _, [], x, h => by simp at h
  | a :: l, b :: m, x, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨0, rfl, rfl⟩
    · obtain ⟨i, h1, h2⟩ := mem_zip_idx l m x h'
      exact ⟨i + 1, h1, h2⟩

/-- Opening k of the stored openings of round i is a member of `opsOf 1 o`, with these numbers. -/
theorem op_mem (o : Fmt.ChainOut)
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings) (i k : ℕ)
    (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) (hp : rc[i]? = some p)
    (z : Fmt.Shape × List ℕ × Fmt.OpenOut) (hz : p.2[k]? = some z) :
    (⟨1, i, k, z.1, z.2.1, z.2.2⟩ : OpAt) ∈ opsOf 1 o := by
  unfold opsOf
  rw [ho]
  refine List.mem_flatMap.2 ⟨(roundWithStoredOpenings p, i), ?_, List.mem_map.2 ⟨(z, k), ?_, rfl⟩⟩
  · refine List.mem_zipIdx_iff_getElem?.2 ?_
    rw [List.getElem?_map, hp]
    rfl
  · refine List.mem_zipIdx_iff_getElem?.2 ?_
    show (p.2 ++ p.1.opens)[k]? = some z
    have hk : k < p.2.length := (List.getElem?_eq_some_iff.1 hz).1
    rw [List.getElem?_append_left hk]
    exact hz

/-- The stored tables' half: at every place that the reader lists in an opening of a stored
table, the string that the wiring builds of `extE`'s symbols holds the place and the listed column.
-/
theorem hy_extE (h : HId) (D : XD) (stm : ByteArray) (o : Fmt.ChainOut)
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hS : List.Forall₂ (fun (ts : List Fmt.Stored)
        (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact h D.base.cfg stm p.1.drawn.poss) ts p.2) D.stored rc)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (hst : ∀ s ∈ D.stored.flatten, s.sh.stored = true)
    (tx : List ((ℕ × ℕ) × TypedOracleCompiler.Slice.Row))
    (htx : tabOf (whichOf D) ((opsOf 1 o).filter fun op => op.sh.stored) = some tx)
    (hA : Agree tx) :
    ∀ tp ∈ D.stored.zip rc, ∀ tz ∈ tp.1.zip tp.2.2, ∀ xc ∈ tz.2.2.1.zip tz.2.2.2.cols,
      ∃ q, xPos (2 ^ D.a) (tz.1.item == 1, xc.1) = some q ∧
        (twoExternalStrings (2 ^ D.a) SgX).rd
          ((weX D.a).build fun p => (extE D.a D.base.cfg tx p).map Opening.sym) q =
          (xc.1, xc.2) := by
  intro tp htp tz htz xc hxc
  obtain ⟨i, hi1, hi2⟩ := mem_zip_idx _ _ tp htp
  obtain ⟨k, hk1, hk2⟩ := mem_zip_idx _ _ tz htz
  obtain ⟨n, hn1, hn2⟩ := mem_zip_idx _ _ xc hxc
  -- the table's data
  have hmem : tz.1 ∈ D.stored.flatten :=
    List.mem_flatten.2 ⟨tp.1, List.mem_of_getElem? hi1, List.mem_of_getElem? hk1⟩
  have hfact : StoredFact h D.base.cfg stm tp.2.1.drawn.poss tz.1 tz.2 := by
    have h1 := List.forall₂_iff_zip.1 hS
    have h2 := List.forall₂_iff_zip.1 (h1.2 htp)
    exact h2.2 htz
  have hok := hfact.okb
  unfold OpenB.ok at hok
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hok
  have hlt : xc.1 < 2 ^ D.a := by
    rw [← (hD _ hmem).1]
    exact hok.1.1.1.1.1.1.2 _ (List.mem_of_getElem? hn1)
  -- the opening is a member of the list
  have hop := op_mem o rc ho i k tp.2 hi2 tz.2 hk2
  have hop' : (⟨1, i, k, tz.2.1, tz.2.2.1, tz.2.2.2⟩ : OpAt) ∈
      (opsOf 1 o).filter fun op => op.sh.stored := by
    refine List.mem_filter.2 ⟨hop, ?_⟩
    show tz.2.1.stored = true
    rw [hfact.sh]
    exact hst _ hmem
  have hw : whichOf D ⟨1, i, k, tz.2.1, tz.2.2.1, tz.2.2.2⟩ = if tz.1.item == 1 then 1 else 0 := by
    unfold whichOf
    show (match (D.stored[i]?).bind (·[k]?) with
      | some t => if t.item == 1 then 1 else 0
      | none => 0) = _
    rw [hi1, Option.bind_some, hk1]
  -- the salt beside the column
  have hnl : n < tz.2.2.2.salts.length := by
    rw [hok.1.1.1.1.2]
    exact (List.getElem?_eq_some_iff.1 hn1).1
  have hrow : (xc.1, xc.2, tz.2.2.2.salts[n]) ∈
      tz.2.2.1.zip (tz.2.2.2.cols.zip tz.2.2.2.salts) := by
    refine List.mem_of_getElem? (i := n) ?_
    rw [List.getElem?_zip_eq_some]
    refine ⟨hn1, ?_⟩
    rw [List.getElem?_zip_eq_some]
    exact ⟨hn2, List.getElem?_eq_getElem hnl⟩
  obtain ⟨path, hpath⟩ := tabOf_mem htx hop' hrow
  rw [hw] at hpath
  obtain ⟨w, hw1, hw2⟩ := lookup_agree tx hA _ _ hpath
  have hw2' : w.1 = xc.2 := hw2
  unfold xPos
  rw [dif_pos hlt]
  refine ⟨_, rfl, ?_⟩
  cases hb : tz.1.item == 1 with
  | true =>
    rw [hb] at hw1
    show ((extE D.a D.base.cfg tx (.inr ⟨xc.1, hlt⟩)).map Opening.sym).getD (0, []) = _
    show (((tx.lookup (1, xc.1)).map fun z =>
      (⟨(xc.1, z.1), _, z.2.2⟩ : Opening 256 SgX)).map Opening.sym).getD (0, []) = _
    rw [show tx.lookup (1, xc.1) = some w from hw1]
    show (xc.1, w.1) = _
    rw [hw2']
  | false =>
    rw [hb] at hw1
    show (((tx.lookup (0, xc.1)).map fun z =>
      (⟨(xc.1, z.1), _, z.2.2⟩ : Opening 256 SgX)).map Opening.sym).getD (0, []) = _
    rw [show tx.lookup (0, xc.1) = some w from hw1]
    show (xc.1, w.1) = _
    rw [hw2']

/-! ## One column a key, where each stored table is opened at most once -/

/-- In a list of lists whose members have unlike marks, a mark names one place. -/
theorem flat_pos {α β : Type} (f : α → β) : ∀ (L : List (List α)), (L.flatten.map f).Nodup →
    ∀ (i k i' k' : ℕ) (a a' : α), (L[i]?).bind (·[k]?) = some a → (L[i']?).bind (·[k']?) = some a' →
      f a = f a' → i = i' ∧ k = k'
  | [], _, i, k, i', k', a, a', h, _, _ => by simp at h
  | l :: L, hn, i, k, i', k', a, a', h, h', e => by
    rw [List.flatten_cons, List.map_append] at hn
    obtain ⟨n1, n2, n3⟩ := List.nodup_append.1 hn
    have inFlat : ∀ (j m : ℕ) (x : α), (L[j]?).bind (·[m]?) = some x → f x ∈ L.flatten.map f := by
      intro j m x hx
      obtain ⟨l', hl', hm⟩ := Option.bind_eq_some_iff.1 hx
      exact List.mem_map.2 ⟨x, List.mem_flatten.2 ⟨l', List.mem_of_getElem? hl',
        List.mem_of_getElem? hm⟩, rfl⟩
    cases i with
    | zero =>
      have h0 : l[k]? = some a := h
      cases i' with
      | zero =>
        have h0' : l[k']? = some a' := h'
        refine ⟨rfl, ?_⟩
        have hk := (List.getElem?_eq_some_iff.1 h0)
        have hk' := (List.getElem?_eq_some_iff.1 h0')
        have e1 : (l.map f)[k]'(by rw [List.length_map]; exact hk.1) =
            (l.map f)[k']'(by rw [List.length_map]; exact hk'.1) := by
          rw [List.getElem_map, List.getElem_map, hk.2, hk'.2]
          exact e
        exact (List.Nodup.getElem_inj_iff n1).1 e1
      | succ j' =>
        exact absurd e (n3 _ (List.mem_map.2 ⟨a, List.mem_of_getElem? h0, rfl⟩) _
          (inFlat j' k' a' h'))
    | succ j =>
      cases i' with
      | zero =>
        have h0' : l[k']? = some a' := h'
        exact absurd e.symm (n3 _ (List.mem_map.2 ⟨a', List.mem_of_getElem? h0', rfl⟩) _
          (inFlat j k a h))
      | succ j' =>
        obtain ⟨e1, e2⟩ := flat_pos f L n2 j k j' k' a a' h h' e
        exact ⟨congrArg Nat.succ e1, e2⟩

/-- A member of `opsOf 1 o` is an opening of some round, with its numbers. -/
theorem op_of_mem (o : Fmt.ChainOut)
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings) (a : OpAt) (ha : a ∈ opsOf 1 o) :
    ∃ (i k : ℕ) (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut))
      (z : Fmt.Shape × List ℕ × Fmt.OpenOut),
      rc[i]? = some p ∧ (p.2 ++ p.1.opens)[k]? = some z ∧ a = ⟨1, i, k, z.1, z.2.1, z.2.2⟩ := by
  unfold opsOf at ha
  rw [ho] at ha
  obtain ⟨r, hr, hx⟩ := List.mem_flatMap.1 ha
  obtain ⟨x, hx1, rfl⟩ := List.mem_map.1 hx
  have h1 := List.mem_zipIdx_iff_getElem?.1 hr
  have h2 := List.mem_zipIdx_iff_getElem?.1 hx1
  rw [List.getElem?_map] at h1
  obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.1 h1
  refine ⟨r.2, x.2, p, x.1, hp, ?_, rfl⟩
  rw [← e] at h2
  exact h2

/-- Two rows of the table of stored openings under one key have one column, if each stored table
is opened at most once in the description, and the own trees' forms do not say "stored". -/
theorem agree_tx (h : HId) (D : XD) (stm : ByteArray) (o : Fmt.ChainOut)
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hS : List.Forall₂ (fun (ts : List Fmt.Stored)
        (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact h D.base.cfg stm p.1.drawn.poss) ts p.2) D.stored rc)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (hown : ∀ p ∈ rc, ∀ x ∈ p.1.opens, x.1.stored = false)
    (tx : List ((ℕ × ℕ) × TypedOracleCompiler.Slice.Row))
    (htx : tabOf (whichOf D) ((opsOf 1 o).filter fun op => op.sh.stored) = some tx) :
    Agree tx := by
  -- what a stored member of the list is
  have key : ∀ a ∈ (opsOf 1 o).filter fun op => op.sh.stored,
      ∃ (i k : ℕ) (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut))
        (z : Fmt.Shape × List ℕ × Fmt.OpenOut) (t : Fmt.Stored),
        rc[i]? = some p ∧ p.2[k]? = some z ∧ a = ⟨1, i, k, z.1, z.2.1, z.2.2⟩ ∧
        (D.stored[i]?).bind (·[k]?) = some t ∧
        StoredFact h D.base.cfg stm p.1.drawn.poss t z := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := List.mem_filter.1 ha
    obtain ⟨i, k, p, z, hp, hz, rfl⟩ := op_of_mem o rc ho a ha1
    have hst : z.1.stored = true := ha2
    have hk : k < p.2.length := by
      by_contra hge
      rw [List.getElem?_append_right (by omega)] at hz
      rw [hown p (List.mem_of_getElem? hp) z (List.mem_of_getElem? hz)] at hst
      cases hst
    rw [List.getElem?_append_left hk] at hz
    have h1 := List.forall₂_iff_zip.1 hS
    have hi : i < rc.length := (List.getElem?_eq_some_iff.1 hp).1
    have hi' : i < D.stored.length := by rw [h1.1]; exact hi
    have hts : D.stored[i]? = some D.stored[i] := List.getElem?_eq_getElem hi'
    have hzip : (D.stored[i], p) ∈ D.stored.zip rc :=
      List.mem_of_getElem? (i := i) (List.getElem?_zip_eq_some.2 ⟨hts, hp⟩)
    have h2 := List.forall₂_iff_zip.1 (h1.2 hzip)
    have hk' : k < D.stored[i].length := by rw [h2.1]; exact hk
    have ht : D.stored[i][k]? = some D.stored[i][k] := List.getElem?_eq_getElem hk'
    have hzip2 : (D.stored[i][k], z) ∈ D.stored[i].zip p.2 :=
      List.mem_of_getElem? (i := k) (List.getElem?_zip_eq_some.2 ⟨ht, hz⟩)
    exact ⟨i, k, p, z, D.stored[i][k], hp, hz, rfl, by rw [hts, Option.bind_some, ht],
      h2.2 hzip2⟩
  refine agree_of_once htx (fun a ha b hb e => ?_) fun a ha => ?_
  · obtain ⟨i, k, p, z, t, hp, hz, rfl, ht, -⟩ := key a ha
    obtain ⟨i', k', p', z', t', hp', hz', rfl, ht', -⟩ := key b hb
    have wa : whichOf D ⟨1, i, k, z.1, z.2.1, z.2.2⟩ = if t.item == 1 then 1 else 0 := by
      unfold whichOf
      show (match (D.stored[i]?).bind (·[k]?) with
        | some t => if t.item == 1 then 1 else 0
        | none => 0) = _
      rw [ht]
    have wb : whichOf D ⟨1, i', k', z'.1, z'.2.1, z'.2.2⟩ = if t'.item == 1 then 1 else 0 := by
      unfold whichOf
      show (match (D.stored[i']?).bind (·[k']?) with
        | some t => if t.item == 1 then 1 else 0
        | none => 0) = _
      rw [ht']
    rw [wa, wb] at e
    have ef : (t.item == 1) = (t'.item == 1) := by
      cases h1 : t.item == 1 <;> cases h2 : t'.item == 1 <;> simp [h1, h2] at e ⊢
    obtain ⟨rfl, rfl⟩ := flat_pos (·.item == 1) D.stored honce i k i' k' t t' ht ht' ef
    obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
    obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
    rfl
  · obtain ⟨i, k, p, z, t, -, -, rfl, -, hf⟩ := key a ha
    exact ((_root_.Run.WalkTie.listOK_spec t.sh.a z.2.1 hf.okl).2.1).imp fun hlt => Nat.ne_of_lt hlt

/-- The stored tables' half, where each stored table is opened at most once. -/
theorem hy_once (h : HId) (D : XD) (stm : ByteArray) (o : Fmt.ChainOut)
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hS : List.Forall₂ (fun (ts : List Fmt.Stored)
        (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact h D.base.cfg stm p.1.drawn.poss) ts p.2) D.stored rc)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (hst : ∀ s ∈ D.stored.flatten, s.sh.stored = true)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (hown : ∀ p ∈ rc, ∀ x ∈ p.1.opens, x.1.stored = false)
    (tx : List ((ℕ × ℕ) × TypedOracleCompiler.Slice.Row))
    (htx : tabOf (whichOf D) ((opsOf 1 o).filter fun op => op.sh.stored) = some tx) :
    ∀ tp ∈ D.stored.zip rc, ∀ tz ∈ tp.1.zip tp.2.2, ∀ xc ∈ tz.2.2.1.zip tz.2.2.2.cols,
      ∃ q, xPos (2 ^ D.a) (tz.1.item == 1, xc.1) = some q ∧
        (twoExternalStrings (2 ^ D.a) SgX).rd
          ((weX D.a).build fun p => (extE D.a D.base.cfg tx p).map Opening.sym) q =
          (xc.1, xc.2) :=
  hy_extE h D stm o rc ho hS hD hst tx htx (agree_tx h D stm o rc ho hS honce hown tx htx)

/-! ## Every symbol at a wanted place carries its place; no part of the draws is shortened -/

/-- Every symbol of the string at a wanted place carries its place. Ds: the rounds' draws.
Asked: every position among the wanted ones is listed in a stored opening of its table (`ListedX` at
"is among the wanted positions"), and every wanted place lies within the tables. At a position
without an opening the wiring's string has the symbol (0, []), so the first is needed. -/
theorem hcar_extE (D : XD) (ops : List OpAt) (tx : List ((ℕ × ℕ) × TypedOracleCompiler.Slice.Row))
    (htx : tabOf (whichOf D) ops = some tx) (Ds : List Fmt.Drawn)
    (isReadE : Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a) → Bool) (hl : ListedX D D.a ops isReadE)
    (hr : ∀ wx ∈ xWanted D.a D.ds D.xs Ds, ∃ p, xPos (2 ^ D.a) wx = some p ∧ isReadE p = true) :
    symbolsCarryTheirPositions D.a D.ds D.xs Ds
      ((weX D.a).build fun p => (extE D.a D.base.cfg tx p).map Opening.sym) = true := by
  unfold symbolsCarryTheirPositions
  rw [List.all_eq_true]
  intro wx hwx
  obtain ⟨p, hp, hrd⟩ := hr wx hwx
  rw [hp]
  have hs := ext_opened htx D.base.cfg hl p hrd
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hs
  unfold xPos at hp
  split at hp
  · rename_i hlt
    have e := Option.some.inj hp
    cases hb : wx.1 with
    | true =>
      rw [hb, if_pos rfl] at e
      subst e
      obtain ⟨z, -, rfl⟩ := Option.map_eq_some_iff.1
        (show ((tx.lookup (1, wx.2)).map fun z =>
          (⟨(wx.2, z.1), _, z.2.2⟩ : Opening 256 SgX)) = some w from hw)
      show ((((extE D.a D.base.cfg tx (.inr ⟨wx.2, hlt⟩)).map Opening.sym).getD (0, [])).1 ==
        wx.2) = true
      rw [hw]
      exact beq_self_eq_true wx.2
    | false =>
      rw [hb, if_neg (by decide)] at e
      subst e
      obtain ⟨z, -, rfl⟩ := Option.map_eq_some_iff.1
        (show ((tx.lookup (0, wx.2)).map fun z =>
          (⟨(wx.2, z.1), _, z.2.2⟩ : Opening 256 SgX)) = some w from hw)
      show ((((extE D.a D.base.cfg tx (.inl ⟨wx.2, hlt⟩)).map Opening.sym).getD (0, [])).1 ==
        wx.2) = true
      rw [hw]
      exact beq_self_eq_true wx.2
  · cases hp

/-- No part of the draws is shortened, at draws that are those of the rounds as read. S: the
description under which the reader has read; asked of it: it is in order, and each round has as many
draws as its entry says (both stand in `read_parts`' conclusion). -/
theorem hfull_read (S : Fmt.SpecX) (hS : S.ok = true) (o : Fmt.ChainOut)
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hlen : List.Forall₂ (fun (x : Fmt.Round × List Fmt.Stored)
        (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) =>
      p.1.drawn.poss.length = x.1.entry.poss) (S.base.rounds.zip S.stored) rc) :
    everyOpeningHasItsDraws (OnBytes.Tie.xsOf S.stored) (o.rounds.toList.map (·.drawn)) = true := by
  have hsnd : (S.base.rounds.zip S.stored).map (·.2) = S.stored :=
    List.map_snd_zip (le_of_eq (specX_len S hS))
  refine OnBytes.Tie.fullX_true S.stored _ ?_
  rw [ho, List.map_map, ← hsnd]
  refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 ?_)
  refine (forall2_and_left hlen (specX_parts S hS)).imp fun x p hh t ht' => ?_
  show t.lo + t.count ≤ p.1.drawn.poss.length
  rw [hh.1]
  exact hh.2 t ht'

/-! ## All three at the typing's string -/

/-- A wanted pair under a stored table's key has a place within the tables, if the own trees'
numbers are below 2 ^ 16. -/
theorem wantedXL_lt (a : ℕ) (all : List RD) (xs : List XO) :
    ∀ (i : ℕ) (ds : List RD) (Ds : List Fmt.Drawn) (kx : ℕ × ℕ), kx ∈ wantedXL a all xs i ds Ds →
      (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) → 2 ^ 16 ≤ kx.1 → kx.2 < 2 ^ a
  | _, [], _, kx, h, _, _ => by
    unfold wantedXL at h
    cases h
  | _, _ :: _, [], kx, h, _, _ => by
    unfold wantedXL at h
    cases h
  | i, d :: ds, D :: Ds, kx, h, hs, hk => by
    unfold wantedXL at h
    rcases List.mem_append.1 h with h1 | h3
    · rcases List.mem_append.1 h1 with h1 | h2
      · obtain ⟨o, -, ho⟩ := List.mem_flatMap.1 h1
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ho
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hx)
        exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))
      · obtain ⟨n, hn, hm⟩ := List.mem_flatMap.1 h2
        have hlt := hs d List.mem_cons_self n hn
        split at hm
        · cases hm
        · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hm
          exact absurd hk (by show ¬ 2 ^ 16 ≤ n; omega)
    · exact wantedXL_lt a all xs (i + 1) ds Ds kx h3
        (fun d' hd' => hs d' (List.mem_cons_of_mem _ hd')) hk

/-- A wanted place of a stored table lies within the tables. -/
theorem xWanted_lt (a : ℕ) (ds : List RD) (xs : List XO) (Ds : List Fmt.Drawn)
    (hs : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) (wx : Bool × ℕ) (h : wx ∈ xWanted a ds xs Ds) :
    wx.2 < 2 ^ a := by
  unfold xWanted at h
  obtain ⟨kx, hkx, e⟩ := List.mem_filterMap.1 h
  have hlt : 2 ^ 16 ≤ kx.1 → kx.2 < 2 ^ a := wantedXL_lt a ds xs 0 ds Ds kx hkx hs
  split at e
  · rename_i hk
    rw [← Option.some.inj e]
    exact hlt (by rw [hk]; show 2 ^ 16 ≤ 2 ^ 16 + _; omega)
  · split at e
    · rename_i hk
      rw [← Option.some.inj e]
      exact hlt (by rw [hk]; show 2 ^ 16 ≤ 2 ^ 16 + _; omega)
    · cases e

/-- The forms of the own openings as read do not say "stored": each stands beside an opening of
the description with the same form (the reader's trace), and that is some own tree's (`TabGood`). -/
theorem hown_of (h : HId) (D : XD)
    (hg : ∀ r ∈ D.base.rounds, ∀ x ∈ r.opens, ∃ n, TypedOracleCompiler.Run.PQ.TabGood D.base x n)
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut))) (c : Fmt.Chain)
    (htr : _root_.Run.PQ.TraceL h D.base.plan D.base.rounds
      (rc.map fun p => _root_.Run.PQ.stripR p.1) c #[]) :
    ∀ p ∈ rc, ∀ z ∈ p.1.opens, z.1.stored = false := by
  intro p hp z hz
  have ht := _root_.Run.PQ.tab_tr h _ _ _ _ _ htr
  obtain ⟨r, hr, x, hx, acc', rest, hxy, -⟩ := _root_.Run.PQ.tab_pairR _ _ _ ht
    (_root_.Run.PQ.stripR p.1) (List.mem_map.2 ⟨p, hp, rfl⟩)
    (z.1, z.2.1, _root_.Run.PQ.stripO z.2.2) (List.mem_map.2 ⟨z, hz, rfl⟩)
  obtain ⟨n, hn⟩ := hg r hr x hx
  have e : z.1 = x.1 := hxy.1
  rw [e]
  exact hn.plain

/-- The stored tables' half, whole, at the typing's string. π: what `assembleS` makes of o; y:
the string that the lax verifier builds of π's external openings; ρ: what the chain draws, with the
draws of the rounds as read. Then: y meets `viewX_cols`' hypothesis `hy`; every symbol of y at a
wanted place carries its place; no part of the draws is shortened. -/
theorem sto_half {X : Type} (h : HId) (D : XD) (stm : ByteArray) (dec : X → View → Bool) (x : X)
    (o : Fmt.ChainOut)
    (π : OneProtocolProof 256 (PSXE D dec).up) (hπ : assembleS D dec o = some π)
    (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds)))
    (hd : drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn))
    (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)))
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hS : List.Forall₂ (fun (ts : List Fmt.Stored)
        (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact h D.base.cfg stm p.1.drawn.poss) ts p.2) D.stored rc)
    (hlen : List.Forall₂ (fun (z : Fmt.Round × List Fmt.Stored)
        (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) =>
      p.1.drawn.poss.length = z.1.entry.poss) (D.base.rounds.zip D.stored) rc)
    (hSok : (⟨{ D.base with statement := stm }, D.stored⟩ : Fmt.SpecX).ok = true)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (hown : ∀ p ∈ rc, ∀ z ∈ p.1.opens, z.1.stored = false)
    (okx : okX D.ds D.a D.xs = true)
    (listed : ListedX D D.a ((opsOf 1 o).filter fun op => op.sh.stored) fun p =>
      (haveI := (wqXE D dec).ext.dec
       decide (p ∈ (PSXE D dec).up.loc.extReads x ρ))) :
    (∀ tp ∈ D.stored.zip rc, ∀ tz ∈ tp.1.zip tp.2.2, ∀ xc ∈ tz.2.2.1.zip tz.2.2.2.cols,
      ∃ q, xPos (2 ^ D.a) (tz.1.item == 1, xc.1) = some q ∧
        (twoExternalStrings (2 ^ D.a) SgX).rd
          ((wqXE D dec).ext.build fun p => (π.ext p).map Opening.sym) q = (xc.1, xc.2)) ∧
      symbolsCarryTheirPositions D.a D.ds D.xs (drawnSL D.C D.ds ρ.2)
        ((wqXE D dec).ext.build fun p => (π.ext p).map Opening.sym) = true ∧
      everyOpeningHasItsDraws D.xs (drawnSL D.C D.ds ρ.2) = true := by
  obtain ⟨run, pl, tab, tx, -, -, -, htx, -, -, -, -, hext, -⟩ := assembleS_some D dec hπ
  rw [hext]
  have hopens : ∀ d ∈ D.ds, ∀ n ∈ d.opens, n < 2 ^ 16 := by
    unfold okX at okx
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at okx
    exact okx.2
  have hst : ∀ s ∈ D.stored.flatten, s.sh.stored = true := fun s hs =>
    (specX_shape ⟨{ D.base with statement := stm }, D.stored⟩ hSok s hs).1
  refine ⟨hy_once h D stm o rc ho hS hD hst honce hown tx htx, ?_, ?_⟩
  · refine hcar_extE D _ tx htx _ _ listed fun wx hwx => ?_
    have hlt := xWanted_lt D.a D.ds D.xs _ hopens wx hwx
    have hp : xPos (2 ^ D.a) wx =
        some (if wx.1 then .inr ⟨wx.2, hlt⟩ else .inl ⟨wx.2, hlt⟩) := by
      unfold xPos
      rw [dif_pos hlt]
    refine ⟨_, hp, decide_eq_true ?_⟩
    exact List.mem_toFinset.2 (List.mem_filterMap.2 ⟨wx, hwx, hp⟩)
  · rw [hd]
    exact hfull_read ⟨{ D.base with statement := stm }, D.stored⟩ hSok o rc ho hlen

/-- The strict reader's view does not read the statement in the description. -/
theorem viewX_statement (S : Fmt.SpecX) (stm : ByteArray) (o : Fmt.ChainOut) :
    Fmt.viewX ⟨{ S.base with statement := stm }, S.stored⟩ o = Fmt.viewX S o := rfl

end OnBytes.K.Left
