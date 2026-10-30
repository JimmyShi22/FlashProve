-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/Whole.lean: WHAT IS PRINTED COMES BACK, AT A WHOLE FILE: the parsed file that
carrierOf (OnBytes/Prover/Print/Carrier.lean) makes of a typed proof string is laid again as that
very string by the typing File.toBPrfAt (OnBytes/Maker/CarrierTyping.lean), where the string
is Printable and the data's rounds have as many items "root" as trees (RootsFit). Statements and
proofs. No prover, no oracle, no byte: the library's types alone.

Called as they stand: ofGots_itemsOf, rootsOf_itemsOf, digs_back, saltFrom_back, slotSalt_rsOf
(OnBytes/Prover/Print/Items.lean); GPlain.mk_old_nonce (Iop/GrindProofs.lean).

Main names.
  lk_rows_none, lk_rows_mem   rows that are made place by place, each under its own place: the
    look-up at a place gives what was made there.
  lk_map_none, lk_map_mem, lk_treesOf_none, lk_treesOf_mem, lk_three   the tables of all trees: the
    look-up at a tree's number over the file gives that tree's entry.
  symIn_colT, symT'_colOfSym   a symbol as a list of words comes back (the converse of
    colT_symIn, colOfSym_symT').
  leafIn_lt, leafAt_lt   a position's leaf lies in its tree.
  rows_lookup, opensT_back   ONE STRETCH: the typing's openings are the string's.
  stored_back   the stored table's.
  plainsT_roundsOf, rootsT_roundsOf, rootsT_back   ONE STRETCH: plain parts and roots.
  mem_treesOf, sender₁, sender₂, sender₃   small steps for the six tests.
  slotFits_carrierOf, treesFit_carrierOf, chainOff_carrierOf   three of the tests.
  bprf_eq   a proof string is its nine fields.
  toBPrfAt_carrierOf   THE STATEMENT.

Which clause of Printable is spent where. salt: the first field. roots with RootsFit: the roots.
own₁, own₂, own₃: the openings' salts. ext: the stored table's openings. slot, path, rsalt: the test
slotFits and the last field. NOT SPENT HERE: run2, run3, answers.

Limits. ONE WAY: that a string which comes back is Printable is not said. Nothing on bytes: that
the parsed file can be written and read is another file's. Nothing here says that any prover's
string is Printable: OnBytes/Prover/Print/Honest.lean has it of the compiled prover's, under
premises that it does not show to be met. rowsOf and storedOf walk all leaves of a tree: the proofs
go by the look-ups' laws; nothing is evaluated. Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Print.Items
import OnBytes.Maker.TypingTLaws
import OnBytes.Maker.ReadsAt
import Run.Toy1TieTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print

open _root_.Run _root_.Run.PQ Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open OnBytes.Maker OnBytes.Maker.Carrier
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (opensL opensR opensApp opensApp_LR pls₁ pls₂ pls₃)

/-! ## Look-ups -/

/-- Rows made place by place: no row at a place that was not walked. -/
theorem lk_rows_none (start : ByteArray) (G : ℕ → Option Carrier.Row)
    (hG : ∀ y r, G y = some r → r.leaf = y) (x : ℕ) :
    ∀ l : List ℕ, x ∉ l → ((l.filterMap G).map (Row.row3 start)).lookup x = none
  | [], _ => rfl
  | y :: l, h => by
    rw [List.mem_cons, not_or] at h
    cases hy : G y with
    | none =>
      rw [List.filterMap_cons_none hy]
      exact lk_rows_none start G hG x l h.2
    | some r =>
      rw [List.filterMap_cons_some hy, List.map_cons]
      show ((r.leaf, r.column, leafSalt start r.salt, r.path.map bytesToDig) ::
        (l.filterMap G).map (Row.row3 start)).lookup x = none
      have hk : (x == r.leaf) = false := by
        rw [beq_eq_false_iff_ne, hG y r hy]
        exact h.1
      rw [List.lookup_cons, hk]
      exact lk_rows_none start G hG x l h.2

/-- Rows made place by place: at a place that was walked, what was made there. -/
theorem lk_rows_mem (start : ByteArray) (G : ℕ → Option Carrier.Row)
    (hG : ∀ y r, G y = some r → r.leaf = y) (x : ℕ) :
    ∀ l : List ℕ, x ∈ l → ((l.filterMap G).map (Row.row3 start)).lookup x =
      (G x).map fun r => (r.column, leafSalt start r.salt, r.path.map bytesToDig)
  | y :: l, h => by
    cases hy : G y with
    | none =>
      rw [List.filterMap_cons_none hy]
      by_cases e : x = y
      · subst e
        rw [hy]
        by_cases hm : x ∈ l
        · rw [lk_rows_mem start G hG x l hm, hy]
        · exact lk_rows_none start G hG x l hm
      · exact lk_rows_mem start G hG x l ((List.mem_cons.1 h).resolve_left e)
    | some r =>
      rw [List.filterMap_cons_some hy, List.map_cons]
      show ((r.leaf, r.column, leafSalt start r.salt, r.path.map bytesToDig) ::
        (l.filterMap G).map (Row.row3 start)).lookup x = _
      rw [List.lookup_cons, hG y r hy]
      by_cases e : x = y
      · subst e
        rw [beq_self_eq_true, hy]
        rfl
      · have hk : (x == y) = false := by
          rw [beq_eq_false_iff_ne]
          exact e
        rw [hk]
        exact lk_rows_mem start G hG x l ((List.mem_cons.1 h).resolve_left e)

/-- A table under keys: nothing under a number that is no key. -/
theorem lk_map_none {β : Type} (key : ℕ → ℕ) (G : ℕ → β) (j : ℕ) :
    ∀ l : List ℕ, (∀ y ∈ l, key y ≠ j) → (l.map fun y => (key y, G y)).lookup j = none
  | [], _ => rfl
  | y :: l, h => by
    have hk : (j == key y) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun e => h y List.mem_cons_self e.symm
    rw [List.map_cons, List.lookup_cons, hk]
    exact lk_map_none key G j l fun z hz => h z (List.mem_cons_of_mem _ hz)

/-- A table under keys that are apart: under a key, its entry. -/
theorem lk_map_mem {β : Type} (key : ℕ → ℕ) (hkey : ∀ a b, key a = key b → a = b) (G : ℕ → β)
    (n : ℕ) : ∀ l : List ℕ, n ∈ l → (l.map fun y => (key y, G y)).lookup (key n) = some (G n)
  | y :: l, h => by
    rw [List.map_cons, List.lookup_cons]
    by_cases e : n = y
    · subst e
      rw [beq_self_eq_true]
    · have hk : (key n == key y) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun e' => e (hkey _ _ e')
      rw [hk]
      exact lk_map_mem key hkey G n l ((List.mem_cons.1 h).resolve_left e)

section Trees
variable {β : Type} (C : CK) (ds : List RDT) (chain base : ℕ)
  (opens : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p)))
  (H : Carrier.TreeRows → β)

/-- One stretch's entries: nothing under a number outside the stretch. -/
theorem lk_treesOf_none (j : ℕ) (hj : j < base ∨ base + (ds.map (·.trees.length)).sum ≤ j) :
    ((treesOf C ds chain base opens).map fun t => (t.tree, H t)).lookup j = none := by
  unfold treesOf
  rw [List.map_map]
  refine lk_map_none (fun y => base + y) (fun y => H ⟨base + y, chain, rowsOf C ds opens y⟩) j _
    fun y hy => ?_
  have hy' := List.mem_range.1 hy
  show base + y ≠ j
  omega

/-- One stretch's entries: under a tree's number over the file, its entry. -/
theorem lk_treesOf_mem (n : ℕ) (hn : n < (ds.map (·.trees.length)).sum) :
    ((treesOf C ds chain base opens).map fun t => (t.tree, H t)).lookup (base + n) =
      some (H ⟨base + n, chain, rowsOf C ds opens n⟩) := by
  unfold treesOf
  rw [List.map_map]
  exact lk_map_mem (fun y => base + y) (fun a b e => Nat.add_left_cancel e)
    (fun y => H ⟨base + y, chain, rowsOf C ds opens y⟩) n _ (List.mem_range.2 hn)

end Trees

/-- **The tables of all trees of three stretches.** -/
theorem lk_three {β : Type} (C : CK) (ds₁ ds₂ ds₃ : List RDT)
    (o₁ : (p : OPos (uLT C ds₁)) → Option (Opening 256 (OSym (uLT C ds₁) p)))
    (o₂ : (p : OPos (uLT C ds₂)) → Option (Opening 256 (OSym (uLT C ds₂) p)))
    (o₃ : (p : OPos (uLT C ds₃)) → Option (Opening 256 (OSym (uLT C ds₃) p)))
    (H : Carrier.TreeRows → β) (t₁ t₂ : ℕ) (h₁ : t₁ = (ds₁.map (·.trees.length)).sum)
    (h₂ : t₂ = (ds₂.map (·.trees.length)).sum) :
    (∀ n, n < (ds₁.map (·.trees.length)).sum →
      ((treesOf C ds₁ 0 0 o₁ ++ (treesOf C ds₂ 1 t₁ o₂ ++ treesOf C ds₃ 2 (t₁ + t₂) o₃)).map
        fun t => (t.tree, H t)).lookup (0 + n) = some (H ⟨0 + n, 0, rowsOf C ds₁ o₁ n⟩)) ∧
    (∀ n, n < (ds₂.map (·.trees.length)).sum →
      ((treesOf C ds₁ 0 0 o₁ ++ (treesOf C ds₂ 1 t₁ o₂ ++ treesOf C ds₃ 2 (t₁ + t₂) o₃)).map
        fun t => (t.tree, H t)).lookup (t₁ + n) = some (H ⟨t₁ + n, 1, rowsOf C ds₂ o₂ n⟩)) ∧
    ∀ n, n < (ds₃.map (·.trees.length)).sum →
      ((treesOf C ds₁ 0 0 o₁ ++ (treesOf C ds₂ 1 t₁ o₂ ++ treesOf C ds₃ 2 (t₁ + t₂) o₃)).map
        fun t => (t.tree, H t)).lookup (t₁ + t₂ + n) =
          some (H ⟨t₁ + t₂ + n, 2, rowsOf C ds₃ o₃ n⟩) := by
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun n hn => ?_⟩
  · rw [List.map_append, List.lookup_append, lk_treesOf_mem C ds₁ 0 0 o₁ H n hn]
    rfl
  · rw [List.map_append, List.map_append, List.lookup_append, List.lookup_append,
      lk_treesOf_none C ds₁ 0 0 o₁ H (t₁ + n) (Or.inr (by omega)),
      lk_treesOf_mem C ds₂ 1 t₁ o₂ H n hn]
    rfl
  · rw [List.map_append, List.map_append, List.lookup_append, List.lookup_append,
      lk_treesOf_none C ds₁ 0 0 o₁ H (t₁ + t₂ + n) (Or.inr (by omega)),
      lk_treesOf_none C ds₂ 1 t₁ o₂ H (t₁ + t₂ + n) (Or.inr (by omega)),
      lk_treesOf_mem C ds₃ 2 (t₁ + t₂) o₃ H n hn]
    rfl

/-! ## Symbols and places -/

/-- A symbol of one round, as a list of words, comes back. -/
theorem symIn_colT : ∀ (ts : List _root_.Fmt.Shape) (p : PosT ts) (a : SymT ts p),
    symIn ts p (colT ts p a) = some a
  | s :: _, .inl _, a => by
    have a' : Fin s.W → UInt64 := a
    show (if h : (List.ofFn (n := s.W) a).length = s.W then
        some (fun i : Fin s.W => (List.ofFn (n := s.W) a)[i.val]'(by rw [h]; exact i.isLt))
      else none) = some a
    rw [dif_pos List.length_ofFn]
    refine congrArg some (funext fun i => ?_)
    exact List.getElem_ofFn _
  | _ :: ts, .inr p, a => symIn_colT ts p a

/-- A symbol of the stretch, as a list of words, comes back. -/
theorem symT'_colOfSym (C : CK) : ∀ (ds : List RDT) (p : OPos (uLT C ds))
    (a : OSym (uLT C ds) p), symT' C ds p (colOfSym C ds p a) = some a
  | d :: _, .inl p, a => symIn_colT d.trees p a
  | _ :: ds, .inr q, a => symT'_colOfSym C ds q a

/-- A position's leaf lies in its tree: one round. -/
theorem leafIn_lt : ∀ (ts : List _root_.Fmt.Shape) (p : PosT ts),
    ∃ s, ts[treeIn ts p]? = some s ∧ leafIn ts p < 2 ^ s.a
  | s :: _, .inl x => ⟨s, rfl, x.isLt⟩
  | _ :: ts, .inr p => by
    obtain ⟨s, h1, h2⟩ := leafIn_lt ts p
    exact ⟨s, h1, h2⟩

/-- A position's leaf lies in its tree: the stretch. -/
theorem leafAt_lt (C : CK) : ∀ (ds : List RDT) (p : OPos (uLT C ds)),
    ∃ s, treeShT ds (treeAt C ds p) = some s ∧ leafAt C ds p < 2 ^ s.a
  | d :: _, .inl p => by
    obtain ⟨s, h1, h2⟩ := leafIn_lt d.trees p
    refine ⟨s, ?_, h2⟩
    show (if treeIn d.trees p < d.trees.length then d.trees[treeIn d.trees p]? else _) = _
    rw [if_pos (treeIn_lt d.trees p)]
    exact h1
  | d :: ds, .inr q => by
    obtain ⟨s, h1, h2⟩ := leafAt_lt C ds q
    refine ⟨s, ?_, h2⟩
    show (if d.trees.length + treeAt C ds q < d.trees.length then _ else
      treeShT ds (d.trees.length + treeAt C ds q - d.trees.length)) = _
    rw [if_neg (by omega), Nat.add_sub_cancel_left]
    exact h1

/-! ## One stretch: the openings -/

section Stretch
variable (C : CK) (ds : List RDT)
  (opens : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p)))

/-- In the table of a position's tree, under its leaf: the position's opening, printed. -/
theorem rows_lookup (start : ByteArray) (p : OPos (uLT C ds)) :
    ((rowsOf C ds opens (treeAt C ds p)).map (Row.row3 start)).lookup (leafAt C ds p) =
      (opens p).map fun op => (colOfSym C ds p op.sym, leafSalt start (ownSalt op.salt),
        (op.path.map digToBytes).map bytesToDig) := by
  obtain ⟨s, hs, hx⟩ := leafAt_lt C ds p
  have hp : posAtST C ds (treeAt C ds p) (leafAt C ds p) = some p := posAtST_place C ds p
  unfold rowsOf
  rw [hs]
  show (((List.range (2 ^ s.a)).filterMap fun x =>
      (posAtST C ds (treeAt C ds p) x).bind fun q => (opens q).map fun op =>
        (⟨x, colOfSym C ds q op.sym, ownSalt op.salt, op.path.map digToBytes⟩ : Carrier.Row)).map
    (Row.row3 start)).lookup (leafAt C ds p) = _
  rw [lk_rows_mem start _ (fun y r hy => by
    obtain ⟨q, -, hq⟩ := Option.bind_eq_some_iff.1 hy
    obtain ⟨op, -, rfl⟩ := Option.map_eq_some_iff.1 hq
    rfl) _ _ (List.mem_range.2 hx), hp]
  show ((opens p).map _).map _ = _
  rw [Option.map_map]
  rfl

/-- **The typing's openings of one stretch are the string's**, where the tables hold, under each
tree's number over the file, the tree's printed rows, and the salts begin with start. -/
theorem opensT_back (base : ℕ) (start : ByteArray) (tabs : List (ℕ × List (ℕ × Row3)))
    (htab : ∀ n, n < (ds.map (·.trees.length)).sum →
      tabs.lookup (base + n) = some ((rowsOf C ds opens n).map (Row.row3 start)))
    (hs : ∀ q op, opens q = some op → SaltFrom start op.salt) (p : OPos (uLT C ds)) :
    opensT C ds base tabs p = opens p := by
  show atTT (symT' C ds p) tabs (base + treeAt C ds p) (leafAt C ds p) = _
  unfold atTT
  rw [htab _ (treeAt_lt C ds p)]
  show atT (symT' C ds p) _ (leafAt C ds p) = _
  unfold atT
  rw [rows_lookup]
  cases hf : opens p with
  | none => rfl
  | some op =>
    obtain ⟨sym, salt, path⟩ := op
    show (symT' C ds p (colOfSym C ds p sym)).map (fun y =>
      (⟨y, leafSalt start (ownSalt salt), (path.map digToBytes).map bytesToDig⟩ :
        Opening 256 (OSym (uLT C ds) p))) = _
    rw [symT'_colOfSym, saltFrom_back (hs p _ hf), digs_back]
    rfl

end Stretch

/-- **The stored table's openings come back.** -/
theorem stored_back (a : ℕ) (cfg : ByteArray) (ext : Fin (2 ^ a) → Option (Opening 256 SgX))
    (h : ∀ p op, ext p = some op → SaltFrom cfg op.salt ∧ op.sym.1 = p.val) (p : Fin (2 ^ a)) :
    atT (fun c => some (p.val, c)) ((storedOf a ext).map (Row.row3 cfg)) p.val = ext p := by
  unfold atT storedOf
  rw [lk_rows_mem cfg _ (fun y r hy => by
    by_cases hlt : y < 2 ^ a
    · rw [dif_pos hlt] at hy
      obtain ⟨op, -, rfl⟩ := Option.map_eq_some_iff.1 hy
      rfl
    · rw [dif_neg hlt] at hy
      cases hy) _ _ (List.mem_range.2 p.isLt), dif_pos p.isLt]
  cases hf : ext p with
  | none => rfl
  | some op =>
    obtain ⟨⟨s1, s2⟩, salt, path⟩ := op
    obtain ⟨hs, hp⟩ := h p _ hf
    have hp' : s1 = p.val := hp
    show some (⟨(p.val, s2), leafSalt cfg (ownSalt salt),
      (path.map digToBytes).map bytesToDig⟩ : Opening 256 SgX) = _
    rw [saltFrom_back hs, digs_back, hp']

/-! ## One stretch: plain parts and roots -/

/-- The plain parts of one stretch come back, whatever roots are laid in. -/
theorem plainsT_roundsOf (C : CK) : ∀ (ds : List RDT) (rts : List (Dig 256))
    (pl : Plains (uLT C ds)), plainsT C ds ((roundsOf C ds rts pl).map Round.out) = some pl
  | [], _, _ => rfl
  | d :: ds, rts, (pl, r) => by
    show (match PlainOf.ofGots d.items (itemsOf d.items ((rts.take d.trees.length).map digToBytes)
        (GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) pl)),
      plainsT C ds ((roundsOf C ds (rts.drop d.trees.length) r).map Round.out) with
      | some p, some r' => some (GPlain.mk d.entry.work p
          (GPlain.nonce (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) pl), r')
      | _, _ => none) = _
    rw [ofGots_itemsOf, plainsT_roundsOf C ds]
    show some (GPlain.mk d.entry.work _ _, r) = _
    rw [GPlain.mk_old_nonce]
    rfl

/-- The roots of one stretch come back, where each round has as many items "root" as trees and as
many roots are given as the stretch has trees. -/
theorem rootsT_roundsOf (C : CK) : ∀ (ds : List RDT) (rts : List (Dig 256))
    (pl : Plains (uLT C ds)), (∀ d ∈ ds, d.items.countP (· == .root) = d.trees.length) →
    rts.length = (ds.map (·.trees.length)).sum →
    ((roundsOf C ds rts pl).map Round.out).flatMap (fun r => _root_.Fmt.rootsOf r.vals) =
      rts.map digToBytes
  | [], rts, _, _, h => by
    have h0 : rts = [] := List.eq_nil_of_length_eq_zero h
    rw [h0]
    rfl
  | d :: ds, rts, (pl, r), hf, h => by
    have hd : d.items.countP (· == .root) = d.trees.length := hf d List.mem_cons_self
    have hs : rts.length = d.trees.length + (ds.map (·.trees.length)).sum := h
    have hl : ((rts.take d.trees.length).map digToBytes).length = d.trees.length := by
      rw [List.length_map, List.length_take]
      omega
    show _root_.Fmt.rootsOf (itemsOf d.items ((rts.take d.trees.length).map digToBytes) _) ++
      ((roundsOf C ds (rts.drop d.trees.length) r).map Round.out).flatMap
        (fun r => _root_.Fmt.rootsOf r.vals) = _
    rw [rootsOf_itemsOf _ _ _ (by rw [hd, hl]), hd, List.take_of_length_le (Nat.le_of_eq hl),
      rootsT_roundsOf C ds _ r (fun e he => hf e (List.mem_cons_of_mem _ he))
        (by rw [List.length_drop]; omega),
      ← List.map_append, List.take_append_drop]

/-- The same in the typing's own form. -/
theorem rootsT_back (C : CK) (ds : List RDT) (rts : List (Dig 256)) (pl : Plains (uLT C ds))
    (hf : ∀ d ∈ ds, d.items.countP (· == .root) = d.trees.length)
    (h : rts.length = (ds.map (·.trees.length)).sum) :
    OnBytes.Maker.rootsT ((roundsOf C ds rts pl).map Round.out) = rts := by
  unfold OnBytes.Maker.rootsT
  rw [rootsT_roundsOf C ds rts pl hf h, digs_back]

/-! ## The tests -/

/-- An entry of one stretch: its number and its chain. -/
theorem mem_treesOf {C : CK} {ds : List RDT} {chain base : ℕ}
    {opens : (p : OPos (uLT C ds)) → Option (Opening 256 (OSym (uLT C ds) p))}
    {t : Carrier.TreeRows} (h : t ∈ treesOf C ds chain base opens) :
    ∃ n, n < (ds.map (·.trees.length)).sum ∧ t.tree = base + n ∧ t.chain = chain := by
  unfold treesOf at h
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 h
  exact ⟨n, List.mem_range.1 hn, rfl, rfl⟩

theorem sender₁ (D : WholeD) {n : ℕ} (h : n < D.t₁) : senderOf D (0 + n) = 0 := by
  unfold senderOf
  rw [if_pos (by omega)]

theorem sender₂ (D : WholeD) {n : ℕ} (h : n < D.t₂) : senderOf D (D.t₁ + n) = 1 := by
  unfold senderOf
  rw [if_neg (by omega), if_pos (by omega)]

theorem sender₃ (D : WholeD) (n : ℕ) : senderOf D (D.t₁ + D.t₂ + n) = 2 := by
  unfold senderOf
  rw [if_neg (by omega), if_neg (by omega)]

/-- A proof string is its nine fields. -/
theorem bprf_eq {Y : Type} {E : ExtSpec} {Q : _root_.Iop.BatchInteractiveOracleProof Y E} (π : OneProtocolProof 256 Q)
    {a : Rom.Bits} {b : List (Dig 256)} {c : Plains Q.loc.shape}
    {d : (p : OPos Q.loc.shape) → Option (Opening 256 (OSym Q.loc.shape p))}
    {e : E.Pos → Option (Opening 256 E.Sym)} {f : Dig 256} {g : ℕ} {h : List (Dig 256)}
    {i : Rom.Bits} (ha : a = π.salt) (hb : b = π.roots) (hc : c = π.plains) (hd : d = π.opens)
    (he : e = π.ext) (hf : f = π.rtreq) (hg : g = π.slot) (hh : h = π.path) (hi : i = π.rsalt) :
    (⟨a, b, c, d, e, f, g, h, i⟩ : OneProtocolProof 256 Q) = π := by
  subst ha hb hc hd he hf hg hh hi
  rfl

/-! ## The whole file -/

section
variable (C : CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {Xi : Type}
  (silent : Xi → FrontMsg (List OnBytes.E) → JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  (run : Xi → View → View → View → Bool) (cfg root : ByteArray) (s : Params.LinBindingShape)
  (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)

local notation "𝔉" => carrierOf C D tF tJ t3 silent run root π

/-- The four fields on the binding tree fit the shape. -/
theorem slotFits_carrierOf (P : Printable C D tF tJ t3 silent run cfg s π) :
    File.slotFits s 𝔉 = true := by
  obtain ⟨sl, hsl, hr⟩ := P.rsalt
  show ((bitsToBytes (π.rsalt.take (π.rsalt.length - 64))).size == s.saltBytes &&
    (π.path.map digToBytes).length == s.logLeaves && 2 ^ π.path.length == 2 ^ s.logLeaves &&
    decide (π.slot < 2 ^ π.path.length)) = true
  rw [hr, slotSalt_rsOf, hsl, List.length_map, P.path, beq_self_eq_true, beq_self_eq_true,
    beq_self_eq_true, decide_eq_true P.slot]
  rfl

/-- Every entry has the number of a tree of the data. -/
theorem treesFit_carrierOf : File.treesFit D 𝔉 = true := by
  have e₁ : D.t₁ = (D.ds₁.map (·.trees.length)).sum := rfl
  have e₂ : D.t₂ = (D.ds₂.map (·.trees.length)).sum := rfl
  show ((treesOf C D.ds₁ 0 0 (op₁ C D tF tJ t3 silent run π) ++
    (treesOf C D.ds₂ 1 D.t₁ (op₂ C D tF tJ t3 silent run π) ++
      treesOf C D.ds₃ 2 (D.t₁ + D.t₂) (op₃ C D tF tJ t3 silent run π))).all
    fun t => decide (t.tree < treesIn D)) = true
  rw [List.all_eq_true]
  intro t ht
  rw [decide_eq_true_eq]
  unfold treesIn
  rcases List.mem_append.1 ht with h | h
  · obtain ⟨n, hn, e, -⟩ := mem_treesOf h
    omega
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨n, hn, e, -⟩ := mem_treesOf h
      omega
    · obtain ⟨n, hn, e, -⟩ := mem_treesOf h
      omega

/-- Every entry's chain is the data's. -/
theorem chainOff_carrierOf : File.chainOff D 𝔉 = none := by
  have e₁ : D.t₁ = (D.ds₁.map (·.trees.length)).sum := rfl
  have e₂ : D.t₂ = (D.ds₂.map (·.trees.length)).sum := rfl
  have hn : (treesOf C D.ds₁ 0 0 (op₁ C D tF tJ t3 silent run π) ++
      (treesOf C D.ds₂ 1 D.t₁ (op₂ C D tF tJ t3 silent run π) ++
        treesOf C D.ds₃ 2 (D.t₁ + D.t₂) (op₃ C D tF tJ t3 silent run π))).find?
      (fun t => t.chain != senderOf D t.tree) = none := by
    rw [List.find?_eq_none]
    intro t ht
    have key : t.chain = senderOf D t.tree := by
      rcases List.mem_append.1 ht with h | h
      · obtain ⟨n, hn, e, c⟩ := mem_treesOf h
        rw [e, c, sender₁ D (by omega)]
      · rcases List.mem_append.1 h with h | h
        · obtain ⟨n, hn, e, c⟩ := mem_treesOf h
          rw [e, c, sender₂ D (by omega)]
        · obtain ⟨n, hn, e, c⟩ := mem_treesOf h
          rw [e, c, sender₃ D n]
    rw [key, bne_self_eq_false]
    exact Bool.false_ne_true
  show ((treesOf C D.ds₁ 0 0 (op₁ C D tF tJ t3 silent run π) ++
      (treesOf C D.ds₂ 1 D.t₁ (op₂ C D tF tJ t3 silent run π) ++
        treesOf C D.ds₃ 2 (D.t₁ + D.t₂) (op₃ C D tF tJ t3 silent run π))).find?
      (fun t => t.chain != senderOf D t.tree)).map (fun t => t.tree) = none
  rw [hn]
  rfl

/-- **WHAT IS PRINTED COMES BACK.** -/
theorem toBPrfAt_carrierOf (hR : RootsFit D) (P : Printable C D tF tJ t3 silent run cfg s π) :
    File.toBPrfAt C D tF tJ t3 silent run 𝔉 cfg s
      (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1
      (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1
      (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1 = some π := by
  have e₁ : D.t₁ = (D.ds₁.map (·.trees.length)).sum := rfl
  have e₂ : D.t₂ = (D.ds₂.map (·.trees.length)).sum := rfl
  have hlen : π.roots.length = D.t₁ + D.t₂ + (D.ds₃.map (·.trees.length)).sum := P.roots
  obtain ⟨sl, hsl, hr⟩ := P.rsalt
  -- the six tests
  have t1 : File.sealBare 𝔉 = true := by
    show (match (roundsOf C D.ds₁ (π.roots.take D.t₁)
        (pls₁ (wholeDesc C D tF tJ t3 silent run) π).2 ++
        [(⟨[], 0⟩ : Carrier.Round)]).getLast? with
      | some r => r.items.isEmpty && r.nonce == 0
      | none => false) = true
    rw [List.getLast?_concat]
    rfl
  have t2 : ((𝔉).places == 2 ^ s.logLeaves) = true := by
    show (2 ^ π.path.length == 2 ^ s.logLeaves) = true
    rw [P.path, beq_self_eq_true]
  have t4 : plainsT C D.ds₁ ((𝔉).rounds1.map Round.out).dropLast =
      some (pls₁ (wholeDesc C D tF tJ t3 silent run) π).2 := by
    show plainsT C D.ds₁ ((roundsOf C D.ds₁ (π.roots.take D.t₁)
      (pls₁ (wholeDesc C D tF tJ t3 silent run) π).2 ++
      [(⟨[], 0⟩ : Carrier.Round)]).map Round.out).dropLast = _
    rw [List.map_append, List.map_singleton, List.dropLast_concat]
    exact plainsT_roundsOf C D.ds₁ _ _
  have t5 : plainsT C D.ds₂ ((𝔉).rounds2.map Round.out) =
      some (pls₂ (wholeDesc C D tF tJ t3 silent run) π).2 := plainsT_roundsOf C D.ds₂ _ _
  have t6 : plainsT C D.ds₃ ((𝔉).rounds3.map Round.out) =
      some (pls₃ (wholeDesc C D tF tJ t3 silent run) π).2 := plainsT_roundsOf C D.ds₃ _ _
  -- the roots
  have r1 : OnBytes.Maker.rootsT ((𝔉).rounds1.map Round.out) = π.roots.take D.t₁ := by
    have h0 := rootsT_back C D.ds₁ (π.roots.take D.t₁)
      (pls₁ (wholeDesc C D tF tJ t3 silent run) π).2
      (fun d hd => hR d (List.mem_append_left _ hd)) (by rw [List.length_take]; omega)
    show OnBytes.Maker.rootsT ((roundsOf C D.ds₁ (π.roots.take D.t₁)
      (pls₁ (wholeDesc C D tF tJ t3 silent run) π).2 ++
      [(⟨[], 0⟩ : Carrier.Round)]).map Round.out) = _
    unfold OnBytes.Maker.rootsT at h0 ⊢
    rw [List.map_append, List.flatMap_append, List.map_append, h0]
    exact List.append_nil _
  have r2 : OnBytes.Maker.rootsT ((𝔉).rounds2.map Round.out) = (π.roots.drop D.t₁).take D.t₂ :=
    rootsT_back C D.ds₂ _ _
      (fun d hd => hR d (List.mem_append_right _ (List.mem_append_left _ hd)))
      (by rw [List.length_take, List.length_drop]; omega)
  have r3 : OnBytes.Maker.rootsT ((𝔉).rounds3.map Round.out) = (π.roots.drop D.t₁).drop D.t₂ :=
    rootsT_back C D.ds₃ _ _
      (fun d hd => hR d (List.mem_append_right _ (List.mem_append_right _ hd)))
      (by rw [List.length_drop, List.length_drop]; omega)
  -- the openings
  obtain ⟨T₁, T₂, T₃⟩ := lk_three C D.ds₁ D.ds₂ D.ds₃ (op₁ C D tF tJ t3 silent run π)
    (op₂ C D tF tJ t3 silent run π) (op₃ C D tF tJ t3 silent run π)
    (fun t => t.rows.map (Row.row3 (File.runOf 𝔉 (senderOf D t.tree)))) D.t₁ D.t₂ rfl rfl
  have o1 : ∀ q, opensT C D.ds₁ 0 (File.tabs D 𝔉) q = op₁ C D tF tJ t3 silent run π q :=
    opensT_back C D.ds₁ _ 0 (bitsToBytes π.salt) _ (fun n hn => by
      have h0 := T₁ n hn
      rw [sender₁ D (by omega)] at h0
      exact h0) P.own₁
  have o2 : ∀ q, opensT C D.ds₂ D.t₁ (File.tabs D 𝔉) q = op₂ C D tF tJ t3 silent run π q :=
    opensT_back C D.ds₂ _ D.t₁ (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.run _
      (fun n hn => by
        have h0 := T₂ n hn
        rw [sender₂ D (by omega)] at h0
        exact h0) P.own₂
  have o3 : ∀ q, opensT C D.ds₃ (D.t₁ + D.t₂) (File.tabs D 𝔉) q =
      op₃ C D tF tJ t3 silent run π q :=
    opensT_back C D.ds₃ _ (D.t₁ + D.t₂) (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1 _
      (fun n hn => by
        have h0 := T₃ n hn
        rw [sender₃ D n] at h0
        exact h0) P.own₃
  -- the nine fields
  have f1 : bytesToBits (bitsToBytes π.salt) = π.salt :=
    bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨32, P.salt⟩)
  have f2 : OnBytes.Maker.rootsT ((𝔉).rounds1.map Round.out) ++
      (OnBytes.Maker.rootsT ((𝔉).rounds2.map Round.out) ++
        OnBytes.Maker.rootsT ((𝔉).rounds3.map Round.out)) = π.roots := by
    rw [r1, r2, r3, List.take_append_drop, List.take_append_drop]
  have f3 : Plains.app (s := (chainsOf C D tF tJ t3).c₁)
      (t := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃)
      (pls₁ (wholeDesc C D tF tJ t3 silent run) π)
      (Plains.app (s := (chainsOf C D tF tJ t3).c₂) (t := (chainsOf C D tF tJ t3).c₃)
        (pls₂ (wholeDesc C D tF tJ t3 silent run) π)
        (pls₃ (wholeDesc C D tF tJ t3 silent run) π)) = π.plains := by
    unfold pls₁ pls₂ pls₃
    rw [Plains.app_fst_snd, Plains.app_fst_snd]
  have b1 : behind tF (opensT C D.ds₁ 0 (File.tabs D 𝔉)) =
      opensL (s := (chainsOf C D tF tJ t3).c₁)
        (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) π.opens := by
    funext p
    rcases p with e | q
    · exact e.elim
    · exact o1 q
  have b2 : behind tJ (opensT C D.ds₂ D.t₁ (File.tabs D 𝔉)) =
      opensL (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
        (opensR (s := (chainsOf C D tF tJ t3).c₁)
          (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) π.opens) := by
    funext p
    rcases p with e | q
    · exact e.elim
    · exact o2 q
  have b3 : behind t3 (opensT C D.ds₃ (D.t₁ + D.t₂) (File.tabs D 𝔉)) =
      opensR (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
        (opensR (s := (chainsOf C D tF tJ t3).c₁)
          (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) π.opens) := by
    funext p
    rcases p with e | q
    · exact e.elim
    · exact o3 q
  have f4 : opensApp (s := (chainsOf C D tF tJ t3).c₁)
      (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃)
      (behind tF (opensT C D.ds₁ 0 (File.tabs D 𝔉)))
      (opensApp (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
        (behind tJ (opensT C D.ds₂ D.t₁ (File.tabs D 𝔉)))
        (behind t3 (opensT C D.ds₃ (D.t₁ + D.t₂) (File.tabs D 𝔉)))) = π.opens := by
    rw [b1, b2, b3]
    have i : opensApp (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
        (opensL (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
          (opensR (s := (chainsOf C D tF tJ t3).c₁)
            (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) π.opens))
        (opensR (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
          (opensR (s := (chainsOf C D tF tJ t3).c₁)
            (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) π.opens)) =
        opensR (s := (chainsOf C D tF tJ t3).c₁)
          (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) π.opens :=
      funext fun p => opensApp_LR (s := (chainsOf C D tF tJ t3).c₂)
        (u := (chainsOf C D tF tJ t3).c₃) _ p
    rw [i]
    exact funext fun p => opensApp_LR (s := (chainsOf C D tF tJ t3).c₁)
      (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) _ p
  have f5 : (fun p : Fin (2 ^ D.a) => atT (fun c => some (p.val, c))
      ((storedOf D.a π.ext).map (Row.row3 cfg)) p.val) = π.ext :=
    funext fun p => stored_back D.a cfg π.ext P.ext p
  have f9 : rsOf (2 ^ s.logLeaves + π.slot)
      (bitsToBytes (π.rsalt.take (π.rsalt.length - 64))) = π.rsalt := by
    rw [hr, slotSalt_rsOf]
  -- the typing
  unfold File.toBPrfAt
  rw [slotFits_carrierOf C D tF tJ t3 silent run cfg root s π P,
    treesFit_carrierOf C D tF tJ t3 silent run root π, Bool.and_self, if_pos rfl]
  unfold File.toBPrf
  rw [t1, t2, chainOff_carrierOf C D tF tJ t3 silent run root π, t4, t5, t6]
  exact congrArg some (bprf_eq π f1 f2 f3 f4 f5 (TieTree.bytes_dig π.rtreq) rfl
    (digs_back π.path) f9)

end

end OnBytes.Prover.Print

#print axioms OnBytes.Prover.Print.lk_rows_none
#print axioms OnBytes.Prover.Print.lk_rows_mem
#print axioms OnBytes.Prover.Print.lk_map_none
#print axioms OnBytes.Prover.Print.lk_map_mem
#print axioms OnBytes.Prover.Print.lk_treesOf_none
#print axioms OnBytes.Prover.Print.lk_treesOf_mem
#print axioms OnBytes.Prover.Print.lk_three
#print axioms OnBytes.Prover.Print.symIn_colT
#print axioms OnBytes.Prover.Print.symT'_colOfSym
#print axioms OnBytes.Prover.Print.leafIn_lt
#print axioms OnBytes.Prover.Print.leafAt_lt
#print axioms OnBytes.Prover.Print.rows_lookup
#print axioms OnBytes.Prover.Print.opensT_back
#print axioms OnBytes.Prover.Print.stored_back
#print axioms OnBytes.Prover.Print.plainsT_roundsOf
#print axioms OnBytes.Prover.Print.rootsT_roundsOf
#print axioms OnBytes.Prover.Print.rootsT_back
#print axioms OnBytes.Prover.Print.mem_treesOf
#print axioms OnBytes.Prover.Print.sender₁
#print axioms OnBytes.Prover.Print.sender₂
#print axioms OnBytes.Prover.Print.sender₃
#print axioms OnBytes.Prover.Print.bprf_eq
#print axioms OnBytes.Prover.Print.slotFits_carrierOf
#print axioms OnBytes.Prover.Print.treesFit_carrierOf
#print axioms OnBytes.Prover.Print.chainOff_carrierOf
#print axioms OnBytes.Prover.Print.toBPrfAt_carrierOf
