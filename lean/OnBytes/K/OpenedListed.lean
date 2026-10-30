-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/OpenedListed.lean: at a chain that the strict reader has read, every position of the two
stored tables that the written link reads is listed in a stored opening of its table.



OnBytes/TypedOracleCompiler/Slice/EntryOpened.lean shows that the checks for the external trees are there at the
entry's typed string (`assembleS_ext`), from `ListedX`: a read position is listed in a stored
opening of its table, whose lists of columns and salts have the length of its list of places. That
file leaves `ListedX` open at a yes of the reader. Here it is shown from what a reading gives, cut
in parts: the rounds as read are rounds with the stored tables' openings joined in front (`roundWithStoredOpenings`),
and each such opening has `StoredFact` (OnBytes/Tie/StoredRead.lean). For proofs only; the program
does not import this file.

Main theorems.
 `listedX_parts` `ListedX D D.a` of the stored openings of `opsOf 1 o`, at every test "read" that
    holds only of members of the written link's external reads at verifier messages ρ. Asked: o's
    rounds are rc with the stored openings joined in; each of these has `StoredFact`; the own part
    is within the limits of OnBytes/TypedOracleCompiler; oo, the chain without the stored openings and the vertices
    met, has `LaxFacts`; all tables have the depth `D.a` and a form marked as stored; what ρ draws
    is what the reader drew.
 `listedX_read`   the same from one yes of `Fmt.readChainX` under a description S, at the hash over
    any function O, by `read_parts` (OnBytes/K/OpenedRead.lean).
In both the typed side's description D and the reader's may differ in their statements: they are
asked to have the same stored tables and the same rounds' data.
Helpers: `listed_zip`, `listed_zipIdx`, `listed_op`.

The road. What the drawn positions ask of the two tables is what the openings list
(`xWanted_asked`, OnBytes/TypedOracleCompiler/Run/StoredGlue.lean); the openings are those of rc, round by round
(`sto_eq`); an opening number k of round number i of rc is the opening number k of round number i of
o, because the stored openings stand first in a round.

What is not claimed. That what ρ draws is what the reader drew: that is the chain's half. Nothing on
the chain's own trees. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Slice.EntryOpened
import OnBytes.K.OpenedRead
import OnBytes.Tie.StoredView

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Run.PQ (View SgX xPos LaxFacts stripR)
open _root_.Run (OpenB HId)
open OnBytes.Tie (roundWithStoredOpenings StoredFact askedOf stoOf)

/-- A member of a zip stands at one place in both lists. -/
theorem listed_zip {α β : Type} : ∀ (l₁ : List α) (l₂ : List β) (a : α) (b : β),
    (a, b) ∈ l₁.zip l₂ → ∃ k : ℕ, l₁[k]? = some a ∧ l₂[k]? = some b
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: l₁, y :: l₂, a, b, h => by
      rw [List.zip_cons_cons] at h
      rcases List.mem_cons.1 h with e | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
        exact ⟨0, rfl, rfl⟩
      · obtain ⟨k, h1, h2⟩ := listed_zip l₁ l₂ a b h
        exact ⟨k + 1, by simpa using h1, by simpa using h2⟩

/-- The member at place k stands with the number n + k in the list numbered from n on. -/
theorem listed_zipIdx {α : Type} : ∀ (l : List α) (n k : ℕ) (a : α), l[k]? = some a →
    (a, n + k) ∈ l.zipIdx n
  | [], _, _, _, h => by simp at h
  | x :: l, n, 0, a, h => by
      obtain rfl : x = a := by simpa using h
      rw [List.zipIdx_cons]
      exact List.mem_cons_self
  | x :: l, n, k + 1, a, h => by
      rw [List.zipIdx_cons, show n + (k + 1) = n + 1 + k by omega]
      exact List.mem_cons_of_mem _ (listed_zipIdx l (n + 1) k a (by simpa using h))

/-- The opening number k of round number i of a chain stands in `opsOf`. -/
theorem listed_op (o : _root_.Fmt.ChainOut) (i k : ℕ) (r : _root_.Fmt.RoundOut)
    (y : _root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut) (hr : o.rounds.toList[i]? = some r)
    (hy : r.opens[k]? = some y) : (⟨1, i, k, y.1, y.2.1, y.2.2⟩ : OpAt) ∈ opsOf 1 o := by
  unfold opsOf
  refine List.mem_flatMap.2 ⟨(r, i), ?_, List.mem_map.2 ⟨(y, k), ?_, rfl⟩⟩
  · have := listed_zipIdx o.rounds.toList 0 i r hr
    rwa [Nat.zero_add] at this
  · have := listed_zipIdx r.opens 0 k y hy
    rwa [Nat.zero_add] at this

section
variable {X : Type} (h : HId) (D D' : XD) (dec : X → View → Bool) (o oo : _root_.Fmt.ChainOut)
  (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))

/-- Every read position of the two tables is listed in a stored opening of its table. -/
theorem listedX_parts (hsto : D'.stored = D.stored) (hds : D'.ds = D.ds)
    (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
    (hS : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
        (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
      List.Forall₂ (StoredFact h D'.base.cfg D'.base.statement p.1.drawn.poss) ts p.2) D'.stored rc)
    (hok : PQ.ok D'.base = true) (hL : LaxFacts h D'.base oo)
    (hoo : oo.rounds.toList = rc.map fun p => stripR p.1)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a)
    (hst : ∀ s ∈ D.stored.flatten, s.sh.stored = true) (x : X)
    (ρ : Rho (_root_.Run.Twin.up (PQ.SOf D.C D.ds)))
    (hd : PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn))
    (isReadE : Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a) → Bool)
    (hread : ∀ p, isReadE p = true → p ∈ (PSXE D dec).extReads x ρ) :
    ListedX D D.a ((opsOf 1 o).filter fun op => op.sh.stored) isReadE := by
  intro p hp
  have hp' : p ∈ ((PQ.xWanted D.a D.ds D.xs (PQ.drawnSL D.C D.ds ρ.2)).filterMap
      (xPos (2 ^ D.a))).toFinset := hread p hp
  have hdr : o.rounds.toList.map (·.drawn) = oo.rounds.toList.map (·.drawn) := by
    rw [ho, hoo, List.map_map, List.map_map]
    rfl
  have ha : D'.a = D.a := by
    unfold XD.a
    rw [hsto]
  have hxs : D'.xs = D.xs := by
    unfold XD.xs
    rw [hsto]
  have key : PQ.xWanted D.a D.ds D.xs (oo.rounds.toList.map (·.drawn)) =
      askedOf (stoOf D.stored rc) := by
    have k := PQ.xWanted_asked h D' o rc ho hS hok oo hL hoo fun s hs => by
      rw [ha]
      exact hD s (hsto ▸ hs)
    rw [PQ.sto_eq h D' o rc ho hS, ha, hds, hxs, hsto] at k
    exact k
  rw [hsto] at hS
  rw [hd, hdr, key] at hp'
  obtain ⟨wx, hwx, hpos⟩ := List.mem_filterMap.1 (List.mem_toFinset.1 hp')
  obtain ⟨e, he, hx⟩ := List.mem_flatMap.1 hwx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  obtain ⟨y, hy, hey⟩ := List.mem_flatMap.1 he
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hey
  obtain ⟨ts, pr⟩ := y
  obtain ⟨t, c⟩ := w
  obtain ⟨i, hi1, hi2⟩ := listed_zip _ _ _ _ hy
  obtain ⟨k, hk1, hk2⟩ := listed_zip _ _ _ _ hw
  have F : StoredFact h D'.base.cfg D'.base.statement pr.1.drawn.poss t c :=
    OnBytes.Tie.forall₂_zip (OnBytes.Tie.forall₂_zip hS (ts, pr) hy) (t, c) hw
  have htm : t ∈ D.stored.flatten :=
    List.mem_flatten.2 ⟨ts, List.mem_of_getElem? hi1, List.mem_of_getElem? hk1⟩
  have hr : o.rounds.toList[i]? = some (roundWithStoredOpenings pr) := by
    rw [ho, List.getElem?_map, hi2]
    rfl
  have hc : (roundWithStoredOpenings pr).opens[k]? = some c := by
    show (pr.2 ++ pr.1.opens)[k]? = some c
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk2).1]
    exact hk2
  obtain ⟨q1, q2⟩ := OnBytes.Tie.xPos_some _ _ _ _ hpos
  have hokb := F.okb
  simp only [OpenB.ok, Bool.and_eq_true, beq_iff_eq] at hokb
  refine ⟨⟨1, i, k, c.1, c.2.1, c.2.2⟩, List.mem_filter.2 ⟨listed_op o i k _ c hr hc, ?_⟩, ?_, ?_,
    hokb.1.1.1.1.1.2, hokb.1.1.1.1.2⟩
  · show c.1.stored = true
    rw [F.sh]
    exact hst t htm
  · show (match (D.stored[i]?).bind (·[k]?) with
      | some t => if t.item == 1 then 1 else 0
      | none => 0) = _
    rw [hi1]
    show (match ts[k]? with
      | some t => if t.item == 1 then 1 else 0
      | none => 0) = _
    rw [hk1]
    cases p with
    | inl _ =>
      have q1' : false = (t.item == 1) := q1
      show (if (t.item == 1) = true then 1 else 0) = 0
      rw [← q1']
      rfl
    | inr _ =>
      have q1' : true = (t.item == 1) := q1
      show (if (t.item == 1) = true then 1 else 0) = 1
      rw [← q1']
      rfl
  · have e2 : (Sum.elim id id p : Fin (2 ^ D.a)).val = z := by
      cases p <;> exact q2
    rw [e2]
    exact hz

end

/-- The same from one yes of the strict reader, at the hash over any function O. D is the typed
side's description; S is the description under which the chain was read. Asked: S lists D's stored
tables; its rounds' data are D's; its own part, the random bytes counted as standing in the file, is
within the limits of OnBytes/TypedOracleCompiler; the chain has random bytes; all tables have the depth `D.a`. The
two descriptions may differ in their statements. -/
theorem listedX_read {X : Type} (D : XD) (dec : X → View → Bool) (S : _root_.Fmt.SpecX)
    (O : ByteArray → ByteArray) (hsto : S.stored = D.stored)
    (hds : PQ.rds (PQ.inFile S.base) = D.ds) (hokb : PQ.ok (PQ.inFile S.base) = true)
    (hn : S.base.rand.isNone = false) (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a)
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S seen b i = some (o, j)) (x : X)
    (ρ : Rho (_root_.Run.Twin.up (PQ.SOf D.C D.ds)))
    (hd : PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn))
    (isReadE : Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a) → Bool)
    (hread : ∀ p, isReadE p = true → p ∈ (PSXE D dec).extReads x ρ) :
    ListedX D D.a ((opsOf 1 o).filter fun op => op.sh.stored) isReadE := by
  obtain ⟨hSok, R, rho0, rc, -, -, g1, hL, -, -, -, hF⟩ := PQ.read_parts S O hokb hn seen b i o j e
  exact listedX_parts (_root_.Fmt.HO O) D (PQ.xdOf S D.stm) dec o
    (PQ.ownOut o.pd R rho0 o.rho rc) rc hsto hds g1 hF hokb hL (by simp [PQ.ownOut]) hD
    (fun t ht => (PQ.specX_shape S hSok t (hsto ▸ ht)).1) x ρ hd isReadE hread

end TypedOracleCompiler.Slice
