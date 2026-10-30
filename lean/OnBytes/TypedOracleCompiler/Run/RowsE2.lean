-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/RowsE2.lean: THE ROW LAW OF AN ENTRY's WRITTEN ROUNDS, BY RECURSION ALONG THE
ROUNDS' DATA, IN ChainFrom.lean's LETTERS: `PQ.RowEnd` (OnBytes/TypedOracleCompiler/Run/ChainFrom.lean) at the
family that the entry's page makes of one oracle, with THE WAY from the skeleton's plain parts
(annotation `Twin.allLo`) into the plain parts of the entry's interface under the tag of Link
(annotation `RoundSplits.allLocal`).

WHY. The walk of a typed chain through a stretch of written rounds (ChainFrom.lean's `chain_end_lo`)
is stated over a skeleton `SL C ds` with the annotation `Twin.allLo`, and takes the family's law
`PQ.RowEnd` as a hypothesis, "by recursion along ds over embP". The entry's interface (`LXE`,
OnBytes/TypedOracleCompiler/Slice/EntryX.lean) has, under the tag of Link, the same shape with the annotation
`RoundSplits.allLocal`. The two annotations are not one by unfolding at a variable list
(OnBytes/TypedOracleCompiler/Run/PageEBack.lean). OnBytes/TypedOracleCompiler/Run/RowsE.lean has the law at each round by its
number, at the page's own way `inE`. Here the two are joined.

 - `toL C ds`: THE WAY: a plain part of some written round under `allLo` as one under `allLocal`:
   summand by summand the identity; `toL_cast`: it is the cast along `PageEBack.pbl_is`;
 - `inA C ds k`: the plain part of round k among those of all written rounds, under `allLo`;
   `toL_inA`: the way carries it to `PlainIn.inLast`;
 - `rowEnd_of_get`: GENERAL, for any interface, family and way: `PQ.RowEnd` from `PQ.RowAt` at every
   round by its number;
 - `wayE`: the way of the whole skeleton's plain parts (the silent front, then the written rounds)
   into the interface's; `wayE_front`: the front's point goes to the page's `p0E`;
 - `toL_pbTo`, `wayE_pbTo`: the way IS OnBytes/TypedOracleCompiler's carrying `pbTo` along the equation
   `Twin.allLo_eq` between the two markings: `embPXE` (OnBytes/TypedOracleCompiler/Slice/EntryPS.lean) is that term;
   `wayB`, `wayE_eq`; `rowEndB`, `s0B`: the two laws through that way;
 - `FitsE D`: what is asked of the description's rounds: no more than 64 bits of work; work, or not
   sealed; as many trees as root items;
 - `rowEndE` : PQ.RowEnd (fun _ => Le D early e) D.C K (famE P dd (K + 1) V back g) .link (oB (g
   ())) P.l D.ds (fun z => wayE D early e (.inr z)) 1 1, for every oracle g;
 - `s0E`: the first query's law in the same letters: the tail at
   `⟨0, .f1 [r₀, r₁] (some ((a₀, a₁), dd)) salt, [], wayE … (.inl (.inr ()))⟩` is the chain's first
     value.

Main definitions: `toL`, `inA`, `wayE`, `FitsE`.
Main theorems: `toL_cast`, `toL_inA`, `wayE_pbTo`, `rowEnd_of_get`, `rowEndE`, `s0E`, `rowEndB`,
`s0B`.

WHAT IS NOT SAID. A SEALED ROUND WITHOUT WORK IS SHUT OUT (`FitsE`): there the page lays the tail
on the row's block 1 (`RowsE.rowE_sealTail`). That the description's rounds meet `FitsE`. The walk
itself.
What the heads of RowsE.lean and ChainFrom.lean do not say. Nothing on soundness. The sibling is a
second form of the library's soundness road, under OnBytes/TypedOracleCompiler/.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.RowsE
import OnBytes.TypedOracleCompiler.Run.PageEBack

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.RowsE2
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.RowsG
open TypedOracleCompiler.Run.RowsE TypedOracleCompiler.Run.PlainIn
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-! ## The way -/

/-- The plain parts of written local rounds, under the skeleton's annotation. -/
abbrev PA (C : _root_.Run.PQ.CK) (ds : List PQ.RD) : Type :=
  PlainPart (PQ.uL C ds) (_root_.Run.Twin.allLo (PQ.SL C ds))

/-- THE WAY: summand by summand the identity. -/
def toL (C : _root_.Run.PQ.CK) : (ds : List PQ.RD) → PA C ds → PQ.PBL C ds
  | [], z => z
  | _ :: _, .inl x => .inl x
  | _ :: ds, .inr z => .inr (toL C ds z)

/-- A cast along an equation of right summands goes under the right injection, and leaves a left
injection alone. -/
theorem cast_sum {A B B' : Type} (h : B = B') :
    (∀ a : A, cast (congrArg (fun T => A ⊕ T) h) (.inl a) = .inl a) ∧
      ∀ b : B, cast (congrArg (fun T => A ⊕ T) h) (.inr b) = .inr (cast h b) := by
  subst h
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- It is the cast along the equation of the two types. -/
theorem toL_cast (C : _root_.Run.PQ.CK) : ∀ (ds : List PQ.RD) (z : PA C ds),
    toL C ds z = cast (PageEBack.pbl_is C ds).symm z
  | [], _ => rfl
  | _ :: ds, .inl x => ((cast_sum (PageEBack.pbl_is C ds).symm).1 x).symm
  | _ :: ds, .inr z => by
      show Sum.inr (toL C ds z) = _
      rw [toL_cast C ds z]
      exact ((cast_sum (PageEBack.pbl_is C ds).symm).2 z).symm

/-- The plain part z of round k of written rounds ds, under the skeleton's annotation. -/
def inA (C : _root_.Run.PQ.CK) : (ds : List PQ.RD) → (k : Fin ds.length) →
    PlainD (ds.get k) → PA C ds
  | _ :: _, ⟨0, _⟩, z => .inl (.inr z)
  | _ :: ds, ⟨k + 1, h⟩, z => .inr (inA C ds ⟨k, Nat.lt_of_succ_lt_succ h⟩ z)

/-- The way carries it to the page's own. -/
theorem toL_inA (C : _root_.Run.PQ.CK) :
    ∀ (ds : List PQ.RD) (k : Fin ds.length) (z : PlainD (ds.get k)),
      toL C ds (inA C ds k z) = inLast C ds k z
  | _ :: _, ⟨0, _⟩, _ => rfl
  | _ :: ds, ⟨k + 1, h⟩, z => congrArg Sum.inr (toL_inA C ds ⟨k, Nat.lt_of_succ_lt_succ h⟩ z)

/-! ## From the law at every round by its number to the law by recursion -/

/-- GENERAL: ChainFrom.lean's law by recursion along the rounds' data, from its law at every round
by the round's number. -/
theorem rowEnd_of_get {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (C : _root_.Run.PQ.CK) (K : ℕ)
    (f : Fam (typedOracleFamily 256 (K + 1) (Lf ()))) (t : Tag) (O : ByteArray → ByteArray) (lab : ℕ) :
    ∀ (ds : List PQ.RD) (embP : PA C ds → PlainPart (shapeOf (Lf ()) t) (annOf (Lf ()) t)) (i n : ℕ),
      (∀ k : Fin ds.length, PQ.RowAt Lf C K f t O lab (fun ρ => .f2 none ρ) (ds.get k)
        (fun pl => embP (inA C ds k pl)) (i + k.val) (n + k.val)) →
      PQ.RowEnd Lf C K f t O lab ds embP i n
  | [], _, _, _, _ => trivial
  | d :: ds, embP, i, n, h =>
    ⟨h ⟨0, Nat.succ_pos _⟩, rowEnd_of_get Lf C K f t O lab ds (fun z => embP (.inr z))
        (i + 1) (n + 1)
      fun k => by
        have h' := h ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
        rw [show i + 1 + k.val = i + (k.val + 1) by omega,
          show n + 1 + k.val = n + (k.val + 1) by omega]
        exact h'⟩

/-! ## At the entry's page -/

variable {Sd : Type} (D : XD)
  (early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd) (e : _root_.Fmt.Entry)

/-- The way of the whole skeleton's plain parts into the interface's, under the tag of Link: the
silent front's summand as it is; then `toL`. -/
def wayE : PlainPart (_root_.Run.Twin.up (PQ.SOf D.C D.ds)) (_root_.Run.Twin.allLo (PQ.SOf D.C D.ds)) →
    PlainPart (shE D early e) (annOf (Le D early e) .link)
  | .inl x => .inl x
  | .inr z => .inr (toL D.C D.ds z)

/-- The front's point goes to the page's. -/
theorem wayE_front : wayE D early e (.inl (.inr ())) = p0E D early e := rfl

/-- The way on the written rounds' plain parts is the carrying along the equation between the two
markings (`pbTo`, OnBytes/TypedOracleCompiler/Run/WireX.lean). -/
theorem toL_pbTo (C : _root_.Run.PQ.CK) : ∀ (ds : List PQ.RD) (q : PA C ds),
    toL C ds q = PQ.pbTo (_root_.Run.Twin.allLo_eq (PQ.SL C ds)) q
  | [], q => q.elim
  | _ :: ds, .inl x => (PQ.pbTo_inl _ (_root_.Run.Twin.allLo_eq (PQ.SL C ds)) _ x).symm
  | _ :: ds, .inr q =>
    (congrArg Sum.inr (toL_pbTo C ds q)).trans
      (PQ.pbTo_inr _ (_root_.Run.Twin.allLo_eq (PQ.SL C ds)) _ q).symm

/-- The whole way is the carrying along the equation between the two markings of the whole shape:
`embPXE` (OnBytes/TypedOracleCompiler/Slice/EntryPS.lean) is that term. -/
theorem wayE_pbTo
    (z : PlainPart (_root_.Run.Twin.up (PQ.SOf D.C D.ds)) (_root_.Run.Twin.allLo (PQ.SOf D.C D.ds))) :
    wayE D early e z = PQ.pbTo (_root_.Run.Twin.allLo_eq (PQ.SOf D.C D.ds)) z := by
  cases z with
  | inl x => exact (PQ.pbTo_inl _ (_root_.Run.Twin.allLo_eq (PQ.SL D.C D.ds)) _ x).symm
  | inr q =>
    exact (congrArg Sum.inr (toL_pbTo D.C D.ds q)).trans
      (PQ.pbTo_inr _ (_root_.Run.Twin.allLo_eq (PQ.SL D.C D.ds)) _ q).symm

/-- What is asked of the description's rounds. -/
structure FitsE (D : XD) : Prop where
  /-- no round has more than 64 bits of work -/
  work : ∀ d ∈ D.ds, d.entry.work ≤ 64
  /-- a round has work, or is not sealed -/
  plain : ∀ d ∈ D.ds, d.entry.work ≠ 0 ∨ d.kind ≠ .sealed
  /-- each round has as many trees as root items -/
  roots : ∀ d ∈ D.ds, d.trees.length = _root_.Fmt.countItem .root d.items
  /-- the rounds' numbers fit a word -/
  few : D.ds.length + 1 < 2 ^ 64

variable {D early e} (P : PinsE D early e) (dd : Sd) (K : ℕ) (V : Leaves (Le D early e))
  (back : StrCode (AllPts 256 (K + 1) (Le D early e))) (g : Fam (rom 256))

/-- THE ROW LAW OF THE ENTRY's WRITTEN ROUNDS, IN ChainFrom.lean's LETTERS, AT THE PAGE: at the
pins' label, from the typed round 1 and the format's index 1 on, through the way behind the front.
-/
theorem rowEndE (F : FitsE D) (hK : K + 1 < 2 ^ 48) :
    PQ.RowEnd (fun _ : Unit => Le D early e) D.C K (famE P dd (K + 1) V back g) .link (oB (g ()))
      P.l D.ds (fun z => wayE D early e (.inr z)) 1 1 :=
  rowEnd_of_get _ D.C K _ .link _ P.l D.ds _ 1 1 fun k => by
    have hm : D.ds.get k ∈ D.ds := List.get_mem D.ds k
    have h := rowE_at P dd K V back g hK k (by have := k.isLt; have := F.few; omega)
      (Nat.lt_of_le_of_lt (F.work _ hm) (by omega)) (F.plain _ hm) (F.roots _ hm)
    have ee : (fun pl => wayE D early e (.inr (inA D.C D.ds k pl))) = inE D early e k :=
      funext fun pl => congrArg Sum.inr (toL_inA D.C D.ds k pl)
    rw [ee, Nat.add_comm 1 k.val]
    exact h

/-- THE FIRST QUERY's LAW, IN THE SAME LETTERS: the tail is the chain's first value. -/
theorem s0E (r₀ r₁ : Dig 256) (a₀ a₁ : List T3) (salt : List Bool) (h₀ : a₀.length < 2 ^ 32)
    (h₁ : a₁.length < 2 ^ 32) (hl : salt = [] ∨ salt.length = 256) :
    (famE P dd (K + 1) V back g (.fb .link)
        ⟨0, .f1 [r₀, r₁] (some ((a₀, a₁), dd)) salt, [], wayE D early e (.inl (.inr ()))⟩ :
        (Fin (K + 1) → Dig 256) × Dig 256).2 =
      bytesToDig (Id.run (_root_.Fmt.firstValueW (m := Id) (hOfG g) P.l (digToBytes P.pd)
        (_root_.Fmt.tableItem "the first table" (digToBytes r₀) a₀ ++
          _root_.Fmt.tableItem "the further table" (digToBytes r₁) a₁)
        ByteArray.empty (runOf salt))) :=
  rowE_first P dd (K + 1) V back g r₀ r₁ a₀ a₁ salt h₀ h₁ hl

/-- The way as OnBytes/TypedOracleCompiler/Slice/EntryPS.lean has it: the carrying along the equation between the
two markings. -/
def wayB (D : XD) (early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd)
    (e : _root_.Fmt.Entry) :
    PlainPart (_root_.Run.Twin.up (PQ.SOf D.C D.ds)) (_root_.Run.Twin.allLo (PQ.SOf D.C D.ds)) →
      PlainPart (shE D early e) (annOf (Le D early e) .link) :=
  PQ.pbTo (_root_.Run.Twin.allLo_eq (PQ.SOf D.C D.ds))

/-- The two ways are one. -/
theorem wayE_eq : wayE D early e = wayB D early e := funext (wayE_pbTo D early e)

/-- The row law through EntryPS.lean's way. -/
theorem rowEndB (F : FitsE D) (hK : K + 1 < 2 ^ 48) :
    PQ.RowEnd (fun _ : Unit => Le D early e) D.C K (famE P dd (K + 1) V back g) .link (oB (g ()))
      P.l D.ds (fun z => wayB D early e (.inr z)) 1 1 := by
  rw [← wayE_eq]
  exact rowEndE P dd K V back g F hK

/-- The first query's law through EntryPS.lean's way. -/
theorem s0B (r₀ r₁ : Dig 256) (a₀ a₁ : List T3) (salt : List Bool) (h₀ : a₀.length < 2 ^ 32)
    (h₁ : a₁.length < 2 ^ 32) (hl : salt = [] ∨ salt.length = 256) :
    (famE P dd (K + 1) V back g (.fb .link)
        ⟨0, .f1 [r₀, r₁] (some ((a₀, a₁), dd)) salt, [], wayB D early e (.inl (.inr ()))⟩ :
        (Fin (K + 1) → Dig 256) × Dig 256).2 =
      bytesToDig (Id.run (_root_.Fmt.firstValueW (m := Id) (hOfG g) P.l (digToBytes P.pd)
        (_root_.Fmt.tableItem "the first table" (digToBytes r₀) a₀ ++
          _root_.Fmt.tableItem "the further table" (digToBytes r₁) a₁)
        ByteArray.empty (runOf salt))) := by
  rw [← wayE_eq]
  exact s0E P dd K V back g r₀ r₁ a₀ a₁ salt h₀ h₁ hl

end TypedOracleCompiler.Run.RowsE2
