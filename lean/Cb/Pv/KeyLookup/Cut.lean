-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Cut.lean: how the «forests» of the library's house are cut into lookups with parts,
and what stands between such a lookup and the house. It imports no file of the program.

Why. The library's house for a witness file (Cb/Ld/LdWf.lean) numbers its lookups («forests») 0 …
P.n and keeps one masked claim a forest. Here forest a + i is part i of a lookup that starts at a.
The record P of the house stays a letter; this file says, in public data alone, which forests belong
together.
  `Cut P`         the lookups 0 … nL; the public record of each (`Pub`,
                  Cb/Pv/KeyLookup/Letters.lean);
                   where each lookup's bits are.
  `Cut.start`     the first forest of lookup l: start 0 = 0, start (l + 1) = start l + (number of
                   parts of l). `start_succ`, `start_mono`, `start_le`.
  `Cut.dat`       the data of the lookup with parts at lookup l, after the library's `Lks.asm`
                   (Cb/Ld/LdWfBlocks.lean): keys read the index's matrix; the bits' places (bAt) lie
                   in the messages' entries. The masks' places are no field of `Dat`: that they lie
                   there is asked where they are named (`SuppN` below).
  `Cut.OK`        four conditions on public data: the parts fill the forests; bits, rows and table
                   of a part are its lookup's.
  `rideM`         what rides past a lookup: the library's `rideL` (Cb/Ld/LdWfBlocksProofs.lean) with
                   two numbers: all is done below a; the forests from a + m on lie in their tables.
  `pullOut`       a read-out, its forms pulled back onto the named entries (after rdN,
                   Cb/Ld/LdLkpAsm2Pull.lean). `SuppN`: the forms read named entries alone.
Under: nothing: definitions, and three lemmas on `start`. Does not say: that a Cut with OK exists
for a given P; anything on Know.

-/
import Cb.Ld.LdWfBlocksProofs    -- keyE, rideL
import Cb.Ld.LdLkpSuppProofs     -- SuppIn, RowsSupp, MCl.pull, Row.pull
import Cb.Pv.KeyLookup.AsmForm       -- Pub, Dat
import Cb.Pv.KeyLookup.FileUp        -- OutN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.LdWfP

variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} (P : LdWfP E C)

/-- How the forests are cut into lookups: public. P stays a letter. -/
structure Cut where
  nL  : ℕ                       -- the lookups 0, …, nL
  S   : ℕ → Pub                 -- Cb/Pv/KeyLookup/Letters.lean
  bAt : ℕ → ℕ → ℕ → P.N        -- where the bit (row u, plane j) of lookup l is
namespace Cut
variable {P} (K : Cut P)
def start : ℕ → ℕ
  | 0 => 0
  | l + 1 => start l + (K.S l).m
/-- The data of the lookup with parts at lookup l: after Lks.asm (Cb/Ld/LdWfBlocks.lean). -/
@[reducible] noncomputable def dat (l : ℕ) : Dat E :=
  { K.S l with
    St := P.WSt, J := P.bt.J, decJ := Classical.decEq _
    key := fun _ μ i => P.keyE (K.start l + i) fun rc => μ (Sum.inl rc)
    tab := fun _ => P.tab (K.start l)
    bAt := fun u j => Sum.inr (K.bAt l u j) }
/-- The conditions, all on public data: after Lks.OK (Cb/Ld/LdWfBlocks.lean). For Know alone these
four. -/
structure OK : Prop where
  n   : K.start (K.nL + 1) = P.n + 1
  v   : ∀ l, l ≤ K.nL → ∀ i, i < (K.S l).m → P.v (K.start l + i) = (K.S l).v i
  d   : ∀ l, l ≤ K.nL → ∀ i, i < (K.S l).m → P.d (K.start l + i) = (K.S l).d
  tab : ∀ l, l ≤ K.nL → ∀ i, i < (K.S l).m → P.tab (K.start l + i) = P.tab (K.start l)
theorem start_succ (l : ℕ) : K.start (l + 1) = K.start l + (K.S l).m := rfl
theorem start_mono {l k : ℕ} (h : l ≤ k) : K.start l ≤ K.start k := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_add_right _ _)
theorem start_le (h : K.OK) {l : ℕ} (hl : l ≤ K.nL) : K.start (l + 1) ≤ P.n + 1 :=
  h.n ▸ K.start_mono (Nat.succ_le_succ hl)
end Cut

/-- The library's rideL (Cb/Ld/LdWfBlocksProofs.lean) with two indices. -/
def rideM (a m : ℕ) : Rels Unit P.WSt C.E0 ((C.Msg × P.S.Msg) × Unit) where
  rel  := fun st _ w =>
    (P.Done a st w.1.1 w.1.2 ∧ ∀ f, a + m ≤ f → f ≤ P.n → P.InT f w.1.1) ∧
    ∀ f, a + m ≤ f → f ≤ P.n → P.mult f w.1.1 (P.body w.1.2)
  relR := fun x w => P.Done a x.1 w.1.1 w.1.2 ∧ ∀ f, a + m ≤ f → f ≤ P.n → P.InT f w.1.1
  on   := fun _ => True
  core := fun _ => ()

/-- The read-out on the named entries: after rdN (Cb/Ld/LdLkpAsm2Pull.lean). -/
def pullOut {St J N : Type} {m : ℕ} (ι : N → J) (o : St × (Fin m → MCl E J) × List (Row E J)) :
    OutN St E N m :=
  (o.1, fun i => (o.2.1 i).pull ι, o.2.2.map (Row.pull ι))

/-- the forms read named entries alone -/
def SuppN {m : ℕ} (o : P.WSt × (Fin m → MCl E P.bt.J) × List (Row E P.bt.J)) : Prop :=
  RowsSupp (fun j => j ∈ Set.range (Sum.inr : P.N → P.bt.J)) o.2.2 ∧
  ∀ i, SuppIn (fun j => j ∈ Set.range (Sum.inr : P.N → P.bt.J)) (o.2.1 i).mf


end Lk6

#print axioms Lk6.Cut.start_le
