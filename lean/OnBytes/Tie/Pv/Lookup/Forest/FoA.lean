-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoA.lean: a value of the assembled lookup's record of letters (LkAsmH,
Cb/Pv/Lookup/Asm/AsmH.lean), built from the public numbers of the lookup that the sub-proofs'
verifier runs (OnBytes/Model/Look.lean, OnBytes/Model/Forest.lean).

forA E h L : LkAsmH E is a builder from the verifier's own record of public numbers h :
OnBytes.Model.Forest.Shape (pub filled in) and the caller's layout L. Sizes, cells, padding and mask
places are read from OnBytes/Tie/Pv/Lookup/Port/FoNums.lean, which reads h's fields; the joint
vectors are Port.key and Port.tab (OnBytes/Tie/Pv/Lookup/Port/ShiftQPort.lean); the orders are
E3.ordKeys and E3.ordDefault (Cb/Pv/Lookup/Order/E3Ord.lean). forA is total in h; it is meant for an
h with FoNums.ok h = true.
 - Lay E St₀ J₀, the caller's layout: K (call c's key vector, its own padding places in it; any
   function of the entries), bc (the entry of bit j of the count of row t of call c), mkS (the mask
   row's entry of the lookup's scalar number s, from 0).
 - J := Option J₀. The entry none stands for bit j of a row whose number c is not the number of a
   call: the verifier has no cell there. The statements on forA read the entries through zext, which
   gives 0 there; no premise on the entries says so.
 - St := St₀ × E, the E being the shift. That it is 0, without a round, if the forest has one call
   is forB's doing (OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean).
 - key and tab are the joint vectors Port.key and Port.tab, shifted. forA_asmH: ShiftQ.asmH at A0 :=
   forA gives forA back, by rfl; so the statements on ShiftQ.allK at A0 := forA speak of forA.
 - oK: the reversal at a plain key level, the last level's own list; oT, oE, oB: the reversal.
   Coordinate t is the verifier's variable t (OnBytes/Tie/Pv/Lookup/Port/FoNums.lean, Points).
 - the ten families of mask places: the numbering of the scalars sent (FoNums.S h).
No letter has a default.

Main definitions: Lay, zext, forT, forK, forP, forOK, forA. Main theorem: forA_asmH.
Not claimed: that forA is the verifier's lookup: no statement of this file compares it with a
function of OnBytes/Model/. What is tied, and to what: OnBytes/Tie/Pv/Lookup/Forest/FoTies.lean,
OnBytes/Tie/Pv/Lookup/Forest/FoVal.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Lists.ShiftKLists
import OnBytes.Tie.Pv.Lookup.Port.E3OrdPort
import OnBytes.Tie.Pv.Lookup.Value.TwEnt
import OnBytes.Tie.Pv.Lookup.Order.E3O65
import OnBytes.Tie.Pv.Lookup.Port.FoNums

set_option autoImplicit false

namespace Cb.Fo
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp
open TwNums.Sizes (Ent)
open Cb.Tw (pEnt)

abbrev Sh : Type := OnBytes.Model.Forest.Shape

/-- What else is public: the caller's layout. -/
structure Lay (E St₀ J₀ : Type) where
  /-- K st μ c i: key number i < 2^(n_c) of call c, not shifted, its own padding places included -/
  K : St₀ → (J₀ → E) → ℕ → ℕ → E
  /-- bc t c j: the entry of bit j of the count of row t of call c (asked at c < NC alone) -/
  bc : ℕ → ℕ → ℕ → J₀
  /-- the mask row's entry of the lookup's slot number s (from 0) -/
  mkS : ℕ → J₀

/-- the entries read with 0 at the entry that is no cell -/
def zext {E J₀ : Type} [Zero E] (μ : J₀ → E) : Option J₀ → E
  | none => 0
  | some j => μ j

section
variable (E : Type) [Field E] {St₀ J₀ : Type}

/-- the tables, off the verifier's record -/
def forT (h : Sh) : St₀ → ℕ → ℕ → E := fun _ c t => (FoNums.tauN h c t : E)
/-- the calls' key vectors on the entries with the one more -/
def forK (L : Lay E St₀ J₀) :
    St₀ → (Option J₀ → E) → ℕ → ℕ → E := fun st μ => L.K st fun j => μ (some j)
/-- the shift's data -/
def forP (h : Sh) (L : Lay E St₀ J₀) :
    ShiftQ E St₀ (Option J₀ → E) := Port.Q h (forT E h) (forK E L)

/-- the key levels' orders, total in h; where Forest.shape refuses (dT < 10) the reversal stands -/
def forOK (h : Sh) (k : ℕ) : Equiv.Perm (Fin k) :=
  if hd : 10 ≤ h.dT then E3.ordKeys h.dT h.rK hd k else E3.ordDefault k

variable [Fintype E] [Fintype J₀] [DecidableEq J₀]

/-- The builder. It is noncomputable for one reason: pEnt walks the list of a sumcheck's formats,
and pDummy in that list is noncomputable. forT, forK, forP, forOK, zext and all of FoNums are
computable. -/
noncomputable def forA (h : Sh) (L : Lay E St₀ J₀) : LkAsmH E where
  St := St₀ × E
  J := Option J₀
  v' := FoNums.v' h
  d := h.d
  w := FoNums.w
  n := FoNums.n
  key := fun x m => shKeyQ (forP E h L).fK ((forP E h L).key x.1 m) (forP E h L).tag x.2
  tab := fun x => shTabQ (forP E h L).fT ((forP E h L).tab x.1) (forP E h L).tag x.2
  bAt := fun u j => (FoNums.cellOf h u j).map fun x => L.bc x.1 x.2.1 x.2.2
  pads := FoNums.pads h
  wAt := fun j i => some (L.mkS ((FoNums.S h).pTie j (pEnt _ i)))
  cZ := some (L.mkS ((FoNums.S h).pTie 0 (.shown (TwNums.shownTie0 none))))
  cAt := fun j b => some
      (L.mkS ((FoNums.S h).pTie j
      (.shown (if j = 0 then TwNums.shownTie0 (some b) else TwNums.shownBool b))))
  wK := fun l i => some (L.mkS ((FoNums.S h).pKey l (pEnt _ i)))
  cK := fun l b => some (L.mkS ((FoNums.S h).pKey l (.shown (TwNums.shownBool b))))
  wT := fun l i => some (L.mkS ((FoNums.S h).pTab l (pEnt _ i)))
  cT := fun l b => some (L.mkS ((FoNums.S h).pTab l (.shown (TwNums.shownBool b))))
  oE := E3.ordDefault (FoNums.w + h.d)
  wE := fun i => some (L.mkS ((FoNums.S h).pEnd (pEnt _ i)))
  oB := E3.ordDefault (FoNums.w + h.d)
  wB := fun i => some (L.mkS ((FoNums.S h).pBit (pEnt _ i)))
  cB := some (L.mkS ((FoNums.S h).pBit (.shown 0)))
  oK := fun l => forOK h (0 + l)
  oT := fun l => E3.ordDefault (FoNums.w + l)

/-- The assembly at the shifted vectors, at A0 := forA, is forA. -/
theorem forA_asmH (h : Sh) (L : Lay E St₀ J₀) : (forP E h L).asmH (forA E h L) = forA E h L := rfl

end
end Cb.Fo
