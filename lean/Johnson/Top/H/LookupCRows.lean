-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/LookupCRows.lean: the lookup of a sub-proof as a kind of block whose joint behind the
block says the number of rows, and the seam from it into the draw that batches a ledger of claims.

The kind of Johnson/Top/H/LookupC.lean ends at Cb.Fo.forOut. By type the list of rows in its
out-statement has any length; a draw that batches one form a row has its property of a block on
ledgers of at most n claims alone. In Johnson/Top/H/LookupSeamsLed.lean the seam's state map
therefore refuses a ledger that is too long. Here the number of rows is paid by the lookup's own
block; the bound 1 + that number + k ≤ n stays a premise.

What the file states.
 - kLookupCN L: the kind of kLookupC L, to the letter (reduction, extractor, error counts, the
   joint before the block), but for the joint behind the block: Cb.Fo.forOutN at Fo.nRows c.h:
   forOut with the clause "the list of rows has length Fo.nRows c.h" in its condition on
   statements.
 - lookupCN_knowAt, lookupCN_good: all four facts of a block at every caller whose record of public
   numbers passes the test FoNums.ok; over the caller's signature every block of the kind has the
   property of a block.
 - ledAll c kp g more: the state map that lays the ledger ledOf
   (Johnson/Top/H/LookupSeamsLed.lean): the keys' row, the rows put out, the caller's further
   claims; it never refuses.
 - seamLedN c kp A0 n g more, seamLedN_ok: the seam from the kind's joint behind the block to the
   draw's joint ledInA A0 n c.msg₀ along ledAll is in order, if each key of the layout is one entry
   or none (KeysAre); the carried joint's condition follows from the caller's; the carried joint's
   relation TOGETHER WITH the caller's further claims more x, all holding of the entries, gives the
   caller's own relation back; where the caller's condition holds these further claims are at most
   k; and 1 + Fo.nRows c.h + k ≤ n. So the statement allows that what rides through the lookup is
   paid by claims of the ledger, not by the carried joint alone.

Limits. KeysAre is shown of the layout digL5 of the lookups on the digits alone (keysAre_dig5,
Johnson/Top/H/LookupSeamsKey.lean); of the layouts of the calls' lookups nothing is shown: so
seamLedN_ok is of use at the lookups on the digits alone. No instance here shows its five premises
met together, or a further claim that pays anything. Else the limits of LookupSeamsLed.lean, but for
the refusing map: that the written row's block behind the lookup begins at ledInA A0 n c.msg₀ with
these arguments and this ledger is said nowhere here; the claims' order in the ledger is ledOf's
own.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Top.H.LookupSeamsLed
import OnBytes.Tie.Pv.Lookup.Forest.FoOutN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.LdLkp Cb.Lkp TWhole Cb.Pv.Att

/-- The lookup of a sub-proof as a kind of block; the joint behind says the number of rows. -/
@[reducible] noncomputable def kLookupCN (L : List LookupCCaller) : BaseKind.{1} Cb.Gl.E :=
  { kLookupC L with B := fun c => forOutN c.h c.L c.R0 c.msg₀ (Fo.nRows c.h) }

theorem lookupCN_knowAt (L : List LookupCCaller) (hL : OkLookupC L) : (kLookupCN L).KnowAtAll :=
  fun c hc => holeC_rows c.h c.L c.R0 c.msg₀ (hL c hc)

theorem lookupCN_good (L : List LookupCCaller) (hL : OkLookupC L) :
    ∀ c ∈ L, ((kLookupCN L).toKind.block c).Good :=
  BaseKind.good_of_knowAt (lookupCN_knowAt L hL)

section
variable (c : LookupCCaller) (kp : ℕ → ℕ → Option c.J₀) {K' P : Type}
  (A0 : IOR.Rels K' P c.Ex (c.Sg.Msg × c.Wp)) (n : ℕ) (g : c.St₀ × Cb.Gl.E → P)
  (more : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → Ledger Cb.Gl.E c.J₀)

/-- The map of states: it never refuses. -/
noncomputable def ledAll (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) :
    Option (P × Ledger Cb.Gl.E c.J₀) :=
  some (g x.1, ledOf c kp more x)

/-- The seam from the lookup, with its number of rows, to the draw that batches the ledger. -/
@[reducible] noncomputable def seamLedN :
    StepD ((kLookupCN [c]).toKind.dst c) (jOver c.Sg (ledInA A0 n c.msg₀)) :=
  stepSame c.Sg (forOutN c.h c.L c.R0 c.msg₀ (Fo.nRows c.h)) (ledInA A0 n c.msg₀)
    (ledAll c kp g more)

theorem seamLedN_ok (hL : KeysAre c.L kp) (hon : ∀ x y, c.R0.on (x.1, y) → A0.on (g x, y))
    (hrd : ∀ x y w, c.R0.on (x.1.1, y) → A0.relR (g x.1, y) w →
      Ledger.Holds (more x) (c.msg₀ w.1) → c.R0.relR (x.1.1, y) w) (k : ℕ)
    (hk : ∀ x y, c.R0.on (x.1.1, y) → (more x).length ≤ k) (hn : 1 + Fo.nRows c.h + k ≤ n) :
    (seamLedN c kp A0 n g more).OK :=
  stepSame_ok c.Sg _ _ _
    (fun x y s' ho hf => by
      obtain rfl := Option.some.inj hf
      refine ⟨hon x.1 y ho.1, ?_⟩
      show (ledOf c kp more x).length ≤ n
      unfold ledOf
      rw [List.length_cons, List.length_append, List.length_map, ho.2]
      have := hk x y ho.1
      omega)
    (fun x y s' w ho hf hw => by
      obtain rfl := Option.some.inj hf
      exact ⟨hrd x y w ho.1 hw.1 fun fm hm => hw.2 _
          (List.mem_cons_of_mem _ (List.mem_append_right _ hm)),
        (keyRow_holds c kp hL x _).1 ((rowForm_holds _ _).1 (hw.2 _ List.mem_cons_self)),
        fun r hr => (rowForm_holds _ _).1 (hw.2 _
          (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hr)))),
        trivial⟩)

end

#print axioms VerifiableInference.OnPublicFiles.lookupCN_good
#print axioms VerifiableInference.OnPublicFiles.seamLedN_ok

end VerifiableInference.OnPublicFiles
