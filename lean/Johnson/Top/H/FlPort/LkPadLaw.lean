-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/LkPadLaw.lean: what a yes of the library's flat function for a lookup's
messages (`lkPad`, OnBytes/K/Kc/FlatHear.lean) gives: the carried chain's last theorems, in one
statement on a ledger and a tape. Typed by hand over the carried files of this folder.

`lkPad_law`: if lkPad calls pub lid, from the ledger F and the tape t, returns g, the ledger F' and
the tape u, then t is some rounds "taken" followed by u; these rounds send and draw as many elements
as the shape's own plan of rounds says (planF), WITHOUT any premise on the ledger; and, where the
ledger's three arrays have their sizes (Sized F): the record's shape is made of the calls by the
public tests (ShapeOf), the ledger is left as PadLeft says, and the record with the ledger behind
holds the record of end values (endsOf) at the rounds taken, read by ρ: for every reading ρ of the
byte-level field in a commutative ring, and every lm. ShapeOf, PadLeft, HeardIs, endsOf, planF and
Sized are the library's own.

It is the twin of the library's Fo.hcOut2V (OnBytes/Tie/Pv/Lookup/Forest/FoPadAll.lean), which
speaks of the verifier program's routine in a context. That no routine in a context is reached from
it is meant, and is not shown in this library.

Limits. A tie: it has no error term. It does not say that lkPad returns, nor anything on the claims
that are made of the record later. Where Sized F fails it gives the rounds' sizes alone. Sized F
(OnBytes.PscRun.Sized) holds of a ledger that Fork.slots has laid (slots_sized,
OnBytes/Tie/Pv/Psc/PscFork.lean; took_sized, owe_sized, paid_sized keep it); lkPad tests none of the
three sizes as such. That lkPad says yes on a real proof's rounds is a matter of runs, not of this
file.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.FlPort.FoPadAll
import Johnson.Top.H.FlPort.FoSzPad

set_option autoImplicit false

namespace Fo.Tp
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.K.Kc

theorem lkPad_law {K : Type} [CommRing K] (ρ : Reading K) (calls : Array Call) (pub : Array Nat)
    (lid lm : ℕ) (F F' : Fork) (t u : Tape) (g : Forest.Heard)
    (h : lkPad calls pub lid F t = some (g, F', u)) :
    ∃ taken : List FlatRound, t = taken ++ u ∧
      taken.map (fun x => (x.sent.length, x.drawn.length)) = planF g.shape ∧
      (Sized F →
        ShapeOf calls pub lid g.shape ∧ PadLeft g.shape F F' g ∧
          HeardIs ρ g F' (endsOf g.shape lm F.next
            (taken.map fun x => (x.sent.map ρ.val, x.drawn.map ρ.val)))) := by
  have h' : lkPad calls pub lid F t = .ok ((g, F'), u) := h
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h'
  obtain ⟨l, e, r, _⟩ := pad_sizes P trivial
  obtain ⟨rv, ht, _⟩ := rds_took ρ r trivial e
  refine ⟨rv, ht.2.2, ?_, fun hF => ?_⟩
  · rw [pad_shape P]
    exact pad_sizes_view P trivial ht
  · obtain ⟨h1, h2, rv', ht', _, hH⟩ := hcOut2V K ρ calls pub lid lm F F' t u g h' hF trivial
    obtain rfl : rv' = rv := took_unique ht' ht
    exact ⟨h1, h2, hH⟩

end Fo.Tp

#print axioms Fo.Tp.lkPad_law
