-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/RngView.lean: the round in which the matrix of a smallness test is drawn, in the
rounds of which a file's chain is made, and in the view that is made of a written transcript.

OnBytes/Maker/Trees.lean lays a chain's rounds from a list of rounds' data (roundT, uLT), and makes
of a written transcript the list of rounds that the Lean verifier's routines read (rvT).
OnBytes/Tie/Pv/Tail/CarryRng.lean has the maps from the written round to the typed round for the
rounds of OnBytes/Slice/Draws.lean (wRound). The two kinds of written round have the same verifier
messages. Here the maps are laid at the rounds of a file's chain, and the premise of
`drawMatrix_typed` (OnBytes/Tie/Pv/Tail/RngRan.lean), that the view's round is made of the written
verifier message, is paid. Definitions, statements and proofs.

Main names:
  `rdOf d`: a round's data without its trees.
  `carryRngT s d h`, `carryRngT_fib`: the maps from the round of a file's chain to the typed round,
    and the bound on how many written verifier messages go to one matrix.
  `carryRngT_tr`: a written round whose test of work passes has an image.
  `rvT_trits`: the first round of the view of a written transcript holds the list of the typed
    challenge of the first written verifier message.
  `drawMatrix_rvT`: if the rounds that the routine's context has not yet begun are the view of a
    written transcript whose first round draws the matrix's entries and nothing else, and the
    routine that draws the matrix ends well: its list is listOf of the typed challenge of that
    round's written verifier message, and the rounds not yet begun are the view of the rest.

Limits: that a run reaches the routine with just these rounds not yet begun is for whoever cuts the
file's run. That the file's accept has passed the round's test of work: the same. Nothing on a dry
run.
-/
import OnBytes.Maker.Trees
import OnBytes.Tie.Pv.Tail.RngRan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Iop Prob OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.PscRun Cb.Pv.Tail

/-- A round's data without its trees. -/
def rdOf (d : RDT) : Run.PQ.RD := ⟨d.entry, d.kind, d.items, none, d.opens⟩

section
variable (s : Size) (d : RDT) (h : OnlyTrits (rdOf d) (s.columns * s.tau))

/-- The maps from the round of a file's chain to the typed round. -/
def carryRngT : Carry [(roundT (Run.ckP .two) d).up] [IOR.drawRound (Dr s)] :=
  (fun _ => ((), ()), fun _ c => chalTo (rdOf d) (matOf s (rdOf d) h) c, fun _ _ => ())

theorem carryRngT_fib (hlog : d.entry.logN ≤ 64) :
    (carryRngT s d h).Fib (((Run.bsRound .two d.entry d.kind).w, ()) : ℕ × Unit) :=
  ⟨fun _ c' => chalTo_fib (rdOf d) (matOf s (rdOf d) h) (matOf_inj s (rdOf d) h) hlog c',
    fun _ _ => trivial⟩

theorem carryRngT_tr (m : (roundT (Run.ckP .two) d).up.Msg)
    (c : (roundT (Run.ckP .two) d).up.Chal) (hp : GChal.pass (b := d.entry.work) c = true) :
    (carryRngT s d h).tr ((m, c, ()) : Tr [(roundT (Run.ckP .two) d).up]) =
      some ((((), ()), matOf s (rdOf d) h (valsOf (rdOf d) c), ()) :
        Tr [IOR.drawRound (Dr s)]) := by
  have e : chalTo (rdOf d) (matOf s (rdOf d) h) c =
      some (matOf s (rdOf d) h (valsOf (rdOf d) c)) := if_pos hp
  show (chalTo (rdOf d) (matOf s (rdOf d) h) c).bind _ = _
  rw [e]
  rfl

/-- The first round of the view holds the list of the typed challenge. -/
theorem rvT_trits (ds : List RDT) (m : (roundT (Run.ckP .two) d).up.Msg)
    (c : (roundT (Run.ckP .two) d).up.Chal) (τ : Tr (uLT (Run.ckP .two) ds)) (rv : Fmt.RoundView)
    (t : List Fmt.RoundView)
    (hv : rvT (Run.ckP .two) (d :: ds) ((m, c, τ) : Tr (uLT (Run.ckP .two) (d :: ds))) = rv :: t) :
    rv.drawn.trits.toArray = listOf (matOf s (rdOf d) h (valsOf (rdOf d) c)) ∧
      t = rvT (Run.ckP .two) ds τ := by
  obtain ⟨rfl, rfl⟩ := List.cons.inj hv
  exact ⟨drawn_view s (rdOf d) h c, rfl⟩

/-- The routine that draws the matrix, on the view of a written transcript. -/
theorem drawMatrix_rvT (tl tl' : HTailF2) (F F' : Fork) (x x' : Ctx) (hc : Clean x)
    (hr : tl.drawMatrixF F x = .ok ((tl', F'), x')) (ds : List RDT)
    (m : (roundT (Run.ckP .two) d).up.Msg) (c : (roundT (Run.ckP .two) d).up.Chal)
    (τ : Tr (uLT (Run.ckP .two) ds))
    (hl : x.ch.left =
      rvT (Run.ckP .two) (d :: ds) ((m, c, τ) : Tr (uLT (Run.ckP .two) (d :: ds)))) :
    tl'.cfF = listOf (matOf s (rdOf d) h (valsOf (rdOf d) c)) ∧
      x'.ch.left = rvT (Run.ckP .two) ds τ := by
  obtain ⟨-, rv, hR, -, rfl⟩ := drawMatrix_view tl tl' F F' x x' hc hr
  obtain ⟨h1, h2⟩ := rvT_trits s d h ds m c τ rv x'.ch.left (hl.symm.trans hR.2.2)
  exact ⟨h1, h2⟩

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.carryRngT_fib
#print axioms OnBytes.Tie.Pv.Tail.carryRngT_tr
#print axioms OnBytes.Tie.Pv.Tail.rvT_trits
#print axioms OnBytes.Tie.Pv.Tail.drawMatrix_rvT
