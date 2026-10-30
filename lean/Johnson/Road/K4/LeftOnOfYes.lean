-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/LeftOnOfYes.lean: AT A `Yes` (CarriageHeard.lean), AT THE SEAT `seatS`'s OWN
READERS: THE LOOKUP's LASTING PROMISE `K3LeftOn` BEHIND, OUT OF ITS SHARP ONE `K3LeftAt` IN FRONT
(Johnson/Top/H/K3LeftStatement.lean); AND A MARK STAYS. Statements and proofs: calls, no new
argument.

  `look_of_yes`, `fork_of_yes`: behind a yes the seat finds what the lookup returned as in front;
    its ledger is the hearing's G.
  **`leftOn_of_yes`**: `K3LeftAt` in front and a `Yes`: `K3LeftOn` behind, at the same shape, lm,
    first and Q: the ledger behind is later than the one behind the lookup's hearing
    (`hearFl_later`; `laterFo_of_psc`) and sized (`Later.sized`, from `K3Left.padLeft.fit`).
  `mark_of_yes`: the record's field failed is the same behind a yes as in front (`Rest.failed`).

Limits. «A YES OF THE PIECE» IS HERE THE RECORD `Yes` (CarriageHeard.lean) AT A PIECE pc THAT IS A
LETTER: nothing in this file ties pc to K4's block. From a yes of a piece's verifier to a `Yes` goes
`yes_of_out`, under three premises: the piece holds `below bk`; bk hears as K4's own block at the
seat (`HearsAs`); the piece puts no round behind (pc.back = []). BOTH PROMISES STAND HERE AT seatS's
READERS (the link's field fo; its ledger). The lookup's own law concludes `K3LeftAt` at the record's
readers `S.fork?` and `S.lookHeard?`: in front the two agree where the link's fo is its lookHeard
(`leftAt_seatS`); BEHIND THE YES NOTHING HERE LEADS BACK TO THESE READERS: LeftOnKept.lean has the
lasting promise there. SO THE TABLE OF JOINTS' ITEM leftOn IS NOT MADE BY THIS FILE. ONE DIRECTION,
FROM A YES. `K3LeftAt` in front is a premise. Nothing on soundness.
-/
import Johnson.Road.K4.KeptOfYes
import Johnson.Top.H.K3LeftStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS seatS_look seatS_laid seatS_fits hearFl_later)
open _root_.Run (ckP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.OnPublicFiles (K3LeftAt K3LeftOn laterFo_of_psc)

variable {Wt Cl : Type} {Fr : Frame} {par : Par} {pc : Piece (ckP .two) Fr S Cl Wt}
  {a : S × Fr.E.Str} {τ : Tr (uLT (ckP .two) pc.ds)} {fo : Forest.Heard} {o : Own} {G : Fork}

/-- Behind a yes the seat's ledger is the hearing's. -/
theorem fork_of_yes (y : Yes seatS par pc a τ fo o G) :
    seatS.fork (behindOf seatS pc a τ o G).1 = G := by
  obtain ⟨al, ha, _⟩ := lay_of_look y.look
  exact seatS_fits ha G o

/-- Behind a yes the seat finds what the lookup returned as in front. -/
theorem look_of_yes (y : Yes seatS par pc a τ fo o G) :
    seatS.look (behindOf seatS pc a τ o G).1 = seatS.look a.1 := by
  obtain ⟨al, ha, _⟩ := lay_of_look y.look
  have e : (behindOf seatS pc a τ o G).1 =
      { a.1 with here := .lay { al with F := G, own := some o }, rowsOwed := none } :=
    seatS_laid ha G o none
  rw [e, seatS_look ha, seatS_look (a := { al with F := G, own := some o }) rfl]

/-- **The lasting promise behind a `Yes`, out of the sharp one in front, at the seat's readers.** -/
theorem leftOn_of_yes {h : Forest.Shape} {lm first : ℕ} {Q : Fork → Prop}
    (y : Yes seatS par pc a τ fo o G)
    (hl : K3LeftAt (fun s => some (seatS.fork s)) seatS.look h lm first Q a.1) :
    K3LeftOn (fun s => some (seatS.fork s)) seatS.look h lm first Q
      (behindOf seatS pc a τ o G).1 := by
  obtain ⟨F, F', g, rs, q, n, L, hg, hf⟩ := hl
  have e : seatS.fork a.1 = F' := Option.some.inj hf
  have hL : PscRun.Later (seatS.fork a.1) G := hearFl_later y.hears
  exact ⟨F, F', G, g, rs, q, n, L, (look_of_yes y).trans hg, congrArg some (fork_of_yes y),
    laterFo_of_psc (e ▸ hL), hL.sized (e ▸ L.padLeft.fit)⟩

/-- A mark stays, and none comes. -/
theorem mark_of_yes (y : Yes seatS par pc a τ fo o G) :
    (behindOf seatS pc a τ o G).1.failed = a.1.failed :=
  (rest_of_yes y).1.failed

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.fork_of_yes
#print axioms OnBytes.Road.K4.look_of_yes
#print axioms OnBytes.Road.K4.leftOn_of_yes
#print axioms OnBytes.Road.K4.mark_of_yes
