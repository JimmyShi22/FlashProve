-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/Alike.lean: **A PIECE's REDUCTION READS OF ITS BLOCK THE NAME, THE DECLARED
ROUNDS AND THE DECISION, AND NOTHING ELSE**: so a plain law of a piece goes over to every piece
whose block is alike in these three, at whatever type of claims. Definitions, statements and proofs.
No kind is named.

Why. A description carries a later chain's blocks to its own type of claims (`Block.retype`), lays a
clause to their tests on the plan (`Chain.blocksInOrder`), and holds them as `held b`
(Johnson/Desc/Sound/PaidAtDesc.lean). A kind's law is proved at the kind's own block, at its own
type of claims.
  `Alike b b'`: two blocks over one state, at two types of claims: one name, the same declared
    rounds, one decision.
  `alike_retype`, `alike_plan`, `Alike.held`, `Alike.symm`, `Alike.trans`: `Block.retype` and a
    turned test on the plan leave a block alike; `held` of alike blocks are alike.
  `run_alike`: alike blocks have one `foldRun` at the list of the one block.
  `leads_alike`: **every plain law goes over**: from a piece p to a piece q with an alike block and
    p's base, data, rounds put back and errors. `leads_alike_iff`: both ways.
Limits. Nothing on soundness. The tests on the plan, the told oracles, the runs of claims and the
runs behind a batching are not compared: no plain law of one piece reads them.

-/
import Johnson.Desc.Plain.LiftBelow
import Johnson.Desc.Sound.PaidAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes.Maker
open Iop _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

variable {S Cl Cl' Cl'' W : Type} {C : PQ.CK} {F : Frame}

/-- One name, the same declared rounds, one decision. -/
structure Alike (b : Block S Cl) (b' : Block S Cl') : Prop where
  name : b'.name = b.name
  rounds : b'.rounds = b.rounds
  decide : b'.decide = b.decide

theorem Alike.symm {b : Block S Cl} {b' : Block S Cl'} (h : Alike b b') : Alike b' b :=
  ⟨h.name.symm, h.rounds.symm, h.decide.symm⟩

theorem Alike.trans {b : Block S Cl} {b' : Block S Cl'} {b'' : Block S Cl''} (h : Alike b b')
    (h' : Alike b' b'') : Alike b b'' :=
  ⟨h'.name.trans h.name, h'.rounds.trans h.rounds, h'.decide.trans h.decide⟩

theorem alike_retype (b : Block S Cl) : Alike b (b.retype (Cl' := Cl')) := ⟨rfl, rfl, rfl⟩

theorem alike_plan (b : Block S Cl) (ok : Bool) : Alike b { b with planOk := ok } :=
  ⟨rfl, rfl, rfl⟩

theorem Alike.held {P : Type} {b : Block S Cl} {b' : Block S Cl'} (h : Alike b b') :
    Alike (held (P := P) b) (held (P := P) b') := by
  refine ⟨h.name, h.rounds, ?_⟩
  show (fun (t : P × S) rs gs => ((below b').decide t.2 rs gs).map fun s => (t.1, s)) =
    fun (t : P × S) rs gs => ((below b).decide t.2 rs gs).map fun s => (t.1, s)
  have e : (below b').decide = (below b).decide := by
    funext s rs gs
    simp only [below, h.decide]
  rw [e]

/-- Alike blocks have one run. -/
theorem run_alike {b : Block S Cl} {b' : Block S Cl'} (h : Alike b b') (back : List Fmt.RoundView) :
    foldRun F b'.name [b'] back = foldRun F b.name [b] back := by
  funext s v
  simp only [foldRun, chainAt, foldBlocks, Block.step, h.name, h.rounds, h.decide,
    List.isEmpty_cons]

/-- **Every plain law goes over.** -/
theorem leads_alike (p : Piece C F S Cl W) (q : Piece C F S Cl' W) (hb : Alike p.b q.b)
    (h1 : q.base = p.base) (h2 : q.ds = p.ds) (h3 : q.back = p.back) (h4 : HEq q.err p.err)
    (on : S × F.E.Str → Prop) (Q : S × F.E.Str → S × F.E.Str → Prop)
    (h : p.ior.red.Leads on Q p.err) : q.ior.red.Leads on Q q.err := by
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  obtain ⟨qb, qbase, qds, qback, qext, qerr⟩ := q
  dsimp only at hb h1 h2 h3 h4
  subst h1 h2 h3
  obtain rfl := eq_of_heq h4
  have e : (⟨qb, qbase, qds, qback, qext, qerr⟩ : Piece C F S Cl' W).run =
      (⟨pb, qbase, qds, qback, pext, qerr⟩ : Piece C F S Cl W).run := run_alike hb qback
  intro a ha
  refine Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b hout
  refine hτ b ?_
  have hout' : ((if sTests C ⟨F.a, qbase, F.all, qds, F.key, F.all⟩ a.2 τ then
      (⟨qb, qbase, qds, qback, qext, qerr⟩ : Piece C F S Cl' W).run a.1
        (sView C ⟨F.a, qbase, F.all, qds, F.key, F.all⟩ a.2 τ) else none).map
      fun xo => (xo, (⟨qb, qbase, qds, qback, qext, qerr⟩ : Piece C F S Cl' W).ior.imp a.2 τ)) =
      some b := hout
  rw [e] at hout'
  exact hout'

/-- Both ways: so the rule gives a law to no piece, and takes it from none, but as its alike ones
have it: a block that says yes to all, or no to all, fares at every type of claims as it fares at
one. -/
theorem leads_alike_iff (p : Piece C F S Cl W) (q : Piece C F S Cl' W) (hb : Alike p.b q.b)
    (h1 : q.base = p.base) (h2 : q.ds = p.ds) (h3 : q.back = p.back) (h4 : HEq q.err p.err)
    (on : S × F.E.Str → Prop) (Q : S × F.E.Str → S × F.E.Str → Prop) :
    q.ior.red.Leads on Q q.err ↔ p.ior.red.Leads on Q p.err :=
  ⟨leads_alike q p hb.symm h1.symm h2.symm h3.symm h4.symm on Q,
    leads_alike p q hb h1 h2 h3 h4 on Q⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.Alike.held
#print axioms VerifiableInference.Desc.K12.Coin.run_alike
#print axioms VerifiableInference.Desc.K12.Coin.leads_alike
#print axioms VerifiableInference.Desc.K12.Coin.leads_alike_iff
