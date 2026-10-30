-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Entry.lean: one record on the carried record at the entry of the kind K5,
from which all that the statements on the kind take of the lookup's kind is drawn.

Why one record suffices. At an attention link the lookup's place and that of K5 are neighbours in
the table of stretches, and the fold over a chain's blocks hands the record that a block's step
returns to the next block untouched (`foldBlocks`, Johnson/Desc/Block.lean). So the ledger at the
entry of K5 is the ledger F' that the lookup's yes left. This is read off the texts; no theorem in
this file says it of the fold.

Definitions, statements and proofs.
Main names:
  `K5Entry seat fork heard x own s ns nx k F F' g rs`: fork and heard are the two readers of the
    lookup's seat. Six fields: the ledger that the seat of K5 reads at s is what fork reads; fork s
    = some F'; heard s = some g; F.next = x.F.next; `K3LeftIs` x.fs x.lm F F' g rs
    (Johnson/Desc/First/Att/K05Left.lean); `Room` F ns nx (Forest.elems x.fs + (slotsOf (script own)
    + k)).
  `hroom_of_entry`: at every ledger that the seat of K5 reads at s, `Room` with ns, nx +
    Forest.elems x.fs and slotsOf (script own) + k.
  `hk3_of_entry`: with `AttOK` and the second tie of the out-statement, `K3Pts` x.fs g.zx g.zy g.zk
    pt.
  `k3join_of_entry`: with `AttOK`, `OutTies`, `Stays` F' G' and G'.ns = F'.ns, `K3Join` at
    `attCaller`, in the world of G' at the mask entries of `attLin0`.
Limits: `K5Entry` and `OutTies` are shown for no run in this file or in what it imports. No
soundness of the protocol is claimed. Nothing on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Left

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Cb Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask)

/-- **The carried record at the kind's entry.** fork, heard: the lookup's seat's two readers. -/
structure K5Entry {St : Type} (seat : Seat St) (fork : St → Option Fork) (heard : St → Option Forest.Heard)
    (x : VerifiableInference.Desc.First.Look.Place) (own : Params.AttentionRounds) (s : St) (ns nx k : ℕ)
    (F F' : Fork) (g : Forest.Heard) (rs : TwV.Rounds Cb.Gl.E) : Prop where
  same : ∀ G, seat.ledger s = some G → fork s = some G
  fork : fork s = some F'
  heard : heard s = some g
  front : F.next = x.F.next
  left : K3LeftIs x.fs x.lm F F' g rs
  room : Room F ns nx (Forest.elems x.fs + (slotsOf (script own) + k))

section Entry
variable {St : Type} {seat : Seat St} {fork : St → Option Fork} {heard : St → Option Forest.Heard}
  {x : VerifiableInference.Desc.First.Look.Place} {own : Params.AttentionRounds} {s : St} {ns nx k : ℕ}
  {F F' : Fork} {g : Forest.Heard} {rs : TwV.Rounds Cb.Gl.E}

/-- The ledger that the kind's seat reads at its entry is the one that the lookup's yes left. -/
theorem K5Entry.ledger (N : K5Entry seat fork heard x own s ns nx k F F' g rs) {G : Fork}
    (h : seat.ledger s = some G) : G = F' := Option.some.inj ((N.same G h).symm.trans N.fork)

/-- **The room at the kind's entry.** -/
theorem hroom_of_entry (N : K5Entry seat fork heard x own s ns nx k F F' g rs) (G : Fork)
    (h : seat.ledger s = some G) : Room G ns (nx + Forest.elems x.fs) (slotsOf (script own) + k) := by
  rw [N.ledger h]
  exact room_of_left N.left N.room

/-- **The points.** -/
theorem hk3_of_entry (N : K5Entry seat fork heard x own s ns nx k F F' g rs) {set : Params.Setting}
    {S : Attention.Shape} {tl : HTailF2} {D : Sent} {rad : OracleShape → Nat} (H : AttOK set x S tl D rad)
    {pt : ℕ → Cb.Gl.E}
    (t2 : ∀ t, pt t = ((Fo.endsOf x.fs x.lm F.next rs).zx ++ (Fo.endsOf x.fs x.lm F.next rs).zy).getD t 0) :
    K3Pts x.fs g.zx g.zy g.zk pt := k3pts_of_left N.left H.four t2

/-- **The join's tie.** -/
theorem k3join_of_entry (N : K5Entry seat fork heard x own s ns nx k F F' g rs) {set : Params.Setting}
    {S : Attention.Shape} {tl : HTailF2} {D : Sent} {rad : OracleShape → Nat} (Ex : Iop.ExtSpec) (Wp : Type)
    (H : AttOK set x S tl D rad) (pl : ℕ → ℕ → JAtt x.ns tl)
    {x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))}
    (T : OutTies x0 (Fo.endsOf x.fs x.lm F.next rs) (Cb.Fo.NumsEq.placeOf (enMask x.ns tl) pl)) {G' : Fork}
    (hs : Stays F' G') (hn : G'.ns = F'.ns) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (m : (attSg x D rad).Msg) :
    K3Join (attCaller x S tl D rad Ex Wp) g
      (G'.worldOf Reading.gl ((attLin0 x S tl D rad).maskOf m) entry) x0 m :=
  k3join_att x S tl D rad Ex Wp H N.front N.left pl T hs hn entry m

end Entry

end VerifiableInference.Desc.First.Att.P
