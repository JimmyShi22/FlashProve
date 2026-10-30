-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05JoinAtt.lean: the chain from the library's records on the lookup to the
equality of worths that `GatheredTop` (Johnson/Desc/First/Att/K05RowTop.lean) holds for the join,
whole, at the letters beside the closed caller of the lookup on an attention link's calls and at the
ledger at which that equality is judged.

Statements and proofs.
Main names:
  `hnu_att`: at every place of the record's cEndInc the caller's entry is the mask entry of
    `attLin0`. The places are mask places from x.F.next on, fewer than nMasks (`onMasksIn_keyTop`,
    OnBytes/Tie/Pv/Lookup/Ends/FoSlotFlat.lean), below x.ns by the field masksIn of `AttOK`; there
    `enMask` is a mask entry, and `msgAtt` reads it off the messages at the address at which maskOf
    does.
  `hjv_of_heard`: from `AttOK`, `HeardIs` Reading.gl gL F' (endsOf x.fs x.lm x.F.next rs), gL.shape
    = x.fs, `Stays` F' G', G'.ns = F'.ns, the four ties of x0
    (Johnson/Desc/First/Att/K05JoinHeard.lean) and ι (.mask j) = some (enMask x.ns tl j): for all
    kv, joinVal (qAt Reading.gl gL) kv (the worth of gL.cEnd in the world of G' at the mask entries
    of `attLin`) is joinVal at the letters meantQ … attQ0. By `k3join_of_stays` and `hjv_att`.
Used: `att_ok`, `finOf_some`, `zext`, `muOf`, `attLin0`, `attQ0`, `meantQ`,
`closedOf`; no routine in a context.
Limits: `HeardIs`, gL.shape = x.fs and the four ties are shown for no run in this file or in what it
imports. No soundness of the protocol is claimed. Nothing on an honest prover, completeness or
hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoSlotFlat
import Johnson.Desc.First.Att.K05JoinHeard
import Johnson.Desc.First.Att.K05RowAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Cb Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK att_ok enMask finOf_some)

section JoinAtt
variable (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (N : Nums)

local notation "cA" => attCaller x S tl D rad Ex Wp
local notation "P0A" => attBase x S tl D rad
local notation "ΛA" => attLin x S tl D rad Ex Wp α ns N
local notation "QA" => meantQ P0A (attLin0 x S tl D rad) ns N (attQ0 x S tl D rad Ex Wp α ns N)

/-- **The caller's mask entries are ours**, at the places that the end of the key side reads. -/
theorem hnu_att {set : Params.Setting} (H : AttOK set x S tl D rad) (rs : TwV.Rounds Cb.Gl.E)
    (ι : Fo.Pl → Option (JAtt x.ns tl)) (hι : ∀ j, ι (.mask j) = some (enMask x.ns tl j))
    (m : (attSg x D rad).Msg) :
    ∀ pc ∈ (Fo.endsOf x.fs x.lm x.F.next rs).cEndInc,
      zext ((cA).msg₀ m) (ι pc.1) = Fo.muOf ((attLin0 x S tl D rad).maskOf m) pc.1 := by
  intro pc hpc
  obtain ⟨j, hj, _, h2⟩ := Fo.Slots.onMasksIn_keyTop x.fs x.lm x.F.next rs pc hpc
  have hlt : j < x.ns := lt_of_lt_of_le h2 H.masksIn
  rw [hj, hι]
  show (cA).msg₀ m (enMask x.ns tl j) = (attLin0 x S tl D rad).maskOf m j
  unfold enMask
  rw [finOf_some hlt]
  rfl

/-- **From the library's records on the lookup to the equality of worths**, at the ledger at which
it is judged. -/
theorem hjv_of_heard {set : Params.Setting} (H : AttOK set x S tl D rad) (rs : TwV.Rounds Cb.Gl.E)
    (ι : Fo.Pl → Option (JAtt x.ns tl)) (hι : ∀ j, ι (.mask j) = some (enMask x.ns tl j))
    {gL : Forest.Heard} {F' G' : Fork}
    (hI : Fo.HeardIs Reading.gl gL F' (Fo.endsOf x.fs x.lm x.F.next rs)) (hsh : gL.shape = x.fs)
    (hs : Stays F' G') (hn : G'.ns = F'.ns) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    {x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))} (m : (attSg x D rad).Msg)
    (t1 : x0.1.2 = (Fo.endsOf x.fs x.lm x.F.next rs).theta)
    (t2 : ∀ t, x0.2.1.pt t =
      ((Fo.endsOf x.fs x.lm x.F.next rs).zx ++ (Fo.endsOf x.fs x.lm x.F.next rs).zy).getD t 0)
    (t3 : ∀ j, x0.2.1.mf j = TwV.dense (Fo.mapL ι (Fo.endsOf x.fs x.lm x.F.next rs).cEndF) j)
    (t4 : x0.2.1.tg = (Fo.endsOf x.fs x.lm x.F.next rs).alpha - (Fo.endsOf x.fs x.lm x.F.next rs).cEndC)
    (kv : Fin 4 → Cb.Gl.E) :
    joinVal (K5Law.qAt Reading.gl gL) kv
        (gL.cEnd.value Reading.gl (G'.worldOf Reading.gl ((ΛA).maskOf m) entry)) =
      joinVal ((QA).q x0) kv (((QA).ce x0).val ((closedOf P0A ΛA ns N).msg m)) :=
  hjv_att x S tl D rad Ex Wp α ns N H
    (k3join_of_stays cA (att_ok Ex Wp H cA (List.mem_singleton.2 rfl)) H.four x.lm x.F.next rs ι hI hsh hs hn
      ((attLin0 x S tl D rad).maskOf m) entry t1 t2 t3 t4 (hnu_att x S tl D rad Ex Wp H rs ι hι m)) kv

end JoinAtt

end VerifiableInference.Desc.First.Att.P
