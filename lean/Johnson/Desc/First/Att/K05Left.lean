-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Left.lean: what the lookup's kind leaves behind its yes, as far as the
kind K5 spends it, and the three records that the statements on the kind K5 take of the lookup,
drawn from it.

Definitions, statements and proofs.
Main names:
  `K3LeftIs h lm F F' g rs`: F: the ledger in front; F', g: what the yes leaves; rs: the rounds. Six
    fields: `HeardIs` Reading.gl g F' (endsOf h lm F.next rs) and `PadLeft` h F F' g
    (OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean); g.shape = h; the sizes of g.zx and g.zy are dT and
    rK; for every call c, g.zk.getD c #[] = g.zy.extract (rK - iota c) g.zy.size ++ g.zx, as arrays.
  `OutTies x0 En ι`: the four ties of the typed out-statement to a record of end values
    (Johnson/Desc/First/Att/K05JoinHeard.lean).
  `k3pts_of_left`: `K3Pts` h g.zx g.zy g.zk pt (Johnson/Desc/First/Att/K05LookAll.lean), at four
    calls and at the point of the second tie.
  `room_of_left`: `Room` behind the lookup's hearing (`room_of_padLeft`,
    Johnson/Desc/First/Att/K05RoomLook.lean).
  `k3join_of_left`: `K3Join` (Johnson/Desc/First/Att/K05JoinMeets.lean) in the world of every ledger
    G' with `Stays` F' G' and G'.ns = F'.ns (`k3join_of_stays`).
  `k3join_att`: the same at `attCaller` and at the mask entries of `attLin0`, at ι := placeOf
    (enMask x.ns tl) pl (OnBytes/Tie/Pv/Lookup/Forest/FoNumsEq.lean): the premise on mask entries is
    `hnu_att` (Johnson/Desc/First/Att/K05JoinAtt.lean).
Used: `rdL_append`, `rdL_getD`, `att_ok`, `zext`, `muOf`; no routine in a context.
Limits: `K3LeftIs` and `OutTies` are shown for no run in this file or in what it imports: they are
what is asked of the law of the lookup's kind at a yes; `K3LeftIs` is a record of this file's own,
until that kind has one. No soundness of the protocol is claimed. Nothing on an honest prover,
completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoNumsEq
import Johnson.Desc.First.Att.K05JoinAtt
import Johnson.Desc.First.Att.K05RoomLook

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Cb Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.OnPublicFiles (LookupCCaller)
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK att_ok enMask)

/-- **What the lookup's kind leaves behind its yes**, as far as the kind K5 spends it. F: the ledger
in front; F', g: what the yes leaves; rs: the rounds. -/
structure K3LeftIs (h : Forest.Shape) (lm : ℕ) (F F' : Fork) (g : Forest.Heard) (rs : TwV.Rounds Cb.Gl.E) :
    Prop where
  heardIs : Fo.HeardIs Reading.gl g F' (Fo.endsOf h lm F.next rs)
  padLeft : Fo.PadLeft h F F' g
  shape : g.shape = h
  zx : g.zx.size = h.dT
  zy : g.zy.size = h.rK
  zkRaw : ∀ c, c < h.NC → g.zk.getD c #[] = g.zy.extract (h.rK - h.iota.getD c 0) g.zy.size ++ g.zx

/-- **The typed out-statement's four ties to a record of end values.** -/
structure OutTies {St₀ J₀ : Type} [DecidableEq J₀] (x0 : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀))
    (En : Fo.Ends Cb.Gl.E) (ι : Fo.Pl → Option J₀) : Prop where
  theta : x0.1.2 = En.theta
  pt : ∀ t, x0.2.1.pt t = (En.zx ++ En.zy).getD t 0
  mf : ∀ j, x0.2.1.mf j = TwV.dense (Fo.mapL ι En.cEndF) j
  tg : x0.2.1.tg = En.alpha - En.cEndC

section Left
variable {h : Forest.Shape} {lm : ℕ} {F F' : Fork} {g : Forest.Heard} {rs : TwV.Rounds Cb.Gl.E}

/-- **The points.** -/
theorem k3pts_of_left (L : K3LeftIs h lm F F' g rs) (nc : h.NC = 4) {pt : ℕ → Cb.Gl.E}
    (t2 : ∀ t, pt t = ((Fo.endsOf h lm F.next rs).zx ++ (Fo.endsOf h lm F.next rs).zy).getD t 0) :
    K3Pts h g.zx g.zy g.zk pt where
  nx := L.zx
  ny := L.zy
  zk := fun q => L.zkRaw q.1 (by rw [nc]; exact q.2)
  z := funext fun t => by
    have e1 : Fo.rdL Reading.gl g.zx = (Fo.endsOf h lm F.next rs).zx := L.heardIs.zx
    have e2 : Fo.rdL Reading.gl g.zy = (Fo.endsOf h lm F.next rs).zy := L.heardIs.zy
    rw [t2 t, ← e1, ← e2, ← Fo.rdL_append, ← Fo.rdL_getD]
    rfl

/-- **The room.** -/
theorem room_of_left (L : K3LeftIs h lm F F' g rs) {ns nx k : ℕ} (R : Room F ns nx (Forest.elems h + k)) :
    Room F' ns (nx + Forest.elems h) k := room_of_padLeft L.padLeft R

end Left

/-- **The join.** -/
theorem k3join_of_left (c : LookupCCaller) {lm : ℕ} {F F' G' : Fork} {g : Forest.Heard}
    {rs : TwV.Rounds Cb.Gl.E} (L : K3LeftIs c.h lm F F' g rs) (ok : FoNums.ok c.h = true) (nc : c.h.NC = 4)
    (ι : Fo.Pl → Option c.J₀) {x0 : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)}
    (T : OutTies x0 (Fo.endsOf c.h lm F.next rs) ι) (hs : Stays F' G') (hn : G'.ns = F'.ns)
    (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {m : c.Sg.Msg}
    (hν : ∀ pc ∈ (Fo.endsOf c.h lm F.next rs).cEndInc, zext (c.msg₀ m) (ι pc.1) = Fo.muOf mask pc.1) :
    K3Join c g (G'.worldOf Reading.gl mask entry) x0 m :=
  k3join_of_stays c ok nc lm F.next rs ι L.heardIs L.shape hs hn mask entry T.theta T.pt T.mf T.tg hν

section AtCaller
variable (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)

/-- **The join at the closed caller and at K5's mask entries.** -/
theorem k3join_att {set : Params.Setting} (H : AttOK set x S tl D rad) {F F' G' : Fork} {g : Forest.Heard}
    {rs : TwV.Rounds Cb.Gl.E} (hF : F.next = x.F.next) (L : K3LeftIs x.fs x.lm F F' g rs)
    (pl : ℕ → ℕ → JAtt x.ns tl) {x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))}
    (T : OutTies x0 (Fo.endsOf x.fs x.lm F.next rs) (Cb.Fo.NumsEq.placeOf (enMask x.ns tl) pl))
    (hs : Stays F' G') (hn : G'.ns = F'.ns) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (m : (attSg x D rad).Msg) :
    K3Join (attCaller x S tl D rad Ex Wp) g
      (G'.worldOf Reading.gl ((attLin0 x S tl D rad).maskOf m) entry) x0 m :=
  k3join_of_left (attCaller x S tl D rad Ex Wp) L (att_ok Ex Wp H _ (List.mem_singleton.2 rfl)) H.four _ T hs hn _
    entry (by rw [hF]; exact hnu_att x S tl D rad Ex Wp H rs _ (fun _ => rfl) m)

end AtCaller

end VerifiableInference.Desc.First.Att.P
