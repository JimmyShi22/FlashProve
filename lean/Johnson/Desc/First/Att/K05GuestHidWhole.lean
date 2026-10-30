-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05GuestHidWhole.lean: `whole_row`
(Johnson/Desc/First/Att/K05GuestWhole.lean) at the base joint `forRest`
(Johnson/Desc/First/Att/K05GuestHid.lean) in the place of `forOut`, where the closed parameters'
three free linear claims are LMat, LDat and LEat (Cb/Pv/Att/End/Hid.lean).

Statements and proofs.
Main names:
  `hidLet_meant`: `HidLet` is met at the closed parameters with `meantLin` and `meantQ`
    (Johnson/Desc/First/Att/K05Meant.lean), at one's own letters of the join.
  `keys_doomed`: (I) the count at the closed parameters, from `keys_link`: `Doomed` with `Good c P
    (forRest c) Dn m a` at the end, at the errors of `guest_link`.
  `whole_row_keys`: from a yes of `decide`: (I), the hearing's return, and at every later ledger
    `WholeRowSays` at A0 := `forRest`: for every statement and transcript of the lookup with output
    (x0, y): `Good`, `forRest` at (x0, y) and the left side of `whole_row` give `forIn` and `Three`.
    Neither `ZCRead` or `LinReads` nor the lookup's out-claim on the keys is a premise.
Premises: `FoNums.ok c.h`; `AttFits`; P0.zOf is the lookup's pt; P0.D.lT ≤ 16; two plane messages;
those of `K05_row`; at the closed parameters made of the plan: `HidLet`, `JoinGives` and Calls.OK,
at letters Qf ns N of the join; the two other premises of `kfExt`.
Used beside these: `good_doomed`, `keys_link`, `K05_row`, `whole_of_row`, `meant_LM`,
`meant_LD`, `meant_LE`; no routine in a context.
Limits: those of Johnson/Desc/First/Att/K05GuestWhole.lean and
Johnson/Desc/First/Att/K05GuestHid.lean. `UnitsLin` and `TailLin` on the left side are now LMat,
LDat and LEat at the data heard (the reading of every tied scalar, and the join on the hidden
values): that the kind's linear claims and the join's form, worth 0, give them there is not shown in
this file or in what it imports. Johnson/Desc/First/Att/K05GuestPaid.lean shows it for the reading
of ZC, at a chain whose LE is that reading alone: where LM and LD accept anything, the premise hΛ of
`whole_row_paid` (Johnson/Desc/First/Att/K05GuestRow.lean) and `HidLet` do not both hold, so the two
statements stand at different letters. `JoinGives` is shown for no caller. Λ is fixed in front,
while `HidLet` is asked at parameters that hang on two numbers of the ledger in front of the kind's
hearing: so Λ has to be laid knowing them. Nothing on an honest prover, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05GuestWhole
import Johnson.Desc.First.Att.K05GuestHid
import Johnson.Desc.First.Att.K05Meant

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.Rider Cb.LdLkp Cb.LdLkp.Kn Cb.Pv.Att Cb.Pv.Att.End Inst.Model
  Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers
open OnBytes.Tie.Pv.Att (recOf)
open VerifiableInference.OnPublicFiles (LookupCCaller)
open VerifiableInference.Desc.Part

section Met
variable {K M0 X Mg : Type} [Field K] [Fintype K]

/-- **HidLet is met** at the closed parameters with the meant linear claims
(Johnson/Desc/First/Att/K05Meant.lean), at one's own letters of the join. -/
theorem hidLet_meant (P0 : OwnPar K M0 X) (Λ0 : Lin P0 Mg) (ns : ℕ) (N : Nums) (Q : JoinLay (closedOf P0 Λ0 ns N)) :
    HidLet (closedOf P0 (meantLin P0 Λ0 ns N Q) ns N) (meantQ P0 Λ0 ns N Q) :=
  ⟨meant_LM P0 Λ0 ns N Q, meant_LD P0 Λ0 ns N Q, meant_LE P0 Λ0 ns N Q⟩

end Met

section HidWhole
variable (c : LookupCCaller) {M0 : Type}
  (P0 : OwnPar Cb.Gl.E M0 (TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀))) (Λ : Lin P0 c.Sg.Msg)
  (tb : Tables)

/-- (I) at the closed parameters, with the lookup's out-claim on the keys off the base joint. -/
theorem keys_doomed (ok : FoNums.ok c.h = true) (F0 : AttFits c.h P0.D P0.C) (hz : ∀ b, P0.zOf b = b.2.1.pt)
    (hT : P0.D.lT ≤ 16) (hk4 : P0.kap = 4) (hn : P0.npl = 2) (ns : ℕ) (N : Nums)
    (Q : JoinLay (closedOf P0 Λ ns N)) (H : HidLet (closedOf P0 Λ ns N) Q)
    (hJ : JoinGives c (closedOf P0 Λ ns N) Q tb) (hC : Calls.OK (scl := Q.scl) P0.C P0.D)
    (hdeep : ∀ u : AttSeg.Fam, u.l P0.D ≤ P0.C.Dk) (h01 : P0.C.a 0 = P0.C.a 1)
    (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) (m : c.Sg.Msg)
    (a : c.St₀ × c.Ex.Str) (ha : (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).on a) :
    Doomed (hostThen c (closedOf P0 Λ ns N)).shape
      (Err.app (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e ((ownA c (closedOf P0 Λ ns N)).ch.eps c.Ex))
      (Good c (closedOf P0 Λ ns N) (forRest c) Dn m a) :=
  good_doomed c (closedOf P0 Λ ns N) (forRest c) Dn
    (keys_link c (closedOf P0 Λ ns N) Q tb ok F0 hz (by
      show P0.D.lT ≤ 2 ^ P0.kap
      rw [hk4]
      omega) hn H hJ hC hdeep h01 Dn) m a ha

/-- **Both halves, from a yes of `decide`, at the library's letters, without the lookup's out-claim
on the keys.** -/
theorem whole_row_keys (ok : FoNums.ok c.h = true) (F0 : AttFits c.h P0.D P0.C) (hz : ∀ b, P0.zOf b = b.2.1.pt)
    (hT : P0.D.lT ≤ 16) (hn : P0.npl = 2) {St : Type} (seat : Seat St) (p : Par) (s s' : St)
    (rs : List Fmt.RoundView) (hd : decide seat p s rs = .ok s') (hzS : ∀ F, seat.ledger s = some F → Sized F)
    (Qf : ∀ (ns : ℕ) (N : Nums), JoinLay (closedOf P0 Λ ns N))
    (hΛ : ∀ F, seat.ledger s = some F →
      HidLet (closedOf P0 Λ F.ns (numsPlan p.own F.next)) (Qf F.ns (numsPlan p.own F.next)) ∧
      JoinGives c (closedOf P0 Λ F.ns (numsPlan p.own F.next)) (Qf F.ns (numsPlan p.own F.next)) tb ∧
      Calls.OK (scl := (Qf F.ns (numsPlan p.own F.next)).scl) P0.C P0.D)
    (hdeep : ∀ u : AttSeg.Fam, u.l P0.D ≤ P0.C.Dk) (h01 : P0.C.a 0 = P0.C.a 1)
    (hk4 : P0.kap = 4) (rows : ℕ) (hrec : p.own = recOf P0 rows) (S : Attention.Shape)
    (hDS : P0.D = OnBytes.Road.L5.dimOf S) (Z : OnBytes.Road.Rows.Sizes S) (hlt : S.cf.lt = P0.D.lT)
    (hNP : (geoOf S).NP = (size18 P0.D).pairs) (hNP2 : S.NP = P0.D.nb) {u1 u2 : UnitG}
    (hgs : (geoOf S).scores = [u1, u2]) (hb1 : u1.below = true) (hb2 : u2.below = false)
    (zk : Array (Array E)) :
    ∃ (F G : Fork) (h : Heard), seat.ledger s = some F ∧ seat.lay s h G = some s' ∧
      (∀ (Dn : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀) → c.Sg.Msg → Prop) (m : c.Sg.Msg)
        (a : c.St₀ × c.Ex.Str), (forIn Cb.Gl.E c.h c.L c.R0 c.msg₀).on a →
        Doomed (hostThen c (closedOf P0 Λ F.ns (numsPlan p.own F.next))).shape
          (Err.app (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).e
            ((ownA c (closedOf P0 Λ F.ns (numsPlan p.own F.next))).ch.eps c.Ex))
          (Good c (closedOf P0 Λ F.ns (numsPlan p.own F.next)) (forRest c) Dn m a)) ∧
      hear p.own (F, rs, 0) = some (h, G, [], 0) ∧
      ∀ G', Stays G G' → G'.ns = G.ns → Sized G' →
        WholeRowSays c (closedOf P0 Λ F.ns (numsPlan p.own F.next)) (forRest c) Λ.maskOf
          p.own F G' rs h S zk (LookAll P0 S zk u1 u2) := by
  obtain ⟨F, G, h, a1, a2, ah, a3⟩ :=
    K05_row P0 Λ seat p s s' rs hd hzS hk4 rows hrec S hDS Z hlt hNP hNP2 hgs hb1 hb2 zk
  obtain ⟨l1, l2, l3⟩ := hΛ F a1
  exact ⟨F, G, h, a1, a2,
    fun Dn m a ha => keys_doomed c P0 Λ tb ok F0 hz hT hk4 hn _ _ _ l1 l2 l3 hdeep h01 Dn m a ha, ah,
    fun G' q1 q2 q3 => whole_of_row c _ _ _ _ F G' rs h S zk _ (a3 G' q1 q2 q3)⟩

end HidWhole

end VerifiableInference.Desc.First.Att.P
