-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05AtCaller.lean: `whole_row_keys`
(Johnson/Desc/First/Att/K05GuestHidWhole.lean) at the closed caller of the lookup on an attention
link's calls (`attCaller`, Johnson/Desc/First/Look/K3CallerAtt.lean): the letters c, P0, Λ, Q and tb
are filled.

Definitions, statements and proofs.
Main names:
  `callsOf_eq`: the two functions callsOf of Johnson/Road/Rows/AttCalls.lean and
    Johnson/Road/Lane5CallsOf.lean are one.
  `attBase x S tl D rad`: the parameters of the kind K5 beside that caller: the same messages
    (`attSg`), the same entries (`JAtt`) by the same reading (`msgAtt`), the cells by the same rule
    of addresses (`enCell` at `addrA`); D := dimOf S; C := callsOf x.fs; zOf := the lookup's end
    point; two plane messages; kap = 4.
  `attLin0`, `attQ0`, `attLin`: the mask entries are the link's mask row's, read off the messages;
    the join's letters are `joinLayOf` (Johnson/Desc/First/Att/K05GuestKeysAt.lean) at the scales
    sclOf S; the three linear claims are `meantLin` (Johnson/Desc/First/Att/K05Meant.lean), laid at
    two numbers ns and N.
  `att_tOf`: the cells of `attBase` are the caller's `attCells`.
  `att_joinGives`: `JoinGives` at that caller, from `AttOK` and `CallsFit`.
  `whole_row_att`: `whole_row_keys` there.
Premises of `whole_row_att`: `AttOK`; `shapeHid` has returned (S, x.fs); `CallsFit` S x.fs; a yes of
`decide`; `Sized`; the ledger in front has ns slots and the plan's numbers are N (hF); p.own = recOf
attBase rows; the place's two score units, the first below the diagonal, the second on it.
Used beside these: `att_ok`, `attFits_of`, `attLay_K`, `rawOf`, `valAt`,
`joinGives_at`, `hidLet_meant`, `lT_le_16`, `callsFit_ok`, `callsFit_deep`, `callsFit_a01`,
`sizes_of_hid`, `norm_of_hid`; no routine in a context.
Limits: those of the files named. K3CallerAtt.lean says of its record `AttReadsOK`: "What guards the
caller's READING against a silent 0: tests on public data that no theorem on the joints spends:
without them a symbol, a mask entry or a cell that has no seat is read as 0". `whole_row_att` asks
`AttOK` and not `AttReadsOK`: what it says of the committed cells is worth only as much as
`AttReadsOK`. x.fs comes from two makers (`AttOK`: the parameters of the lookup's kind; `shapeHid`):
that they agree at a plan is not shown in this file or in what it imports. Two numbers of slots
stand side by side, untied: x.ns (the caller's entries hold x.ns mask entries) and ns (`closedOf`
lays ns slots beside them): the mask stands twice among the entries, both read off the messages at
the same addresses. α is a free letter. On the left side of the second half there still stand
`forRest`, `LookAll`, `PointsAre`, `SayAt`, Dn, the letters' linear claims at the data heard and
what the end values' readers mean. The lookup's half is tied to no view. No soundness of the
protocol is claimed: the premises named are not shown. Nothing on an honest prover, completeness or
hiding.

-/
import Johnson.Desc.First.Look.K3CallerAtt
import Johnson.Desc.First.Att.K05GuestHidWhole
import Johnson.Desc.First.Att.K05GuestKeysAt
import Johnson.Desc.First.Att.K05SevenAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.Rider Cb.LdLkp Cb.LdLkp.Kn Cb.Pv.Att Cb.Pv.Att.End Inst.Model
  Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Road.L5 (callsOf CallsFit dimOf sclOf tbOf addrA)
open VerifiableInference.OnPublicFiles (LookupCCaller)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt msgAtt enCell rawOf attLay_K AttOK
  attFits_of att_ok attRider sigListCalls seatCalls valAt attCells)

/-- The library's two writings of the lookup's numbers are one (Johnson/Road/Rows/AttCalls.lean,
Johnson/Road/Lane5CallsOf.lean). -/
theorem callsOf_eq (fs : Model.Forest.Shape) : OnBytes.Road.Rows.callsOf fs = callsOf fs := by
  unfold OnBytes.Road.Rows.callsOf OnBytes.Road.L5.callsOf
  congr 1
  funext c
  rw [Array.getD_eq_getD_getElem?]
  cases fs.calls[c.val]? <;> rfl

section AtCaller
variable (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat)

/-- **The parameters of the kind K5 beside the closed caller.** The places of mask entries and the
three free linear claims are idle here: `closedOf` lays them. -/
noncomputable def attBase :
    OwnPar Cb.Gl.E (attSg x D rad).Msg (TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) where
  D := dimOf S
  C := callsOf x.fs
  J := JAtt x.ns tl
  msg := msgAtt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl x.ns
  rd := fun e c => e (enCell x.ns tl (addrA S c).1 (addrA S c).2.1 (addrA S c).2.2)
  zOf := fun b => b.2.1.pt
  npl := 2
  kap := 4
  wAt := fun _ _ => none
  cAt := fun _ _ => none
  w18 := fun _ => none
  c18 := fun _ => none
  wH := fun _ => none
  cH := fun _ => none
  kM := fun _ => none
  kD := fun _ => none
  kE := fun _ => none
  kV := fun _ => none
  kF := fun _ => none
  LM := fun _ _ _ => True
  LD := fun _ _ _ => True
  LE := fun _ _ _ => True

/-- The readings of a message: the mask row's entries; the message itself. -/
noncomputable def attLin0 : Lin (attBase x S tl D rad) (attSg x D rad).Msg where
  maskOf := fun m j => (valAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) m (.mask j)).getD 0
  restOf := id
  LM := fun _ _ _ => True
  LD := fun _ _ _ => True
  LE := fun _ _ _ => True

/-- The caller's cells are these parameters' cells. -/
theorem att_tOf (m : (attSg x D rad).Msg) : (attBase x S tl D rad).tOf m = attCells x S tl D rad m := rfl

variable (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (N : Nums)

local notation "cA" => attCaller x S tl D rad Ex Wp
local notation "P0A" => attBase x S tl D rad

/-- The join's letters, made of the lookup's, at the scales of the shape. -/
noncomputable def attQ0 : JoinLay (closedOf P0A (attLin0 x S tl D rad) ns N) :=
  joinLayOf cA (closedOf P0A (attLin0 x S tl D rad) ns N) (sclOf S) α Sum.inr

/-- The readings with the library's three linear claims, laid at ns and N. -/
noncomputable def attLin : Lin P0A (attSg x D rad).Msg :=
  meantLin P0A (attLin0 x S tl D rad) ns N (attQ0 x S tl D rad Ex Wp α ns N)

local notation "ΛA" => attLin x S tl D rad Ex Wp α ns N

/-- **JoinGives at the closed caller.** -/
theorem att_joinGives {set : Params.Setting} (H : AttOK set x S tl D rad) (hf : CallsFit S x.fs) :
    JoinGives cA (closedOf P0A ΛA ns N)
      (meantQ P0A (attLin0 x S tl D rad) ns N (attQ0 x S tl D rad Ex Wp α ns N)) (tbOf S) :=
  joinGives_at (c := cA) (P := closedOf P0A ΛA ns N)
    (att_ok Ex Wp H cA (List.mem_singleton.2 rfl)) (sclOf S) α Sum.inr (tbOf S) hf rfl (fun _ => rfl) H.four
    (fun _ _ => rfl) (rawOf S x.ns tl) (fun _ μ q i => attLay_K x.fs x.lm x.F.next x.ns μ q i) (fun _ => rfl)

/-- **Both halves, from a yes of `decide`, at the closed caller of the lookup on an attention link's
calls.** -/
theorem whole_row_att {set : Params.Setting} (H : AttOK set x S tl D rad) {lid : ℕ} {cf : Attention.Cfg}
    (hh : Attention.shapeHid lid cf = Except.ok (S, x.fs)) (hf : CallsFit S x.fs) {St : Type} (seat : Seat St)
    (p : Par) (s s' : St) (rs : List Fmt.RoundView) (hd : decide seat p s rs = .ok s')
    (hzS : ∀ F, seat.ledger s = some F → Sized F)
    (hF : ∀ F, seat.ledger s = some F → F.ns = ns ∧ numsPlan p.own F.next = N) (rows : ℕ)
    (hrec : p.own = recOf P0A rows) {u1 u2 : UnitG} (hgs : (geoOf S).scores = [u1, u2])
    (hb1 : u1.below = true) (hb2 : u2.below = false) (zk : Array (Array E)) :
    ∃ (F G : Fork) (h : Heard), seat.ledger s = some F ∧ seat.lay s h G = some s' ∧
      (∀ (Dn : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → (attSg x D rad).Msg → Prop) (m : (attSg x D rad).Msg)
        (a : Unit × Ex.Str), (forIn Cb.Gl.E (cA).h (cA).L (cA).R0 (cA).msg₀).on a →
        Doomed (hostThen cA (closedOf P0A ΛA F.ns (numsPlan p.own F.next))).shape
          (Err.app (forB Cb.Gl.E (cA).h (cA).L V₀ V₀C (Ex := Ex)).e
            ((ownA cA (closedOf P0A ΛA F.ns (numsPlan p.own F.next))).ch.eps Ex))
          (Good cA (closedOf P0A ΛA F.ns (numsPlan p.own F.next)) (forRest cA) Dn m a)) ∧
      hear p.own (F, rs, 0) = some (h, G, [], 0) ∧
      ∀ G', Stays G G' → G'.ns = G.ns → Sized G' →
        WholeRowSays cA (closedOf P0A ΛA F.ns (numsPlan p.own F.next)) (forRest cA) (ΛA).maskOf
          p.own F G' rs h S zk (LookAll P0A S zk u1 u2) :=
  whole_row_keys cA P0A ΛA (tbOf S) (att_ok Ex Wp H cA (List.mem_singleton.2 rfl))
    (show AttFits x.fs (dimOf S) (callsOf x.fs) by
      rw [← callsOf_eq]
      exact attFits_of H.fits)
    (fun _ => rfl) (lT_le_16 hh) rfl seat p s s' rs hd hzS
    (fun ns' N' => joinLayOf cA (closedOf P0A ΛA ns' N') (sclOf S) α Sum.inr)
    (fun F hFs => by
      obtain ⟨e1, e2⟩ := hF F hFs
      rw [e1, e2]
      exact ⟨hidLet_meant P0A (attLin0 x S tl D rad) ns N (attQ0 x S tl D rad Ex Wp α ns N),
        att_joinGives x S tl D rad Ex Wp α ns N H hf, OnBytes.Road.L5.callsFit_ok hf⟩)
    (OnBytes.Road.L5.callsFit_deep hf) (OnBytes.Road.L5.callsFit_a01 hf) rfl rows hrec S rfl
    (OnBytes.Road.Rows.sizes_of_hid hh) (OnBytes.Road.Rows.norm_of_hid hh).lt rfl rfl hgs hb1 hb2 zk

end AtCaller

end VerifiableInference.Desc.First.Att.P
