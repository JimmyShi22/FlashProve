-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5TiedPlus.lean: kind K5: FROM K5AtMg TO THE TIE AT THE TABLE, IN
BOTH FORMS, AT ONE PLACE OF THE KIND.

IS IT EMPTY HERE? Implications. NO MEMBER IS SHOWN.

Main names:
  `k5_tiedAt_any`: at ANY filling Mg: K05_seatLaws_atMg's own premises
    (Johnson/Desc/First/Att/K05AtMg.lean: cut by program, letter for letter: K5AtMg last among
    them), and that the description's piece q holds, beneath the lift over the public part, a
    sub-protocol's text B that narrows the seat's blk (SeatOf), give TiedAt N Mg links ps (fun a =>
    a) k (q.withMap Ee), Ee an extractor that lays nothing: K05_seatLaws_atMg ·
    tiedBy_of_seatLaws (Johnson/Desc/Sound/TiedSeat.lean) · TiedBy.tiedAt.
  `k5_tiedAtR_plus`: **the same premises AT THE WIDER FILLING mgPlus …, with the bridge's (k5_tiedR,
    Johnson/Desc/First/Att/Door/Law/PlusBridge.lean), give TiedAtR N Mg links ps (fun a => a) Rch k
    (q.withMap Ee) AT THE NARROWER Mg**: the sentence that KindTiedR
    (Johnson/Desc/Sound/TiedR.lean) asks at each place of the kind.
PREMISES LEFT: all of K05_seatLaws_atMg's (its hQ asks that the BASE row's asks be open; the wider
list's own asks at the place are open by OpenQ) · SeatOf · hq · hEe · the bridge's: hpub · Facts5 ·
the sixth and the seventh fact at border k (hbare · hleft), each under the narrower promise · the
test on the two lists at k and k + 1 · hopen' · HandsOn Rch k q (ChainOfPromisesR.lean: kind-free;
reported paid at its own condition). AT THE WRITTEN DESCRIPTION the first group is
paid from an opening by K05_tied_at (TiedAtEntry.lean).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05AtMg
import Johnson.Desc.First.Att.Door.Law.PlusBridge
import Johnson.Desc.Sound.TiedSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Road.L5 (dimOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask lookAt)
open VerifiableInference.Desc.Sound (Frame Piece strsOf)
open VerifiableInference.Desc (Claim RoundAsG Place)
open VerifiableInference.Desc.First (Item Pub Meaning Numbers ModelPart onAt stepOpen pubStep rowOf pubRowOf
  pubRowM moreItem tiesOf)

open VerifiableInference.Desc.First (openSets pubSets start openSets_succ pubSets_succ segRow)
open VerifiableInference.Desc.Sound (TiedAt onQ relQ meansQ insQ outsQ rowQ relAt openAfter)
open VerifiableInference.Desc.Sound (openIsList openL insL outsL openL_iff_openSets rowsApart)
open VerifiableInference.Desc.First (readsOpen)
open OnBytes.Road.L5 (callsOf)
open VerifiableInference.Desc.First.Look (attCells)
open VerifiableInference.Desc.Sound (SeatLawsN seatLaws_of_tied)
open VerifiableInference.Desc.Sound (SeatLaws seatLaws_of_N)
open VerifiableInference.Desc.Sound (TiedAtR HandsOn SeatOf tiedBy_of_seatLaws below doorsFitB)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (More PubData pubOfItems pubAll)
open VerifiableInference.Desc.K12.Door (Laid)
open H2K5.Door (mgPlus morePlus isThreeQ isWideQ bareAttB leftAttB Facts5 k5_tiedR)

open Classical in
/-- **The tie at the table, first form, at any filling.** -/
theorem k5_tiedAt_any {W Cl Pp : Type}
    [Nonempty Pp]
    {Fr : Frame}
    (q : Piece (ckP .two) Fr (Pp × First.S) Claim W)
    (hback : q.back = [])
    (herr : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    (claim : Aff → Cl)
    {Wv : Verify.Public}
    (hP : PlanIs Wv)
    (hp4 : Wv.p4 = true)
    (g m : ℕ)
    (hm : m = 2 * g + 1)
    (before : List (ℕ × ℕ))
    (blk : VerifiableInference.Desc.Block First.S Claim)
    (hblk : k5AtN Wv m g before = some blk)
    (hok : blk.planOk = true)
    (hG : k5GuardN Wv m g = true)
    {a : Attention.Plan}
    (ha : Wv.A[g]? = some a)
    {x : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt Wv m false = some x)
    (D : Sent)
    (rad : OracleShape → Nat)
    (Ex : Iop.ExtSpec)
    (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E)
    (ns : ℕ)
    (hds : List.Forall₂ RoundAsG q.ds (rounds (parO Wv m a before)))
    (tj : OnBytes.K.Kc.Tape)
    (x0 : Pp → First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str)
    (gOf : Pp → First.S × Fr.E.Str → Forest.Heard)
    (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
    (I : PinItemP Fr seatSO q.base W (attSg x D rad).Msg)
    (R' : Pp → First.S × Fr.E.Str → W → Prop)
    (N : Numbers)
    (Mg : Meaning Pp W)
    (links : List ModelPart)
    (pl pl' : Place)
    (O : List Item)
    (Q : List Pub)
    (pC pD : Look.P)
    (hS : Forest.Shape)
    (arr : Array (ℕ × String))
    (first kr nsPlan : ℕ)
    (Ix : K5Place links m pl pl')
    (Bk : K5Book N pl pl')
    (Pn : K5Plan (parO Wv m a before).own m pC pD hS first kr nsPlan)
    (hQ : ∀ q ∈ (pubRowOf links pl).asks, q ∈ Q)
    (ps : List Place)
    (k : ℕ)
    (hk : ps[k]? = some pl)
    (hk' : ps[k + 1]? = some pl')
    (hO : O = (openSets links ps (start links))[k]?.getD [])
    (hQs : Q = (pubSets Mg.more links ps)[k]?.getD [])
    (hR' : ∀ π : Pp, (R' π) = relAt (meansQ N Mg fun s => (π, s)) (outsQ links ps k))
    (hr : readsOpen links ps (start links) = true)
    (hap : rowsApart links ps = true)
    (hB : ridersB links ps k m = true)
    (H : K5AtMg q.base claim Wv m before a x D rad Ex Wp α ns tj x0 gOf plJ I R' N Mg links pl O Q pC pD arr first nsPlan)
    (B : Block First.S Claim) (hSeat : SeatOf blk B) (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s))
    (Ee : (Pp × First.S) × Fr.E.Str → (Pp × First.S) × Fr.E.Str → W → W) (hEe : ∀ u v w, Ee u v w = w) :
    TiedAt N Mg links ps (fun u => u) k (q.withMap Ee) :=
  (tiedBy_of_seatLaws links ps k blk B q hSeat hq N Mg Ee hEe
    (K05_seatLaws_atMg q hback herr claim hP hp4 g m hm before blk hblk hok hG ha hx D rad Ex Wp α ns hds tj x0 yOf gOf plJ I R' N Mg links pl pl' O Q pC pD hS arr first kr nsPlan Ix Bk Pn hQ ps k hk hk' hO hQs hR' hr hap hB H)).tiedAt

open Classical in
/-- **The tie at the table, second form, at the narrower filling.** -/
theorem k5_tiedAtR_plus {W Cl Pp : Type}
    [Nonempty Pp]
    {Fr : Frame}
    (q : Piece (ckP .two) Fr (Pp × First.S) Claim W)
    (hback : q.back = [])
    (herr : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    (claim : Aff → Cl)
    {Wv : Verify.Public}
    (hP : PlanIs Wv)
    (hp4 : Wv.p4 = true)
    (g m : ℕ)
    (hm : m = 2 * g + 1)
    (before : List (ℕ × ℕ))
    (blk : VerifiableInference.Desc.Block First.S Claim)
    (hblk : k5AtN Wv m g before = some blk)
    (hok : blk.planOk = true)
    (hG : k5GuardN Wv m g = true)
    {a : Attention.Plan}
    (ha : Wv.A[g]? = some a)
    {x : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt Wv m false = some x)
    (D : Sent)
    (rad : OracleShape → Nat)
    (Ex : Iop.ExtSpec)
    (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E)
    (ns : ℕ)
    (hds : List.Forall₂ RoundAsG q.ds (rounds (parO Wv m a before)))
    (tj : OnBytes.K.Kc.Tape)
    (x0 : Pp → First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str)
    (gOf : Pp → First.S × Fr.E.Str → Forest.Heard)
    (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
    (I : PinItemP Fr seatSO q.base W (attSg x D rad).Msg)
    (R' : Pp → First.S × Fr.E.Str → W → Prop)
    (N : Numbers)
    (Mg : Meaning Pp W)
    (M0 : More) (Dd : PubData) (Ld : Laid) (Ms : List OracleShape) (base : Pub → Pp × First.S → Bool) (cs : Codes)
    (links : List ModelPart)
    (pl pl' : Place)
    (O : List Item)
    (Q : List Pub)
    (pC pD : Look.P)
    (hS : Forest.Shape)
    (arr : Array (ℕ × String))
    (first kr nsPlan : ℕ)
    (Ix : K5Place links m pl pl')
    (Bk : K5Book N pl pl')
    (Pn : K5Plan (parO Wv m a before).own m pC pD hS first kr nsPlan)
    (hQ : ∀ q ∈ (pubRowOf links pl).asks, q ∈ Q)
    (ps : List Place)
    (k : ℕ)
    (hk : ps[k]? = some pl)
    (hk' : ps[k + 1]? = some pl')
    (hO : O = (openSets links ps (start links))[k]?.getD [])
    (hQs : Q = (pubSets (morePlus M0) links ps)[k]?.getD [])
    (hR' : ∀ π : Pp, (R' π) = relAt (meansQ N (mgPlus Mg M0 Dd Ld Ms base cs) fun s => (π, s)) (outsQ links ps k))
    (hr : readsOpen links ps (start links) = true)
    (hap : rowsApart links ps = true)
    (hB : ridersB links ps k m = true)
    (H : K5AtMg q.base claim Wv m before a x D rad Ex Wp α ns tj x0 gOf plJ I R' N (mgPlus Mg M0 Dd Ld Ms base cs) links pl O Q pC pD arr first nsPlan)
    (B : Block First.S Claim) (hSeat : SeatOf blk B) (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s))
    (Ee : (Pp × First.S) × Fr.E.Str → (Pp × First.S) × Fr.E.Str → W → W) (hEe : ∀ u v w, Ee u v w = w)
    (Rch : ℕ → (Pp × First.S) × Fr.E.Str → Prop) (hpub : Mg.pub = pubAll Dd base)
    (F : Facts5 (fun u : Pp × First.S => u) Dd Ld Ms cs Rch)
    (hbare : ∀ u, Rch k u → onQ N Mg links ps (fun u => u) k u → u.1.2.failed = none → bareAttB u.1.2 = true)
    (hleft : ∀ u, Rch k u → onQ N Mg links ps (fun u => u) k u → u.1.2.failed = none → leftAttB u.1.2 = true)
    (hD : doorsFitB Mg.more (morePlus M0) isWideQ links ps k = true) (hD' : doorsFitB Mg.more (morePlus M0) isWideQ links ps (k + 1) = true)
    (hopen' : ∀ t ∈ (pubSets (morePlus M0) links ps)[k + 1]?.getD [],
      t ∈ (pubSets Mg.more links ps)[k + 1]?.getD [] ∨ isThreeQ t = true)
    (hs : HandsOn Rch k q) :
    TiedAtR N Mg links ps (fun u => u) Rch k (q.withMap Ee) :=
  k5_tiedR N Mg links ps (fun u => u) M0 Dd Ld Ms base cs Rch hpub F k (q.withMap Ee) hbare hleft hD hD' hopen'
    (fun u τ v hu hv => hs u τ v hu hv)
    (k5_tiedAt_any q hback herr claim hP hp4 g m hm before blk hblk hok hG ha hx D rad Ex Wp α ns hds tj x0 yOf gOf plJ I R' N (mgPlus Mg M0 Dd Ld Ms base cs) links pl pl' O Q pC pD hS arr first kr nsPlan Ix Bk Pn hQ ps k hk hk' hO hQs hR' hr hap hB H B hSeat hq Ee hEe)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5_tiedAt_any
#print axioms VerifiableInference.Desc.First.Att.P.k5_tiedAtR_plus
