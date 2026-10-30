-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05SeatLaws.lean: THE KIND K5 AT A SEAT OF THE PROOF FILE's FIRST CHAIN: what the rule "from a
seat to the table's tie, whatever the kind" (tiedBy_of_seatLaws, Johnson/Desc/Sound/TiedSeat.lean) asks of the kind's files (that file's SeatLaws: four things at every block that narrows the
kind's own, for every value z of the public part): HAD, under K05_tiedAt_all's premises ASKED FOR EVERY z. One theorem, by
seatLaws_of_tied (Johnson/Desc/Sound/SeatLawsOfTied.lean) over K05_tiedAt_all (Johnson/Desc/First/Att/K05Closes.lean).
IT PROVES NO FILLING AND NAMES NO MEMBER. Every premise that names the public part π is asked at every π: K5Fill · keptForms ·
madeForms · madeMore · hleftIs · hokI · K5Behind · K5FillRel · K5FillIns; the letters x0, gOf and R' may hang on π.
NOT HERE (other files' to show; owed, as reported of Johnson/Desc/Sound/TiedSeat.lean): the facts on the description's own piece q: q.back = [] · q.ds against the
plan's rounds · q.err = the cap · the seats below q.base; and that the block at the seat narrows k5AtN's.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05Closes
import Johnson.Desc.Sound.SeatLawsOfTied

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

open Classical in
/-- **What is owed at a seat, at the kind's own block k5AtN.** -/
theorem K05_seatLaws {W Cl Pp : Type} [Nonempty Pp]
    {Fr : Frame}
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
    (ns base : ℕ)
    (ds : List RDT)
    (hds : List.Forall₂ RoundAsG ds (rounds (parO Wv m a before)))
    (tj : OnBytes.K.Kc.Tape)
    (x0 : Pp → First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str)
    (gOf : Pp → First.S × Fr.E.Str → Forest.Heard)
    (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg)
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
    (Fi : ∀ π : Pp, K5Fill Mg N π Fr base m O Q (parO Wv m a before).own pC pD arr first nsPlan)
    (hQ : ∀ q ∈ (pubRowOf links pl).asks, q ∈ Q)
    (keptForms : ∀ π : Pp, ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear (parO Wv m a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ i ∈ O, (rowOf links pl).ins.contains i = false → i ≠ .pinI → ∀ q ∈ tiesOf i,
        Mg.pub q (π, s) = true → Mg.pub q (π, behind s att hd G) = true)
    (madeForms : ∀ π : Pp, ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear (parO Wv m a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ q ∈ [Pub.formsInT m 3 "own", Pub.formsInT m 2 "planes", Pub.formsInT m 2 "join"],
        Mg.pub q (π, behind s att hd G) = true)
    (madeMore : ∀ π : Pp, ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear (parO Wv m a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ x ∈ (Mg.more.rows links pl).makes, Mg.pub (moreItem x) (π, behind s att hd G) = true ∧
        Mg.pubP (moreItem x) (π, behind s att hd G))
    (hleftIs : ∀ π : Pp, ∀ a' : First.S × Fr.E.Str, Mg.pubP (.left m) (π, a'.1) →
      K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork
        (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
        (Cb.Fo.NumsEq.placeOf (enMask x.ns a.seam.tl) plJ)
        (fun F => Room F ns x.F.next
          (Forest.elems x.fs + (slotsOf (script (parO Wv m a before).own) + 0))) ((x0 π) a') ((gOf π) a') a'.1)
    (hokI : ∀ π : Pp, ∀ a', onT N Mg links π Fr pl O Q a' → I.ok (I.rc a'.1) a'.2)
    (Bh : ∀ π : Pp, K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv m a before) ns base a.nW (plannedK a)
      (padOfO a.fs) tj (gOf π) (onT N Mg links π Fr pl O Q) I (R' π))
    (ps : List Place)
    (k : ℕ)
    (hk : ps[k]? = some pl)
    (hk' : ps[k + 1]? = some pl')
    (hO : O = (openSets links ps (start links))[k]?.getD [])
    (hQs : Q = (pubSets Mg.more links ps)[k]?.getD [])
    (hR' : ∀ π : Pp, (R' π) = relAt (meansQ N Mg fun s => (π, s)) (outsQ links ps k))
    (Rel : ∀ π : Pp, K5FillRel Mg N links π Fr base m pl O Q (parO Wv m a before).own)
    (hr : readsOpen links ps (start links) = true)
    (hap : rowsApart links ps = true)
    (hB : ridersB links ps k m = true)
    (Ins : ∀ π : Pp, K5FillIns Mg N links π Fr base m pl O Q (parO Wv m a before).own x a.S a.seam.tl D rad Ex Wp α ns
      (numsPlan (parO Wv m a before).own (x.F.next + Forest.elems x.fs)) (x0 π) I.part) :
    SeatLawsN (C := ckP .two) (Fr := Fr) (W := W) N Mg links ps k base ds []
      (Err.cap 128 (uLT (ckP .two) ds)) blk :=
  seatLaws_of_tied N Mg links ps k base ds [] _ blk fun z =>
    K05_tiedAt_all claim hP hp4 g m hm before blk hblk hok hG ha hx D rad Ex Wp α ns base ds hds tj (x0 z) yOf (gOf z) plJ
      I (R' z) N Mg links z pl pl' O Q pC pD hS arr first kr nsPlan Ix Bk Pn (Fi z) hQ (keptForms z) (madeForms z)
      (madeMore z) (hleftIs z) (hokI z) (Bh z) ps k hk hk' hO hQs (hR' z) (Rel z) hr hap hB (Ins z)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_seatLaws
