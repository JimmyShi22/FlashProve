-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05SeatLaws2.lean: THE KIND K5 AT A SEAT: ANOTHER FILE's PROPOSITION BY NAME: SeatLaws links ps k q N Mg blk
(Johnson/Desc/Sound/TiedSeat.lean), at a piece q of the description over (the public part × the carried record), blk :=
the kind's own block k5AtN: FROM K05_seatLaws (Johnson/Desc/First/Att/K05SeatLaws.lean) at base := q.base, ds := q.ds, UNDER TWO FACTS ON q:
q.back = [] · q.err = the cap at 128 (other files' to show; owed, as reported of Johnson/Desc/Sound/TiedSeat.lean; q.ds against the plan's rounds is the premise hds).
One theorem. IT PROVES NO FILLING AND NAMES NO MEMBER: K05_seatLaws' premises stand, each that names the public part at every value of it:
IT IS MEANT FOR A FILLING WHOSE Bools AND SENTENCES DO NOT READ THE PUBLIC PART FOR THE PLAN (the plan is the description's: Wv · pC · pD · arr ·
first · nsPlan are fixed letters): K5's own layer is so by its make.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05SeatLaws
import Johnson.Desc.Sound.SeatLawsOfTied2

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

open Classical in
/-- **What is owed at a seat, at the kind's own block: SeatLaws, by name.** -/
theorem K05_seatLaws_named {W Cl Pp : Type} [Nonempty Pp]
    {Fr : Frame}
    (q : Piece (ckP .two) Fr (Pp × First.S) Claim W) (hback : q.back = [])
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
    (Fi : ∀ π : Pp, K5Fill Mg N π Fr q.base m O Q (parO Wv m a before).own pC pD arr first nsPlan)
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
    (Bh : ∀ π : Pp, K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv m a before) ns q.base a.nW (plannedK a)
      (padOfO a.fs) tj (gOf π) (onT N Mg links π Fr pl O Q) I (R' π))
    (ps : List Place)
    (k : ℕ)
    (hk : ps[k]? = some pl)
    (hk' : ps[k + 1]? = some pl')
    (hO : O = (openSets links ps (start links))[k]?.getD [])
    (hQs : Q = (pubSets Mg.more links ps)[k]?.getD [])
    (hR' : ∀ π : Pp, (R' π) = relAt (meansQ N Mg fun s => (π, s)) (outsQ links ps k))
    (Rel : ∀ π : Pp, K5FillRel Mg N links π Fr q.base m pl O Q (parO Wv m a before).own)
    (hr : readsOpen links ps (start links) = true)
    (hap : rowsApart links ps = true)
    (hB : ridersB links ps k m = true)
    (Ins : ∀ π : Pp, K5FillIns Mg N links π Fr q.base m pl O Q (parO Wv m a before).own x a.S a.seam.tl D rad Ex Wp α ns
      (numsPlan (parO Wv m a before).own (x.F.next + Forest.elems x.fs)) (x0 π) I.part) :
    SeatLaws links ps k q N Mg blk := by
  refine seatLaws_of_N links ps k q N Mg blk ?_
  rw [hback, herr]
  exact K05_seatLaws claim hP hp4 g m hm before blk hblk hok hG ha hx D rad Ex Wp α ns q.base q.ds hds tj x0 yOf gOf plJ I R' N
    Mg links pl pl' O Q pC pD hS arr first kr nsPlan Ix Bk Pn Fi hQ keptForms madeForms madeMore hleftIs hokI Bh ps k hk hk' hO
    hQs hR' Rel hr hap hB Ins

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_seatLaws_named
