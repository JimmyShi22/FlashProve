-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05AtMg.lean: KIND K5: ALL THAT THE KIND's LAW AT THE TABLE OF JOINTS ASKS OF THE TABLE's MEANING Mg, IN ONE STRUCTURE; and the top from it.
Why. The files that compose the table's filling give, for each kind, one lemma "the kind's premises hold at the composed meaning". For that the premises
must stand in one place. In K05_seatLaws_named (Johnson/Desc/First/Att/K05SeatLaws2.lean) they are nine binders.
  `K5AtMg`: nine fields, each at every value π of the public part. Its letters: the plan's (Wv · m · before · a · x · pC · pD · arr · first · nsPlan), the table's
    (N · Mg · links · pl · O · Q · base), and the law's own (claim · D · rad · Ex · Wp · α · ns · tj · x0 · gOf · plJ · I · R').
  `K05_seatLaws_atMg`: **SeatLaws links ps k q N Mg blk** (Johnson/Desc/Sound/TiedSeat.lean) from K5AtMg, the public facts on the plan and the block,
    three facts on the description's piece q, and the tests and equations on the table alone.
Limits. A GATHERING: no premise falls by it. IT PROVES NO FILLING AND NAMES NO MEMBER. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05SeatLaws2

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

/-- **What kind K5's law asks of the table's meaning at attention segment m.** -/
structure K5AtMg {W Cl Pp : Type} {Fr : Frame} (base : ℕ)
    (claim : Aff → Cl)
    (Wv : Verify.Public)
    (m : ℕ)
    (before : List (ℕ × ℕ))
    (a : Attention.Plan)
    (x : VerifiableInference.Desc.First.Look.Place)
    (D : Sent)
    (rad : OracleShape → Nat)
    (Ex : Iop.ExtSpec)
    (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E)
    (ns : ℕ)
    (tj : OnBytes.K.Kc.Tape)
    (x0 : Pp → First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (gOf : Pp → First.S × Fr.E.Str → Forest.Heard)
    (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg)
    (R' : Pp → First.S × Fr.E.Str → W → Prop)
    (N : Numbers)
    (Mg : Meaning Pp W)
    (links : List ModelPart)
    (pl : Place)
    (O : List Item)
    (Q : List Pub)
    (pC pD : Look.P)
    (arr : Array (ℕ × String))
    (first nsPlan : ℕ) : Prop where
  /-- What the promise in front of the block needs in order to ride over the block: seventeen facts on how the public items and the oracles' clauses are filled. -/
  fill : ∀ π : Pp, K5Fill Mg N π Fr base m O Q (parO Wv m a before).own pC pD arr first nsPlan
  /-- The public tests tied to the items that stay open ride over the block's lay. -/
  keptForms : ∀ π : Pp, ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear (parO Wv m a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ i ∈ O, (rowOf links pl).ins.contains i = false → i ≠ .pinI → ∀ q ∈ tiesOf i,
        Mg.pub q (π, s) = true → Mg.pub q (π, behind s att hd G) = true
  /-- The public tests tied to the three items that the block's row opens hold behind the lay. -/
  madeForms : ∀ π : Pp, ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear (parO Wv m a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ q ∈ [Pub.formsInT m 3 "own", Pub.formsInT m 2 "planes", Pub.formsInT m 2 "join"],
        Mg.pub q (π, behind s att hd G) = true
  /-- What the door's filling says the block makes holds behind the lay. -/
  madeMore : ∀ π : Pp, ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear (parO Wv m a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ x ∈ (Mg.more.rows links pl).makes, Mg.pub (moreItem x) (π, behind s att hd G) = true ∧
        Mg.pubP (moreItem x) (π, behind s att hd G)
  /-- What the item "left" says in front of the block is what the lookup on the calls leaves: its ledger, what it heard, and room for the block's slots. -/
  leftIs : ∀ π : Pp, ∀ a' : First.S × Fr.E.Str, Mg.pubP (.left m) (π, a'.1) →
      K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork
        (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
        (Cb.Fo.NumsEq.placeOf (enMask x.ns a.seam.tl) plJ)
        (fun F => Room F ns x.F.next
          (Forest.elems x.fs + (slotsOf (script (parO Wv m a before).own) + 0))) ((x0 π) a') ((gOf π) a') a'.1
  /-- The pin's own side condition holds wherever the promise does. -/
  pinOk : ∀ π : Pp, ∀ a', onT N Mg links π Fr pl O Q a' → I.ok (I.rc a'.1) a'.2
  /-- What the kind's law asks behind the block: the pinned messages, and that the gathered forms and the join's form are worth 0. -/
  behind : ∀ π : Pp, K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv m a before) ns base a.nW (plannedK a)
      (padOfO a.fs) tj (gOf π) (onT N Mg links π Fr pl O Q) I (R' π)
  /-- What stays open of the relation rides back over the block's lay: eight facts. -/
  rel : ∀ π : Pp, K5FillRel Mg N links π Fr base m pl O Q (parO Wv m a before).own
  /-- What the kind's own relation says in front gives what the block's row closes: four facts. -/
  ins : ∀ π : Pp, K5FillIns Mg N links π Fr base m pl O Q (parO Wv m a before).own x a.S a.seam.tl D rad Ex Wp α ns
      (numsPlan (parO Wv m a before).own (x.F.next + Forest.elems x.fs)) (x0 π) I.part

open Classical in
/-- **What is owed at a seat, at the kind's own block, from the one structure.** -/
theorem K05_seatLaws_atMg {W Cl Pp : Type}
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
    (H : K5AtMg q.base claim Wv m before a x D rad Ex Wp α ns tj x0 gOf plJ I R' N Mg links pl O Q pC pD arr first nsPlan) :
    SeatLaws links ps k q N Mg blk :=
  K05_seatLaws_named q hback herr claim hP hp4 g m hm before blk hblk hok hG ha hx D rad Ex Wp α ns hds tj x0 yOf gOf plJ I R' N Mg links pl pl' O Q pC pD hS arr first kr nsPlan Ix Bk Pn H.fill hQ H.keptForms H.madeForms H.madeMore H.leftIs H.pinOk H.behind ps k hk hk' hO hQs hR' H.rel hr hap hB H.ins

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_seatLaws_atMg
