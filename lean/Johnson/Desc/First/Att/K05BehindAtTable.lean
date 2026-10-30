-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05BehindAtTable.lean: kind K5: THE LAW's PREMISE K5Behind (Att/K05LawOne.lean: what is asked of the relation behind the kind), WHOLE, AS ONE THEOREM WITH ITS PREMISES LISTED: at the filled pin I := k5Pin …
(Att/K05LawPin.lean) and at the relation behind R' := what the kind's row of the table opens and reads (relAt (meansQ Nn Mg' fun s => (π, s)) (outsQ links pls k)).
  worth := k5Behind_worth_readers (Att/K05BehindWorthReaders.lean) · item := pinned_of_table (Att/Door/Law/PinnedOfTable.lean).
OVER THE CURED Returns and files of a trial
build: NOTHING COUNTED.
Main names: k5Pin_part (the filled pin's part is msgsOf at the sending's own letters: by rfl) · k5Behind_at_table.
THE LETTERS: tj := [] · k3 := padOfO hs · nW := A.nW · Kc := plannedK A · tl := A.seam.tl.
THE PREMISES, ALL: OF worth: hfT (at this link the table's meaning of an item formsT GIVES THE SENTENCE ITSELF: formsTQ at every run that the table lists under the item: an implication at values; no constant of the filling stands in it) · o1 · o2 (the two items are open in the row) · hpub (TiePub: four facts on public data) · r1 r2 r3 (memberships in runs) · hRds (what the run itself gives at block 2 the link's readers give too) · hst (block 2 states the
  kind's four runs) · hleft (what the lookup's kind leaves: the law's own) · hm · hSt · hfront · OF item: hpin · hopen · hsome · hSB (the list of members need not hold the caller's own list as a sending: it holds, at each place, a member with the same entry and seat; the samples hang on entry and seat) · hsent · hsm.
THE LETTERS UNDER "FOR ALL" IN THE PREMISES: hfT: j, name, b, w: free on purpose: a law of the meaning's make; the others are the two theorems' own, at the same letters.
EQUATIONS BETWEEN FUNCTIONS THAT ARE ASKED WHERE VALUES ARE SPENT: ONE IS LEFT: hpin : Mg'.pin = pinJT … (pinned_of_table's own premise: spent at the seats of Nn.sent m 0): whether the meaning that is meant meets it as an equation is not held here.
IS IT EMPTY HERE? An implication: whether the premises can be met together is shown nowhere.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05BehindWorthReaders
import Johnson.Desc.First.Att.Door.Law.PinnedOfTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Params
open VerifiableInference.Desc (Wit Place)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Item)
open VerifiableInference.Desc.K9 (Readers segAt? atMoment1)
open VerifiableInference.Desc.Sound (Alike SmpBySeat)
open VerifiableInference.Desc.Sound (Stated Mem msgsOf MsgT formsTQ seatTab Frame strsOf relAt meansQ outsQ
  second)
open VerifiableInference.Desc.First.Look (Sent JAtt attSg sigListCalls bornAt)
open K5Law (funsAt inAt_is firstAt_is secondAt_is readers_at runsN_is)
open VerifiableInference.Desc.K9 (Read lateOf ownRow readerOf RunOf runOfForms)

open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Sound (Sending pinJT)

section
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan)
  (D : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns A.seam.tl)) → Cb.Gl.E)

/-- The filled pin's part. -/
theorem k5Pin_part {Xi : Type} (Gd : FileDescription Xi) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
    (smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((Johnson.Pack.sigOf D.codes (sigListCalls D rad x.link)).om i).Smp)
    (arr : ℕ → ℕ → ℕ) (Fr : Frame) (base : ℕ) (hlow : ∀ i, (seat i).1 < base) :
    (k5Pin (Cells := Cells) (Tok := Tok) Gd x D rad seat smpR arr Fr base hlow).part =
      fun w => msgsOf D.codes (sigListCalls D rad x.link) seat arr w := rfl

/-- **K5Behind, whole, at the filled pin and the kind's row of the table.** -/
theorem k5Behind_at_table {Pp Xi : Type} {Fr : Frame} (Gd : FileDescription Xi) (p : Par) (ns base : ℕ)
    (gOf : First.S × Fr.E.Str → Forest.Heard) (on : First.S × Fr.E.Str → Prop) (Rds : ℕ → Readers)
    (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated) (Nn : Numbers)
    (Mg' : Meaning Pp (Wit Cells Tok MsgT)) (π : Pp) (links : List ModelPart) (pls : List Place) (k : ℕ)
    (arr : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem) (hi : ℕ)
    (smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((Johnson.Pack.sigOf D.codes (sigListCalls D rad x.link)).om i).Smp)
    (hlow : ∀ i, (seat i).1 < base)
    (hfT : ∀ (j : ℕ) (name : String) (b : First.S × Fr.E.Str) (w : Wit Cells Tok MsgT),
      Mg'.formsT x.link j name (π, b.1) (strsOf Fr b.2) w →
      ∀ p ∈ runs x.link j name, formsTQ (Rds x.link) St (Nn.sent x.link 0) p.1 p.2 b.1 (seatTab D.codes arr ms w))
    (o1 : outsQ links pls k (.formsT x.link 3 "own")) (o2 : outsQ links pls k (.formsT x.link 2 "join"))
    (hpub : TiePub D x A.seam.tl hi rad)
    (r1 : (2, "first") ∈ runs x.link 3 "own") (r2 : (2, "second") ∈ runs x.link 3 "own")
    (r3 : (2, "join") ∈ runs x.link 2 "join")
    {states : ℕ → List (VerifiableInference.Desc.K9.RunOf First.S)}
    (hRds : ∀ (name : String) (s : First.S) (R : VerifiableInference.Desc.K9.Read), (name == "K8.equations") = false →
      readerOf states 2 name s = some R → (Rds x.link).forms 2 name s = some R)
    (hst : states 2 = runsN A)
    {Cl St₀ J₀ : Type} [DecidableEq J₀] (claim : Aff → Cl) (hs : Forest.Shape) (lm first : ℕ) (ι : Fo.Pl → Option J₀)
    (Q : Fork → Prop) (x0 : First.S × Fr.E.Str → TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀))
    (hleft : ∀ a, on a →
      K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard hs lm first ι Q (x0 a) (gOf a) a.1)
    (hm : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link →
      StatedAtt St A (funsAt A) s)
    (hfront : ∀ a : First.S × Fr.E.Str, on a →
      FrontAll x A D (Nn.sent x.link 0)
        (psOf (sigListCalls D rad x.link) seat (readMsgs D x A.seam.tl))
        (qsOf (sigListCalls D rad x.link) (readMsgs D x A.seam.tl)) hi (gOf a) a.1)
    (m : ℕ) (smp : Pp × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((Johnson.Pack.sigOf D.codes s.l).om i).Smp)
    (hpin : Mg'.pin = pinJT D.codes Gd arr smp ms) (hopen : outsQ links pls k (.pin m 0))
    (hsome : ∀ i, ∃ y ∈ ms, Alike y (⟨⟨sigListCalls D rad x.link, seat⟩, i⟩ : Mem)) (hSB : SmpBySeat D.codes smp)
    (hsent : ∀ i, seat i ∈ Nn.sent m 0)
    (hsm : ∀ (s : First.S) i, smpR (s.st.oracles, s.book) i = smp (π, s) ⟨sigListCalls D rad x.link, seat⟩ i) :
    K5Behind x A.seam.tl D rad Ex Wp α A p ns base A.nW (plannedK A) (padOfO hs) [] gOf on
      (k5Pin (Cells := Cells) (Tok := Tok) Gd x D rad seat smpR arr Fr base hlow)
      (relAt (meansQ (Fr := Fr) Nn Mg' fun s => (π, s)) (outsQ links pls k)) where
  worth := k5Behind_worth_readers x A D rad Ex Wp α p ns base gOf on _ _ Rds runs St Nn
    arr seat ms hi (k5Pin_part x D rad Gd seat smpR arr Fr base hlow)
    (fun b w _ h => by
      have e1 : Mg'.formsT x.link 3 "own" (π, b.1) (strsOf Fr b.2) w := h _ o1
      have e2 : Mg'.formsT x.link 2 "join" (π, b.1) (strsOf Fr b.2) w := h _ o2
      exact ⟨hfT 3 "own" b w e1, hfT 2 "join" b w e2⟩)
    hpub r1 r2 r3 hRds hst claim hs lm first ι Q x0 hleft hm hSt hfront
  item := fun b w _ hR =>
    H2K5.Door.pinned_of_table Gd x D rad seat smpR arr Fr base hlow Nn Mg' links pls k m π smp ms hpin hopen hsome hSB hsent hsm b w hR

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5Pin_part
#print axioms VerifiableInference.Desc.First.Att.P.k5Behind_at_table
