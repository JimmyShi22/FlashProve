-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05AtMgBehind.lean: kind K5: THE FIELD "behind" OF K5AtMg (Att/K05AtMg.lean: what the kind's law asks of the table's meaning at attention segment m), TO THE LETTER, AS ONE THEOREM: at every π:
  K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv m a before) ns base a.nW (plannedK a) (padOfO a.fs) tj (gOf π) (onT N Mg links π Fr pl O Q) I (R' π)
at tj := [] · I := the filled pin k5Pin … · R' π := what the kind's row of the table opens and reads (relAt (meansQ N Mg fun s => (π, s)) (outsQ links pls k)).
By k5Behind_at_table (Att/K05BehindAtTable.lean), called at the law's own letters: hs := x.fs · lm := x.lm · first := x.F.next · ι := placeOf (enMask x.ns a.seam.tl) plJ · Q := "room for the lookup's and the block's slots" · St₀ := Unit ·
J₀ := JAtt x.ns a.seam.tl · on := the table's promise in front onT.
OVER THE CURED Returns and files of a trial
build: NOTHING COUNTED.
Main names: k5AtMg_behind · k5AtMg_behind_door (hSt and hfront paid: in their place hA · hP · hdoor) · k5AtMg_fits (Lean's own check that the premise leftIs and the conclusion are K5AtMg's two fields' types, at these letters).
WHAT IT TAKES OF K5AtMg ITSELF: its field leftIs, to the letter (so the two fields are tied: "behind" follows from "leftIs" and the premises below).
THE PREMISES BESIDE: hfs : x.fs = a.fs · hleftQ : the public item "left m" is in the promise's list Q · and k5Behind_at_table's own, those that name π under "for all π": hfT · hsm · hfront.
THE LETTERS UNDER "FOR ALL": π: free on purpose (the field's own) · a' in leftIs: the field's own · the rest as in k5Behind_at_table.
IS IT EMPTY HERE? An implication: whether the premises can be met together is shown nowhere.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05BehindAtTable
import Johnson.Desc.First.Att.K05AtMg
import Johnson.Desc.First.Att.K05FrontOfDoor
import Johnson.Desc.First.Att.K05StatedArm

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

open VerifiableInference.Desc.First (Pub)
open VerifiableInference.Desc.First.Look (enMask)

theorem k5AtMg_behind {Cells Tok Cl Pp Xi : Type} {Fr : Frame} (base : ℕ) (claim : Aff → Cl) (Wv : Verify.Public) (m : ℕ)
    (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns : ℕ)
    (x0 : Pp → First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (gOf : Pp → First.S × Fr.E.Str → Forest.Heard) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl) (N : Numbers)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (links : List ModelPart) (pl : Place) (O : List Item) (Q : List Pub)
    (leftIs : ∀ π : Pp, ∀ a' : First.S × Fr.E.Str, Mg.pubP (.left m) (π, a'.1) →
      K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork
        (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
        (Cb.Fo.NumsEq.placeOf (enMask x.ns a.seam.tl) plJ)
        (fun F => Room F ns x.F.next
          (Forest.elems x.fs + (slotsOf (script (parO Wv m a before).own) + 0))) ((x0 π) a') ((gOf π) a') a'.1)
    (hfs : x.fs = a.fs) (hleftQ : Pub.left m ∈ Q)
    (Gd : FileDescription Xi) (Rds : ℕ → Readers) (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
    (pls : List Place) (k : ℕ)
    (arrN : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem) (hi : ℕ)
    (smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((Johnson.Pack.sigOf D.codes (sigListCalls D rad x.link)).om i).Smp)
    (hlow : ∀ i, (seat i).1 < base)
    (hfT : ∀ (π : Pp) (j : ℕ) (name : String) (b : First.S × Fr.E.Str) (w : Wit Cells Tok MsgT),
      Mg.formsT x.link j name (π, b.1) (strsOf Fr b.2) w →
      ∀ p ∈ runs x.link j name, formsTQ (Rds x.link) St (N.sent x.link 0) p.1 p.2 b.1 (seatTab D.codes arrN ms w))
    (o1 : outsQ links pls k (.formsT x.link 3 "own")) (o2 : outsQ links pls k (.formsT x.link 2 "join"))
    (hpub : TiePub D x a.seam.tl hi rad)
    (r1 : (2, "first") ∈ runs x.link 3 "own") (r2 : (2, "second") ∈ runs x.link 3 "own")
    (r3 : (2, "join") ∈ runs x.link 2 "join")
    {states : ℕ → List (VerifiableInference.Desc.K9.RunOf First.S)}
    (hRds : ∀ (name : String) (s : First.S) (R : VerifiableInference.Desc.K9.Read), (name == "K8.equations") = false →
      readerOf states 2 name s = some R → (Rds x.link).forms 2 name s = some R)
    (hst : states 2 = runsN a)
    (hm : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr a.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link →
      StatedAtt St a (funsAt a) s)
    (hfront : ∀ (π : Pp) (a' : First.S × Fr.E.Str), onT N Mg links π Fr pl O Q a' →
      FrontAll x a D (N.sent x.link 0)
        (psOf (sigListCalls D rad x.link) seat (readMsgs D x a.seam.tl))
        (qsOf (sigListCalls D rad x.link) (readMsgs D x a.seam.tl)) hi (gOf π a') a'.1)
    (mP : ℕ) (smp : Pp × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((Johnson.Pack.sigOf D.codes s.l).om i).Smp)
    (hpin : Mg.pin = pinJT D.codes Gd arrN smp ms) (hopen : outsQ links pls k (.pin mP 0))
    (hsome : ∀ i, ∃ y ∈ ms, Alike y (⟨⟨sigListCalls D rad x.link, seat⟩, i⟩ : Mem)) (hSB : SmpBySeat D.codes smp)
    (hsent : ∀ i, seat i ∈ N.sent mP 0)
    (hsm : ∀ (π : Pp) (s : First.S) i, smpR (s.st.oracles, s.book) i = smp (π, s) ⟨sigListCalls D rad x.link, seat⟩ i) :
    ∀ π : Pp, K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv m a before) ns base a.nW (plannedK a)
      (padOfO a.fs) [] (gOf π) (onT N Mg links π Fr pl O Q)
      (k5Pin (Cells := Cells) (Tok := Tok) Gd x D rad seat smpR arrN Fr base hlow)
      (relAt (meansQ (Fr := Fr) N Mg fun s => (π, s)) (outsQ links pls k)) := by
  intro π
  have h := k5Behind_at_table x a D rad Ex Wp α Gd (parO Wv m a before) ns base (gOf π) (onT N Mg links π Fr pl O Q) Rds runs St
    N Mg π links pls k arrN seat ms hi smpR hlow (hfT π) o1 o2 hpub r1 r2 r3 hRds hst claim x.fs x.lm x.F.next
    (Cb.Fo.NumsEq.placeOf (enMask x.ns a.seam.tl) plJ)
    (fun F => Room F ns x.F.next (Forest.elems x.fs + (slotsOf (script (parO Wv m a before).own) + 0))) (x0 π)
    (fun a' hon => leftIs π a' (onAt_pubP hon.1 hon.2 _ hleftQ)) hm hSt (hfront π) mP smp hpin hopen hsome hSB hsent (hsm π)
  rw [hfs] at h
  exact h

/-- **The same, with hSt and hfront paid**: the stated function is the one of three arms, K5's uArm Wv (Att/K05StatedArm.lean: hSt_of_arm); what is asked in front follows from the yes of six public tests with code at the verifier's state, one
bound, what was received from the lookup argument and five equations on the open link (Att/K05FrontOfDoor.lean: DoorYes · frontAll_of_door). -/
theorem k5AtMg_behind_door {Cells Tok Cl Pp Xi : Type} {Fr : Frame} (base : ℕ) (claim : Aff → Cl) (Wv : Verify.Public) (m : ℕ)
    (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns : ℕ)
    (x0 : Pp → First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (gOf : Pp → First.S × Fr.E.Str → Forest.Heard) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl) (N : Numbers)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (links : List ModelPart) (pl : Place) (O : List Item) (Q : List Pub)
    (leftIs : ∀ π : Pp, ∀ a' : First.S × Fr.E.Str, Mg.pubP (.left m) (π, a'.1) →
      K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork
        (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
        (Cb.Fo.NumsEq.placeOf (enMask x.ns a.seam.tl) plJ)
        (fun F => Room F ns x.F.next
          (Forest.elems x.fs + (slotsOf (script (parO Wv m a before).own) + 0))) ((x0 π) a') ((gOf π) a') a'.1)
    (hfs : x.fs = a.fs) (hleftQ : Pub.left m ∈ Q)
    (Gd : FileDescription Xi) (Rds : ℕ → Readers) (runs : ℕ → ℕ → String → List (ℕ × String))
    (uL uH : ℕ → VerifiableInference.Desc.Sound.UFn)
    (pls : List Place) (k : ℕ)
    (arrN : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem) (hi : ℕ)
    (smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((Johnson.Pack.sigOf D.codes (sigListCalls D rad x.link)).om i).Smp)
    (hlow : ∀ i, (seat i).1 < base)
    (hfT : ∀ (π : Pp) (j : ℕ) (name : String) (b : First.S × Fr.E.Str) (w : Wit Cells Tok MsgT),
      Mg.formsT x.link j name (π, b.1) (strsOf Fr b.2) w →
      ∀ p ∈ runs x.link j name, formsTQ (Rds x.link) (Stated.of (VerifiableInference.Desc.Sound.uBySort uL (uArm Wv) uH)) (N.sent x.link 0) p.1 p.2 b.1
        (seatTab D.codes arrN ms w))
    (o1 : outsQ links pls k (.formsT x.link 3 "own")) (o2 : outsQ links pls k (.formsT x.link 2 "join"))
    (hpub : TiePub D x a.seam.tl hi rad)
    (r1 : (2, "first") ∈ runs x.link 3 "own") (r2 : (2, "second") ∈ runs x.link 3 "own")
    (r3 : (2, "join") ∈ runs x.link 2 "join")
    {states : ℕ → List (VerifiableInference.Desc.K9.RunOf First.S)}
    (hRds : ∀ (name : String) (s : First.S) (R : VerifiableInference.Desc.K9.Read), (name == "K8.equations") = false →
      readerOf states 2 name s = some R → (Rds x.link).forms 2 name s = some R)
    (hst : states 2 = runsN a)
    (hm : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr a.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hA : Wv.A[x.link / 2]? = some a) (hP : K5Law.OfPlan a)
    (hdoor : ∀ (π : Pp) (a' : First.S × Fr.E.Str), onT N Mg links π Fr pl O Q a' →
      DoorYes Wv x D (VerifiableInference.Desc.First.Look.bornAt D x.link) (VerifiableInference.Desc.First.Look.keptAt D x.link).length
        (N.sent x.link 0)
        (psOf (sigListCalls D rad x.link) seat (readMsgs D x a.seam.tl))
        (qsOf (sigListCalls D rad x.link) (readMsgs D x a.seam.tl)) hi (gOf π a') a'.1)
    (mP : ℕ) (smp : Pp × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((Johnson.Pack.sigOf D.codes s.l).om i).Smp)
    (hpin : Mg.pin = pinJT D.codes Gd arrN smp ms) (hopen : outsQ links pls k (.pin mP 0))
    (hsome : ∀ i, ∃ y ∈ ms, Alike y (⟨⟨sigListCalls D rad x.link, seat⟩, i⟩ : Mem)) (hSB : SmpBySeat D.codes smp)
    (hsent : ∀ i, seat i ∈ N.sent mP 0)
    (hsm : ∀ (π : Pp) (s : First.S) i, smpR (s.st.oracles, s.book) i = smp (π, s) ⟨sigListCalls D rad x.link, seat⟩ i) :
    ∀ π : Pp, K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv m a before) ns base a.nW (plannedK a)
      (padOfO a.fs) [] (gOf π) (onT N Mg links π Fr pl O Q)
      (k5Pin (Cells := Cells) (Tok := Tok) Gd x D rad seat smpR arrN Fr base hlow)
      (relAt (meansQ (Fr := Fr) N Mg fun s => (π, s)) (outsQ links pls k)) :=
  k5AtMg_behind base claim Wv m before a x D rad Ex Wp α ns x0 gOf plJ N Mg links pl O Q leftIs hfs hleftQ Gd Rds runs
    (Stated.of (VerifiableInference.Desc.Sound.uBySort uL (uArm Wv) uH)) pls k arrN seat ms hi smpR hlow hfT o1 o2 hpub r1 r2 r3
    hRds hst hm (fun s a₀ h hl => hSt_of_arm hA uL uH s a₀ h hl) (fun π a' hon => frontAll_of_door hA hP (hdoor π a' hon)) mP smp hpin
    hopen hsome hSB hsent hsm

/-- **Lean's own check that the letters fit**: in a K5AtMg at tj := [], the filled pin and the row's relation, the field "behind" may be laid anew by k5AtMg_behind, called at that structure's own field leftIs: so the premise leftIs above IS that
field's type, and the conclusion above IS the field "behind"'s type. (It proves nothing new: H holds a "behind" already.) -/
theorem k5AtMg_fits {Cells Tok Cl Pp Xi : Type} {Fr : Frame} (base : ℕ) (claim : Aff → Cl) (Wv : Verify.Public) (m : ℕ)
    (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns : ℕ)
    (x0 : Pp → First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (gOf : Pp → First.S × Fr.E.Str → Forest.Heard) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl) (N : Numbers)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (links : List ModelPart) (pl : Place) (O : List Item) (Q : List Pub)
    (hfs : x.fs = a.fs) (hleftQ : Pub.left m ∈ Q)
    (Gd : FileDescription Xi) (Rds : ℕ → Readers) (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
    (pls : List Place) (k : ℕ)
    (arrN : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem) (hi : ℕ)
    (smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls D rad x.link).length) →
      Option ((Johnson.Pack.sigOf D.codes (sigListCalls D rad x.link)).om i).Smp)
    (hlow : ∀ i, (seat i).1 < base)
    (hfT : ∀ (π : Pp) (j : ℕ) (name : String) (b : First.S × Fr.E.Str) (w : Wit Cells Tok MsgT),
      Mg.formsT x.link j name (π, b.1) (strsOf Fr b.2) w →
      ∀ p ∈ runs x.link j name, formsTQ (Rds x.link) St (N.sent x.link 0) p.1 p.2 b.1 (seatTab D.codes arrN ms w))
    (o1 : outsQ links pls k (.formsT x.link 3 "own")) (o2 : outsQ links pls k (.formsT x.link 2 "join"))
    (hpub : TiePub D x a.seam.tl hi rad)
    (r1 : (2, "first") ∈ runs x.link 3 "own") (r2 : (2, "second") ∈ runs x.link 3 "own")
    (r3 : (2, "join") ∈ runs x.link 2 "join")
    {states : ℕ → List (VerifiableInference.Desc.K9.RunOf First.S)}
    (hRds : ∀ (name : String) (s : First.S) (R : VerifiableInference.Desc.K9.Read), (name == "K8.equations") = false →
      readerOf states 2 name s = some R → (Rds x.link).forms 2 name s = some R)
    (hst : states 2 = runsN a)
    (hm : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr a.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link →
      StatedAtt St a (funsAt a) s)
    (hfront : ∀ (π : Pp) (a' : First.S × Fr.E.Str), onT N Mg links π Fr pl O Q a' →
      FrontAll x a D (N.sent x.link 0)
        (psOf (sigListCalls D rad x.link) seat (readMsgs D x a.seam.tl))
        (qsOf (sigListCalls D rad x.link) (readMsgs D x a.seam.tl)) hi (gOf π a') a'.1)
    (mP : ℕ) (smp : Pp × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((Johnson.Pack.sigOf D.codes s.l).om i).Smp)
    (hpin : Mg.pin = pinJT D.codes Gd arrN smp ms) (hopen : outsQ links pls k (.pin mP 0))
    (hsome : ∀ i, ∃ y ∈ ms, Alike y (⟨⟨sigListCalls D rad x.link, seat⟩, i⟩ : Mem)) (hSB : SmpBySeat D.codes smp)
    (hsent : ∀ i, seat i ∈ N.sent mP 0)
    (hsm : ∀ (π : Pp) (s : First.S) i, smpR (s.st.oracles, s.book) i = smp (π, s) ⟨sigListCalls D rad x.link, seat⟩ i)
    (pC pD : Look.P) (arr : Array (ℕ × String)) (first nsPlan : ℕ)
    (H : K5AtMg base claim Wv m before a x D rad Ex Wp α ns [] x0 gOf plJ
      (k5Pin (Cells := Cells) (Tok := Tok) Gd x D rad seat smpR arrN Fr base hlow)
      (fun π => relAt (meansQ (Fr := Fr) N Mg fun s => (π, s)) (outsQ links pls k)) N Mg links pl O Q pC pD arr first nsPlan) :
    K5AtMg base claim Wv m before a x D rad Ex Wp α ns [] x0 gOf plJ
      (k5Pin (Cells := Cells) (Tok := Tok) Gd x D rad seat smpR arrN Fr base hlow)
      (fun π => relAt (meansQ (Fr := Fr) N Mg fun s => (π, s)) (outsQ links pls k)) N Mg links pl O Q pC pD arr first nsPlan :=
  { H with
    behind := k5AtMg_behind base claim Wv m before a x D rad Ex Wp α ns x0 gOf plJ N Mg links pl O Q H.leftIs hfs hleftQ Gd Rds runs St
      pls k arrN seat ms hi smpR hlow hfT o1 o2 hpub r1 r2 r3 hRds hst hm hSt hfront mP smp hpin hopen hsome hSB hsent hsm }

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5AtMg_behind
#print axioms VerifiableInference.Desc.First.Att.P.k5AtMg_behind_door
#print axioms VerifiableInference.Desc.First.Att.P.k5AtMg_fits
