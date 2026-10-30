-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5AtEqsPlus.lean: kind K5: **K5AtMg**
(Johnson/Desc/First/Att/K05AtMg.lean: all that the kind's law asks of the table's filling at an
attention segment: nine fields) AT ANY FILLING Mg THAT MEETS A LEAN STRUCTURE OF EQUATIONS: MEANT:
Mg := THE WIDER FILLING (Johnson/Desc/First/Att/Door/Plus.lean) OVER THE COMPOSED FILLING.
A TOOL, NOT A RESULT: most fields of K5AtMg are fenced by the table's
promise: at a filling whose promise never holds they are idle. What counts is the instance at the
composed meaning's one closed term (P5J.mgAtAll, Johnson/P5J/MgAtAll.lean).

After K5AtEqs.lean (not in this library; at another form of the composed
filling): what stays is taken over line for line, by program. WHAT TURNS:
  MgIs.pub: the composed tower over the wider foot: pubAll D (pubPlus L M D.d3 Mg0.pub) ·
  MgIs.inOrder: ((in0 a && c5 a.1) && "the statement's codes are cs") (mgAll_inOrder_at,
  with the wider clause) · MgIs.more: morePlus Mg0.more · K5Left.openQ: the ten, quiet9's eight,
  ledger.treesAre or K5.lookLeft · the calls k5Fill_at ↦ k5Fill_plus, madeMore_at ↦ madeMore_plus;
  every other file is called at base := the wider foot.
THREE STRUCTURES: MgIs (fifteen fields) · DataIs (five ties: by the make at mgAll's 𝔇.pubD) ·
K5Left (what is left: each field bears its owner in its docstring).
THE TOP: k5AtMg_of_eqs_plus. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5FillPlus
import Johnson.Desc.First.Att.Door.Law.LeftIsAt
import Johnson.Desc.First.Att.Door.Law.K5RelAt
import Johnson.Desc.First.Att.Door.Law.K5PublicAt
import Johnson.Desc.First.Att.Door.Law.KeptFormsAt
import Johnson.Desc.First.Att.Door.Law.MadeFormsAt
import Johnson.Desc.First.Att.Door.Law.MadeMorePlus
import Johnson.Desc.First.Att.Door.Law.MadeBehind
import Johnson.Desc.First.Att.Door.Law.ReadsThereTie
import Johnson.Desc.First.Att.K05AtMg
import Johnson.Desc.First.Att.K05GeoAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent attSg JAtt enMask lookAt placeAt k3SortAt)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.K9 (RunOf readerOf)
open VerifiableInference.Desc.K13.Law (DataK13 fillK13)
open VerifiableInference.OnPublicFiles (k3LeftItemAt k3LeftOnItemAt)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)

section
variable {Pp Xi Cells Tok Cl : Type} {nR : ℕ} {Fr : Frame}
  (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData)
  (cs : OnBytes.Codes) (G0 : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells)
  (in0 : Pp × S → Bool) (c5 : Pp → Bool) (Ld : Laid) (Ms : List OracleShape)
  (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR)

/-- **The equations on the filling.** Beside each: mgAll's own lemma. -/
structure MgIs : Prop where
  /-- mgAll_pub, with the wider foot -/
  pub : Mg.pub = pubAll D (pubPlus Ld Ms D.d3 Mg0.pub)
  /-- mgAll_pubP with the lookups' fill_pubP_left -/
  pubPl : ∀ m a, Mg.pubP (.left m) a = k3LeftItemAt D.d3.X m a.2
  /-- mgAll_pubP with the lookups' fill_pubP_leftOn -/
  pubPlo : ∀ m a, Mg.pubP (.leftOn m) a = k3LeftOnItemAt D.d3.X m a.2
  /-- mgAll_pubP with the lookups' fill_pubP_other; fillP1 (Johnson/Top/H0/Fill/FillP1.lean) stands between (its pubP hands every item that is not its own down) -/
  pubPo : ∀ q a, (∀ m, q ≠ .left m) → (∀ m, q ≠ .leftOn m) → (Mg0.pubP q a → Mg.pubP q a)
  /-- by the wider filling's own make (pubPPlus): at the five names nothing is said beside the test -/
  pubPw : ∀ q a, isWideQ q = true → Mg.pubP q a
  /-- mgAll_held -/
  held : Mg.held = fun j t (a : Pp × S) => smpHeld a.2.st a.2.book j t
  /-- mgAll_shown -/
  shown : Mg.shown = shownJT cs G0 ms
  /-- mgAll_noColl -/
  noColl : Mg.noColl = noCollJT cs G0 smp ms
  /-- mgAll_decodes -/
  decodes : Mg.decodes = decodesOf decT
  /-- mgAll_inOrder_at (in0: the base's own; c5: the request file's bytes are a request's), with the wider clause -/
  inOrder : ∀ a : Pp × S, Mg.inOrder a = ((in0 a && c5 a.1) && decide (a.2.st.codes = cs))
  /-- mgAll_pin -/
  pin : Mg.pin = pinJT cs G0 arr smp ms
  /-- mgAll_pinW -/
  pinW : Mg.pinW = pinWOf decT
  /-- mgAll_row, with the rows' layer's own text -/
  row : Mg.row = rowSays D.N (wordsAtFirst arr)
  /-- mgAll_pile -/
  pile : Mg.pile = (fillK13 D13 Mg0).pile
  /-- the wider list over mgAll_more_merges' merges -/
  more : Mg.more = morePlus Mg0.more

variable (Wv : Verify.Public) (links : List ModelPart) (m : ℕ)

/-- **The composed data's letters are the kind's.** By the make at mgAll's 𝔇.pubD
(Johnson/Desc/Sound/MgAll.lean). -/
structure DataIs : Prop where
  d3X : D.d3.X = Wv
  d5W : D.d5.W = Wv
  d5links : D.d5.links = links
  links : D.links = links
  own : D.d5.ownOf m = D.N.sent m 0

end

section
variable {Pp Xi Cells Tok Cl : Type} {nR : ℕ} {Fr : Frame}
  (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData)
  (cs : OnBytes.Codes)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (in0 : Pp × S → Bool)
  (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR)
  (bs : ℕ) (claim : Aff → Cl) (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : Look.Place)
  (Dn : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
  (I : PinItemP Fr seatSO bs (Wit Cells Tok MsgT) (attSg x Dn rad).Msg)
  (R' : Pp → S × Fr.E.Str → Wit Cells Tok MsgT → Prop)
  (links : List ModelPart) (pl : VerifiableInference.Desc.Place) (O : List Item) (Q : List Pub) (states : ℕ → List (RunOf S))

/-- K5AtMg's field leftIs, at ns := a.ns, as a sentence on the two letters that are found. -/
def LeftIsP (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (gOf : Pp → S × Fr.E.Str → Forest.Heard) : Prop :=
  ∀ π : Pp, ∀ a' : S × Fr.E.Str, Mg.pubP (.left (2 * g + 1)) (π, a'.1) →
    K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard x.fs x.lm x.F.next
      (Cb.Fo.NumsEq.placeOf (enMask x.ns a.seam.tl) plJ)
      (fun F => Room F a.ns x.F.next (Forest.elems x.fs + (slotsOf (script (parO Wv (2 * g + 1) a before).own) + 0)))
      ((x0 π) a') ((gOf π) a') a'.1

/-- **WHAT IS LEFT OF K5AtMg AT THE COMPOSED MEANING.** Each field with its owner. The guards of a
field over a verifier's state are the structure K5AtMg's own: the promise in front, no mark, an open
attention segment, the hearing's return. -/
structure K5Left : Prop where
  /-- THE COMPOSED MEANING's letter nsOf: the plan's number of slots at the segment. -/
  nsOf : D.nsOf (2 * g + 1) = some a.ns
  /-- THE COMPOSED MEANING's base: what it says beside the tests holds AT THE ITEMS THAT THE LAW TOUCHES (those open in front; three that the row makes), the two with a sentence of the lookup's files and the wider filling's five names apart. (At the closed constant P5J.mgAtAll the base's sentence is "somebody answers for the item": a written table: so this is a test on the list with that table; payer by name: mgAll_pubP_said, Johnson/Desc/Sound/MgBase.lean.) -/
  baseP : ∀ q a, (q ∈ Q ∨ q ∈ made3 (2 * g + 1)) → isWideQ q = false → (∀ m', q ≠ .left m') → (∀ m', q ≠ .leftOn m') → Mg0.pubP q a
  /-- THE COMPOSED MEANING's: the base's own "in order" rides over the lay (true outright at the closed base). -/
  baseIn : ∀ π s a h G, s.here = .att a → in0 (π, s) = true → in0 (π, behind s a h G) = true
  /-- THE COMPOSED MEANING's base: its door's filling makes nothing at the place (empty at the closed base). -/
  baseMakes : (Mg0.more.rows links pl).makes = []
  /-- THE COMPOSED MEANING's letter decT reads nothing that the kind's lay turns. -/
  decTq : ∀ π c s a h G, s.here = .att a → decT c (π, behind s a h G) = decT c (π, s)
  /-- THE COMPOSED MEANING's letter smp reads nothing that the kind's lay turns. -/
  smpq : ∀ π s a h G, s.here = .att a → smp (π, behind s a h G) = smp (π, s)
  /-- K13's FILES' letter rw13 reads nothing that the kind's lay turns. -/
  rwq : ∀ π s a h G, s.here = .att a → D13.rw (π, behind s a h G) = D13.rw (π, s)
  /-- PieceSeated.lean's seated_fenced: the sampled tenants of the open set lie below the base. -/
  low : ∀ t ∈ sampledIn D.N O, t.1 < bs
  /-- The same for the index masks' tenant. -/
  lowI : D.N.index.1 < bs
  /-- The same for the first sending's tenants. -/
  low0 : ∀ t ∈ D.N.sent (2 * g + 1) 0, t.1 < bs
  /-- THE TABLE (evaluated at two written lists; a law at every list is nobody's): every public item open in front of the sub-protocol is one of twenty. -/
  openQ : ∀ q ∈ Q, q ∈ ten (2 * g + 1) ∨ q ∈ quiet9 (2 * g + 1) ∨ q = .more (some (2 * g + 1)) "ledger.treesAre" ∨
    q = .more (some (2 * g + 1)) "K5.lookLeft"
  /-- THE TABLE: the ledger's item is open in front (the row asks it). -/
  ledQ : Pub.ledger (2 * g + 1) ∈ Q
  /-- THE TABLE: K5's item K5.readsThere is open in front (K5's door's row asks it). -/
  readsQ : Pub.more (some (2 * g + 1)) "K5.readsThere" ∈ Q
  /-- THE TABLE (evaluated): beside the index's, one tied test is met at the border: the run "objects"'. -/
  tiesO : ∀ i ∈ O, (rowOf links pl).ins.contains i = false → i ≠ .pinI → ∀ q ∈ tiesOf i, q = .formsInT (2 * g + 1) 2 "objects"
  /-- K5's WITH THE LOOKUPS': the reader of the run "objects" answers alike in front of and behind the lay. -/
  objR : ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
    onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
    hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → ∀ p ∈ D.runs (2 * g + 1) 2 "objects",
      (D.Rd (2 * g + 1)).forms p.1 p.2 (behind s att hd G) = (D.Rd (2 * g + 1)).forms p.1 p.2 s
  /-- K5's WITH THE LOOKUPS': the slots that this reader names as late lie below the ledger's next free slot. -/
  objLate : ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn), onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) →
    s.failed = none → s.here = .att att → ∀ p ∈ D.runs (2 * g + 1) 2 "objects", ∀ R,
      (D.Rd (2 * g + 1)).forms p.1 p.2 s = some R → ∀ t ∈ R.late, t.1 < att.F.next
  /-- THE COMPOSED MEANING's letter runs (Johnson/Desc/Sound/MgAt/Runs.lean). -/
  runs3 : D.runs (2 * g + 1) 3 "own" = [(2, "first"), (2, "keys"), (2, "second")]
  /-- The same. -/
  runsJ : D.runs (2 * g + 1) 2 "join" = [(2, "join")]
  /-- K5's (hRds_of_link | hRds_seated): what "the run itself" answers at block 2 the link's readers answer too. -/
  rds : ∀ (name : String) (s : S) (R : K9.Read), (name == "K8.equations") = false →
    readerOf states 2 name s = some R → (D.Rd (2 * g + 1)).forms 2 name s = some R
  /-- K5's: the letter states at block 2 (free: fun _ => runsN a pays it by rfl). -/
  st2 : states 2 = runsN a
  /-- K5's: the guard's (guardList_gives, from the door's seven rows). -/
  okAll : planOkAll a.S.cf a.S a.fs = true
  /-- K5's: the kind's four runs return at the state behind the lay; three facts on what was received from the lookup argument. -/
  runsRet : ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
    onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
    hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → RunsReturn a s att hd G
  /-- THE LOOKUPS' WITH K5's: the test tied to the run "planes" holds at the state behind the lay. -/
  planesIn : ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
    onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
    hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
    Mg.pub (.formsInT (2 * g + 1) 2 "planes") (π, behind s att hd G) = true
  /-- P5J.constrQAt (its text stands in files that did not compile in this file's build): another segment's constraint rides back. -/
  constr : ∀ π : Pp, ∀ n p, n ≠ 2 * g + 1 → ∀ s att hd G rs y y' w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) →
    s.failed = none → s.here = .att att → hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
    SameBelow Fr bs y y' → Mg.constr n p (π, behind s att hd G) (strsOf Fr y') w → Mg.constr n p (π, s) (strsOf Fr y) w
  /-- The same at this segment's smallness constraint. -/
  small : ∀ π : Pp, ∀ s att hd G rs y y' w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
    s.here = .att att → hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
    Mg.constr (2 * g + 1) .small (π, behind s att hd G) (strsOf Fr y') w → Mg.constr (2 * g + 1) .small (π, s) (strsOf Fr y) w
  /-- K5's WITH THE LOOKUPS': "the forms of the run objects are worth 0" rides back over the lay. -/
  objects : ∀ π : Pp, ∀ s att hd G rs y y' w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
    s.here = .att att → hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
    Mg.formsT (2 * g + 1) 2 "objects" (π, behind s att hd G) (strsOf Fr y') w →
    Mg.formsT (2 * g + 1) 2 "objects" (π, s) (strsOf Fr y) w
  /-- K5's: outright at the filled pin (pinOk_at_pin). -/
  pinOk : ∀ π : Pp, ∀ a', onT D.N Mg links π Fr pl O Q a' → I.ok (I.rc a'.1) a'.2
  /-- K5's (behind_plus): at whichever x0 | gOf meet leftIs. -/
  behind : ∀ x0 gOf, LeftIsP Mg claim Wv g before a x plJ x0 gOf → ∀ π : Pp,
    K5Behind x a.seam.tl Dn rad Ex Wp α a (parO Wv (2 * g + 1) a before) a.ns bs a.nW (plannedK a) (padOfO a.fs) [] (gOf π)
      (onT D.N Mg links π Fr pl O Q) I (R' π)
  /-- K5's WITH THE LOOKUPS' (ins_plus: idn · rider · keys are theorems; planes: not joined): at whichever x0 | gOf meet leftIs. -/
  ins : ∀ x0 gOf, LeftIsP Mg claim Wv g before a x plJ x0 gOf → ∀ π : Pp,
    K5FillIns Mg D.N links π Fr bs (2 * g + 1) pl O Q (parO Wv (2 * g + 1) a before).own x a.S a.seam.tl Dn rad Ex Wp α a.ns
      (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs)) (x0 π) I.part

end

section
variable {Pp Xi Cells Tok Cl : Type} {nR : ℕ} {Fr : Frame}

open Classical in
/-- **K5AtMg AT ANY MEANING THAT MEETS THE EQUATIONS.** -/
theorem k5AtMg_of_eqs_plus (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData) (cs : OnBytes.Codes) (G0 : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ) (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (in0 : Pp × S → Bool) (c5 : Pp → Bool)
    (Ld : Laid) (Ms : List OracleShape) (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR)
    (E : MgIs Mg Mg0 D cs G0 arr smp ms decT in0 c5 Ld Ms D13)
    (bs : ℕ) (claim : Aff → Cl) (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ)) (a : Attention.Plan) (x xd : Look.Place)
    (links : List ModelPart) (T : DataIs D Wv links (2 * g + 1))
    (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hx : lookAt Wv (2 * g + 1) false = some x)
    (hxd : lookAt Wv (2 * g + 1) true = some xd) {pl pl' : VerifiableInference.Desc.Place} (Ix : K5Place links (2 * g + 1) pl pl')
    (Dn : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
    (I : PinItemP Fr seatSO bs (Wit Cells Tok MsgT) (attSg x Dn rad).Msg)
    (R' : Pp → S × Fr.E.Str → Wit Cells Tok MsgT → Prop) (O : List Item) (Q : List Pub) (states : ℕ → List (RunOf S))
    (L : K5Left Mg Mg0 D cs smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ I R' links pl O Q states) :
    ∃ (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
      (gOf : Pp → S × Fr.E.Str → Forest.Heard),
      K5AtMg bs claim Wv (2 * g + 1) before a x Dn rad Ex Wp α a.ns [] x0 gOf plJ I R' D.N Mg links pl O Q
        (Look.P.ofPlace (Params.settingOf Wv.P.frame) false x) (Look.P.ofPlace (Params.settingOf Wv.P.frame) true xd)
        (D.d3.arrayOf.getD (2 * g + 1) #[]) (Forest.elems a.fs) a.ns := by
  obtain ⟨x0, gOf, hL⟩ := leftIs_at claim hP h4 ha hx (Cb.Fo.NumsEq.placeOf (enMask x.ns a.seam.tl) plJ)
  have hLP : LeftIsP (Fr := Fr) Mg claim Wv g before a x plJ (fun _ a' => x0 a'.1) (fun _ a' => gOf a'.1) := by
    intro π a' h
    rw [E.pubPl, T.d3X] at h
    exact hL a'.1 h
  have hsub : links[2 * g + 1]? = some .attention := Ix.sub
  have hatt : D.d5.isAtt (2 * g + 1) = true := isAtt_of D.d5 (by rw [T.d5links]; exact hsub)
  have hlay : isLay D.links (2 * g + 1) = false := att_not_lay (by rw [T.links]; exact hsub)
  have hf : D.d5.first? (2 * g + 1) = some (Forest.elems a.fs) :=
    first_at D.d5 (by rw [T.d5W]; exact hP) (by rw [T.d5W]; exact h4) (by rw [T.d5W]; exact ha) (by rw [T.d5W]; exact hx)
  have hPo : ∀ q a, (q ∈ Q ∨ q ∈ made3 (2 * g + 1)) → (∀ m', q ≠ .left m') → (∀ m', q ≠ .leftOn m') → Mg.pubP q a :=
    fun q a hq h1 h2 => by
      cases hw : isWideQ q with
      | true => exact E.pubPw q a hw
      | false => exact E.pubPo q a h1 h2 (L.baseP q a hq hw h1 h2)
  have gf : GeoFits (parCOf a).geo (parO Wv (2 * g + 1) a before).own := geoFits_at_seat hP ha L.okAll
  have hAm : D.d5.W.A[(2 * g + 1) / 2]? = some a := by
    rw [T.d5W, show (2 * g + 1) / 2 = g by omega]
    exact ha
  have hlink : ∀ {π : Pp} {s : S} {y : Fr.E.Str} {att : AttOwn}, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) →
      s.failed = none → s.here = .att att → att.L.link = 2 * g + 1 :=
    fun hon hu e => k5_link Ix e (onAt_shape hon hu)
  have hreads : ∀ {π : Pp} {s : S} {y : Fr.E.Str}, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      readsThereB D.d5.W (D.N.sent (2 * g + 1) 0) s = true := by
    intro π s y hon hu
    have := onAt_pub hon hu _ L.readsQ
    rwa [E.pub, pubAll_more_readsThere D _ _ hatt, T.own] at this
  have hsz : ∀ {π : Pp} {s : S} {y : Fr.E.Str}, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.fork?.any K3.sizedB = true := by
    intro π s y hon hu
    have := onAt_pub hon hu _ L.ledQ
    rwa [E.pub] at this
  refine ⟨fun _ a' => x0 a'.1, fun _ a' => gOf a'.1, ?_⟩
  exact
    { fill := fun π => k5Fill_plus D (pubPlus Ld Ms D.d3 Mg0.pub) Mg π Ld Ms Mg0.pub rfl E.pub E.pubPl E.pubPlo E.held cs G0 smp ms
        E.shown E.noColl decT E.decodes in0 cs c5 E.inOrder hatt hlay hf L.nsOf
        (by rw [T.d3X]; exact placeAt_of hx) (by rw [T.d3X]; exact placeAt_of hxd)
        (by rw [T.d3X]; exact sort2 h4 g) (by rw [T.d3X]; exact sort7 h4 g) (L.decTq π) (L.smpq π) (L.baseIn π)
        D.N O Q Fr bs _ L.low L.openQ hPo
      keptForms := keptForms_at D (pubPlus Ld Ms D.d3 Mg0.pub) Mg E.pub D.N links pl O Q Fr (2 * g + 1) _ L.ledQ L.tiesO L.objR L.objLate
      madeForms := madeForms_at D (pubPlus Ld Ms D.d3 Mg0.pub) Mg E.pub D.N links pl O Q Fr (2 * g + 1) _ a states L.ledQ L.runs3 L.runsJ L.rds L.st2 gf
        (fun π s y att hon hu e => u3There_of_sheet D.d5.W _ s att e a (by rw [hlink hon hu e]; exact hAm) (hreads hon hu))
        L.runsRet L.planesIn
      madeMore := madeMore_plus D (pubPlus Ld Ms D.d3 Mg0.pub) Mg E.pub Mg0.more E.more D.N links O Q Fr Ix L.baseMakes _ hatt hAm
        (fun a' => ⟨hPo _ a' (Or.inr (by simp [made3])) (fun _ => by simp) (fun _ => by simp),
          hPo _ a' (Or.inr (by simp [made3])) (fun _ => by simp) (fun _ => by simp)⟩)
        (fun π s y att hd G rs hon hu e hh => ok_made_behind e hh (hsz hon hu) gf)
        (fun π s y att hd G rs hon hu e hh => plain_made_behind D.d5.W _ e (by rw [hlink hon hu e]; exact hAm) hh (hsz hon hu)
          (hreads hon hu))
      leftIs := hLP
      pinOk := L.pinOk
      behind := L.behind _ _ hLP
      rel := fun π => k5Rel_at D.d5 Mg Mg0 π D13 E.pile cs G0 arr smp ms E.pin D.N E.row decT E.pinW (L.rwq π) (L.smpq π) (L.decTq π)
        links Fr bs (2 * g + 1) pl O Q _ L.lowI L.low0 (L.constr π) (L.small π) (L.objects π)
      ins := L.ins _ _ hLP }

end

#print axioms k5AtMg_of_eqs_plus

end H2K5.Door
