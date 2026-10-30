-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5AtMgPaid.lean: kind K5: **WHAT IS LEFT OF THE KIND's LAW AT THE
TABLE, AS ONE LEAN STRUCTURE (K5Owes), AND K5AtMg FROM IT.** K5AtMg
(Johnson/Desc/First/Att/K05AtMg.lean) is all that the kind's law asks of the table's filling at an
attention segment. Here it follows, at any filling Mg that meets four structures of equations (MgIs
· MgGains · DataIs · DataSent: meant: the wider filling over the composed filling),
from facts on the plan and K5Owes: every premise that the
theorems of K5's files still take, a field each, with the files that owe it in the docstring.

IS IT EMPTY HERE? NO MEMBER OF K5Owes IS SHOWN: whether its fields can be met together is shown
nowhere. Most conclusions are fenced by the table's promise: at a filling whose promise never holds
they are idle. A TOOL, NOT A RESULT.

Main names:
  `K5Table`: four of the fields, apart: tests on the table's lists alone: at the full written list
    of segments another file decides all four by the kernel
    (Johnson/Desc/First/Att/Door/Law/K5ListsFull.lean, at this wider list, if its version is this
    file's): k5Table_full (Johnson/Desc/First/Att/Door/Law/K5TableFull.lean).
  `K5Rest`, `K5Owes`: the other fields; both together (cut in two parents, so that at a
    written list K5Owes is made from K5Rest alone; planesIn AND the clause "planes" of
    K5FillIns are no fields: planesIn_plus | planes_plus
    (Johnson/Desc/First/Att/Door/Law/K5LeftFitsF.lean | K5LeftFitsG.lean) are called, the first over
    hleft_plus (the fifth name's test under the promise), the second over hBare_plus |
    hH5_plus (K5LeftFitsH.lean); in their place six fields, none on a state: lmIs · posG ·
    planesOkAt · planesAt · clForm · colsFit: 45 in all). FIRST: thirteen fields of K5Left
    (K5AtEqsPlus.lean) that no theorem of K5's files pays yet, text for text, cut by program. THEN:
    the leaves of the payers of its other sixteen. NOT FIELDS: bare (a lemma
    from the promise at the wider filling's fourth name: hbare_plus) · mem (the caller's list is no
    sending of the composed meaning's (mgAll, MgAll.lean) list of members: the fields are someMem
    · smpBySeat).
    OUT, PAID BY THEOREMS (K5LeftFitsD.lean · K5LeftFitsE.lean): runs3 · runsJ ·
    runsO · okAll · st2 · rds · objR · objLate · notHead · attOK · callsFit · planOk · claimsOk.
  `k5Left_plus`: K5Left, a structure instance: ledQ, readsQ: OpenQ's · pinOk: pinOk_at_pin · behind:
    behind_plus · runsRet, objects, small, constr, ins: ‹field›_plus
    (Johnson/Desc/First/Att/Door/Law/K5LeftFitsB.lean), with hdoor := hdoor_plus, the small joins of
    Johnson/Desc/First/Att/Door/Law/K5LeftSmall.lean, hWr | hWk := hW_rider | hW_keys.
  `k5AtMg_plus`: **K5AtMg**, with x0 and gOf found by leftIs_at.
A TAG IN EACH FIELD's DOCSTRING SAYS ITS KIND: [L] a test on the written lists · [P] a test on
public data · [C] a test at a closed letter of the composed meaning (P5J.At) · [M] by a letter's
make (an equation, or a law that is true at all states or at none) · [O] on the seated segment: from
an opening of the written description · [T] mathematics · [S] a law over witnesses that hides the
tie to the model. FOR A MEMBER AT mgAll's CLOSED TERM ALL BUT THE FIRST THREE MUST REACH ZERO (as
theorems at that term); what may stay is what a test with code can show. (The tags are by reading:
digitsBack | bodyBack are [M] on a survey of
the closed letters' texts.) LETTERS THAT THE JOIN FIXES: cs := Dn.codes · states := fun _ => runsN a
· the setting := Params.settingOf Wv.P.frame · the lookup argument's files' seats and numbers are
the pin's (seat, arr) · I := the filled pin · R' := the table's relation behind the sub-protocol.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Door.Law.K5LeftFits
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsB
import Johnson.Desc.First.Att.Door.Law.K5LeftSmall
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsE
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsF
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsH
import Johnson.Desc.First.Look.K3GoodInCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent attSg JAtt enMask lookAt sigListCalls keptAt CellsAre)
open VerifiableInference.Desc.K9 (RunOf readerOf)
open VerifiableInference.Desc.K13.Law (DataK13)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open OnBytes.Road.L5 (dimOf Zs cellsA)

section
variable {Pp Xi Cells Tok Cl Ix : Type} {nR : ℕ} {Fr : Frame}
  (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData) (Dn : Sent) (G0 : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf Dn.codes s.l).om i).Smp) (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (in0 : Pp × S → Bool)
  (Ld : Laid) (Ms : List OracleShape) (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR)
  (bs : ℕ) (claim : Aff → Cl) (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : Look.Place)
  (links : List ModelPart) (pl : VerifiableInference.Desc.Place) (rad : OracleShape → Nat) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
  (O : List Item) (Q : List Pub) (uL uH : ℕ → UFn)
  (seat : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ)
  (smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls Dn rad x.link).length) →
    Option ((sigOf Dn.codes (sigListCalls Dn rad x.link)).om i).Smp)
  (lk : ℕ → Option (Link S Claim)) (Lk : Link S Claim) (same : S → S → Bool) (blk : Block S Claim)
  (claimC : Aff → Claim) (nm : String)
  (Hd : Cells → Ix → Prop) (bsW : ℕ → Wit Cells Tok MsgT → Prop)
  (dP : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop) (body : ℕ → First.Part → Ix → Pp × S → Strs → Wit Cells Tok MsgT → Prop)
  (Zof : Wit Cells Tok MsgT → Zs)

/-- **The four fields that are tests on the table's lists alone** (no filling, no plan, no state):
at a written list of segments each is decided by evaluation. -/
structure K5Table : Prop where
  /-- [L] THE TABLE (evaluated at two written lists; a law at every list is nobody's): every public item open in front of the sub-protocol is one of twenty. -/
  openQ : ∀ q ∈ Q, q ∈ ten (2 * g + 1) ∨ q ∈ quiet9 (2 * g + 1) ∨ q = .more (some (2 * g + 1)) "ledger.treesAre" ∨
    q = .more (some (2 * g + 1)) "K5.lookLeft"
  /-- [L] THE TABLE (evaluated): beside the index's, one tied test is met at the border: the run "objects"'. -/
  tiesO : ∀ i ∈ O, (rowOf links pl).ins.contains i = false → i ≠ .pinI → ∀ q ∈ tiesOf i, q = .formsInT (2 * g + 1) 2 "objects"
  /-- [L] THE TABLE (evaluated at two written lists of segments; to be decided by the kernel): fourteen public items are open in front of the sub-protocol, at the wider list. -/
  openIn : OpenQ (2 * g + 1) Q
  /-- [L] THE TABLE: the test tied to the item "objects" is asked at the border. -/
  tiedObj : Pub.formsInT (2 * g + 1) 2 "objects" ∈ pubOfItems O

/-- **The other fields**: on the filling, the plan, the composed meaning's letters, the verifier's
states. A field a premise; the files that owe it in the docstring. -/
structure K5Rest : Prop where
  /-- [C] THE COMPOSED MEANING's letter nsOf: the plan's number of slots at the segment. -/
  nsOf : D.nsOf (2 * g + 1) = some a.ns
  /-- [M] THE COMPOSED MEANING's base: what it says beside the tests holds AT THE ITEMS THAT THE LAW TOUCHES (those open in front; three that the row makes), the two with a sentence of the lookup argument's files and the wider filling's five names apart. At the closed constant the base's sentence is "somebody answers for the item" (a written table, saysNone, Johnson/Desc/First/AllSaid.lean): payer by name: mgAll_pubP_said (Johnson/Desc/Sound/MgBase.lean), WITH a test on the list against that table (a reported evaluation at the full list, not shown here: every such item is answered for). -/
  baseP : ∀ q a, (q ∈ Q ∨ q ∈ made3 (2 * g + 1)) → isWideQ q = false → (∀ m', q ≠ .left m') → (∀ m', q ≠ .leftOn m') → Mg0.pubP q a
  /-- [M] THE COMPOSED MEANING's: the base's own "in order" rides over the lay (true outright at the closed base). -/
  baseIn : ∀ π s a h G, s.here = .att a → in0 (π, s) = true → in0 (π, behind s a h G) = true
  /-- [M] THE COMPOSED MEANING's base: its door's filling makes nothing at the place (empty at the closed base). -/
  baseMakes : (Mg0.more.rows links pl).makes = []
  /-- [M] THE COMPOSED MEANING's letter decT reads nothing that the kind's lay turns. -/
  decTq : ∀ π c s a h G, s.here = .att a → decT c (π, behind s a h G) = decT c (π, s)
  /-- [M] THE COMPOSED MEANING's letter smp reads nothing that the kind's lay turns. -/
  smpq : ∀ π s a h G, s.here = .att a → smp (π, behind s a h G) = smp (π, s)
  /-- [M] OTHER FILES' letter rw13 reads nothing that the kind's lay turns. -/
  rwq : ∀ π s a h G, s.here = .att a → D13.rw (π, behind s a h G) = D13.rw (π, s)
  /-- [C] seated_fenced (PieceSeated.lean): the open set's sampled tenants lie below the base. -/
  low : ∀ t ∈ sampledIn D.N O, t.1 < bs
  /-- [C] The same for the index masks' tenant. -/
  lowI : D.N.index.1 < bs
  /-- [C] The same for the first sending's tenants. -/
  low0 : ∀ t ∈ D.N.sent (2 * g + 1) 0, t.1 < bs
  /-- [P] K5's FILES' (K05_public_of_open, Johnson/H2K5R/PublicAtEntry.lean) BUT FOR ONE HALF: SymsOK: THE LOOKUP ARGUMENT's FILES' test readsB: unpaid, theirs: four facts on public data. -/
  tiePub : TiePub Dn x a.seam.tl a.ns rad
  /-- [P] K5's FILES' (K05_facts_of_open, Johnson/H2K5R/LawAtLaid.lean): the guard's yes. -/
  guard : k5GuardN Wv (2 * g + 1) g = true
  /-- [C] TWO TESTS ON PUBLIC DATA (K5's files'; STATED AT THE COMPOSED DATA's dS: RUN NOWHERE AT THAT TERM): the seats. -/
  seatsPlan : seatsPlanB D.dS (2 * g + 1) (keptAt Dn x.link).length Ld
    (psOf (sigListCalls Dn rad x.link) seat (readMsgs Dn x a.seam.tl)) (D.N.sent x.link 0) (D.N.msgsAt (some pl)) = true
  /-- [C] The shapes. -/
  shapesPlan : shapesPlanB D.dS (2 * g + 1) (keptAt Dn x.link).length Ms
    (qsOf (sigListCalls Dn rad x.link) (readMsgs Dn x a.seam.tl)) (D.N.msgsAt (some pl)) = true
  /-- [C] THE COMPOSED MEANING's list of members: each message that the law reads is a member at its seat. -/
  memAt : ∀ (fs : List Aff) (j : Fin (sigListCalls Dn rad x.link).length),
    ReadMsg (ReadAddr a.seam.tl fs) Dn x.link j.val → MemAt ms (sigListCalls Dn rad x.link) seat j
  /-- [C] THE COMPOSED MEANING's numbers: the seats lie in the segment's first sending. -/
  sent : ∀ i, seat i ∈ D.N.sent (2 * g + 1) 0
  /-- [M] THE COMPOSED MEANING's letter smp: the filled pin's sample is smp at the sending. -/
  smpIs : ∀ (π : Pp) (s : S) i, smpR (s.st.oracles, s.book) i = smp (π, s) ⟨sigListCalls Dn rad x.link, seat⟩ i
  /-- [O] THE LOOKUP ARGUMENT's FILES' WITH K5's (by Lake at the seated link; the join to the composed meaning's readers: untyped): the reader of the run "objects". -/
  objIs : ∀ (t : S) (F : Fork) (g₁ : Forest.Heard), t.fork? = some F → t.lookHeard? = some g₁ →
    (∀ f ∈ g₁.rows.toList, f.ents = #[]) → (D.Rd (2 * g + 1)).forms 1 "objects" t = some { forms := g₁.rows.toList, late := [] }
  /-- [O] The same: the reader of the run "guests". -/
  gstIs : ∀ (t : S) (F : Fork), t.fork? = some F → (D.Rd (2 * g + 1)).forms 1 "guests" t = some { forms := [], late := [] }
  /-- [M] constrQAt (MeansQ.lean), its shape (payable by Iff.rfl in a build with all it imports). -/
  constrIs : ∀ n p a₁ y w, Mg.constr n p a₁ y w ↔
    if p = .lookDigits then dP n a₁ y w
    else (p = .small → bsW n w) ∧ ∀ M i, decT y.cell a₁ = some M → Hd M i → body n p i a₁ y w
  /-- [M] THE COMPOSED MEANING's MAKE OVER THE INTEGER MODEL's CLAUSES (two sets of files owe it): this segment's smallness constraint reads neither the verifier's state nor the strings. -/
  bodySmall : ∀ i a₁ a₂ y y' w, body (2 * g + 1) .small i a₁ y w → body (2 * g + 1) .small i a₂ y' w
  /-- [M] THE LOOKUP ARGUMENT's FILES' letter digitsPart rides back over the lay (UNSEEN). -/
  digitsBack : ∀ (π : Pp) n, n ≠ 2 * g + 1 → ∀ s att hd G rs (y y' : Fr.E.Str) w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) →
    s.failed = none → s.here = .att att → hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
    SameBelow Fr bs y y' → dP n (π, behind s att hd G) (strsOf Fr y') w → dP n (π, s) (strsOf Fr y) w
  /-- [M] THE OTHER SEGMENTS' constraints' bodies ride back over the lay (the output head's files' letter among them: UNSEEN). -/
  bodyBack : ∀ (π : Pp) n p, n ≠ 2 * g + 1 → ∀ i s att hd G rs (y y' : Fr.E.Str) w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) →
    s.failed = none → s.here = .att att → hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
    SameBelow Fr bs y y' → body n p i (π, behind s att hd G) (strsOf Fr y') w → body n p i (π, s) (strsOf Fr y) w
  /-- [S] THE HINGE TO THE MODEL (UNPAID): under the smallness constraint the cells read off the pinned messages are the model's integers. -/
  cells : ∀ w, bsW (2 * g + 1) w → CellsAre x a.S a.seam.tl Dn rad (msgsOf Dn.codes (sigListCalls Dn rad x.link) seat arr w) (Zof w)
  /-- [T] THE COMPOSED MEANING's MAKE OVER THE INTEGER MODEL's CLAUSES (two sets of files owe it): the identities' constraint's body is the two families of identities at the model's integers. -/
  bodyIdn : ∀ i a₁ y w,
    ((∀ k b g' n, (Inst.Model.AttSeg.Idn.at1 k b g' n).Valid (dimOf a.S) →
        Inst.Model.AttSeg.idnVal (dimOf a.S) (Inst.Model.AttSeg.castT (cellsA a.S (Zof w)) : Inst.Model.AttSeg.Raw → Cb.Gl.F) (.at1 k b g' n) = 0) ∧
      ∀ b g' n, (Inst.Model.AttSeg.Idn.at2 b g' n).Valid (dimOf a.S) →
        Inst.Model.AttSeg.idnVal (dimOf a.S) (Inst.Model.AttSeg.castT (cellsA a.S (Zof w)) : Inst.Model.AttSeg.Raw → Cb.Gl.F) (.at2 b g' n) = 0) →
    body (2 * g + 1) .idn i a₁ y w
  /-- [C] The composed meaning's list of members (someB | listSits_some, Johnson/P5J/Rad3Seat3At.lean; its tests are evaluated, not proved: Johnson/P5J/Rad3Seat3Tests.lean): for each member of the caller's list some member of ms is alike: one entry (shape and radius), one seat. (The caller's list itself is no sending of ms.) -/
  someMem : ∀ i, ∃ y ∈ ms, Alike y (⟨⟨sigListCalls Dn rad x.link, seat⟩, i⟩ : Mem)
  /-- [M] THE COMPOSED MEANING's letter smp (smpNamed_bySeat, Johnson/Desc/Sound/SmpNamed.lean): the OOD samples hang on the entry and the seat, not on the list. -/
  smpBySeat : SmpBySeat Dn.codes smp
  /-- [M] THE COMPOSED MEANING's make of its data: the letter runs. -/
  runsIs : D.runs = runsAt links
  /-- [M] THE COMPOSED MEANING's make: the output head's segment's number. -/
  mHIs : D.mH = (if Wv.p4 then 2 else 1) * Wv.NGr
  /-- [M] THE COMPOSED MEANING's make: the letter Rd. -/
  rdIs : D.Rd = K9.readersAt lk Wv D.mH
  /-- [O] THE COMPOSED MEANING's letter lk at the segment. -/
  lkAt : lk (2 * g + 1) = some Lk
  /-- [O] K5's FILES', BY LAKE IN A BUILD APART FROM THE LIBRARY's, AT THE SEATED LINK (not called here): the link's runs at piece 2 are the kind's, guarded. -/
  statesAt : K9.statesOfLink Lk 2 = (runsN a).map (guardC same)
  /-- [O] The same: the guard lets pass what leaves the output alone. -/
  sameOut : ∀ s t : S, t.out = s.out → same s t = true
  /-- [P] K5's FILES' (from an opening of the description): the seat's sub-protocol. -/
  seated : k5AtN Wv (2 * g + 1) g before = some blk
  /-- [P] The same: its own test on the plan says yes. -/
  seatedOk : blk.planOk = true
  /-- [P] PUBLIC (place_att, Johnson/Desc/First/Look/K3PlaceLetters.lean, reported, not shown here): the place's packing number is the shape's. -/
  lmIs : x.lm = a.S.cf.lmb
  /-- [P] K5's FILES' (the guard's test posOk: posG_of_ok): the geometry's numbers are positive. -/
  posG : K5Law.PosG (parCOf a).geo
  /-- [O] OTHER FILES' (k03_planes_of, Johnson/Desc/First/Look/K03States.lean, at the seated link): the link's run "planes" at piece 1 is the lookup argument's, guarded. -/
  planesAt : ((K9.statesOfLink Lk 1).find? fun c => c.1 == "planes") = some (guardC same
    (nm, K3.planesRun (K3.seatCalls claimC) a.S.cf.lmb (readersOfO a)))
  /-- [P] ONE COMPARISON OF PUBLIC NUMBERS (run nowhere): the planes' columns fit the matrix of the reads. -/
  colsFit : x.fs.NC * 2 ^ (x.fs.kT + 5 - a.S.cf.lmb) ≤
    (a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).k * ((a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).m / 2 ^ a.S.cf.lmb)
  /-- [M] The same: the claim's form is the form, and it bears no run and no first equation. -/
  clForm : ∀ f, (claimC f).form = f ∧ (claimC f).runs.isEmpty = true ∧ (claimC f).eqFirst.isNone = true
  /-- [P] K5's FILES' (the guard's K5Public.planes): the program's own test on the planes' packing says yes. -/
  planesOkAt : Look.planesOk x.fs (parCOf a).geo.lmb = true

/-- **WHAT IS LEFT OF THE KIND's LAW AT THE TABLE**: K5Table's four and K5Rest's. -/
structure K5Owes : Prop extends K5Table g links pl O Q,
    K5Rest (Fr := Fr) Mg Mg0 D Dn arr smp ms decT in0 Ld Ms D13 bs Wv g before a x links pl rad O Q seat smpR lk Lk same blk claimC nm Hd bsW dP body Zof
end

section
variable {Pp Xi Cells Tok Cl Ix : Type} {nR : ℕ} {Fr : Frame}
  (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData) (Dn : Sent) (G0 : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf Dn.codes s.l).om i).Smp) (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (in0 : Pp × S → Bool) (c5 : Pp → Bool)
  (Ld : Laid) (Ms : List OracleShape) (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR)
  (E : MgIs Mg Mg0 D Dn.codes G0 arr smp ms decT in0 c5 Ld Ms D13)
  (bs : ℕ) (claim : Aff → Cl) (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : Look.Place)
  (links : List ModelPart) (T : DataIs D Wv links (2 * g + 1)) (Sn : DataSent D Dn.codes Dn)
  (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hx : lookAt Wv (2 * g + 1) false = some x)
  {pl pl' : VerifiableInference.Desc.Place} (Ix5 : K5Place links (2 * g + 1) pl pl')
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
  (O : List Item) (Q : List Pub)
  (uL uH : ℕ → UFn) (wt : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop)
  (seat : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ)
  (G : MgGains Mg Dn.codes arr ms D.Rd D.runs (Stated.of (uBySort uL (uArm Wv) uH)) D.N wt (2 * g + 1) x a.S a.seam.tl Dn rad seat arr)
  (pls : List VerifiableInference.Desc.Place) (k : ℕ) (hk : pls[k]? = some pl)
  (smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls Dn rad x.link).length) →
    Option ((sigOf Dn.codes (sigListCalls Dn rad x.link)).om i).Smp)
  (hlow : ∀ i, (seat i).1 < bs)
  (lk : ℕ → Option (Link S Claim)) (Lk : Link S Claim) (same : S → S → Bool) (blk : Block S Claim)
  (claimC : Aff → Claim) (nm : String)
  (Hd : Cells → Ix → Prop) (bsW : ℕ → Wit Cells Tok MsgT → Prop)
  (dP : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop) (body : ℕ → First.Part → Ix → Pp × S → Strs → Wit Cells Tok MsgT → Prop)
  (Zof : Wit Cells Tok MsgT → Zs)
  (Ow : K5Owes (Fr := Fr) Mg Mg0 D Dn arr smp ms decT in0 Ld Ms D13 bs Wv g before a x links pl rad O Q seat smpR lk Lk same blk claimC nm Hd bsW dP body Zof)

include E T Sn hP h4 ha hx Ix5 G hk Ow in
/-- **K5Left, a structure instance over the payers.** -/
theorem k5Left_plus (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (gOf : Pp → S × Fr.E.Str → Forest.Heard) (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) :
    K5Left Mg Mg0 D Dn.codes smp decT in0 D13 bs claim Wv g before a x Dn rad Ex Wp α plJ
      (k5Pin (Cells := Cells) (Tok := Tok) G0 x Dn rad seat smpR arr Fr bs hlow)
      (fun π => relAt (meansQ (Fr := Fr) D.N Mg fun s => (π, s)) (outsQ links pls k)) links pl O Q (fun _ => runsN a) := by
  obtain ⟨_, hxns, hxl, hfs⟩ := place_calls h4 ha hx
  have hOf : K5Law.OfPlan a := by
    obtain ⟨A0, pf, h0, e⟩ := hP g a ha
    exact ⟨_, _, _, A0, pf, h0, e⟩
  have hA : Wv.A[x.link / 2]? = some a := by
    rw [hxl, show (2 * g + 1) / 2 = g by omega]
    exact ha
  have hs : links[2 * g + 1]? = some .attention := Ix5.sub
  have hatt : D.d5.isAtt (2 * g + 1) = true := isAtt_of D.d5 (by rw [T.d5links]; exact hs)
  have hlay : FillK4.isLay D.links (2 * g + 1) = false := att_not_lay (by rw [T.links]; exact hs)
  have r3 := runs3_plus D g links Ow.runsIs hs
  have rJ := runsJ_plus D g links Ow.runsIs hs
  have rO := runsO_plus D g links Ow.runsIs hs
  have nH : (2 * g + 1 == D.mH) = false := notHead_plus Ow.mHIs h4
  have pOk := planOk_plus before Ow.seated Ow.seatedOk ha
  have cOk := claimsOk_plus before Ow.seated Ow.seatedOk ha
  have hrds := rds_plus D g a _ Lk (hRd_plus Ow.rdIs Ow.lkAt) same Ow.statesAt Ow.sameOut
  have hbare := hbare_plus Mg Mg0 D Dn.codes G0 arr smp ms decT in0 c5 Ld Ms D13 E claim Wv g before a x links pl O Q Ow.openIn plJ x0 gOf
    hLI
  have hdoor := hdoor_plus Mg Mg0 D Dn.codes G0 arr smp ms decT in0 c5 Ld Ms D13 E claim Wv g before a x links T Dn Sn Ix5 hxl nH
    Ow.nsOf O Q Ow.openIn plJ x0 gOf hLI _ _ Ow.seatsPlan Ow.shapesPlan
  have hRet := runsRet_plus Mg D claim Wv g before a x Dn rad Ex Wp α plJ links pl O Q hP h4 ha hx Ow.guard pOk cOk x0 gOf hLI
    Ow.openIn.q6 hA hOf hdoor
  exact
    { nsOf := Ow.nsOf
      baseP := Ow.baseP
      baseIn := Ow.baseIn
      baseMakes := Ow.baseMakes
      decTq := Ow.decTq
      smpq := Ow.smpq
      rwq := Ow.rwq
      low := Ow.low
      lowI := Ow.lowI
      low0 := Ow.low0
      openQ := Ow.openQ
      tiesO := Ow.tiesO
      planesIn := planesIn_plus Mg D claim Wv g before a x Dn plJ links pl O Q E.pub hxl (by rw [Ow.runsIs]; exact runsAt_planes hs) _ Lk
        (hRd_plus Ow.rdIs Ow.lkAt) claimC Ow.clForm a.S.cf.lmb Ow.planesAt Ow.sameOut hRet x0 gOf hLI Ow.openIn.q6 hA hOf hdoor Ow.planesOkAt
        Ow.posG Ow.colsFit rfl
        (hleft_plus Mg Mg0 D Dn.codes G0 arr smp ms decT in0 c5 Ld Ms D13 E claim Wv g before a x links pl O Q Ow.openIn plJ x0 gOf hLI)
      runs3 := r3
      runsJ := rJ
      okAll := okAll_plus Wv g before a Dn rad hP h4 ha Ow.guard pOk cOk
      st2 := st2_plus a
      rds := hrds
      objR := objR_plus Mg D claim Wv g before a x plJ links pl O Q x0 gOf hLI Ow.openIn.q6 Ow.objIs Ow.gstIs hbare rO
      objLate := objLate_plus Mg D claim Wv g before a x plJ links pl O Q x0 gOf hLI Ow.openIn.q6 Ow.objIs Ow.gstIs hbare rO
      ledQ := Ow.openIn.q4
      readsQ := Ow.openIn.q2
      pinOk := pinOk_at_pin G0 x Dn rad seat smpR arr Fr bs hlow D.N Mg links pl O Q
      behind := behind_plus Mg Mg0 D Dn G0 arr smp ms decT in0 c5 Ld Ms D13 E bs claim Wv g before a x links T Sn hP h4 ha hx Ix5 rad
        Ex Wp α plJ O Q (fun _ => runsN a) uL uH wt seat arr G pls k hk seat smpR hlow nH Ow.nsOf Ow.openIn r3 rJ hrds (st2_plus a)
        Ow.tiePub Ow.memAt Ow.seatsPlan Ow.shapesPlan Ow.someMem Ow.smpBySeat Ow.sent Ow.smpIs
      runsRet := hRet
      objects := objects_plus Mg D bs claim Wv g before a x plJ links pl O Q x0 gOf hLI Ow.openIn.q6 (D.Rd (2 * g + 1))
        (Stated.of (uBySort uL (uArm Wv) uH)) (D.N.sent (2 * g + 1) 0) (seatTab Dn.codes arr ms) Ow.objIs hbare
        (hIn_plus E.pub rO Ow.tiedObj) (hMask_plus _) (hTo_plus G rO) Ow.gstIs (hFrom_plus G rO)
      small := small_plus Mg D decT bs Wv g before a links pl O Q Hd bsW dP body Ow.constrIs Ow.decTq Ow.bodySmall
      constr := constr_plus Mg D decT bs Wv g before a links pl O Q Hd bsW dP body Ow.constrIs Ow.decTq Ow.digitsBack Ow.bodyBack
      ins := ins_plus Mg D decT bs claim Wv g before a x Dn rad Ex Wp α plJ
        (k5Pin (Cells := Cells) (Tok := Tok) G0 x Dn rad seat smpR arr Fr bs hlow) links pl O Q Hd bsW dP body Ow.constrIs Iop.extNone Unit
        (attOK_plus before Dn rad hP h4 ha hx Ow.guard pOk cOk) (callsFit_plus hP h4 ha hx Ow.guard) Ow.openIn.q6 Zof Ow.cells Ow.bodyIdn
        seat arr (hms_plus G0 x Dn rad seat smpR arr Fr bs hlow) (fun π => hW_rider G claim π) (fun π => hW_keys G claim π)
        (planes_plus Mg D bs claim Wv g before a x Dn rad Ex Wp α plJ links pl O Q arr ms uL uH seat G hxl hfs Ow.lmIs
          (VerifiableInference.OnPublicFiles.foOk_of_shape (attOK_plus before Dn rad hP h4 ha hx Ow.guard pOk cOk).shape) hA hOf Ow.posG _ Lk
          (by rw [hxl]; exact hRd_plus Ow.rdIs Ow.lkAt) (fun s => by rw [silent_none Wv nH Lk]) claimC (fun f => (Ow.clForm f).1) Ow.planesAt
          (by rw [hxl, Ow.runsIs]; exact runsAt_planes hs) hRet x0 gOf hLI Ow.openIn.q6 hdoor Ow.tiePub (Nat.le_of_eq hxns.symm) Ow.memAt
          Ow.colsFit
          (hH5_plus Mg D g links pl O Q E.pub hlay hatt Ow.openIn.q14)
          (hBare_plus Mg D claim Wv g before a x plJ links pl O Q E.pubPl x0 gOf hLI Ow.openIn.q6)) }

include E T Sn hP h4 ha hx Ix5 G hk Ow in
open Classical in
/-- **K5AtMg, from the equations, the plan and K5Owes.** -/
theorem k5AtMg_plus (xd : Look.Place) (hxd : lookAt Wv (2 * g + 1) true = some xd) :
    ∃ (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
      (gOf : Pp → S × Fr.E.Str → Forest.Heard),
      K5AtMg bs claim Wv (2 * g + 1) before a x Dn rad Ex Wp α a.ns [] x0 gOf plJ
        (k5Pin (Cells := Cells) (Tok := Tok) G0 x Dn rad seat smpR arr Fr bs hlow)
        (fun π => relAt (meansQ (Fr := Fr) D.N Mg fun s => (π, s)) (outsQ links pls k)) D.N Mg links pl O Q
        (Look.P.ofPlace (Params.settingOf Wv.P.frame) false x) (Look.P.ofPlace (Params.settingOf Wv.P.frame) true xd)
        (D.d3.arrayOf.getD (2 * g + 1) #[]) (Forest.elems a.fs) a.ns := by
  obtain ⟨x0, gOf, hL⟩ := leftIs_at claim hP h4 ha hx (Cb.Fo.NumsEq.placeOf (enMask x.ns a.seam.tl) plJ)
  have hLP : LeftIsP (Fr := Fr) Mg claim Wv g before a x plJ (fun _ a' => x0 a'.1) (fun _ a' => gOf a'.1) := by
    intro π a' h
    rw [E.pubPl, T.d3X] at h
    exact hL a'.1 h
  exact k5AtMg_of_eqs_plus Mg Mg0 D Dn.codes G0 arr smp ms decT in0 c5 Ld Ms D13 E bs claim Wv g before a x xd links T hP h4 ha hx hxd Ix5
    Dn rad Ex Wp α plJ _ _ O Q (fun _ => runsN a)
    (k5Left_plus Mg Mg0 D Dn G0 arr smp ms decT in0 c5 Ld Ms D13 E bs claim Wv g before a x links T Sn hP h4 ha hx Ix5 rad Ex Wp α plJ O Q
      uL uH wt seat G pls k hk smpR hlow lk Lk same blk claimC nm Hd bsW dP body Zof Ow _ _ hLP)

end

end H2K5.Door

#print axioms H2K5.Door.k5Left_plus
#print axioms H2K5.Door.k5AtMg_plus
