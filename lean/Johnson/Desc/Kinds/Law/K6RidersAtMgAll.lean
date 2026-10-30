-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6RidersAtMgAll.lean: THE OUTPUT HEAD'S SUB-PROTOCOL'S FIFTH TIE TO THE TABLE
OF CLAIMS BETWEEN SUB-PROTOCOLS, AT THE COMPOSED MEANING mgAll D Mg (Johnson/Desc/Sound/MgAll.lean),
AT THE FULL CHAIN: each claim that is open in front of the sub-protocol at place 341, and that its
row neither closes nor reads, holds of the statement in front if it holds of the statement behind,
at one witness. General in a condition Rch that stands beside the table's promise.

Which claims these are is another file's evaluation by the kernel (Johnson/Desc/Sound/K6Fifth.lean:
riders341_full): the pile of pending rows; the index masks' pin; three classes of linear claims on
segment 24's group of oracle messages (carried, the first sending's samples, position); and "the
forms of the lookup's runs (2, "objects") and (2, "guests") are worth 0" (formsT 24 3 "objects").

WHY THEY GO BACK. An accept of this sub-protocol turns, of the verifier's state, three fields of the
open head's own part alone: the ledger of hidden values, what was heard, one sumcheck
(Johnson/Desc/Sound/K6Tied.lean: k6_behind). The pile and the three classes of rows read none of the
three. The pin is paid as in K6Fifth.lean. The forms read the ledger: there the rule
formsTQ_rides (Johnson/Desc/Sound/FormsQ.lean) is called.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  keptOf name o: what the reader of these two runs answers, as a function of what the lookup on the
      calls has heard.
  readerOf_objects, readerOf_guests, readers_kept: where the segment's reader answers at one of the
      two names, in either arm (the run itself; the run at the state with the tables laid), it
      answers keptOf.
  segAt_head: the open segment's part at an opened head, written out.
  kept_back: the sentence formsTQ at one of the two names goes back over the three fields' turning.
  pile_back, row_back, objects_back: the riders, each at one accept of the piece.
  pinI_open, fenceI_full: the index masks' tree was sent in front of the piece.
  runs_objects_full: the premise hobj holds where the meaning's list of segments is the full
      chain's.
  k6_t5_mgAllR: THE FIFTH TIE, in the form in which Johnson/Desc/Sound/K6TiedR.lean
      (k6_tiedBy_of_lawR) takes it.

The named premise ObjectsStates stands in Johnson/Desc/Kinds/Law/ObjectsStates.lean.
Every letter under "there is": none in this file's statements.
For-all letters that one premise alone reads: small (hreaders); bef, B, bS (Hs); numD, bs (hmore,
hblocks, hbook). P8 is read by hreaders alone: the tie holds at every value of it.

What it does not say. THAT ITS PREMISES CAN BE MET TOGETHER: NO EXAMPLE. THREE PREMISES ARE NEW
AGAINST THE STRUCTURE K6Riders, WHOSE PLACE THIS TIE TAKES: hobj (an equation on the meaning's
parameters), hruns (on the IOP as written in Lean), hbare (ON THE VERIFIER'S STATE IN FRONT: no row
that the lookup on the calls keeps names an entry of an array). WITHOUT hbare THE LAST RIDER DOES
NOT GO BACK: its sentence reads each entry that a kept row names through the stated function of the
second sending's arrays, and the head's arm of that function reads what this sub-protocol itself
lays. No test of the promise at place 341 says hbare: so it is asked under Rch. The case of the
index masks' pin FOLLOWS, LINE BY LINE, the proof in Johnson/Desc/Sound/K6Fifth.lean
(k6_t5_of_riders): that theorem takes its riders without Rch and could not be called. THE FULL CHAIN
ALONE. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6AtMgAll
import Johnson.Desc.Kinds.Law.K6LedgerAt
import Johnson.Desc.Kinds.Law.K6PieceFacts
import Johnson.Desc.Sound.K6Fifth
import Johnson.Desc.Sound.Border62At
import Johnson.Desc.Sound.OnParts
import Johnson.Desc.Kinds.Law.ObjectsStates
import Johnson.Desc.First.StateLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Model (Fork Aff)
open OnBytes.PscRun (Later)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Item Numbers Meaning HeadOwn bookFit fenceFit start
  readsOpen)
open VerifiableInference.Desc.K9 (RunOf readerOf lateOf readersOfLink statesOfLink segAt? formsInT)
open VerifiableInference.Desc.Sound (Piece Frame Mem MsgT MsgQ onQ meansQ relQ insQ outsQ insL
  openAfter openQ strsOf linksFull PieceMore toldOf MgData mgAll formsTQ formsTQ_rides Rides Stated
  UFn ridersK6 open_iff_mem reads_full apart_full mark_full len_full riders341_full onParts_of_on
  runsAt seatTab)

/-! ## 1 What the two runs' reader answers -/

/-- What the reader answers: the rows that the lookup on the calls keeps; for "guests": no form. No
slot is late. -/
def keptOf (name : String) (g : Option Model.Forest.Heard) : Option K9.Read :=
  if name = "objects" then g.map fun x => ⟨x.rows.toList, []⟩ else some ⟨[], []⟩

/-- Marking an owed claim as added fills no slot. -/
theorem lateOf_paid (F : Fork) (i : ℕ) : lateOf F (F.paid i) = [] := by
  unfold lateOf
  refine List.filterMap_eq_nil_iff.2 fun j _ => ?_
  show (if (!(F.gotF.getD j false) && F.gotF.getD j false) = true then _ else none) = none
  cases F.gotF.getD j false <;> rfl

theorem lateOf_self (F : Fork) : lateOf F F = [] := by
  unfold lateOf
  refine List.filterMap_eq_nil_iff.2 fun j _ => ?_
  cases F.gotF.getD j false <;> rfl

theorem readerOf_objects {states : ℕ → List (RunOf S)} {b : ℕ}
    {run : ℕ → S → Except String (List Claim × S)}
    (hf : (states b).find? (fun r => r.1 == "objects") = some ("objects", run))
    (hu : ∀ k t y, run k t = .ok y → K9.objectsCalls k t = .ok y) (t : S) (R : K9.Read)
    (h : readerOf states b "objects" t = some R) : keptOf "objects" t.lookHeard? = some R := by
  unfold readerOf at h
  rw [hf] at h
  simp only [Option.bind_some] at h
  cases hr : run 0 t with
  | error e => simp [hr] at h
  | ok z =>
    cases hF : t.fork? with
    | none => simp [hr, hF] at h
    | some F =>
      have h0 := hu 0 t z hr
      cases hg : t.lookHeard? with
      | none =>
        simp [K9.objectsCalls, K9.objectsBy, hF, hg, named, bind, Except.bind] at h0
      | some g =>
        simp [K9.objectsCalls, K9.objectsBy, hF, hg, named, bind, Except.bind, pure,
          Except.pure] at h0
        subst h0
        simp only [hr, hF, S.fork_putFork t F _ hF, Option.bind_some, lateOf_paid] at h
        split at h
        · rw [← Option.some.inj h]
          simp [keptOf, List.map_map, Function.comp_def]
        · exact nomatch h

theorem readerOf_guests {states : ℕ → List (RunOf S)} {b : ℕ}
    {run : ℕ → S → Except String (List Claim × S)}
    (hf : (states b).find? (fun r => r.1 == "guests") = some ("guests", run))
    (hu : ∀ k t y, run k t = .ok y → K9.guestsNone k t = .ok y) (t : S) (R : K9.Read)
    (h : readerOf states b "guests" t = some R) : keptOf "guests" t.lookHeard? = some R := by
  unfold readerOf at h
  rw [hf] at h
  simp only [Option.bind_some] at h
  cases hr : run 0 t with
  | error e => simp [hr] at h
  | ok z =>
    cases hF : t.fork? with
    | none => simp [hr, hF] at h
    | some F =>
      have h0 := hu 0 t z hr
      simp [K9.guestsNone, K9.readRun, Except.map] at h0
      subst h0
      simp only [hr, hF, Option.bind_some, lateOf_self] at h
      split at h
      · rw [← Option.some.inj h]
        simp [keptOf]
      · exact nomatch h

/-- Laying the tables leaves what the lookup on the calls has heard. -/
theorem lookHeard_withTables (P8 : K8.ReadsQuiet.PH) (s e : S) (h : withTables P8 s = some e) :
    e.lookHeard? = s.lookHeard? := by
  unfold withTables at h
  cases hh : s.here with
  | head a =>
    rw [hh] at h
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold S.lookHeard?
    rw [hh]
  | _ => rw [hh] at h; exact nomatch h

/-- **Where the segment's reader answers at one of the two names, it answers keptOf.** -/
theorem readers_kept {Lk : Link S Claim} {b : ℕ} (hS : ObjectsStates (statesOfLink Lk) b)
    (P8 : K8.ReadsQuiet.PH) (small : S → Option K9.Read) (name : String)
    (hn : name = "objects" ∨ name = "guests") (s : S) (R : K9.Read)
    (h : (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk).forms b name s = some R) :
    keptOf name s.lookHeard? = some R := by
  obtain ⟨⟨r1, f1, u1⟩, r2, f2, u2⟩ := hS
  have key : ∀ t R', readerOf (statesOfLink Lk) b name t = some R' →
      keptOf name t.lookHeard? = some R' := by
    intro t R' h'
    rcases hn with rfl | rfl
    · exact readerOf_objects f1 u1 t R' h'
    · exact readerOf_guests f2 u2 t R' h'
  have hne : (name == "K8.equations") = false := by
    rcases hn with rfl | rfl <;> decide
  have h' : (match readerOf (statesOfLink Lk) b name s with
      | some R => some R
      | Option.none => k6Silent P8 (statesOfLink Lk) b name s) = some R := by
    have h2 : (if (name == "K8.equations") = true then small s
        else match readerOf (statesOfLink Lk) b name s with
          | some R => some R
          | Option.none => k6Silent P8 (statesOfLink Lk) b name s) = some R := h
    rw [hne] at h2
    exact h2
  cases e : readerOf (statesOfLink Lk) b name s with
  | some R' =>
    rw [e] at h'
    rw [← Option.some.inj h']
    exact key s R' e
  | none =>
    rw [e] at h'
    obtain ⟨t, ht, hR⟩ := Option.bind_eq_some_iff.1 (show (withTables P8 s).bind
      (readerOf (statesOfLink Lk) b name) = some R from h')
    rw [← lookHeard_withTables P8 s t ht]
    exact key t R hR

/-! ## 2 The sentence on the forms goes back -/

/-- The open segment's part at an opened head. -/
theorem segAt_head (s : S) (o : HeadOwn) (ho : s.here = .head o) (hop : o.opened = true) :
    segAt? s = some
      { owed := K9.owedOf s, used := (K9.usedOf s).getD 0, laid := K9.laidOf o.tl, L := o.L,
        F := o.F
        d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } } := by
  have h1 : s.link? = some o.L := by
    unfold S.link?
    rw [ho]
    show (if o.opened then some o.L else none) = some o.L
    rw [hop]
    rfl
  have h2 : s.fork? = some o.F := by
    unfold S.fork?
    rw [ho]
    show (if o.opened then some o.F else none) = some o.F
    rw [hop]
    rfl
  have h3 : s.tl? = some o.tl := by
    unfold S.tl?
    rw [ho]
    show (if o.opened then some o.tl else none) = some o.tl
    rw [hop]
    rfl
  unfold segAt?
  rw [h1, h2, h3]
  rfl

/-- **At one of the two names the sentence goes back over the turning of the head's ledger, of what
it has heard and of its sumcheck**, where the later ledger keeps what is filled, the promise's test
holds in front, and no kept row names an entry. -/
theorem kept_back {Lk : Link S Claim} {b : ℕ} (hS : ObjectsStates (statesOfLink Lk) b)
    (P8 : K8.ReadsQuiet.PH) (small : S → Option K9.Read) (u : UFn) (own : List (ℕ × ℕ))
    (name : String) (hn : name = "objects" ∨ name = "guests") (s : S) (o : HeadOwn)
    (F1 : Fork) (X : Model.Head.Heard) (Q : Model.Psc) (ho : s.here = .head o)
    (hop : o.opened = true) (hL : Later o.F F1)
    (hbare : ∀ g, s.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[])
    (rd : ℕ × ℕ → MsgQ)
    (hin : formsInT (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk) own b name s = true)
    (h : formsTQ (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk) (Stated.of u) own b name
      { s with here := .head { o with F := F1, x := some X, squaresP := some Q } } rd) :
    formsTQ (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk) (Stated.of u) own b name s
      rd := by
  have ha := segAt_head s o ho hop
  have hb := segAt_head { s with here := .head { o with F := F1, x := some X, squaresP := some Q } }
    { o with F := F1, x := some X, squaresP := some Q } rfl hop
  have hlk : ({ s with here := .head { o with F := F1, x := some X, squaresP := some Q } } :
      S).lookHeard? = s.lookHeard? := by
    unfold S.lookHeard?
    rw [ho]
  obtain ⟨R0, hR0⟩ : ∃ R0, (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk).forms b name s
      = some R0 := by
    unfold formsInT at hin
    rw [ha] at hin
    cases e : (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk).forms b name s with
    | some R0 => exact ⟨R0, rfl⟩
    | none =>
      rw [e] at hin
      exact absurd hin Bool.false_ne_true
  have k0 := readers_kept hS P8 small name hn s R0 hR0
  refine formsTQ_rides own _ _ b name s _ _ _ rd ha hb ?_ hin ?_ ?_ h
  · obtain ⟨_, R1, _, hR1, _⟩ := h
    have k1 := readers_kept hS P8 small name hn _ R1 hR1
    rw [hlk, k0] at k1
    rw [hR0, hR1, Option.some.inj k1]
  · exact ⟨rfl, rfl, fun _ _ _ e => e, fun _ e => e, fun _ _ e => e, fun _ _ _ _ => ⟨rfl, rfl⟩,
      fun j _ hj => ⟨(hL.keep j hj).2.1, (hL.keep j hj).2.2⟩⟩
  · intro R hR f hf
    refine ⟨fun x hx => ?_, fun _ _ => rfl⟩
    obtain rfl : R0 = R := Option.some.inj (hR0.symm.trans hR)
    exfalso
    unfold keptOf at k0
    rcases hn with rfl | rfl
    · rw [if_pos rfl] at k0
      obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 k0
      rw [hbare g hg f hf] at hx
      exact nomatch hx
    · rw [if_neg (by decide)] at k0
      rw [← Option.some.inj k0] at hf
      exact nomatch hf

/-! ## 3 The riders, each at one accept of the piece -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) {Fr : Frame}
  {q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

set_option quotPrecheck false in
/-- The composed meaning. -/
local notation "MGA" => mgAll D Mg

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

/-- The pile of pending rows. -/
theorem pile_back (Hs : Seated Wp .two Fr q 24 bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP .two) q.ds)) (hb : q.ior.red.out a τ = some b)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (h : (MGA).pile b.1 (strsOf Fr b.2) w) :
    (MGA).pile a.1 (strsOf Fr a.2) w := by
  obtain ⟨o, F1, X, Q, ho, _, _, e⟩ := k6_behind Hs a b τ hb
  rw [e] at h
  show K13.Law.RowsTrue (D.rw13 a.1) a.1.2 w
  intro r hr
  refine h r ?_
  show r ∈ First.S.rows _
  unfold First.S.rows at hr ⊢
  rw [ho] at hr
  exact hr

/-- A class of linear claims on a segment's group of oracle messages. -/
theorem row_back (Hs : Seated Wp .two Fr q 24 bef B bS) (m : ℕ) (c : First.RowClass)
    (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP .two) q.ds))
    (hb : q.ior.red.out a τ = some b) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (h : (MGA).row m c b.1 (strsOf Fr b.2) w) : (MGA).row m c a.1 (strsOf Fr a.2) w := by
  obtain ⟨o, F1, X, Q, _, _, _, e⟩ := k6_behind Hs a b τ hb
  rw [e] at h
  exact h

/-- The forms of the lookup's two runs. -/
theorem objects_back (Hs : Seated Wp .two Fr q 24 bef B bS) {Lk : Link S Claim}
    {P8 : K8.ReadsQuiet.PH} {small : S → Option K9.Read}
    (hreaders : D.Rd 24 = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hobj : D.runs 24 3 "objects" = [(2, "objects"), (2, "guests")])
    (hruns : ObjectsStates (statesOfLink Lk) 2) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP .two) q.ds))
    (ha : onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a) (hm : a.1.2.failed = none)
    (hb : q.ior.red.out a τ = some b)
    (hbare : ∀ g, a.1.2.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[])
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (h : (MGA).formsT 24 3 "objects" b.1 (strsOf Fr b.2) w) :
    (MGA).formsT 24 3 "objects" a.1 (strsOf Fr a.2) w := by
  obtain ⟨o, F1, X, Q, ho, hop, _, e⟩ := k6_behind Hs a b τ hb
  have hL := later_at_piece Hs a b τ hb
  have hL' : Later o.F F1 := by
    have fa : a.1.2.fork? = some o.F := by
      unfold S.fork?
      rw [ho]
      show (if o.opened then some o.F else none) = some o.F
      rw [hop]
      rfl
    have fb : b.1.2.fork? = some F1 := by
      rw [e]
      show (if o.opened then some F1 else none) = some F1
      rw [hop]
      rfl
    have h0 : Later (a.1.2.fork?.getD {}) (b.1.2.fork?.getD {}) := hL
    rw [fa, fb] at h0
    exact h0
  have hpub : (MGA).pub (.formsInT 24 3 "objects") a.1 = true :=
    (onParts_of_on D.N MGA linksFull PS (fun a => a) 341 a ha hm).pub _
      (List.mem_append_right _ (by decide +kernel))
  have hin : ∀ p ∈ D.runs 24 3 "objects",
      formsInT (D.Rd 24) (D.N.sent 24 0) p.1 p.2 a.1.2 = true :=
    fun p hp => List.all_eq_true.1 hpub p hp
  rw [e] at h
  refine ⟨fun p hp => ?_, fun e' => absurd e' (by decide)⟩
  have h1 := h.1 p hp
  have h2 := hin p hp
  rw [hobj] at hp
  have hp' : p.1 = 2 ∧ (p.2 = "objects" ∨ p.2 = "guests") := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨rfl, Or.inl rfl⟩
    · exact ⟨rfl, Or.inr rfl⟩
  rw [hreaders, hp'.1] at h1 h2 ⊢
  exact kept_back hruns P8 small _ _ p.2 hp'.2 a.1.2 o F1 X Q ho hop hL' hbare _ h2 h1

/-! ## 4 The tie -/

set_option maxRecDepth 1000000 in
/-- The index masks' pin is open in front of the sub-protocol. -/
theorem pinI_open : Item.pinI ∈ openQ linksFull PS 341 := by decide +kernel

/-- The index masks' tree was sent in front of the piece. -/
theorem fenceI_full {numD : Fmt.TreeSource → ℕ} {bs : List (Block (P × S) Claim)}
    (hmore : PieceMore numD 0 bs 341 q) (hblocks : blocksOk bs = true)
    (hbook : bookFit D.N PS (toldOf bs) = true) (hfenceT : fenceFit D.N linksFull PS = true) :
    D.N.index.1 < q.base :=
  (fences_full hmore hblocks D.ms D.N hbook hfenceT).1 D.N.index
    (List.mem_flatMap.2 ⟨.pinI, pinI_open, List.mem_singleton.2 rfl⟩)

/-- The premise hobj, where the meaning's list of segments is the full chain's. -/
theorem runs_objects_full : runsAt linksFull 24 3 "objects" = [(2, "objects"), (2, "guests")] := by
  decide +kernel

/-- **THE FIFTH TIE AT THE COMPOSED MEANING, AT SUB-PROTOCOL 341 OF THE FULL CHAIN.** -/
theorem k6_t5_mgAllR (Rch : ℕ → (P × S) × Fr.E.Str → Prop)
    (Hs : Seated Wp .two Fr q 24 bef B bS) {numD : Fmt.TreeSource → ℕ}
    {bs : List (Block (P × S) Claim)} (hmore : PieceMore numD 0 bs 341 q)
    (hblocks : blocksOk bs = true) (hbook : bookFit D.N PS (toldOf bs) = true)
    (hfenceT : fenceFit D.N linksFull PS = true) (hBl : Blind D.cs D.smp D.decT)
    {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH} {small : S → Option K9.Read}
    (hreaders : D.Rd 24 = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hobj : D.runs 24 3 "objects" = [(2, "objects"), (2, "guests")])
    (hruns : ObjectsStates (statesOfLink Lk) 2)
    (hbare : ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
      a.1.2.failed = none → ∀ g, a.1.2.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[]) :
    ∀ a τ b w i, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
      a.1.2.failed = none → q.ior.red.out a τ = some b →
      onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) (341 + 1) b →
      relQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) (341 + 1) b w →
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) 341 i →
      ¬ insQ linksFull PS 341 i → meansQ (Fr := Fr) D.N MGA (fun a => a) i a w := by
  intro a τ b w i ha hrc hm hb _ hall hi hin
  have hbw : meansQ (Fr := Fr) D.N MGA (fun a => a) i b w := hall i (Or.inl ⟨hi, hin⟩)
  rcases riders341_full i
    ((open_iff_mem linksFull PS reads_full apart_full mark_full 341 len_full i).1 hi) with h | h
  · exact absurd h hin
  · unfold ridersK6 at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact pile_back D Mg Hs a b τ hb w hbw
    · obtain ⟨h1, h2⟩ := hbw
      refine ⟨h1, fun x hx hsx => ?_⟩
      have e : x.1.seat x.2 = (D.N.index.1, D.N.index.2) := hsx
      refine ((Sound.rides (Cells := Fin rows → Fin cols → GE) (Tok := Tok) D.cs D.G D.arr D.smp q
        [x] ?_ ?_ a b τ hb x (List.mem_singleton.2 rfl)).1 w).1 (h2 x hx hsx)
      · intro x' hx'
        rw [List.mem_singleton.1 hx', e]
        exact fenceI_full D hmore hblocks hbook hfenceT
      · intro a' τ' b' hb' x' _
        obtain ⟨o, F1, X, Q, _, _, _, e'⟩ := k6_behind Hs a' b' τ' hb'
        rw [e', hBl.smp]
    · exact row_back D Mg Hs 24 .carried a b τ hb w hbw
    · exact row_back D Mg Hs 24 (.sample 0) a b τ hb w hbw
    · exact row_back D Mg Hs 24 .position a b τ hb w hbw
    · exact objects_back D Mg Hs hreaders hobj hruns a b τ ha hm hb (hbare a ha hrc hm) w hbw

end

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.readers_kept
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.kept_back
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.pile_back
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.row_back
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.objects_back
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.fenceI_full
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.runs_objects_full
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_t5_mgAllR
