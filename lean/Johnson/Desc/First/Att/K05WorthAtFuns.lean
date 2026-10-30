-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05WorthAtFuns.lean: kind K5: THE LAW's PREMISE ON THE FORMS' WORTH AT THE
TABLE OF JOINTS' OWN FILLING (billsWorthJ_at, Johnson/Desc/First/Att/K05WorthAt.lean), WITH ITS
PREMISES BROUGHT TO WHERE THEIR PAYERS STAND: the list of tables is the claims' seat's own reading
(funsAt, Johnson/Desc/First/Att/Claims/FunsAt.lean); what the promise holds IN FRONT of the
hearing's lay is asked in front, and carried over the lay here; hok is paid (laidOkAt_of,
Johnson/Desc/First/Att/K05LayoutOk.lean); the relation behind is the table's own two filled items.

IS IT EMPTY HERE? NO MEMBER IS SHOWN. A CARRIAGE BETWEEN TWO WORLDS, NO PAYMENT. D : Sent IS BUILT
NOWHERE in this library. hRd AND hbehind ARE ASKED UNDER ALL THAT BillsWorthJ HANDS (the witness
and the relation behind at it; what the hearing's law says; Stays; the ledgers' numbers of slots),
AND Returns (Johnson/Desc/First/Att/K05GatheredZero.lean) MUST HAVE ITS FIELD u3: without the first
they ran over every ledger that anybody writes into the lay, without the second over every number of
an array: both ways they could be met at no honest run.

Main names:
  `FrontFacts … s L`: WHAT IS ASKED OF THE RECORD IN FRONT OF THE LAY: three Bools with code
    (liveReqB · seatsOnB · shapesOnB) · FIVE equations (the open link's number; its own copy of the
    live request has D's shape and layout; its list of arrays is D's; the statement's codes are D's)
    · the open link · its list names an array at A.iU3.
  `BehindFacts … s L pt fs`: what is asked behind it: the ledger has at most hi slots · the array at
    A.iU3 is of the second sending · every entry of the forms names row 0 of A.iU3.
  `tieFacts_of`: the two, the lay, reqLayoutOk and SymsOK give TieFacts behind the lay
    (lay_keeps and the three rides, Johnson/Desc/First/Att/K05DoorLaws.lean).
  `billsWorthJ_funs`: **BillsWorthJ at the law's letters**, at every St that meets StatedAtt at uAtt
    A (funsAt A) AT THE RECORDS OF THE SEGMENT ITSELF.
  `billsWorthJ_table`: **the same at every relation behind that holds the table's own two filled
    items'** sentences, written out (formsT m 3 "own" and formsT m 2 "join": hitems): formsT_gives
    IS CALLED: Lean holds that Rd := Rd m, own := N.sent m 0, cs := D.codes fit.
IN FRONT, BESIDE FrontFacts: the open segment's own field g holds a record g with SeatReadsSame g
(gOf a) (Johnson/Desc/First/Att/K05SameRead.lean: six equations: what the claims' seat reads of the
lookup's record): NOT that the two records are one: meant to come of the table's item on the two
readers of what the lookup returned (a Bool that compares them field by field) with the lookup's
promise, which pins gOf a at the other reader: not joined here.
WHO PAYS WHAT: on the faces of K05AddrTieAt.lean, K05WorldTieAt.lean and K05LayoutOk.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05WorthAt
import Johnson.Desc.First.Att.K05LayoutOk
import Johnson.Desc.First.Att.K05SameRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Params
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Meaning Numbers)
open VerifiableInference.Desc.K9 (Readers segAt?)
open VerifiableInference.Desc.Sound (Stated Mem seatTab msgsOf MsgT formsTQ second)
open VerifiableInference.Desc.First.Look (Sent JAtt sigListCalls keptAt bornAt)
open K5Law (oldOf funsAt)

/-- **What is asked of the record in front of the lay.** -/
structure FrontFacts (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan) (D : Sent)
    (own : List (ℕ × ℕ)) (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape)) (s : First.S)
    (L : LinkCtx) : Prop where
  hB1 : liveReqB (bornAt D x.link) s = true
  hB2 : seatsOnB (keptAt D x.link).length ps own s = true
  hB3 : shapesOnB (keptAt D x.link).length qs s = true
  hlink : L.link = x.link
  hshape : L.check.frame.shape = D.shape
  hlay : L.check.rows.layout = D.layout
  harr : L.arrayOf = D.arrayOf.getD x.link #[]
  hcodes : s.st.codes = D.codes
  hL : s.link? = some L
  there : (L.arrayOf[A.iU3]?).isSome = true

/-- What is asked of the record behind the lay. -/
structure BehindFacts (A : Attention.Plan) (hi : ℕ) (s : First.S) (L : LinkCtx)
    (pt : VerifiableInference.Desc.K9.Part) (fs : List Aff) : Prop where
  hns : pt.F.ns ≤ hi
  sec : ∀ b, L.arrayOf[A.iU3]? = some b → second s b = true
  ents : ∀ f ∈ fs, ∀ y ∈ f.ents.toList, y.tree = A.iU3 ∧ y.row = 0

/-- The bundle of K05WorldTieAt.lean behind the lay, from what stands in front and behind: the Bools
and the equations ride over the lay; hok is paid. -/
theorem tieFacts_of {x : VerifiableInference.Desc.First.Look.Place} {A : Attention.Plan} {D : Sent}
    {rad : OracleShape → Nat} {own : List (ℕ × ℕ)} {ps : List (ℕ × (ℕ × ℕ))}
    {qs : List (ℕ × OracleShape)} {hi : ℕ} {a b : First.S} {L : LinkCtx} {F G : Fork} {h : Heard}
    {pt : VerifiableInference.Desc.K9.Part} {fs : List Aff}
    (hlo : reqLayoutOk D.codes D.shape D.layout = true) (hR : SymsOK x A.seam.tl D rad)
    (hq : ∀ k : Fin (sigListCalls D rad x.link).length,
      ReadMsg (ReadAddr A.seam.tl []) D x.link k.val →
      (k.val, ((sigListCalls D rad x.link).get k).1) ∈ qs)
    (T : FrontFacts x A D own ps qs a L) (hl : seatSO.ledger a = some F)
    (e : seatSO.lay a h G = some b) (hpt : segAt? b = some pt) (B : BehindFacts A hi b L pt fs) :
    TieFacts x A D rad own ps qs hi b L pt fs := by
  obtain ⟨k1, k2, _⟩ := lay_keeps hl e
  have hLb : b.link? = some L := k1.trans T.hL
  have b1 : liveReqB (bornAt D x.link) b = true := (live_rides hl e _).trans T.hB1
  have b3 : shapesOnB (keptAt D x.link).length qs b = true := (shapesOn_ride hl e _ _).trans T.hB3
  exact ⟨b1, (seatsOn_ride hl e _ _ _).trans T.hB2, b3, T.hlink, T.hshape, T.hlay, T.harr,
    laidOkAt_of hlo hR (frameIs_of_B b1 hLb T.hlink T.hshape) hLb qs b3 hq (by rw [k2]; exact T.hcodes),
    hpt, hLb, B.hns, T.there, B.sec, B.ents⟩

section
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan)
  (D : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns A.seam.tl)) → Cb.Gl.E)

/-- **The law's premise on the forms' worth, at the stated function of the seat's own tables.** -/
theorem billsWorthJ_funs {Y : Type} (ns : ℕ) (N : Nums) (A0 : Attention.Plan) (k3 : Runs.PadIn)
    (tj : OnBytes.K.Kc.Tape) (gOf : First.S × Y → Forest.Heard) (xr : Params.AttentionRounds)
    (on : First.S × Y → Prop) (R' : First.S × Y → Wit Cells Tok MsgT → Prop) (Rd : Readers)
    (St : Stated) (own : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ)
    (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem) (hi : ℕ)
    (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape))
    (hR' : ∀ b w, R' b w → formsTQ Rd St own 2 "first" b.1 (seatTab D.codes arr ms w) ∧
      formsTQ Rd St own 2 "second" b.1 (seatTab D.codes arr ms w) ∧
      formsTQ Rd St own 2 "join" b.1 (seatTab D.codes arr ms w))
    (hRd : ∀ (a b : First.S × Y) (w : Wit Cells Tok MsgT), on a → R' b w →
      ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i (plannedK A) l₁ l₂ jn k3 kf G tj xj
          A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∃ R₁ R₂ R₃ : VerifiableInference.Desc.K9.Read,
          Rd.forms 2 "first" b.1 = some R₁ ∧ R₁.late = [] ∧ (∀ f ∈ l₁, f ∈ R₁.forms) ∧
          Rd.forms 2 "second" b.1 = some R₂ ∧ R₂.late = [] ∧ (∀ f ∈ l₂, f ∈ R₂.forms) ∧
          Rd.forms 2 "join" b.1 = some R₃ ∧ R₃.late = [] ∧ xj.1 ∈ R₃.forms)
    (hR : SymsOK x A.seam.tl D rad) (hmk : masksUpTo D x hi = true)
    (hlo : reqLayoutOk D.codes D.shape D.layout = true)
    (hone : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      ((sigListCalls D rad x.link).get ⟨k, hk⟩).1.maskRows = 1)
    (hm : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hcov : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val →
      (k.val, seat k) ∈ ps ∧ (k.val, ((sigListCalls D rad x.link).get k).1) ∈ qs)
    (hcovM : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      (k, ((sigListCalls D rad x.link).get ⟨k, hk⟩).1) ∈ qs)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link →
      StatedAtt St A (funsAt A) s)
    (hfront : ∀ a : First.S × Y, on a → (∃ L, FrontFacts x A D own ps qs a.1 L) ∧
      ∀ a₀, a.1.here = .att a₀ → ∃ g, a₀.g = some g ∧ SeatReadsSame g (gOf a))
    (hbehind : ∀ (a b : First.S × Y) (w : Wit Cells Tok MsgT), on a → R' b w →
      ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i (plannedK A) l₁ l₂ jn k3 kf G tj xj
          A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∀ (pt : VerifiableInference.Desc.K9.Part) (L : LinkCtx), segAt? b.1 = some pt →
          a.1.link? = some L →
          BehindFacts A hi b.1 L pt (l₁ ++ l₂ ++ [xj.1]) ∧ (G.trees[A.iU3]?).isSome = true) :
    BillsWorthJ x A.seam.tl D rad Ex Wp α A.S ns N A0 (plannedK A) k3 A.nW tj gOf
      (fun a => lookOfO (parCOf A).geo.lmb (gOf a)) seatSO xr
      (fun a : First.S × Y => a.1) (fun a : First.S × Y => a.1) on
      (fun w => msgsOf D.codes (sigListCalls D rad x.link) seat arr w) R' := by
  refine billsWorthJ_at x A D rad Ex Wp α ns N A0 k3 tj gOf xr on R' Rd St own arr seat ms hi ps qs
    (funsAt A) hR' hRd hR hmk hone hm hcov hcovM hSt ?_
  intro a b w ha hRw F G h Ls h1 h2 s1 s2 s3 l i l₁ l₂ jn kf xj Rt pt hpt
  obtain ⟨⟨L, T⟩, hg⟩ := hfront a ha
  obtain ⟨B, hT⟩ := hbehind a b w ha hRw F G h Ls h1 h2 s1 s2 s3 l i l₁ l₂ jn kf xj Rt pt L hpt T.hL
  obtain ⟨att, e, _, eb⟩ := lay_is h1 h2
  have hs : b.1.here = .att { att with F := G, heard5 := some h } := by
    rw [eb]
    rfl
  obtain ⟨g, hg1, hg2⟩ := hg att e
  exact ⟨⟨L, tieFacts_of hlo hR (fun k hk => (hcov [] k hk).2) T h1 h2 hpt B⟩,
    funsAt_same A hs hg1 hg2 rfl rfl Rt.left Rt.geo Rt.points Rt.tables hT⟩

/-- **The same, with the relation behind := the table's own two filled items.** -/
theorem billsWorthJ_table {Y : Type} (ns : ℕ) (N : Nums) (A0 : Attention.Plan) (k3 : Runs.PadIn)
    (tj : OnBytes.K.Kc.Tape) (gOf : First.S × Y → Forest.Heard) (xr : Params.AttentionRounds)
    (on : First.S × Y → Prop) (R' : First.S × Y → Wit Cells Tok MsgT → Prop) (Rds : ℕ → Readers)
    (runs : ℕ → ℕ → String → List (ℕ × String))
    (St : Stated) (Nn : Numbers) (m : ℕ)
    (arr : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem)
    (hi : ℕ) (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape))
    (r1 : (2, "first") ∈ runs m 3 "own") (r2 : (2, "second") ∈ runs m 3 "own")
    (r3 : (2, "join") ∈ runs m 2 "join")
    (hitems : ∀ b w, R' b w →
      (∀ p ∈ runs m 3 "own", formsTQ (Rds m) St (Nn.sent m 0) p.1 p.2 b.1 (seatTab D.codes arr ms w)) ∧
      ∀ p ∈ runs m 2 "join", formsTQ (Rds m) St (Nn.sent m 0) p.1 p.2 b.1 (seatTab D.codes arr ms w))
    (hRd : ∀ (a b : First.S × Y) (w : Wit Cells Tok MsgT), on a → R' b w →
      ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i (plannedK A) l₁ l₂ jn k3 kf G tj xj
          A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∃ R₁ R₂ R₃ : VerifiableInference.Desc.K9.Read,
          (Rds m).forms 2 "first" b.1 = some R₁ ∧ R₁.late = [] ∧ (∀ f ∈ l₁, f ∈ R₁.forms) ∧
          (Rds m).forms 2 "second" b.1 = some R₂ ∧ R₂.late = [] ∧ (∀ f ∈ l₂, f ∈ R₂.forms) ∧
          (Rds m).forms 2 "join" b.1 = some R₃ ∧ R₃.late = [] ∧ xj.1 ∈ R₃.forms)
    (hR : SymsOK x A.seam.tl D rad) (hmk : masksUpTo D x hi = true)
    (hlo : reqLayoutOk D.codes D.shape D.layout = true)
    (hone : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      ((sigListCalls D rad x.link).get ⟨k, hk⟩).1.maskRows = 1)
    (hm : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hcov : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val →
      (k.val, seat k) ∈ ps ∧ (k.val, ((sigListCalls D rad x.link).get k).1) ∈ qs)
    (hcovM : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      (k, ((sigListCalls D rad x.link).get ⟨k, hk⟩).1) ∈ qs)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link →
      StatedAtt St A (funsAt A) s)
    (hfront : ∀ a : First.S × Y, on a → (∃ L, FrontFacts x A D (Nn.sent m 0) ps qs a.1 L) ∧
      ∀ a₀, a.1.here = .att a₀ → ∃ g, a₀.g = some g ∧ SeatReadsSame g (gOf a))
    (hbehind : ∀ (a b : First.S × Y) (w : Wit Cells Tok MsgT), on a → R' b w →
      ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i (plannedK A) l₁ l₂ jn k3 kf G tj xj
          A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∀ (pt : VerifiableInference.Desc.K9.Part) (L : LinkCtx), segAt? b.1 = some pt →
          a.1.link? = some L →
          BehindFacts A hi b.1 L pt (l₁ ++ l₂ ++ [xj.1]) ∧ (G.trees[A.iU3]?).isSome = true) :
    BillsWorthJ x A.seam.tl D rad Ex Wp α A.S ns N A0 (plannedK A) k3 A.nW tj gOf
      (fun a => lookOfO (parCOf A).geo.lmb (gOf a)) seatSO xr
      (fun a : First.S × Y => a.1) (fun a : First.S × Y => a.1) on
      (fun w => msgsOf D.codes (sigListCalls D rad x.link) seat arr w) R' :=
  billsWorthJ_funs x A D rad Ex Wp α ns N A0 k3 tj gOf xr on R' (Rds m) St (Nn.sent m 0) arr seat ms hi
    ps qs
    (fun b w hb => formsT_gives D.codes arr ms Rds runs St Nn m b.1 w r1 r2 r3
      (hitems b w hb).1 (hitems b w hb).2)
    hRd hR hmk hlo hone hm hcov hcovM hSt hfront hbehind

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.tieFacts_of
#print axioms VerifiableInference.Desc.First.Att.P.billsWorthJ_funs
#print axioms VerifiableInference.Desc.First.Att.P.billsWorthJ_table
