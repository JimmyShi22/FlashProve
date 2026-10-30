-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OkPlanes.lean (kind K9): WHAT THE CALLER's CLAUSES OF THE
  LOOKUP's RUNS "planes" AND "join" ASK OF THE FIXED PART, AND NO CLAUSE OF THE NAMED Ok
  (OkOne.lean) HOLDS: AS TWO NAMED STRUCTURES, ONE A SORT OF LINK, with a test with code for each
  clause. Definitions, and theorems. It changes no other file.

Why. The worth of a caller's form in the world of a full later state is a function of the fixed part
  only if each entry that it names stands at virtual row 0 of a table's vector (`EntsOk`). The named
  Ok has such clauses for first | second · K6 | join | merge · front | back: none for "planes" at
  either sort of link, none for the attention's key forms.

  `seatCQ rd c`: the attention's claims' seat (`SeatC`, Att/RunsK.lean) AT THE FIXED PART AND THE
    SNAPSHOT: seatCO's five readers (Att/SeatO.lean), what was heard read by rd, the ledger the
    snapshot's. So `readersOfK (seatCQ rd c) c q` and `keysOfK (seatCQ rd c) c q` are the kind's own
    texts at q: nothing of THEM is typed again. The seat's five fields ARE typed after seatCO's:
    `seatCQ_at` | `readers_at`: THE TIE: at a state in an attention segment whose heard values rd
    reads at q and whose ledger is the snapshot's, they read just what the run's own seat reads.
  `planesQ iU3 kap`: the head's three further reads (`planesAt`, Stored/HeadSeatAt.lean) at q: the
    tables read by kap, the width the snapshot's; nothing unless the head's link is opened.
    `planesQ_at`: THE TIE: it is planesAt at a state that kap sees at q, its ledger the snapshot's.
  `PlanesAttOk rd c nU q`: **planes: whatever form a reader of "planes" hands in at q passes EntsOk
    · keysEnts: the key forms pass EntsOk.** `PlanesHeadOk iU3 kap nU q`: **planes**, likewise. A
    clause says nothing where its reader answers nothing.
  `formsUpTo r n`: the forms that two readers hand in at the columns below n. `planesAttB` |
    `planesHeadB` (at the columns below n) · `keysEntsB`: the tests; `answersB`: against an idle
    yes: how many forms the readers hand in. `entsOk_of_B`, `keysEnts_of_B`: a yes of keysEntsB
    gives keysEnts. FROM planesAttB | planesHeadB NO LAW LEADS TO THE CLAUSE planes.
NO CLAUSE keysFilled («every slot of a key form is filled in the
  snapshot's ledger») STANDS HERE, and no test of it: it is a theorem off the
  named Ok's own k5 (filled_keys_att, Johnson/P1K9R/CallerAtLetters.lean).
  One structure would take the letters of both sorts together; cut by
  sort, nothing idle is owed.
Limits. SHOWN OF NO STATE. OF THIS FILE ONLY seatCQ, planesQ AND THE TWO STRUCTURES ARE SPENT BY A
  LAW: the five theorems and the six definitions of tests served an evaluation and are called by no
  other file of the library. On one honest run at the full size (evaluated; no theorem) the four key
  forms name slots and NO ENTRY: keysEnts holds idly there; the readers of "planes" do hand in
  forms. The two tests on "planes" ask the columns below n alone. THE TIES HERE
  STAND AT A STATE WHOSE LEDGER IS THE SNAPSHOT's (so at the front itself); at a state that goes on
  from q Johnson/P1K9R/CallerReads.lean has the equations. The head's key forms
  are not treated. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.OkOne
import Johnson.Desc.First.Att.Guest
import Johnson.Desc.First.Att.SeatO
import Johnson.Stored.HeadSeatAt
import Johnson.Desc.Kinds.HeadCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC SeatC readersOfK keysOfK)
open VerifiableInference.Desc.Kinds.Head (PlaneSeat planeEntry callerReaders)
open VerifiableInference.Desc.Kinds.Head.Law (Seen)

variable {β : Type}

/-- The attention's claims' seat at the fixed part and the snapshot. -/
def seatCQ (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : ParC) : SeatC (Q β) where
  pts q := (rd q.1).bind fun gh => q.2.bind fun u => P.ptsFrom c.geo gh.1.zk gh.2 u.F
  cols q := q.2.bind fun u => (u.F.trees[c.iU3]?).map (·.K)
  look q := (rd q.1).map fun gh => P.lookOfO c.geo.lmb gh.1
  pad q := (rd q.1).map fun gh => P.padOfO gh.1.shape
  zk q := (rd q.1).map fun gh => gh.1.zk

/-- The head's three further reads at the fixed part and the snapshot. -/
def planesQ (iU3 : ℕ) (kap : Phi β → Option Seen) : PlaneSeat (Q β) := fun q =>
  (kap q.1).bind fun z => if z.opened then
    z.t.bind fun tt => q.2.bind fun u => (u.F.trees[iU3]?).bind fun tr =>
      if tr.K == 0 then none else some (planeEntry tt.tab iU3 tr.K)
  else none

/-- **THE TIE, ATTENTION**: at a state in an attention segment whose heard values rd reads at q and
whose ledger is the snapshot's: the seat at q reads just what the run's own seat reads at the
state. -/
theorem seatCQ_at {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : ParC} {q : Q β}
    {s : First.S} {a : First.AttOwn} {g : Forest.Heard} {h : First.Att.P.Heard} {u : Pub9}
    (hs : s.here = .att a) (hg : a.g = some g) (hh : s.heard5? = some h)
    (hrd : rd q.1 = some (g, h)) (hu : q.2 = some u) (hF : u.F = a.F) :
    (seatCQ rd c).pts q = (P.seatCO c).pts s ∧ (seatCQ rd c).cols q = (P.seatCO c).cols s ∧
      (seatCQ rd c).look q = (P.seatCO c).look s ∧ (seatCQ rd c).pad q = (P.seatCO c).pad s ∧
      (seatCQ rd c).zk q = (P.seatCO c).zk s := by
  unfold seatCQ P.seatCO
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [hs, hg, hh, hrd, hu, hF]

/-- So the readers of "planes" and the key forms at q are the run's own at the state. -/
theorem readers_at {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : ParC} {q : Q β}
    {s : First.S} {a : First.AttOwn} {g : Forest.Heard} {h : First.Att.P.Heard} {u : Pub9}
    (hs : s.here = .att a) (hg : a.g = some g) (hh : s.heard5? = some h)
    (hrd : rd q.1 = some (g, h)) (hu : q.2 = some u) (hF : u.F = a.F) :
    readersOfK (seatCQ rd c) c q = readersOfK (P.seatCO c) c s ∧
      keysOfK (seatCQ rd c) c q = keysOfK (P.seatCO c) c s := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := seatCQ_at (c := c) hs hg hh hrd hu hF
  have ei : P.inOf (seatCQ rd c) c q = P.inOf (P.seatCO c) c s := by
    unfold P.inOf
    rw [e1, e2, e3, e5]
  unfold readersOfK keysOfK
  rw [ei, e4]
  exact ⟨rfl, rfl⟩

/-- **THE TIE, THE HEAD**: at a state in the head's link that kap sees at q, its ledger the
snapshot's. -/
theorem planesQ_at {iU3 : ℕ} {kap : Phi β → Option Seen} {q : Q β} {s : First.S}
    {o : First.HeadOwn} {z : Seen} {u : Pub9} (hs : s.here = .head o) (hk : kap q.1 = some z)
    (ho : z.opened = o.opened) (ht : z.t = o.t) (hu : q.2 = some u) (hF : u.F = o.F) :
    planesQ iU3 kap q = VerifiableInference.Desc.Kinds.Head.planesAt iU3 s := by
  unfold planesQ VerifiableInference.Desc.Kinds.Head.planesAt First.S.fork?
  simp only [hs, hk, ho, ht, hu, hF, Option.bind_some]
  cases hop : o.opened <;> simp

/-- **WHAT "planes" AND "join" ASK OF THE FIXED PART AT AN ATTENTION LINK.** -/
structure PlanesAttOk (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : ParC)
    (nU : Array ℕ) (q : Q β) : Prop where
  planes : ∀ r, readersOfK (seatCQ rd c) c q = some r →
    (∀ e col f, r.1 e col = some f → EntsOk nU q [f]) ∧ ∀ col f, r.2 col = some f → EntsOk nU q [f]
  keysEnts : ∀ KF, keysOfK (seatCQ rd c) c q = some KF → EntsOk nU q KF.toList

/-- **WHAT "planes" ASKS OF THE FIXED PART AT THE HEAD's LINK.** -/
structure PlanesHeadOk (iU3 : ℕ) (kap : Phi β → Option Seen) (nU : Array ℕ) (q : Q β) : Prop where
  planes : ∀ r, callerReaders (planesQ iU3 kap) q = some r →
    (∀ e col f, r.1 e col = some f → EntsOk nU q [f]) ∧ ∀ col f, r.2 col = some f → EntsOk nU q [f]

/-- The forms that two readers hand in at the columns below n. -/
def formsUpTo (r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)) (n : ℕ) : List Aff :=
  (List.range n).filterMap (r.1 0) ++ (List.range n).filterMap (r.1 1) ++
    (List.range n).filterMap r.2

/-- EntsOk's test at q; yes where the structure or the snapshot is not there, as EntsOk is. -/
def entsOkB (nU : Array ℕ) (q : Q β) (l : List Aff) : Bool :=
  match (pi8 q.1).1, q.2 with
  | some tlb, some v => entsAtB nU tlb (v.F.trees.toList.map look) l
  | _, _ => true

theorem entsOk_of_B {nU : Array ℕ} {q : Q β} {l : List Aff} (h : entsOkB nU q l = true) :
    EntsOk nU q l := by
  intro tlb v h1 h2
  unfold entsOkB at h
  rw [h1, h2] at h
  exact h

def planesAttB (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : ParC) (nU : Array ℕ)
    (n : ℕ) (q : Q β) : Bool :=
  match readersOfK (seatCQ rd c) c q with
  | some r => entsOkB nU q (formsUpTo r n)
  | none => true

def planesHeadB (iU3 : ℕ) (kap : Phi β → Option Seen) (nU : Array ℕ) (n : ℕ) (q : Q β) : Bool :=
  match callerReaders (planesQ iU3 kap) q with
  | some r => entsOkB nU q (formsUpTo r n)
  | none => true

def keysEntsB (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : ParC) (nU : Array ℕ)
    (q : Q β) : Bool :=
  match keysOfK (seatCQ rd c) c q with
  | some KF => entsOkB nU q KF.toList
  | none => true

/-- Against an idle yes: how many forms are handed in at the columns below n and at just n: by the
attention's readers, by the head's; how many key forms, slots and entries in them. -/
def answersB (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (c : ParC) (iU3 : ℕ)
    (kap : Phi β → Option Seen) (n : ℕ) (q : Q β) : List ℕ :=
  let cnt (x : Option ((ℕ → ℕ → Option Aff) × (ℕ → Option Aff))) : List ℕ :=
    match x with
    | some r => [(formsUpTo r n).length, (formsUpTo r (n + 1)).length - (formsUpTo r n).length]
    | none => [0, 0]
  let KF := ((keysOfK (seatCQ rd c) c q).map (·.toList)).getD []
  cnt (readersOfK (seatCQ rd c) c q) ++ cnt (callerReaders (planesQ iU3 kap) q) ++
    [KF.length, (KF.map fun f => f.slots.size).sum, (KF.map fun f => f.ents.size).sum]

theorem keysEnts_of_B {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : ParC}
    {nU : Array ℕ} {q : Q β} (h : keysEntsB rd c nU q = true) :
    ∀ KF, keysOfK (seatCQ rd c) c q = some KF → EntsOk nU q KF.toList := by
  intro KF h1
  unfold keysEntsB at h
  rw [h1] at h
  exact entsOk_of_B h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.seatCQ_at
#print axioms VerifiableInference.Desc.LinkJoin.readers_at
#print axioms VerifiableInference.Desc.LinkJoin.planesQ_at
#print axioms VerifiableInference.Desc.LinkJoin.entsOk_of_B
#print axioms VerifiableInference.Desc.LinkJoin.keysEnts_of_B
