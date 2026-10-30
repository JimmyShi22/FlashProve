-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadsAfter.lean: CONDITIONAL: at the place of an attention segment that
sends the array of the segment's tables, the verifier's sub-protocol is a sending with a quiet step
joined behind it (the step that makes the tables of what was heard and closes the list,
`readsAtSO`, Johnson/Desc/First/Att/ReadsO.lean). Here: what the sending's own yes leaves of the
state; that the quiet step says yes behind it, where the points' and the tables' functions return
IN FRONT of the sending; and so the yes of the whole sub-protocol as it stands in the first chain.

How the sub-protocol is laid (Johnson/IMR/K1Seat.lean, Johnson/IMR/SeatForm.lean):
`IM.k1Reads Z G l X pr reads` is `k.andThen k.name (IM.k1Quiet G l X)`, with k the sending
(`K1.laterAt`, Johnson/Desc/K1/Places.lean); in the chain it stands as
`IM.seatedAs ProofFile.sameReply (..).retype name place`: carried to the chain's type of claims; on its
yes follow a test that the state it returns bears no mark and a guard that the reply is as it was.

Main names:
  `k1_leaves`: behind a yes of the sending at an open attention segment the segment is open still,
    with a new link's context and a new ledger and NOTHING ELSE of the segment turned: what its own
    rounds heard, what the lookup returned, the smallness test's part are as they were; the new
    ledger has the old one's slots; the mark and the output are as they were. By the library's
    `commitAtS_slots` (Johnson/Desc/K1/KeepsSlots.lean) and `here_commit`
    (Johnson/Desc/First/Att/Claims/FunsAtTl.lean).
  `reads_after`: the quiet step's yes behind the sending's.
  `quiet_is`: at a link of the attention sort the joined block's decision is `readsAtSO`.
  `seated_reads_yes`: **the yes of the sub-protocol as it stands in the chain**, from the sending's
    own yes AND the quiet step's behind it, where the state behind has no mark and the old output.

Limits. All are conditional. THE SENDING'S OWN YES IS A PREMISE. So are: an attention segment is
open in front and holds what its own rounds heard and what the lookup returned; the points' and the
tables' functions return there; the list of tables is open in front; there is one shape a matrix;
the guard of order says yes at the link's context and the statement BEHIND the sending. None is
shown to be met here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ReadsReturn
import Johnson.Desc.First.Att.Claims.FunsAtTl
import Johnson.IMR.K1Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S AttOwn K8.Order.orderOk)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.K1 (laterAt)

/-- **What the sending's own yes leaves, at an open attention segment.** Conditional: h: the yes;
ha: the open segment. -/
theorem k1_leaves {Cl : Type} {q : Params.First} {gp : _root_.Desc.Plain.GPar}
    {link piece moment : ℕ} {arrays : Option (List ℕ)} {s m : S} {a₀ : AttOwn} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (laterAt (Cl := Cl) q gp link piece moment arrays).decide s rs gs = .ok m)
    (ha : s.here = .att a₀) :
    ∃ L' F', m.here = .att { a₀ with L := L', F := F' } ∧ PscRun.SlotsSame a₀.F F' ∧
      m.failed = s.failed ∧ m.out = s.out := by
  obtain ⟨_, F, _, y, _, hF, _, em, ss⟩ := VerifiableInference.Desc.K1.commitAtS_slots h
  have hf : s.fork? = some a₀.F := by
    unfold S.fork?
    rw [ha]
  obtain rfl : a₀.F = F := Option.some.inj (hf.symm.trans hF)
  have hm := K5Law.here_commit ha y.w y.L y.F
  rw [← em] at hm
  refine ⟨y.L, y.F, hm, ss, ?_, ?_⟩
  · rw [em]
    unfold S.putFork S.putLink VerifiableInference.Desc.K1.laid
    simp only [ha]
  · rw [em]
    unfold S.putFork S.putLink VerifiableInference.Desc.K1.laid
    simp only [ha]

/-- **The quiet step says yes behind the sending.** Conditional:
  hs, h5, hg, ho: in front of the sending an attention segment is open, what its own rounds heard
    and what the lookup returned are laid, the list of tables is open;
  hp, ht: the points' and the tables' functions return at the ledger in front;
  hshp: there is one shape a matrix;
  h1: the sending's own yes;
  hord: the guard of order says yes at the link's context and the statement behind the sending. -/
theorem reads_after {Cl : Type} (A : Attention.Plan) {q : Params.First}
    {gp : _root_.Desc.Plain.GPar} {link piece moment : ℕ} {arrays : Option (List ℕ)} {s m : S}
    {a₀ : AttOwn} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {hh : P.Heard}
    {g : Forest.Heard} {p : P.Pts} {t : P.TablesP} (hs : s.here = .att a₀)
    (h5 : a₀.heard5 = some hh) (hg : a₀.g = some g) (ho : a₀.tl.funClosed = false)
    (hp : P.ptsFrom (P.parCOf A).geo g.zk hh a₀.F = some p)
    (ht : P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
      (P.lookOfO (P.parCOf A).geo.lmb g) p = some t)
    (hshp : a₀.tl.shp.size = a₀.tl.NM)
    (h1 : (laterAt (Cl := Cl) q gp link piece moment arrays).decide s rs gs = .ok m)
    (hord : ∀ L', m.link? = some L' → K8.Order.orderOk a₀.tl L' m.st = true) :
    ∃ a₁, m.here = .att a₁ ∧ readsAtSO A m = .ok (behindReads m a₁ t) ∧
      (behindReads m a₁ t).failed = s.failed ∧ (behindReads m a₁ t).out = s.out := by
  obtain ⟨L', F', hm, ss, hf, hout⟩ := k1_leaves h1 hs
  have hL : m.link? = some L' := by
    unfold S.link?
    rw [hm]
  refine ⟨_, hm, reads_return_of A hm h5 hg ho ?_ ht hshp
    ((order_any _ _ _ _ _).trans (hord L' hL)), hf, hout⟩
  show P.ptsFrom (P.parCOf A).geo g.zk hh F' = some p
  rw [K5Law.ptsFrom_same (K5Law.shown_same ss)]
  exact hp

/-- At a link of the attention sort whose group has the plan A the joined block's decision is the
quiet step. -/
theorem quiet_is (G : ProofFile.Ground) (l : ℕ) (X : Stages.LinkH) {A : Attention.Plan}
    (hk : X.kind = 1) (hA : G.W.A[X.g]? = some A) (m : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) :
    (IM.k1Quiet G l X).decide m rs gs = readsAtSO A m := by
  unfold IM.k1Quiet ProofFile.readsQuietAt readsAtO
  simp only [hk, hA]
  rfl

/-- **The yes of the sub-protocol as it stands in the first chain, from its two halves' yes.**
Conditional: hk, hA: the link is of the attention sort and its group has the plan A; h1: the
sending's own yes, at its share of the rounds and the groups; h2: the quiet step's yes behind it;
hf: the state behind bears no mark; hout: it has the whole output of the state in front (the guard
reads the reply alone). -/
theorem seated_reads_yes (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : Stages.LinkH)
    (reads : Option (List ℕ)) (name : String) {A : Attention.Plan} (hk : X.kind = 1)
    (hA : G.W.A[X.g]? = some A) {s m s₂ : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h1 : (laterAt (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l 4 1 reads).decide s
      (rs.take (laterAt (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l 4 1
        reads).rounds.length)
      (gs.take (laterAt (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l 4 1
        reads).openings) = .ok m)
    (h2 : readsAtSO A m = .ok s₂) (hf : s₂.failed = none) (hout : s₂.out = s.out) :
    (IM.seatedAs ProofFile.sameReply (IM.k1Reads Z G l X 4 reads).retype name
      ⟨1, some l, 4, .K1⟩).decide s rs gs = .ok s₂ := by
  have hj : (IM.k1Reads Z G l X 4 reads).decide s rs gs = .ok s₂ := by
    unfold IM.k1Reads
    show ((laterAt (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l 4 1 reads).decide s
      _ _).bind (fun s' => (IM.k1Quiet G l X).decide s' _ _) = _
    rw [h1]
    show (IM.k1Quiet G l X).decide m _ _ = _
    rw [quiet_is G l X hk hA]
    exact h2
  show (((IM.k1Reads Z G l X 4 reads).decide s rs gs).bind fun t =>
      match t.failed with
      | none => .ok t
      | some e => .error ("marked: " ++ e)).bind
    (VerifiableInference.Desc.seatSame ProofFile.sameReply s) = .ok s₂
  rw [hj]
  show ((match s₂.failed with
      | none => (.ok s₂ : Except String S)
      | some e => .error ("marked: " ++ e))).bind
    (VerifiableInference.Desc.seatSame ProofFile.sameReply s) = .ok s₂
  rw [hf]
  show VerifiableInference.Desc.seatSame ProofFile.sameReply s s₂ = .ok s₂
  unfold VerifiableInference.Desc.seatSame ProofFile.sameReply
  rw [hout]
  simp

end H2K5.Honest

#print axioms H2K5.Honest.k1_leaves
#print axioms H2K5.Honest.reads_after
#print axioms H2K5.Honest.quiet_is
#print axioms H2K5.Honest.seated_reads_yes
