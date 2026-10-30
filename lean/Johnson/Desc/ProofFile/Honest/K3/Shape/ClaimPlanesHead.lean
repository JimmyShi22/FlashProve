-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/ClaimPlanesHead.lean: at the output head's link the
hypothesis of the law of "planes" (`ReadersAgree`, Honest/K3/Shape/ClaimPlanes.lean) holds at every
state: the calling kind's readers there read of the state the table of its tables and one array's
number of columns, and the chain's shape holds both. Definitions with code; theorems.

Terms. Honest/K3/GLOSSARY.md, and the head of Honest/K3/Shape/ClaimRuns.lean for "run on shapes",
"law" and "the guard on the reply". In this file: iU3 is a letter for the number of the reads'
array; lm is a letter: the planes' matrix has 2 ^ lm rows.

What is shown.
  `headReadersG iU3`: the head's readers on shapes: the library's own `planeEntry`
    (Johnson/Stored/HeadSeat.lean), called at what the shape holds.
  `planesAt_head`: the library's reader `planesAt` (Johnson/Stored/HeadSeatAt.lean) at a state in
    the head's link, unfolded.
  `readersAgree_head`: `ReadersAgree` at the head's readers, at every state. No hypothesis.
  `lawOfPre`: general in the run: a law whose hypothesis always holds, as a law at the hypothesis
    "true".
  `planesLawHead`, `planesLawHeadG`: the law of "planes" at the head's readers, at the hypothesis
    "true"; the same behind the guard on the reply.

Hypotheses that remain.
  `hs`, `hF`, `ht`, `htr`, `hk`: (in `planesAt_head`) five facts on the state: it stands in the
    head's link; a ledger is open; the tables are set; the array number iU3 is there; it has a
    column.
The other statements have none. In both fields of the two laws the return of the run on shapes
remains a hypothesis.

Users. `member_states_planes_head` (Honest/K3/Shape/ClaimAtHead.lean [not in this library]) and
`find_planes_head` (Honest/K3/Shape/ClaimAtHeadLink.lean [not in this library]) show that
`planesRun` at the head's readers, behind the guard, is stated at the head's link; that this is the
run of `planesLawHeadG` stands as Lean checks it in `found_planes_head_law` (ClaimAtHeadLink.lean
[not in this library]). `planesHead_preB` (Honest/K3/Shape/ClaimKeeps.lean) calls `planesLawHead`.

Limits. `headReadersG` answers only where the chain stands in the head's link with its ledger open,
the tables set, and the array there with a column; elsewhere the run on shapes refuses and the law
is silent. Whether the run on shapes returns at the shape that the chain reaches there is not shown:
each of the three tables must be as long as the planes' matrix has columns. Nothing at attention
links. No instance of these hypotheses is exhibited in this file. Nothing is evaluated here.
The letters lm and iU3 are free in this file. That these are the readers which the lot's
sub-protocol states at the head's link is the library's `readersAt_head`
(Johnson/Desc/First/Link/Law/SortK3PlanesRun.lean), which is not called here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.ClaimPlanes
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes.Model (Fork HTree)
open VerifiableInference.Desc.K3 (seatCalls planesRun)
open VerifiableInference.Desc.K9.Shape (RunLaw)
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt planeEntry)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh ledSh affSh treeSh headSh)
open ProofFile (sameReply)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "RunT" => VerifiableInference.Desc.K9.Shape.Run

/-- **The head's readers on shapes.** Here iU3 is the number of the reads' array. -/
def headReadersG (iU3 : Nat) (c : ChainSh) : Option ReadersSh :=
  c.head.bind fun hd => c.led.bind fun L => hd.tab.bind fun tab => (L.trees[iU3]?).bind fun T =>
    if T.K == 0 then none
    else some (fun e col =>
        (planeEntry tab iU3 T.K (if e == 0 then .bits0 else .bits1) col).map affSh,
      fun col => (planeEntry tab iU3 T.K .pin col).map affSh)

/-- The library's reader at a state in the head's link. Conditional on the five facts on the state.
-/
theorem planesAt_head (iU3 : Nat) (s : FS) {o : VerifiableInference.Desc.First.HeadOwn} {F : Fork}
    {tt : OnBytes.Model.Head.Tables} {tr : HTree} (hs : s.here = .head o)
    (hF : s.fork? = some F) (ht : o.t = some tt) (htr : F.trees[iU3]? = some tr)
    (hk : ¬ (tr.K == 0) = true) : planesAt iU3 s = some (planeEntry tt.tab iU3 tr.K) := by
  unfold planesAt
  rw [hs, hF]
  show (o.t.bind fun tt => (F.trees[iU3]?).bind fun tr =>
    if tr.K == 0 then none else some (planeEntry tt.tab iU3 tr.K)) = _
  rw [ht]
  show ((F.trees[iU3]?).bind fun tr =>
    if tr.K == 0 then none else some (planeEntry tt.tab iU3 tr.K)) = _
  rw [htr]
  show (if tr.K == 0 then none else some (planeEntry tt.tab iU3 tr.K)) = _
  rw [if_neg hk]

/-- **The hypothesis of the law of "planes" holds at the head's readers, at every state.** No
hypothesis. -/
theorem readersAgree_head (lm iU3 : Nat) (s : FS) :
    ReadersAgree lm (callerReaders (planesAt iU3)) (headReadersG iU3) s := by
  intro q hq
  unfold headReadersG at hq
  obtain ⟨hd, h1, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨L, h2, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨tab, h3, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨T, h4, hq⟩ := Option.bind_eq_some_iff.1 hq
  have h1' : VerifiableInference.Desc.First.Shape.headOf s.here = some hd := h1
  have h2' : s.fork?.map ledSh = some L := h2
  obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.1 h2'
  cases hs : s.here with
  | head o =>
    rw [hs] at h1'
    obtain rfl : headSh o = hd := Option.some.inj h1'
    have h3' : o.t.map (·.tab) = some tab := h3
    obtain ⟨tt, ht, rfl⟩ := Option.map_eq_some_iff.1 h3'
    have h4' : (F.trees.toList.map treeSh)[iU3]? = some T := h4
    rw [List.getElem?_map, Array.getElem?_toList] at h4'
    obtain ⟨tr, htr, rfl⟩ := Option.map_eq_some_iff.1 h4'
    have hq' : (if tr.K == 0 then none
        else some ((fun e col =>
            (planeEntry tt.tab iU3 tr.K (if e == 0 then .bits0 else .bits1) col).map affSh,
          fun col => (planeEntry tt.tab iU3 tr.K .pin col).map affSh) : ReadersSh)) = some q := hq
    split at hq'
    · exact nomatch hq'
    · rename_i hk
      obtain rfl := Option.some.inj hq'
      refine ⟨(fun e col => planeEntry tt.tab iU3 tr.K (if e == 0 then .bits0 else .bits1) col,
        planeEntry tt.tab iU3 tr.K .pin), ?_, fun _ _ => ⟨fun _ _ => rfl, rfl⟩⟩
      show (planesAt iU3 s).map _ = _
      rw [planesAt_head iU3 s hs hF ht htr hk]
      rfl
  | _ =>
    rw [hs] at h1'
    exact nomatch h1'

/-- **A law whose hypothesis always holds, as a law at the hypothesis "true".** General in the run.
-/
def lawOfPre {run : RunT} (R : RunLaw run) (h : ∀ n s, R.pre n s) : RunLaw run where
  runG := R.runG
  pre := fun _ _ => True
  carries := fun n s s' cs y _ => R.carries n s s' cs y (h n s)
  returns := fun n s y hg _ => R.returns n s y hg (h n s)

/-- **The law of "planes" at the head's readers.** Its hypothesis is "true". -/
def planesLawHead (lm iU3 : Nat) :
    RunLaw (planesRun (seatCalls K3Lot.ofForm) lm (callerReaders (planesAt iU3))) :=
  lawOfPre (planesLaw lm (callerReaders (planesAt iU3)) (headReadersG iU3))
    fun _ s => readersAgree_head lm iU3 s

/-- The same behind the guard on the reply. -/
def planesLawHeadG (lm iU3 : Nat) : RunLaw (IM.guardRun sameReply
    (planesRun (seatCalls K3Lot.ofForm) lm (callerReaders (planesAt iU3)))) :=
  guardLaw (planesLawHead lm iU3) (planesRun_reply lm (callerReaders (planesAt iU3)))

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.planesAt_head
#print axioms ProofFile.Honest.K3.Shape.readersAgree_head
#print axioms ProofFile.Honest.K3.Shape.lawOfPre
#print axioms ProofFile.Honest.K3.Shape.planesLawHead
#print axioms ProofFile.Honest.K3.Shape.planesLawHeadG
