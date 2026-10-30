-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TableAt.lean: CONDITIONAL: the hypothesis `K4Table`
(Law/Table.lean) at the library's own parameters of the first chain's thread (`lettersAt`,
Honest/Thread/FirstAt.lean). Statements and proofs, by unfolding and rewriting.

Not shown here. THAT THE HYPOTHESIS h ON THE PUBLIC FILES HOLDS OF ANY FILES: the side library
AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Where h holds of nothing, every statement here but `owes_k4` is empty.
THE FULL SIZE ALONE, AND THE OLDER HASH (secondHashFunction) ALONE, as that file has it. That the
member stands at piece 3 of a layers' segment, and that the chain has a link of that number, are
hypotheses on public data. The thread's list of the segments' sorts and the data's are one by
unfolding.
WHAT THIS FILE's IMPORTS REACH, by a program's walk of import lines that stops, unopened, at every
module under Johnson/Goal/, Johnson/D/ or ThirdParty/ and at the names RecCompile.Honest…, Both… and
PassH…: 46 modules whose names hold RecCompile; it stopped at 16 under Johnson/Goal/ and 2 under
ThirdParty/, and what these import is not counted; none under Johnson/D/, none of the three names.
Nothing on soundness, on completeness or on any other property.

  `owes_k4`: general in the parameters L of a first chain: at a member that stands at piece 3 of a
    layers' segment m (`AtK4`, Johnson/Road/K4/K4AtTable.lean) the thread's forward row owes eight
    items: the four that the table's row opens, and the four that it reads, again.
  `restK4 m`: the five of them beside K4's own item and the two for which no run is listed.
  `means_formsT_at`: at the library's parameters the thread's sentence at an item "the forms of the
    runs that the table names (m, k, r) are worth 0" is, by unfolding: at every run that the data
    list: `formsTQ` at the data's readers, stated function and first sending's seats, on the
    witness's tables; and a clause that says nothing unless r is "weights".
  `runs_own`, `runs_planes`, `runs_join`: at a layers' segment the data list K4's two runs for (m,
    3, "own"), and none for (m, 2, "planes") and (m, 2, "join").
  `holesK4 Zp m l`: the filling of the two holes of the link's readers, by name.
  `k4Table_at`: SO `K4Table` HOLDS THERE, at that filling.
  Two `example`s at the foot lay `k4Table_at` into `k4_own_share` (Law/Kept.lean) and
    `exchange_of_shares`, and into `k4_own_share_of_worths` (Law/Worth.lean) and
    `exchangeS_of_shares`: they say nothing new; they stand so that Lean holds the types together.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Worth
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt
import Johnson.Desc.Sound.MgAt.Runs
import Johnson.Road.K4.K4AtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open ProofFile.Honest.FirstThread (Letters Script WtF lettersAt)
open VerifiableInference.Desc (Place Strs Chain Link)
open VerifiableInference.Desc.First (Item ModelPart)
open VerifiableInference.Desc.K9 (LinkHoles readersOfLink readersAt_some holesAt)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ formsTQ seatTab runsAt runsAt_of)
open VerifiableInference.OnPublicFiles (headLink)
open OnBytes.Road.K4 (AtK4)
open P5J (AtMgA TS CellsM)

/-- The five items that K4's row owes beside its own and the two for which no run is listed: the
pending row's, and the four that the row reads. -/
def restK4 (m : Nat) : List Item := [.wo m, .pin m 0, .pinW, .constr m .small, .pinI]

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M)

/-- **What the thread owes behind K4's member**: eight items. -/
theorem owes_k4 {b m : Nat} {pl : Place} (H : AtK4 L.links L.ps b m pl) :
    (L.thread.row b).owes =
      Item.formsT m 3 "own" :: .formsT m 2 "planes" :: .formsT m 2 "join" :: restK4 m := by
  have hr : VerifiableInference.Desc.First.rowOf L.links pl =
      VerifiableInference.Desc.First.segRow .layers m 3 := by
    simp only [VerifiableInference.Desc.First.rowOf, H.link, H.sub, H.piece]
  show (FirstRows.rows L.links L.ps b).owes = _
  simp only [FirstRows.rows, H.here, Option.map_some, Option.getD_some, FirstRows.rowAt,
    FirstRows.turn, H.link, Option.isNone_some, Bool.false_and, hr]
  rfl

end

/-- The filling of the two holes of the readers of link number m, as the library's data lay it. -/
def holesK4 (Zp : ProofFile.Pub) (m : Nat) (l : Link TS ProofFile.Cl) : LinkHoles :=
  holesAt (P5J.At.X Zp) (headLink (P5J.At.X Zp)) m l

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- An item on the forms of runs, at the library's own parameters, unfolded. -/
theorem means_formsT_at (m k : Nat) (rn : String) (w : Local W₀ Rc ProofFile.Inst Tr)
    (a : ProofFile.InstPub × TS) (y : Strs) (v : WtF) :
    (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.means w
        (Item.formsT m k rn) a y v ↔
      (∀ p ∈ h.𝔇.runs m k rn, formsTQ (h.𝔇.Rd m) h.𝔇.St (h.𝔇.N.sent m 0) p.1 p.2 a.2
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) ∧ (rn = "weights" → h.𝔇.wt m a y v) :=
  Iff.rfl

/-- At a layers' segment the data list K4's two runs for its own item. -/
theorem runs_own {m : Nat} (hsub : h.𝔇.links[m]? = some ModelPart.layers) :
    h.𝔇.runs m 3 "own" = [(2, "front"), (2, "back")] := by
  show runsAt h.𝔇.links m 3 "own" = _
  rw [runsAt_of _ m _ hsub]
  rfl

/-- At a layers' segment the data list no run for the item on the planes. -/
theorem runs_planes {m : Nat} (hsub : h.𝔇.links[m]? = some ModelPart.layers) :
    h.𝔇.runs m 2 "planes" = [] := by
  show runsAt h.𝔇.links m 2 "planes" = _
  rw [runsAt_of _ m _ hsub]
  rfl

/-- At a layers' segment the data list no run for the item on the join. -/
theorem runs_join {m : Nat} (hsub : h.𝔇.links[m]? = some ModelPart.layers) :
    h.𝔇.runs m 2 "join" = [] := by
  show runsAt h.𝔇.links m 2 "join" = _
  rw [runsAt_of _ m _ hsub]
  rfl

/-- **`K4Table` at the library's own parameters.** CONDITIONAL: on h; the member number b stands at
piece 3 of the layers' segment m; l is the chain's link number m. -/
theorem k4Table_at {b m : Nat} {pl : Place} {l : Link TS ProofFile.Cl}
    (H : AtK4 P5J.At.links P5J.At.ps b m pl) (hl : h.𝔇.lk m = some l) :
    K4Table (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread b
      (Item.formsT m 3 "own") (Item.formsT m 2 "planes") (Item.formsT m 2 "join") (restK4 m)
      (holesK4 Zp m l) l h.𝔇.St (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) := by
  have hsub : h.𝔇.links[m]? = some ModelPart.layers := H.sub
  have e2 : h.𝔇.Rd m = readersOfLink (holesK4 Zp m l) l := readersAt_some h.𝔇.lk _ _ m l hl
  refine ⟨owes_k4 (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) H,
    fun w a y v hq => ?_, fun w a y v => ?_, fun w a y v => ?_⟩
  · refine (means_formsT_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps m 3 "own" w a
      y v).2 ⟨fun p hp => ?_, fun e => absurd e (by decide)⟩
    rw [runs_own h hsub] at hp
    rw [e2]
    exact hq p hp
  · refine (means_formsT_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps m 2 "planes"
      w a y v).2 ⟨fun p hp => ?_, fun e => absurd e (by decide)⟩
    rw [runs_planes h hsub] at hp
    cases hp
  · refine (means_formsT_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps m 2 "join" w
      a y v).2 ⟨fun p hp => ?_, fun e => absurd e (by decide)⟩
    rw [runs_join h hsub] at hp
    cases hp

/-- It says nothing new: it stands so that Lean holds the types of `k4Table_at`, `k4_own_share` and
`exchange_of_shares` together at the library's own parameters. -/
example {b m : Nat} {pl : Place} {l : Link TS ProofFile.Cl} (H : AtK4 P5J.At.links P5J.At.ps b m pl)
    (hl : h.𝔇.lk m = some l)
    {M : TS → Bound GQ → Road.Mats GQ} {tl : HTailF2} {p : Par}
    (hSit :
      K4Sits (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread b p)
    (hF : K4Front (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      (Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread b) b M
      (holesK4 Zp m l) l h.𝔇.St (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) tl p)
    (hV : K4Values (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      (Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread b) b M
      (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) tl p)
    (hR : ShareAt (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      (Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread b) b
      (restK4 m)) :
    Exchange (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread b :=
  exchange_of_shares
    (k4Table_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps H hl)
    (k4_own_share (k4Table_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps H hl)
      hSit hF hV) hR

/-- The like from the pair of the thread and a sentence on what earlier rounds have shown, and from
the worths group by group. It says nothing new. -/
example {b m : Nat} {pl : Place} {l : Link TS ProofFile.Cl} (H : AtK4 P5J.At.links P5J.At.ps b m pl)
    (hl : h.𝔇.lk m = some l)
    {M : TS → Bound GQ → Road.Mats GQ} {tl : HTailF2} {p : Par}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSit :
      K4Sits (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread b p)
    (hF : K4Front (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      (ThrS (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread Said b) b
      M (holesK4 Zp m l) l h.𝔇.St (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) tl p)
    (hW : K4Worths (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      (ThrS (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread Said b) b
      M (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) tl p)
    (hR : ShareAt (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      (ThrS (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread Said b) b
      (restK4 m)) :
    ExchangeS (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread Said
      b :=
  exchangeS_of_shares
    (k4Table_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps H hl) Said
    (k4_own_share_of_worths
      (k4Table_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps H hl) hSit hF hW) hR

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.owes_k4
#print axioms ProofFile.Honest.K4.means_formsT_at
#print axioms ProofFile.Honest.K4.runs_own
#print axioms ProofFile.Honest.K4.runs_planes
#print axioms ProofFile.Honest.K4.runs_join
#print axioms ProofFile.Honest.K4.k4Table_at
