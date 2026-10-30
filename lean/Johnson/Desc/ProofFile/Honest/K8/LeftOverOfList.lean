-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/LeftOverOfList.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE,
AT THE STANDS OF THE HONEST THREAD: OF THE NAMED PREMISE `LeftNameAtStand`
(Johnson/Desc/ProofFile/Honest/K8/LeftOverOfName.lean) FOUR OF ITS FIVE CLAUSES ARE PAID AT EVERY
STAND, AT THE 24 SEGMENTS IN FRONT OF THE HEAD's, WHERE `ChainThread` HOLDS: THE STATE SHOWS THE
TEST's DATA · A LEDGER · THE TABLES' ROUTINES · THE DIGITS' ARRAY BEARS THE NAME "ZZ". WHAT STAYS IS
ONE CLAUSE, `LeftListAtStand`. One definition, one lemma, two implications; none of the library's
goals.

  `funs_shown_at_batch` the scope · the files read · an opening of the description · l < 24 · a
                   state reached at 14 l + 9 ⊢ there are funs with s.funs? = some funs
  `LeftListAtStand Lk p T b` the named premise that stays: at every stand the link's list has a
                   member for each array of whatever ledger the state in front holds open
                   (a0.L.list.nt.size = F.trees.size)
  **`leftNameAtStand_of_list`** the scope · the files read · the opening · the description's test on
                   its plan · l < 24 · the built segment · ChainThread T b c Z l · LeftListAtStand ⊢
                   LeftNameAtStand
  **`leftOverAtStand_of_list`** so: LeftOverAtStand (the premise of the three sentences of
                   ValuesJoin.lean)
By: `zzName_at_batch` (Johnson/Desc/K8/Honest/NamesAtBatch.lean) · `drawn_at_batch`
(Johnson/P1K8R/DrawAtBatch.lean) · `sized_at_batch` (HeardAtBatch.lean) · the library's
LinkJoin.funsSkel_at_batch (Johnson/Desc/First/Link/Law/FunsAtBatch.lean: the layers' segments) and
LinkJoin.attSkel_at_batch (AttSkelAtBatch.lean: the attention segments) · `reach_below`
(Johnson/Desc/ProofFile/Honest/Thread/SaidOk.lean), called at its statement · the library's
`reach_raw` · `leftOverAtStand_of_name`.
WRITTEN A FURTHER TIME: the four lines from a stand to a reached state are those of
`leftBelowAtStand_of_name`.
`by omega` STANDS IN IT SEVEN TIMES, on numbers of segments and borders alone; two of them inside a
rewrite (`if_neg (by omega)`).
IN SIGHT FOR THE CLAUSE THAT STAYS, NOT JOINED: each built segment's planned ledger has as many
arrays as its list has entries (`built_trees`, Johnson/P5T/NamesAtMg.lean) · the open ledger has as
many arrays as the planned one (`arrayNames_at_batch`) · that the open link's list is the plan's is
a test of the frame (`SamePlan`, Johnson/Top/H0/Walk/FrameProps.lean): a law that hands it on to the
state in front of the batching was not sought to the end.
Limits. IMPLICATIONS STILL: `LeftListAtStand` AND `ChainThread` ARE PAID BY NOBODY. NO MEMBER: where
there is no stand all is idle. NOTHING AT THE HEAD's SEGMENT. IN SCOPE ALONE. No prover stands in
it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.LeftOverOfName
import Johnson.Desc.K8.Honest.NamesAtBatch
import Johnson.Desc.First.Link.Law.FunsAtBatch
import Johnson.Desc.First.Link.Law.AttSkelAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K9 (BatStand)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- At a state reached in front of the batching of a segment l < 24 the tables' routines are
shown: the library's two laws, at the layers' and at the attention segments, joined. -/
theorem funs_shown_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 24)
    {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s)) :
    ∃ funs : Array HFun, s.funs? = some funs := by
  rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
  · have e : 14 * (2 * g) + 9 = 28 * g + 9 := by omega
    rw [e] at h
    obtain ⟨funs, hf, -⟩ := LinkJoin.funsSkel_at_batch hS hR O (g := g) (by omega) h
    exact ⟨funs, hf⟩
  · obtain ⟨-, funs, -, hf, -⟩ := LinkJoin.attSkel_at_batch hS hR O (g := g) (by omega) h
    exact ⟨funs, hf⟩

variable {Lk : Link S Claim} {p : Desc.K9.Where}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}

variable (Lk p T b) in
/-- **The named premise that stays**: at every stand the link's list has a member for each array
of whatever ledger the state in front holds open. -/
def LeftListAtStand : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    ∀ F a0, s.fork? = some F → Desc.K9.atS.get? s = some a0 →
      a0.L.list.nt.size = F.trees.size

/-- **The test's data, the ledger, the tables' routines and the name are paid at every stand.** -/
theorem leftNameAtStand_of_list (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (C : ChainThread T b c Z l) (hL : LeftListAtStand Lk p T b) : LeftNameAtStand Lk p T b := by
  intro κ s m En ds y cols s' x z G hSt
  obtain ⟨q, hq⟩ := C.begun κ m
  have r := reach_below T (ProofFile.startS Z) q C.len hq C.stored hSt.thr
  rw [C.ft, C.bs, C.border, if_neg (by omega)] at r
  have r' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (q, s) := by
    rw [if_neg (by omega)]
    exact reach_raw r
  obtain ⟨tl, ht, -, -⟩ := _root_.P1K8.drawn_at_batch hS hR O (by omega : l < 25) r'
  obtain ⟨Fk, hF, -⟩ := _root_.P1K8.sized_at_batch hS hR O hOk hl (reach_raw r)
  obtain ⟨funs, hf⟩ := funs_shown_at_batch hS hR O hl (reach_raw r)
  exact ⟨tl, Fk, funs, ht, hF, hf, fun _ _ => zzName_at_batch hS hR O (by omega) e3 r' ht hF,
    fun a0 h0 => hL κ s m En ds y cols s' x z G hSt Fk a0 hF h0⟩

/-- **And so the premise of the three sentences.** -/
theorem leftOverAtStand_of_list (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (C : ChainThread T b c Z l) (hL : LeftListAtStand Lk p T b) : LeftOverAtStand Lk p T b :=
  leftOverAtStand_of_name hS hR O hOk hl e3 C (leftNameAtStand_of_list hS hR O hOk hl e3 C hL)

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.funs_shown_at_batch
#print axioms ProofFile.Honest.K8.leftNameAtStand_of_list
#print axioms ProofFile.Honest.K8.leftOverAtStand_of_list
