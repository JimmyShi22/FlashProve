-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/MsgFirstAtJoin.lean: the honest side of the smallness test (K8): AT
THE JOINED SCRIPT (`joinQ`, Johnson/Desc/ProofFile/Honest/Thread/Join.lean) OVER A FIT LIST OF JOBS
THAT HOLDS THE FIRST SEGMENT's OPENING, AT THE LOT's OWN DATA: THE WITNESS's MESSAGE OF THE NUMBER
OF THE OPENING's MESSAGE n HOLDS, AT THE ROW AND PLACE AT WHICH THE LAYOUT LAYS AN ELEMENT OF AN
ARRAY "M mu" THAT LIES IN IT, THE PACKED CELLS OF THE READER's CELLS; AND THAT PLACE IS NO PLACE OF
A PAD. "The owner form" at segment 0. Two statements with their proofs; no definition. NO THREAD, NO
STEP, NO STATE OF A VERIFIER.

IT NAMES THE SCRIPT's WITNESS AND, THROUGH THE LETTER wit, WHAT A READER YIELDS OF THE INPUT: AN
EQUATION ON THE SCRIPT: DATA AGAINST DATA. The run's coins k stand on the left, inside the witness;
on the right: none. No measure; no stop. NOT IN FRONT OF A LAW OVER COINS. hcoins
(`coinsB`) is asked: whoever quotes it at a book names hasCoins at that book beside it.

  `first_job_in_list`   under the library's head and an opening: the opening's job, at the lot's own
                    data, stands with the number 2 in the list of jobs by their places' numbers
                    (`byNo`) over the two lists of jobs: by `members_by_border`
                    (Johnson/Desc/ProofFile/Honest/K1/Law/MembersByBorder.lean, of other authors).
                    Places, numbers and the prover's text alone
  **`msg_first_at_join`** from F (`JoinFit`), hcoins, hx (the job is in the list), hJ (it is the
                    opening's at the lot's data), hn (n is one of the job's messages), a valid
                    input, a list of challenges no shorter than the rounds in front of the member,
                    and the public premises of `msg_is_packed`
                    (Johnson/Desc/ProofFile/Honest/K8/TabIsPacked.lean)
The tie: `join_tie_k1_fit` (Johnson/Desc/ProofFile/Honest/Thread/JoinFit.lean, of other authors).
The cut: `lentCut_isSome` at `hbook_of_test` (Johnson/Desc/ProofFile/Honest/K8/ZzAtJoin.lean).
No option is raised; one instance is taken away, as in the files beneath. No tactic that searches.
Limits. Implications. None of the public premises is shown here. THE EQUATION COMES OF HOW THE
JOINED SCRIPT IS BUILT: at the opening it is built of a lot whose data are these packed cells of the
reader's answers: what is proved is that the witness agrees with the lots' own text, whichever
reader is taken; nothing here rests on a run. NOT SAID: that an honest prover's Script is the joined
one; that the letter wit reads the trace of the model; anything of another sender's messages. At the
message's first sending alone. The number is the plan's number of the member's seat
(`seatAtMember`): that it is the number under which the table of joints reads the message is not
said here. It stands over files of other houses that are not in the seal (Thread/Join.lean,
Thread/JoinFit.lean, K1/Law/MembersByBorder.lean and K1/Law/FirstIsPacked.lean among them).
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.TabIsPacked
import Johnson.Desc.ProofFile.Honest.K8.ZzAtJoin
import Johnson.Desc.ProofFile.Honest.K1.Law.MembersByBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Slice VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Params (ReqArray)
open OnBytes.HonestTrace (packedCells)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest.FirstThread (Others joinQ JoinFit join_tie_k1_fit coinsB byNo)
open OnBytes.SendSim.Seat (wJobs)
open Johnson.Prover.Send (shapeAt)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5J (AtMgA TS)

/-- The opening's job, at the lot's own data, stands with the number 2 in the list. -/
theorem first_job_in_list {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    {X : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (S₀ : OnBytes.HonestTrace.Sz)
    (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst) :
    (2, K1.placeJob (X := X) (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (no ⟨1, some 0, 1, .K1⟩)
        (K1.firstFold Bs.G₀.first) (K1.lotData S₀ Zp Bs.G₀)) ∈
      byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                 wJobs (X := X) no Dd Zp Bs.G₀) := by
  unfold byNo
  rw [K1.members_by_border h O₁ no (K1.lotData S₀) Dd]
  exact K1.mem_k1MembersW.2 (Or.inl (K1.mem_k1Members.2 (Or.inl rfl)))

/-- **The owner form at segment 0, at the joined Script.** An equation on the Script; no coin on its
right. NOT IN FRONT OF A LAW OVER COINS. Whoever quotes it at a book names hasCoins
at that book beside it. -/
theorem msg_first_at_join {Bk : ProverCoinCounts} {Cl Wl Cw Tok X : Type} (bs : List (Block S Cl))
    (cellsQ : Wl → Cw) (tokQ : Wl → Tok) (arr : ℕ → ℕ → ℕ) (wit : Wl → K1.PlaceIn ProofFile.Inst)
    (own₀ : X) (jobs : List (ℕ × K1.SendJob (K1.PlaceIn ProofFile.Inst) X)) (O : Others Bk Wl)
    {seats : List (ℕ × ℕ)} (F : JoinFit bs 0 arr seats wit own₀ jobs O)
    (hcoins : coinsB Bk jobs = true) {no : ℕ} {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) X}
    (hx : (no, J) ∈ jobs) (S₀ : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground)
    (gp : _root_.Desc.Plain.GPar) (first : ℕ)
    (hJ : J = K1.placeJob (X := X) (K1.firstPar G.first gp) first (K1.firstFold G.first)
      (K1.lotData S₀ Z G))
    {n : ℕ} (hn : n < J.P.sent.size) (Vd : Wl → Prop) (k : Coins Bk) (w : Wl) (hw : Vd w)
    (hd : List Fmt.Drawn) (hN : 0 + roundsTo bs no ≤ hd.length)
    (hlen : G.first.codes.lengthsOk = true) {a : ReqArray}
    (t1 : K1.firstSeat G.first.shape 0 ⟨K1.firstAddr, n⟩ = some (0, a.message))
    (hfit : msgFits G.first.codes G.first.shape G.first.layout 0 a.message = true)
    (ha : a ∈ (G.first.layout.link.getD 0 []).filter fun y => y.message == a.message) {i cc : ℕ}
    {rp : ℕ × ℕ} (hrp : laidAt a i cc = some rp) {mu : ℕ} (hmu : K1.labelNo a.name = some mu)
    {z : ℕ × ℕ} (hz : (K1.cellsVals S₀).size 0 a.name = some z) (hi : i < z.1 ∧ cc < z.2) :
    ((joinQ bs 0 cellsQ tokQ arr wit own₀ jobs O).wit k w hd).msg
          (arr (K1.seatAtMember bs no J.P n).1 (K1.seatAtMember bs no J.P n).2) false rp.1 rp.2 =
        algebraMap GF GE (packedCells S₀ (wit w).R.cells.cell 0 mu i cc) ∧
      padB J.P.codes (shapeAt J.P n) false rp.1 rp.2 = false := by
  have hm := (join_tie_k1_fit F cellsQ tokQ Vd hx).1 n hn
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1
    ((K1.lentCut_isSome k 0 (Nat.zero_le 1) _ _).trans (hbook_of_test hcoins hx))
  exact msg_is_packed _ Vd _ 0 wit S₀ Z G gp first hJ own₀ _ n _ _ hm (fun _ _ _ _ hv => hv) k c hc
    w hw hd hN hlen t1 hfit ha hrp hmu hz hi

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.first_job_in_list
#print axioms ProofFile.Honest.K8.msg_first_at_join
