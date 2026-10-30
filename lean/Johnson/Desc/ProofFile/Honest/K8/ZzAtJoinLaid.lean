-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ZzAtJoinLaid.lean: the honest side of the smallness test (K8): THAT
THE PAYERS FIT THE PREMISES OF `zz_at_join_head` (Johnson/Desc/ProofFile/Honest/K8/ZzAtJoin.lean),
HELD BY LEAN AND NOT BY EYE: the field zz of `K8TwoAt` at the head's letters, at the joined Script
over the list of jobs by their places' numbers, with hx, hJ, hbook, htl and hSt laid in. One
abbreviation; one theorem.

`K8TwoAt.zz` is exchanged here for hR, proved nowhere, for F and hc on the joined lists and the
book, for `K8Seated`, the opening, and for public premises. It is not paid. Behind a yes at which
the second stop is silent. An equation on the Script. NOT IN FRONT OF A LAW OVER COINS.
At the digits' message's first sending alone. Whoever quotes it at a book names hasCoins at
that book beside it: hc is asked here.

  `zzJob`         the job that sends the digits: the shared sending's second later job of segment l
                  at the lot's own data: an abbreviation, so that the statement can be read
  **`zz_at_join_laid`**   one call of `zz_at_join_head`, with: hx by `zz_job_in_list`
                  (Johnson/Desc/ProofFile/Honest/K8/ZzJobInList.lean) · hJ by unfolding · hbook by
                  `hbook_of_test` · htl by the built segment · hSt by `hSt_at_head`
                  (Johnson/Desc/ProofFile/Honest/K8/ZzStateAtHead.lean), with the job's plan by
                  `later_plan_head` (Johnson/Desc/ProofFile/Honest/K1/Law/LotJobsAtHead.lean)
The premises that stay, sorted. The head h, an opening of the description O₁ and the built segment
e3. On the joined lists: F. On the book: hc. On two readers of the hidden input: hR, not public. On
what is said: hOk. On the prover's list and the thread: hK. On public data: seventeen: ok, ha,
hname, hM, hans, hlen, hne, hmom, hB, hcs, hsI, hsC, hn, and haA, hansJ, hseat, hmz of `hSt_at_head`
(eighteen with l below 25).
One option is raised (maxHeartbeats) and one instance is taken away, as in the files beneath. No
tactic that searches. The sign 𝔇 is the name of a field of
the library's head, as the library writes it.
Limits. An implication. No letters are given at which the premises hold together. Counted nowhere.
The Limits of ZzAtJoin.lean and of ZzStateAtHead.lean are its own too. The field tie is not touched.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ZzAtJoin
import Johnson.Desc.ProofFile.Honest.K8.ZzStateAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Slice VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Params (ReqArray)
open OnBytes.Model (HTailF2)
open OnBytes.Model.Stages (LinkH)
open OnBytes.HonestTrace (pairOf seatsOf seatAt)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.K8 (cellsAhead)
open VerifiableInference.Desc.First.K8.Honest (allRows)
open ProofFile.Honest.FirstThread (Others joinQ JoinFit lettersHead WtF coinsB byNo)
open OnBytes.SendSim.Seat (wJobs)
open Johnson.Prover.Send (shapeAt)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5J (AtMgA CellsM TS)

/-- The job that sends segment l's digits. -/
abbrev zzJob {X : Type} (Zp : ProofFile.Pub) (G : Ground) (no : Place → Nat)
    (S₀ : OnBytes.HonestTrace.Sz) (l : ℕ) : K1.SendJob (K1.PlaceIn ProofFile.Inst) X :=
  K1.laterJobAt G.first (K1.gpOf Zp) l (IM.k1Ix l true + 1) 2
    (no ⟨1, some l, IM.k1Ix l true + 1, .K1⟩) (K1.lotData S₀ Zp G)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The field zz at the head's letters and the joined Script, with five premises laid in.**
Exchanged for hR, proved nowhere, F, hc, `K8Seated`, the opening and public premises. Behind a yes
at which the second stop is silent. At the digits' message's first sending alone. An equation on the
Script. NOT IN FRONT OF A LAW OVER COINS. Whoever quotes it at a book names hasCoins
at that book beside it. -/
theorem zz_at_join_laid {Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (S₀ : OnBytes.HonestTrace.Sz)
    (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst) (blk : Block S ProofFile.Cl) (cells : Tr → Cells)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : X)
    (O : Others Bk (Local W₀ Rc ProofFile.Inst Tr)) {seats : List (ℕ × ℕ)}
    (F : JoinFit cF.blocksInOrder 0 h.𝔇.arr seats wit own₀
      (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                 wJobs (X := X) no Dd Zp Bs.G₀)) O)
    (hc : coinsB Bk (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
               wJobs (X := X) no Dd Zp Bs.G₀)) = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    {matsK : List (Nat × String × Nat)}
    (hK : K8Seated (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp Bs.G₀ Xl l, matsK))
    {n : ℕ} (hn : n < (zzJob (X := X) Zp Bs.G₀ no S₀ l).P.sent.size) {nm : String} {a : ReqArray}
    (ok : reqLayoutOk Bs.G₀.first.codes Bs.G₀.first.shape Bs.G₀.first.layout = true)
    (ha : arrayOf Bs.G₀.first.layout l nm = some a) (hname : a.name = "ZZ")
    {M : Params.ReqMessage}
    (hM : Meaning.messageAt Bs.G₀.first.shape l a.message = some M) (hans : M.shape.answers ≠ 0)
    (hlen : Bs.G₀.first.codes.lengthsOk = true)
    (hne : (⟨(zzJob (X := X) Zp Bs.G₀ no S₀ l).P.place, 0⟩ : Addr) ≠ K1.firstAddr)
    (hmom : ∀ t, (seatAt (seatsOf Zp Bs.G₀ "BZ")
        ⟨⟨(zzJob (X := X) Zp Bs.G₀ no S₀ l).P.place, 0⟩, n⟩ = some t ∨
      seatAt (seatsOf Zp Bs.G₀ "U3")
        ⟨⟨(zzJob (X := X) Zp Bs.G₀ no S₀ l).P.place, 0⟩, n⟩ = some t) → K1.momentIs t 2 = true)
    (hB : bearsZz Bs.G₀.first.layout (pairOf (seatsOf Zp Bs.G₀ "BZ"))
      ⟨⟨(zzJob (X := X) Zp Bs.G₀ no S₀ l).P.place, 0⟩, n⟩ = some (l, a.message))
    (hcs : h.𝔇.cs = (zzJob (X := X) Zp Bs.G₀ no S₀ l).P.codes) (hsI : Xl.tl.tau ≤ a.sizeI)
    (hsC : 2 * allRows (parOfTail Xl.tl) ≤ a.sizeC)
    (hR : ∀ v, v = w ∧ Vd v → (wit v).R.cells = cells v.trace)
    (haA : ∀ bn, Xl.arrayOf[Xl.tl.ix.ZZ]? = some bn →
      reqArray Bs.G₀.first.layout l bn.2 = some a)
    (hansJ : (shapeAt (zzJob (X := X) Zp Bs.G₀ no S₀ l).P n).answers ≠ 0)
    (hseat : P5J.At.seat3At Zp l true a.message =
      K1.seatAtMember cF.blocksInOrder (14 * l + (if l = 24 then 5 else 4) + 2 + 1)
        (zzJob (X := X) Zp Bs.G₀ no S₀ l).P n)
    (hmz : Xl.tl.mz ≤ allRows (parOfTail Xl.tl)) :
    ∀ k s m E ds y cols s' tl' (d : Fmt.Drawn) e (z : ProofFile.InstPub),
      ThrS (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
          (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                     wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
          (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                     wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.Stepped blk k s m E ds y cols s' →
      (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
          (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                     wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.Form (14 * l + (if l = 24 then 5 else 4) + 2 + 1) k s' y.2 →
      s'.tl? = some tl' → tl'.cfF = d.trits.toArray →
      ZzBy tl'
        (cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s')
          ((lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
              (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                         wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp
            w).thread.wit k m.st.input (m.st.heard ++ d :: e)))
        (cellsAtOf (cells m.st.input.trace) (K3.matsOwn Bs.G₀.W l)) :=
  have hx := zz_job_in_list (X := X) h O₁ no S₀ Dd hl
  zz_at_join_head h H test carryX item n₁ n₂ b₀ Vd Rd Kp w Said blk cells cellsQ tokQ wit own₀ _ O F
    hl hx hn S₀ Bs.G₀ (K1.gpOf Zp) l (IM.k1Ix l true + 1)
    (no ⟨1, some l, IM.k1Ix l true + 1, .K1⟩) rfl (hbook_of_test hc hx) ok ha hname hM hans hlen hne
    hmom hB (tl₀ := Xl.tl)
    (show (Bs.G₀.built[l]?).map (·.tl) = some Xl.tl by rw [e3]; rfl) hcs hsI hsC hR
    (hSt_at_head h H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w hOk hl O₁ e3 hK
      (K1.later_plan_head Zp Bs.G₀ l true _ _) haA hn hansJ hseat hmz)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.zzJob
#print axioms ProofFile.Honest.K8.zz_at_join_laid
