-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AllJoined.lean: CONDITIONAL: ALL THE DEBTS OF THE MEMBER AT AN
ATTENTION SEGMENT's OWN ROUNDS (kind K5) IN ONE STATEMENT, WITH ALL THE LAWS JOINED THAT EACH STRIKE
A PREMISE OF `k5_owes_all_T` (Honest/K5/Law/RidesT.lean). It proves nothing new: it joins. That no
shorter list of premises can be had is not said.

WHAT IS JOINED, AND WHAT EACH STRIKES.
  the clause of T.keeps with "no mark behind" inside (`K5KeepsM`; Honest/K5/Law/KeepsMT.lean): Kp,
    Rd and `K5RidersT` give way to KpM, RdM and `K5RidersM`
  ans := `ansJT` (Honest/K5/Law/AtHeadLetters.lean): `AnsReadsRest` and `AnsOn` fall
  the identities from what the row asks (Honest/K5/Law/Idn12/AllMT2.lean): `IdnOwed` gives way to
    `HoldsOwed`
  the ties on the witness from equations on the Script alone (`k5Script_of_Q_T`,
    Honest/K5/Law/ScriptQAt.lean): `K5Script` gives way to `K5ScriptQ`, `LedgerIs`, the count of the
    row's coins and the text on the key points
  that count from "the lending returns" (`coinsFew_of_lent`, Honest/K5/Law/CoinsFewOf.lean)
  of the text on the key points its first clause ("the lookup on the calls has laid what it heard"):
    `Thr` T in front gives it (`readyO_T`, Honest/K5/Law/DebtsT.lean)

  `keyTie_of`             the text on the key points with its first clause, from the text without it
  `k5_owes_all_joined_T`    CONDITIONAL, T A VARIABLE: **`Plays`, `Behind`, `Exchange`, `RidesPast`
                          and, for every fall, `Accepted`** at the kind's border
  `k5_owes_all_joined_head` CONDITIONAL: the same at the first chain's letters as they are laid, b₀
                          at `replyBorder`
  `k5_owes_all_joined_kind` CONDITIONAL: the same at Kp := `kpBy` f (Honest/Thread/KeepsBy.lean)
                          with `K5KeepsAt` at K5

THE PREMISES OF `k5_owes_all_joined_T`, ALL OF THEM. h: the hypothesis `P5J.AtMgA` · A: `K5AtT` at
`ansJT` · R: `K5RidersM` at `ansJT` and the plan's numbers · hg: g below 12 · ha: the group's plan ·
hx: the place of the segment's lookup on the calls · Hs: `K5Seated` · hfit, hb: the test T.fits ·
KpM, RdM: T.keeps and T.rides over the clause · hw: T's witness, read by wt, is the Script's · hc:
T's chain has the number 0 · hv: T's valid inputs meet Vd · hN: N is at most the number of
challenges heard at the border · HQ: `K5ScriptQ`: TWO EQUATIONS ON THE SCRIPT: SHOWN NOWHERE · hL5:
`LedgerIs`: NOT SHOWN HERE (at `lettersHead`: Honest/K5/Law/AllJoined2.lean strikes it) · hl:
`Lends5`: the lending to the row returns at all coins · hK: the text on the key points: NOT SHOWN
HERE (at `lettersHead`: AllJoined3.lean trades it for H3, which AllJoined5.lean has paid under h and
g < 12) · hP · hH: `HoldsOwed`: SHOWN OF NO `valid`.

THREE LETTERS ARE CALLED CELLS, AND THEY ARE THREE. cq: the cells that the honest side's letters lay
for an input: it enters through what A and R say of T.means, and through hH, and is spent as the
guard of one asked item alone. Q: the Script: it enters through hw and HQ, which read its witness's
messages and never its cells. cells: this kind's reader of the trace: in Hs, HQ and hl. With T a
variable no equation ties cq to Q, and none is spent; at `lettersHead` cq is the Script's cells.

THE PREMISES OF `k5_owes_all_joined_head`, ALL OF THEM. h · hg · hG, hKey, hKs, hL: the four under
which `K5Seated` holds at that `Thread` (Honest/K5/Law/Whole.lean) · hfit, hb · hKpM: the letter Kp
at the kind's place is `K5KeepsM` at the group's plan's numbers · hRdM: the letter Rd's part goes on
along the clause · hr: `ready` returns once: SHOWN NOWHERE · hN · HQ · hL5 · hK · hH: where the
run's own input meets Vd, the cells that the Script lays for it hold an index. Kp and b₀ are letters
of `lettersHead`: that they are or will be laid so is said by nobody.

THE FORMS WITH hLent. Of hr (one return of the frame's `ready`, a routine over the whole prover, the
whole book and all three chains) the laws here spend one thing alone: hLent: the book's lending to
the kind's own row returns, at all coins: `Lends5` (Honest/K5/Law/CoinsFewOf.lean) at what the maker
of the place's public data yields. It names no input, no trace, no other kind's half and no other
chain; of the book it reads the first chain's rows and the entries. `k5_owes_all_joined_head_lent`
and `k5_owes_all_joined_kind_lent` take hLent in hr's stead. `k5_lent_of_ready`: hr, with hg, hG,
hKey, hKs and hL, gives hLent (by `k5_lent_head`, Honest/K5/Law/Lent.lean). The forms with hr keep
their names and statements and follow from these. hLent is shown nowhere either.

Limits. Conditional. TWO LIMITS STAND AS IN THE FILES THAT ARE JOINED, AND A WORD ON WHERE THE
STATEMENT IS MET FOR NOTHING. On ans: its premises fall because `ansJT` reads no oracle and of the
state the statement alone; what a pin is worth there is said in Honest/Thread/Ans.lean's own Limits:
the weight has moved, not gone. On the identities: they now come from three items that `Thr` T holds
in front of the member, of T's own witness: whoever shows that a run meets `Thr` T there owes them:
the weight has moved, not gone. Met for nothing: where no input is valid (so at a Vd that nothing
meets: there `K5ScriptQ` holds of every Script, and by hv no input is valid); and at a list ms in
which no member sits at the tenant of a pin that is open at the border. At `lettersHead` ms is the
list that it lays: that a member sits at each such tenant there is not shown here. One member of the
chain. At the library's full size and the format's second hash function alone. The laws that are joined
stand beside this one.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Idn12.AllMT2
import Johnson.Desc.ProofFile.Honest.K5.Law.CoinsFewOf
import Johnson.Desc.ProofFile.Honest.K5.Law.Lent
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P (K3Pts slotsOf script)
open VerifiableInference.Desc.Sound (seatTab Mem MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt k5KeepsAt_iff)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open P5J (AtMgA TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : VerifiableInference.Desc.First.Item → T.ι} {pb : T.P → ProofFile.InstPub}
  {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (A : K5AtT h T g it pb wt ans test carryX cq)
include A

/-- **The text on the key points with its first clause, from the text without it.** T IS A VARIABLE.
CONDITIONAL: under the hypothesis h and `K5AtT`; g below 12; hK. `Thr` T in front says that the
lookup on the calls has laid what it heard. -/
theorem keyTie_of (hg : g < 12) {a : Attention.Plan} {Z5 : Seat5} {blk : Block TS ProofFile.Cl}
    (hK : ∀ k s m E, Thr T (borderOf g) k s m E → ∀ att g', s.here = .att att →
      att.g = some g' →
      K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
        ∀ ds n, drawsFit blk.rounds ds = true → Z5.keyAt (m.st.heard ++ ds.take n) = g'.zk)
    (k : Coins Bk) (s : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env)
    (hT : Thr T (borderOf g) k s m E) (att : VerifiableInference.Desc.First.AttOwn)
    (e : s.here = .att att) :
    ∃ g', att.g = some g' ∧
      K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
      ∀ ds n, drawsFit blk.rounds ds = true → Z5.keyAt (m.st.heard ++ ds.take n) = g'.zk := by
  obtain ⟨-, a', -, Pl, -⟩ := k5_member h hg
  obtain ⟨att', gL, e', hgL, -⟩ := (readyO_T h A hg Pl hT).open_
  rw [e] at e'
  cases e'
  exact ⟨gL, hgL, hK k s m E hT att gL e hgL⟩

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : VerifiableInference.Desc.First.Item → T.ι} {pb : T.P → ProofFile.InstPub}
  {wt : T.Wt → WtF} {ms : List Mem}
  {test : Nat → TS → Option String} {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (A : K5AtT h T g it pb wt
    (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) ms) test carryX cq)
include A

/-- **ALL OF THE MEMBER's DEBTS IN ONE STATEMENT, WITH ALL THE LAWS JOINED THAT STRIKE A PREMISE.**
T IS A VARIABLE. CONDITIONAL: every premise stands, by name, in the file's head, with the limits. HQ
and hH are shown nowhere. hL5 and hK are not shown here: at `lettersHead`
Honest/K5/Law/AllJoined2.lean strikes hL5, AllJoined3.lean trades hK for a premise H3, and
AllJoined5.lean has H3 paid under h and g < 12. -/
theorem k5_owes_all_joined_T {a : Attention.Plan}
    (R : K5RidersM h T g it pb wt
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) ms) test carryX cq a.own)
    {n : Nat} (hg : g < 12) (ha : (P5J.At.X Zp).A[g]? = some a)
    {x₁ : VerifiableInference.Desc.First.Look.Place}
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (KpM : ∀ s s', K5KeepsM a.own s s' → T.keeps (borderOf g) s s')
    (RdM : ∀ w s s', T.rides (borderOf g) w s → K5KeepsM a.own s s' →
      T.rides (borderOf g + 1) w s')
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    {Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop} {N ν₅ : Nat}
    (hw : ∀ k v hd, wt (T.wit k v hd) = Q.wit k v hd) (hc : T.chain = 0)
    (hv : ∀ v, T.valid v → Vd v) (hN : N ≤ T.front + roundsTo T.bs (borderOf g))
    (HQ : K5ScriptQ h Q Vd N x₁ a cells Z5 ν₅) (hL5 : LedgerIs T (borderOf g) ν₅)
    (hl : Lends5 W₀ Rc ProofFile.Inst X Bk cells Z5)
    (hK : ∀ k s m E, Thr T (borderOf g) k s m E → ∀ att g', s.here = .att att →
      att.g = some g' →
      K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
        ∀ ds n, drawsFit blk.rounds ds = true → Z5.keyAt (m.st.heard ++ ds.take n) = g'.zk)
    (hP : Z5.P = ⟨a.S, a.own⟩) (hH : HoldsOwed T.valid cq) :
    (Plays T (borderOf g) ∧ Behind T (borderOf g) ∧ Exchange T (borderOf g) ∧
      RidesPast T (borderOf g)) ∧ ∀ fall, Accepted T fall (borderOf g) := by
  have hfew : CoinsFew Bk Z5 (slotsOf (script a.own)) := by
    have e := coinsFew_of_lent hl
    rw [hP] at e
    exact e
  exact k5_owes_all_M_T₂ h A R hg ha Hs hfit hb KpM RdM (ansReadsRest_JT Zp ms _)
    (ansOn_JT Zp ms _ _)
    (k5Script_of_Q_T h A hg (decides_T h A hg ha Hs.member).1 hx hw hc hv hN HQ hL5 hfew
      (keyTie_of h A hg hK)) hP hH

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop)
  (RdL : Nat → (Local W₀ Rc ProofFile.Inst Tr) → TS → Prop) (KpL : Place → TS → TS → Prop)
  (w : (Local W₀ Rc ProofFile.Inst Tr))

include h Q test carryX item n₁ n₂ Vd RdL KpL w in
/-- **ONE RETURN OF `ready` GIVES hLent**: the book's lending to the kind's own row returns, at all
coins, at what the maker of the place's public data yields. CONDITIONAL: g is below 12; hG, hKey,
hKs, hL as in `k5_owes_all_joined_head`; hr. By `k5_seated_keys` and `k5_lent_head`
(Honest/K5/Law/Lent.lean). The letters Q to w stand in the proof alone. -/
theorem k5_lent_of_ready {g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hKey : ∀ a, (P5J.At.X Zp).A[g]? = some a → (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true)
    (hKs : ∀ a, (P5J.At.X Zp).A[g]? = some a → KeySizes (seatOf keyOf Zp G cF g a))
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOf Zp G) cells G)
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {c : Coins Bk} {R₀ : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (hr : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ c = .ok R₀) :
    ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ Rc ProofFile.Inst X Bk cells (seatOf keyOf Zp G cF g a) := by
  intro a ha k
  obtain ⟨blk, a', ha', Hs⟩ := k5_seated_keys h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (replyBorder ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s')
    hg hG hKey hKs hL
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  exact k5_lent_head h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w hr Hs k

/-- **THE SAME AT THE FIRST CHAIN's LETTERS AS THEY ARE LAID** (`lettersHead`,
Honest/Thread/FirstHead.lean), WITH b₀ AT THE BORDER BEHIND THE MEMBER THAT HEARS THE REPLY.
CONDITIONAL: every premise stands, by name, in the file's head. What unfolds at these letters has
fallen: A, R, hw, hc, hv, hP; KpM comes down to hKpM, on the letter Kp at the kind's place; hl falls
for one return of `ready`.
HERE WITH hLent (the book's lending to the kind's own row returns, at all coins) IN THE STEAD OF hr
(one return of `ready`), which gives it. -/
theorem k5_owes_all_joined_head_lent {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hKey : ∀ a, (P5J.At.X Zp).A[g]? = some a → (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true)
    (hKs : ∀ a, (P5J.At.X Zp).A[g]? = some a → KeySizes (seatOf keyOf Zp G cF g a))
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOf Zp G) cells G)
    (hfit : (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread.fits n =
      true)
    (hb : borderOf g < n)
    (hKpM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ s s',
      KpL ⟨1, some (2 * g + 1), 3, .K5⟩ s s' ↔ K5KeepsM a.own s s')
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ Rc ProofFile.Inst X Bk cells (seatOf keyOf Zp G cF g a)) {N ν₅ : Nat}
    (hN : N ≤ (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread.front +
      roundsTo cF.blocksInOrder (borderOf g))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd N x₁ a cells (seatOf keyOf Zp G cF g a) ν₅)
    (hL5 : LedgerIs (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
      (borderOf g) ν₅)
    (hK : ∀ a blk, (P5J.At.X Zp).A[g]? = some a → cF.blocksInOrder[borderOf g]? = some blk →
      ∀ k s m E,
        Thr (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
          (borderOf g) k s m E →
        ∀ att g', s.here = .att att → att.g = some g' →
        K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
          ∀ ds n, drawsFit blk.rounds ds = true →
            (seatOf keyOf Zp G cF g a).keyAt (m.st.heard ++ ds.take n) = g'.zk)
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
        (borderOf g) ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
        (borderOf g) ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
        fall (borderOf g) := by
  obtain ⟨blk, a, ha, Hs⟩ := k5_seated_keys h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (replyBorder ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s')
    hg hG hKey hKs hL
  obtain ⟨x₁, hx⟩ := (seated_decides h hg ha Hs.member).1.look
  exact k5_owes_all_joined_T h
    (k5AtT_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (replyBorder ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s') hg)
    (k5RidersM_thrAt h H.first Q (fun v => H.storedWords v.w₀ v.rc)
      (ansJT (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay))
      test carryX item n₁ n₂ (fun v => v = w ∧ Vd v)
      (fun b v s => (replyBorder ≤ b → s.out.reply = some v.x.asked) ∧ RdL b v s)
      (fun b s s' => ∀ p, P5J.At.ps[b]? = some p → KpL p s s') hg
      fun s s' k => (hKpM a ha s s').1
        ((keeps_head h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w hg s s').1 k))
    hg ha hx Hs hfit hb
    (fun s s' k => (keeps_head h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w hg s s').2
      ((hKpM a ha s s').2 k))
    (rides_head_M h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w
      (Nat.ne_of_gt (reply_behind hg)) (hRdM a ha))
    (fun _ _ _ => rfl) rfl (fun _ hv => hv.2) hN (HQ a x₁ ha hx) hL5
    (hLent a ha)
    (hK a blk ha Hs.member) rfl (holdsOwed_head Vd w hH)

/-- **THE SAME AT THE FIRST CHAIN's LETTERS AS THEY ARE LAID** (`lettersHead`,
Honest/Thread/FirstHead.lean), WITH b₀ AT THE BORDER BEHIND THE MEMBER THAT HEARS THE REPLY.
CONDITIONAL: every premise stands, by name, in the file's head. What unfolds at these letters has
fallen: A, R, hw, hc, hv, hP; KpM comes down to hKpM, on the letter Kp at the kind's place; hl falls
for one return of `ready`.
By `k5_owes_all_joined_head_lent`: one return of `ready` gives hLent. -/
theorem k5_owes_all_joined_head {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hKey : ∀ a, (P5J.At.X Zp).A[g]? = some a → (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true)
    (hKs : ∀ a, (P5J.At.X Zp).A[g]? = some a → KeySizes (seatOf keyOf Zp G cF g a))
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOf Zp G) cells G)
    (hfit : (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread.fits n =
      true)
    (hb : borderOf g < n)
    (hKpM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ s s',
      KpL ⟨1, some (2 * g + 1), 3, .K5⟩ s s' ↔ K5KeepsM a.own s s')
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {c : Coins Bk} {R₀ : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (hr : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ c = .ok R₀) {N ν₅ : Nat}
    (hN : N ≤ (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread.front +
      roundsTo cF.blocksInOrder (borderOf g))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd N x₁ a cells (seatOf keyOf Zp G cF g a) ν₅)
    (hL5 : LedgerIs (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
      (borderOf g) ν₅)
    (hK : ∀ a blk, (P5J.At.X Zp).A[g]? = some a → cF.blocksInOrder[borderOf g]? = some blk →
      ∀ k s m E,
        Thr (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
          (borderOf g) k s m E →
        ∀ att g', s.here = .att att → att.g = some g' →
        K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
          ∀ ds n, drawsFit blk.rounds ds = true →
            (seatOf keyOf Zp G cF g a).keyAt (m.st.heard ++ ds.take n) = g'.zk)
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
        (borderOf g) ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
        (borderOf g) ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL KpL w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_head_lent h H Q test carryX item n₁ n₂ Vd RdL KpL w hg hG hKey hKs hL hfit hb
    hKpM hRdM (k5_lent_of_ready h H Q test carryX item n₁ n₂ Vd RdL KpL w hg hG hKey hKs hL hr) hN
    HQ hL5 hK hH

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop)
  (RdL : Nat → (Local W₀ Rc ProofFile.Inst Tr) → TS → Prop) (f : KindName → Place → TS → TS → Prop)
  (w : (Local W₀ Rc ProofFile.Inst Tr))

/-- **THE SAME WITH THE LETTER Kp LAID BY THE PLACE's KIND** (`kpBy` f), f AT THE KIND K5 THE
CLAUSE BY THE PLACE (`K5KeepsAt` at the public input). CONDITIONAL: the premises of
`k5_owes_all_joined_head`, with hf in hKpM's stead. hf asks more than is spent: an equation at all
places, where hKpM speaks of one.
HERE WITH hLent (the book's lending to the kind's own row returns, at all coins) IN THE STEAD OF hr
(one return of `ready`), which gives it. -/
theorem k5_owes_all_joined_kind_lent {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hKey : ∀ a, (P5J.At.X Zp).A[g]? = some a → (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true)
    (hKs : ∀ a, (P5J.At.X Zp).A[g]? = some a → KeySizes (seatOf keyOf Zp G cF g a))
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOf Zp G) cells G)
    (hfit :
      (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread.fits n =
        true)
    (hb : borderOf g < n)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ Rc ProofFile.Inst X Bk cells (seatOf keyOf Zp G cF g a)) {N ν₅ : Nat}
    (hN : N ≤
      (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread.front +
        roundsTo cF.blocksInOrder (borderOf g))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd N x₁ a cells (seatOf keyOf Zp G cF g a) ν₅)
    (hL5 : LedgerIs
      (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
      (borderOf g) ν₅)
    (hK : ∀ a blk, (P5J.At.X Zp).A[g]? = some a → cF.blocksInOrder[borderOf g]? = some blk →
      ∀ k s m E,
        Thr (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
          (borderOf g) k s m E →
        ∀ att g', s.here = .att att → att.g = some g' →
        K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
          ∀ ds n, drawsFit blk.rounds ds = true →
            (seatOf keyOf Zp G cF g a).keyAt (m.st.heard ++ ds.take n) = g'.zk)
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted
        (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_head_lent h H Q test carryX item n₁ n₂ Vd RdL (kpBy f) w hg hG hKey hKs hL hfit
    hb
    (fun a ha s s' => (kpBy_at f rfl s s').trans (by
      rw [hf]
      exact k5KeepsAt_iff ha s s'))
    hRdM hLent hN HQ hL5 hK hH

/-- **THE SAME WITH THE LETTER Kp LAID BY THE PLACE's KIND** (`kpBy` f), f AT THE KIND K5 THE
CLAUSE BY THE PLACE (`K5KeepsAt` at the public input). CONDITIONAL: the premises of
`k5_owes_all_joined_head`, with hf in hKpM's stead. hf asks more than is spent: an equation at all
places, where hKpM speaks of one.
By `k5_owes_all_joined_kind_lent`: one return of `ready` gives hLent. -/
theorem k5_owes_all_joined_kind {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hKey : ∀ a, (P5J.At.X Zp).A[g]? = some a → (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true)
    (hKs : ∀ a, (P5J.At.X Zp).A[g]? = some a → KeySizes (seatOf keyOf Zp G cF g a))
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOf Zp G) cells G)
    (hfit :
      (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread.fits n =
        true)
    (hb : borderOf g < n)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {c : Coins Bk} {R₀ : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (hr : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ c = .ok R₀) {N ν₅ : Nat}
    (hN : N ≤
      (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread.front +
        roundsTo cF.blocksInOrder (borderOf g))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd N x₁ a cells (seatOf keyOf Zp G cF g a) ν₅)
    (hL5 : LedgerIs
      (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
      (borderOf g) ν₅)
    (hK : ∀ a blk, (P5J.At.X Zp).A[g]? = some a → cF.blocksInOrder[borderOf g]? = some blk →
      ∀ k s m E,
        Thr (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
          (borderOf g) k s m E →
        ∀ att g', s.here = .att att → att.g = some g' →
        K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
          ∀ ds n, drawsFit blk.rounds ds = true →
            (seatOf keyOf Zp G cF g a).keyAt (m.st.heard ++ ds.take n) = g'.zk)
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted
        (lettersHead h H Q test carryX item n₁ n₂ replyBorder Vd RdL (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_kind_lent h H Q test carryX item n₁ n₂ Vd RdL f w hg hG hKey hKs hL hfit hb hf
    hRdM (k5_lent_of_ready h H Q test carryX item n₁ n₂ Vd RdL (kpBy f) w hg hG hKey hKs hL hr) hN
    HQ hL5 hK hH

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.keyTie_of
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_T
#print axioms ProofFile.Honest.K5.k5_lent_of_ready
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_head_lent
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_head
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_kind_lent
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_kind
