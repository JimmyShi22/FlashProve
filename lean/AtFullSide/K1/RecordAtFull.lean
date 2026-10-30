-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K1/RecordAtFull.lean: THE SHARED "SENDING" (the kind K1): THE RECORD OF PREMISES K1Seated
(Honest/K1/Seated.lean), ALL TWENTY FIELDS, AT 51 OF THE KIND's 52 MEMBERS, AT ProofFile's JOINED SCRIPT
joinQ OVER ALL THREE SENDERS' LOTS OF THE FIRST CHAIN: K1's OWN, AND FOR THE OTHERS' RECORD THE SUM
OF THE CODE SWITCH's SHARE (switchShareAt, Honest/K2/JoinShare.lean, of other authors) AND THE
PROXIMITY TEST's (K12.k12Share, Honest/K12/JoinShare.lean, of other authors). RecordAtJoin.lean's
(J1) AND (J2), CALLED AS THEY STAND, AT THAT RECORD. Four theorems; no definition. BY CALLS.
IMPLICATIONS. A TRIAL THAT COUNTS IN NO COLUMN.

ON THE TIE. (J1)–(J3) show it at joinQ for any record of the other senders that meets four premises.
One such record is laid: K2's and K12's shares, summed, with twelve free letters and two
numbers written by hand. Its four premises are paid there, under the head, the opening and hJ.
Here THE TIE holds at no Script that a run is shown to have. None of this says that the thread's
invariant holds in front of a member at any run. AtFullSide/K1/RecordAtBase.lean
(k1Seated_at_base) takes the record to the base prover, under the same limit.

- four_at_full (F0): UNDER h, O AND hJ, at any book, any front: RecordAtJoin.lean's four premises on
    the others' record (hm, hfm, hp, hfp) hold at the sum: in four_at_empty's form.
- k1Seated_two_at_full (J1★): number 2, the opening: (J1)'s statement with the sum laid for the
    letter Oth.
- k1Seated_fifty_at_full (J2★): number K1.noL l d, at l < 25 and both d: (J2)'s, the like.
- fit_at_full_members (F1): the list is fit (JoinFit, Honest/Thread/JoinFit.lean, of other authors)
    at this file's list k1MembersW J₂ Jl Jw and that sum.

WHICH LAW GIVES WHAT. "The others' lots agree": the first two conjuncts of sum_of_shares
(Honest/K2/Law/SharesApartAtHead.lean), whose five premises on the test's share's public face are
the first five conjuncts of k12_face (AtFullSide/K2/JoinFitFull.lean), under hJ: THERE "AGREE" RESTS
ON Nodup: at the sum no number and no seat stands twice · "far", half by half:
share_far_msgs_at_head, share_far_pads_at_head (Honest/K2/Law/JoinShareAtHead.lean) at the switch's
lots; K12.hfarM_k12, K12.hfarP_k12 (Honest/K12/ShareAtHead.lean) at the test's; the sum's lists are
appended by Others.add's text · (J1★), (J2★): one call each of k1Seated_two_at_join,
k1Seated_fifty_at_join (Honest/K1/Law/RecordAtJoin.lean) · (F1): ProofFile.Honest.K2.Law.joinFit_full
(JoinFitFull.lean) at front 0 and the numbers lotNo OnBytes.secondHashFunction Zp, carried to this file's list
by byNo_at_head (Honest/Thread/JoinAtHead.lean). ALL THESE BUT OUR OWN TWO ARE OTHER AUTHORS'
TRIALS.

THE BOOK. As in RecordAtJoin.lean: hasCoins is paid at the returned prover's own book by
hasCoins_two_at_book, hasCoins_fifty_at_book (HasCoinsAtBook.lean), inside the laws that (J1), (J2)
call. Of the code switch's and the proximity test's counts in the book nothing is asked here.

Limits. IMPLICATIONS: each holds of nothing where its premises are unmet. LEFT AS PREMISES OF (J1★),
(J2★): h, O, hA, hexK, hoK, hJ, and hJ₂, hJl, hJw, three equations that name K1's jobs, which a
caller meets by rfl. THAT THESE CAN BE MET TOGETHER IS NOT SHOWN HERE; whether a job of six stages
exists is not said; hexK is met at widerFillAt, hoK there under WiderKinds (RecordAtJoin.lean's
Limits). Whether the prover that onlineProverFromPublicFiles returns plays the switch's and the test's halves with these
lots' texts is asked by no field of K1Seated. (J3), W's sending, is not stated at this record: its
premise hexW is met here at no filling. WHETHER A LOT's TEXT ANSWERS IS NOT PAID BY Nodup: that
is another question than "agree": for the switch it is had by its authors at the lot's own closing
alone; for the test's pads, messages and trees it is not had here (no LotsAnswer.lean of the test's
is in this library: the file of that name, Honest/K2/Law/, is the switch's);
the question lies under "a Script that a run has". The proofs beneath
sum_of_shares and the four far laws were not read
for this file. THE FIRST CHAIN ALONE. THE FULL SIZE. THE FORMAT's EARLIER HASH.
Nothing on any run, thread or measure. No property is claimed.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.RecordAtJoin
import AtFullSide.K2.JoinFitFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.K1 (momL)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open P5T (PSeat)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2 (switchShareAt)
open ProofFile.Honest.K2.Law (sum_of_shares k12_face share_far_msgs_at_head share_far_pads_at_head
  joinFit_full)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block TS ProofFile.Cl)} {W₀ Rc Tr : Type}

/-- «WHAT IT IS NOT, FIRST. The other senders' record is a term with twelve free letters; the tree
77 and the member 354 are written by hand; J is any job of six stages, tied to no job that a thread
lays. That any lot's text returns a value is not said: every tie here can hold idly. That the
premises can be met together is shown by nobody.» **(F0) THE FOUR PREMISES OF RecordAtJoin.lean ON
THE OTHERS' RECORD, AT THE SUM OF THE CODE SWITCH's SHARE AND THE PROXIMITY TEST's.** h, O AND hJ
ARE PREMISES. hO names the record; a caller meets it by rfl. -/
theorem four_at_full {Bk : ProverCoinCounts} {Xi : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (front : Nat) (Ds : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr))
    {X₂ : Type} (ch : Nat) (J : K12.TestJob (Local W₀ Rc Xi Tr) X₂)
    (hJ : J.p.nums.stages.length = 6) (own₂ : X₂) (n₀ : Nat)
    (ok : Local W₀ Rc Xi Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot Bk (Local W₀ Rc Xi Tr))
    {Oth : Others Bk (Local W₀ Rc Xi Tr)}
    (hO : Oth = (switchShareAt Bk cF.blocksInOrder front Zp Bs.G₀ Ds readers rest).add
      (K12.k12Share ch J own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂)) :
    MsgsAgree Oth.ml ∧
    (∀ L' ∈ Oth.ml, ∃ (j t : ℕ) (q : PSeat),
      ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
        L'.n = P5J.At.arr Zp j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
        (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81) ∧
    PadsAgree Oth.pl ∧
    ∀ L' ∈ Oth.pl, ∃ q ∈ P5J.At.pseatsAll Zp, L'.j = q.j ∧
      L'.t = q.t ∧ q.send ≠ 0 ∧ (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81 := by
  subst hO
  obtain ⟨f1, f2, f3, f4, f5, -, -⟩ := k12_face h ch J hJ own₂ n₀ ok codes sh sh₁ rest₂ rfl
  obtain ⟨a1, a2, -⟩ := sum_of_shares h O front Ds readers rest f1 f2 f3 f4 f5
  refine ⟨a1, ?_, a2, ?_⟩
  · intro L' hL'
    rcases List.mem_append.1 hL' with c | c
    · exact share_far_msgs_at_head h.toAtMg O cF.blocksInOrder front Ds readers rest L' c
    · exact K12.hfarM_k12 h ch J hJ own₂ n₀ ok L' c
  · intro L' hL'
    rcases List.mem_append.1 hL' with c | c
    · exact share_far_pads_at_head h.toAtMg O cF.blocksInOrder front Ds readers rest L' c
    · exact K12.hfarP_k12 h ch J hJ codes sh sh₁ L' c

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  {X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
  (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst)
  (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
  (cells : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
  (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (own₀ : X)
  {J₂ : SendJob (PlaceIn ProofFile.Inst) X} {Jl : ℕ → Bool → SendJob (PlaceIn ProofFile.Inst) X}
  {Jw : SendJob (PlaceIn ProofFile.Inst) X}
  (hJ₂ : J₂ = placeJob (K1.firstPar Bs.G₀.first (K1.gpOf Zp))
    (lotNo OnBytes.secondHashFunction Zp ⟨1, some 0, 1, .K1⟩) (firstFold Bs.G₀.first) (Dt Zp Bs.G₀))
  (hJl : ∀ l d, Jl l d = laterJobAt Bs.G₀.first (K1.gpOf Zp) l (IM.k1Ix l d + 1)
    (if d then 2 else 1) (lotNo OnBytes.secondHashFunction Zp ⟨1, some l, IM.k1Ix l d + 1, .K1⟩)
    (Dt Zp Bs.G₀))
  (hJw : Jw = wJobAt Zp.first (wGp Zp) 4 wMsgFull (lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩)
    (Dd Zp Bs.G₀))
  (Ds : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
  (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
  {X₂ : Type} (ch : Nat) (J : K12.TestJob (Local W₀ Rc ProofFile.Inst Tr) X₂)
  (hJ : J.p.nums.stages.length = 6) (own₂ : X₂) (n₀ : Nat)
  (ok : Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
  (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
  (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
include h O hA hJ₂ hJl hJw hJ

/-- «WHAT IT IS NOT, FIRST. The other senders' record is a term with twelve free letters; the tree
77 and the member 354 are written by hand; J is any job of six stages, tied to no job that a thread
lays. That any lot's text returns a value is not said: every tie here can hold idly. That the
premises can be met together is shown by nobody. "There is blk, K1Seated" is premises met, not a
thread that holds. The joined Script is not shown to be the honest prover's. WHAT IT IS. Under the
head and the opening, at the prover that onlineProverFromPublicFiles returns, two premises on K1's lots and one on the
test's job:» hexK, hoK; hJ. **(J1★) NUMBER 2: ALL TWENTY FIELDS, AT joinQ OVER ALL THREE SENDERS'
LOTS.** The tie (the fields msgs and pads) is paid inside (J1); its four premises on the others'
record by (F0). -/
theorem k1Seated_two_at_full
    (hexK : ∃ M ∈ P.lots,
      M.halves A.Z A.G = lotHalves wit (lotNo OnBytes.secondHashFunction A.Z) Dt A.Z A.G)
    (hoK : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind = .K1 → x.place.link = none) ∨
      M.halves A.Z A.G = lotHalves wit (lotNo OnBytes.secondHashFunction A.Z) Dt A.Z A.G) :
    ∃ blk, K1Seated (lettersHead h A.H
      (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ (k1MembersW J₂ Jl Jw)
        ((switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ Ds readers rest).add
        (K12.k12Share ch J own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂)))
      test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      2 blk wit J₂ own₀ .opening (P5J.At.arr Zp) (P5J.At.seats Zp) (P5J.At.ms Zp Z.lay)
      (K1.radRec 0 J₂.P) := by
  obtain ⟨a1, a2, a3, a4⟩ := four_at_full (Bk := A.B) h O 0 Ds readers rest ch J hJ own₂ n₀ ok
    codes sh sh₁ rest₂ rfl
  exact k1Seated_two_at_join h O hA wit Dt Dd cells tok own₀ hJ₂ hJl hJw _ a1 a2 a3 a4 test carryX
    item n₁ n₂ b₀ Vd Rd Kp w hexK hoK

/-- «WHAT IT IS NOT, FIRST. The other senders' record is a term with twelve free letters; the tree
77 and the member 354 are written by hand; J is any job of six stages, tied to no job that a thread
lays. That any lot's text returns a value is not said: every tie here can hold idly. That the
premises can be met together is shown by nobody. "There is blk, K1Seated" is premises met, not a
thread that holds. The joined Script is not shown to be the honest prover's. WHAT IT IS. Under the
head and the opening, at the prover that onlineProverFromPublicFiles returns, two premises on K1's lots and one on the
test's job:» hexK, hoK; hJ. **(J2★) EACH OF THE FIFTY: ALL TWENTY FIELDS, AT joinQ OVER ALL THREE
SENDERS' LOTS.** The tie is paid inside (J2); its four premises on the others' record by (F0). -/
theorem k1Seated_fifty_at_full
    (hexK : ∃ M ∈ P.lots,
      M.halves A.Z A.G = lotHalves wit (lotNo OnBytes.secondHashFunction A.Z) Dt A.Z A.G)
    (hoK : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind = .K1 → x.place.link = none) ∨
      M.halves A.Z A.G = lotHalves wit (lotNo OnBytes.secondHashFunction A.Z) Dt A.Z A.G)
    {l : ℕ} (hl : l < 25) (d : Bool) :
    ∃ blk, K1Seated (lettersHead h A.H
      (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ (k1MembersW J₂ Jl Jw)
        ((switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ Ds readers rest).add
        (K12.k12Share ch J own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂)))
      test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      (K1.noL l d) blk wit (Jl l d) own₀ (cond d (.digits l) (.reads l)) (P5J.At.arr Zp)
      (P5J.At.seats Zp) (P5J.At.ms Zp Z.lay)
      (K1.radRec (3 * l + (if d then 2 else 1)) (Jl l d).P) := by
  obtain ⟨a1, a2, a3, a4⟩ := four_at_full (Bk := A.B) h O 0 Ds readers rest ch J hJ own₂ n₀ ok
    codes sh sh₁ rest₂ rfl
  exact k1Seated_fifty_at_join h O hA wit Dt Dd cells tok own₀ hJ₂ hJl hJw _ a1 a2 a3 a4 test
    carryX item n₁ n₂ b₀ Vd Rd Kp w hexK hoK hl d

/-- «WHAT IT IS NOT, FIRST. The other senders' record is a term with twelve free letters; the tree
77 and the member 354 are written by hand; J is any job of six stages, tied to no job that a thread
lays. That any lot's text returns a value is not said: every tie here can hold idly. That the
premises can be met together is shown by nobody.» **(F1) THE LIST IS FIT, AT THIS FILE's LIST AND
THAT SUM**: the fields owned and trees among its eleven. h, O, hA, hJ AND THE THREE JOBS' EQUATIONS
ARE PREMISES. By other authors' joinFit_full. -/
theorem fit_at_full_members :
    JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀ (k1MembersW J₂ Jl Jw)
      ((switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ Ds readers rest).add
        (K12.k12Share ch J own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂)) := by
  have F := joinFit_full h O hA (lotNo OnBytes.secondHashFunction Zp) Dt Dd 0 wit own₀ Ds readers rest ch J hJ
    own₂ n₀ ok codes sh sh₁ rest₂
  rw [byNo_at_head h O (lotNo OnBytes.secondHashFunction Zp) Dt Dd] at F
  obtain rfl : Jl = headJl Zp Bs.G₀ (lotNo OnBytes.secondHashFunction Zp) Dt :=
    funext fun l => funext fun d => hJl l d
  subst hJ₂ hJw
  exact F

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.four_at_full
#print axioms ProofFile.Honest.K1.k1Seated_two_at_full
#print axioms ProofFile.Honest.K1.k1Seated_fifty_at_full
#print axioms ProofFile.Honest.K1.fit_at_full_members
