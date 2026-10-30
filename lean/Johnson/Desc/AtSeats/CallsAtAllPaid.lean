-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/CallsAtAllPaid.lean: THE FIELD hCallsB OF WHAT IS STILL OWED FOR KIND K1's
CONDITION (`K1Owed`, Johnson/Desc/AtSeats/K01CondOfRest.lean), AT THE FIRST TABLE's CLOSED
CONSTANT, IN THE FIELD's OWN TYPE: the closed test `callsB` (
Johnson/Desc/K1/Law/CallsAtAll.lean: "what ties the caller's public letters to the table's",
matrix by matrix at the output head's segment) accepts, at that file's own letters. Definitions,
and statements with their proofs. THE TEST ASKS, OF EACH MATRIX μ OF SEGMENT 24 THAT COUNTS, AT
THE LAYOUT's ARRAY A UNDER THE MATRIX's LABEL: (i) the segment's list of arrays names the matrix's
symbol array by the label; (ii) A's message is a member k of the caller's list; (iii) A's blocks
lie inside member k's table; (iv) the segment's group holds member k's seat; (v) the table's
number at that seat is the witness's number of A's message; (vi) the list of sampled oracle
messages has a member at that seat, of member k's shape. HOW. (i) IS A THEOREM:
`names_tie_head_all` (Johnson/Desc/AtSeats/NamesTieHeadStream.lean). THE OTHER FIVE READ NO LIST
OF ARRAYS: they read the codes, the shape, the layout, the plan's seats and the numbers' field
sent, ALL OF WHICH ARE THE WRITTEN ONES UNDER THE HEAD AND THE FIRST PIN (
`seats_in_scope`, Johnson/P5T/PlanSeatsTie.lean; `layout_in_scope`,
`sends_in_scope`; `atAll_letters`, `rows_atAll`): SO THEY ARE ONE FACT BY LEAN's
KERNEL. Clause (vi) reads a member's shape and seat, not its radius: it is had from a test on the
plan's pairs (shape, seat) by `mems_sameR` (Johnson/P5T/MembersByMake.lean). `pairB Y s sh`: some
  pair of Y has the seat s, and every such pair has the shape sh. `c6_of_pairs`: so clause (vi).
  `restCB`: clauses (ii) to (vi) at a pair (segment, name), with `pairB` for (vi).
  `calls_of_rest`: **the law: (i) and `restCB` at every matrix give `callsB`**: general in all
  letters. `sentCB`, `pairsCB`, `headPair`: the written letters. `calls_written`: the kernel's
  fact, at all eight matrices. LOOKED AT WITH THE EVALUATOR FIRST, CLAUSE BY CLAUSE, UNDER A
  FORECAST LAID IN THE OPEN. `calls_bite`: it can fail: the seats shifted by one member; every
  number one more; another segment's array: each rejects. `hCallsB_atAll`: the field. PREMISES:
  the head hA, the opening O, the first pin hP1.
A PAYMENT BENEATH A FROZEN CONDITION: no statement above turns.
What is not claimed. That the head, the opening or the pin can be met. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.CallsAtAll
import Johnson.Desc.K1.Law.RadiiAtAll
import Johnson.Desc.AtSeats.NamesTieHeadStream
import Johnson.P5T.PlanSeatsTie
import Johnson.P5T.SeatsAt
import Johnson.P5T.MembersByMake
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Meaning.HidPlanNM

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model OnBytes.Params Johnson.G
open OnBytes.Maker (WholeD)
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls keptAt bornAt)
open VerifiableInference.Desc.Sound (Mem seatOf msOf)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.PlanWritten (madePinnedAt)
open Johnson.Pack (pMain)
open P5T (psFull seatsAllFull N0Full arrOf numOfPlan memberListsR)
open _root_.Desc.K14.Law (seatZ secondAt)
open _root_.Meaning (labAt ownerK ownerA nameOf)
open ProofFile (Cl)
open IM (Open)

/-- Some pair has the seat, and every pair with the seat has the shape. -/
def pairB (Y : List (OracleShape × (ℕ × ℕ))) (s : ℕ × ℕ) (sh : OracleShape) : Bool :=
  (Y.any fun y => decide (y.2 = s)) && Y.all fun y => !decide (y.2 = s) || decide (sh = y.1)

/-- So clause (vi). -/
theorem c6_of_pairs {ms : List Mem} {Y : List (OracleShape × (ℕ × ℕ))}
    (hY : ∀ y, y ∈ ms.map (fun x => ((x.1.l.get x.2).1, seatOf x)) ↔ y ∈ Y) {s : ℕ × ℕ}
    {sh : OracleShape} (h : pairB Y s sh = true) :
    ((ms.find? fun y => Decidable.decide (seatOf y = s)).any fun y =>
      decide (sh = (y.1.l.get y.2).1)) = true := by
  unfold pairB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨y0, hy0, e0⟩ := List.any_eq_true.1 h.1
  obtain ⟨x, hx, ex⟩ := List.mem_map.1 ((hY y0).2 hy0)
  have hs : seatOf x = s := by
    have := of_decide_eq_true e0
    rw [← ex] at this
    exact this
  cases hf : ms.find? fun y => Decidable.decide (seatOf y = s) with
  | none =>
    have := List.find?_eq_none.1 hf x hx
    rw [hs] at this
    simp at this
  | some z =>
    have hz : z ∈ ms := List.mem_of_find?_eq_some hf
    have hp : seatOf z = s := by
      have hq := List.find?_some hf
      exact of_decide_eq_true hq
    have hm : ((z.1.l.get z.2).1, seatOf z) ∈ Y := (hY _).1 (List.mem_map.2 ⟨z, hz, rfl⟩)
    have ha := List.all_eq_true.1 h.2 _ hm
    rw [Bool.or_eq_true] at ha
    rcases ha with ha | ha
    · rw [show (((z.1.l.get z.2).1, seatOf z) : OracleShape × (ℕ × ℕ)).2 = s from hp] at ha
      simp at ha
    · exact ha

/-- Clauses (ii) to (vi), at the array of the name nm in segment K's layout. -/
def restCB (grp : List (ℕ × ℕ)) (arr num : ℕ → ℕ → ℕ) (Y : List (OracleShape × (ℕ × ℕ)))
    (lay : ReqLayout) (D : Sent) (f : ℕ → ℕ × ℕ) (K : ℕ) (nm : String) : Bool :=
  (Desc.arrayOf lay K nm).all fun A =>
    (memberNo D 24 K A.message).any fun k =>
      if hk : k < (sigListCalls D (fun _ => 0) 24).length then
        blocksInB A ((sigListCalls D (fun _ => 0) 24).get ⟨k, hk⟩).1.mainRows
          (pMain D.codes ((sigListCalls D (fun _ => 0) 24).get ⟨k, hk⟩).1).ell &&
        grp.contains (f k) && decide (arr (f k).1 (f k).2 = num K A.message) &&
        pairB Y (f k) ((sigListCalls D (fun _ => 0) 24).get ⟨k, hk⟩).1
      else false

/-- **The law: clause (i) and the rest, at every matrix, give the test.** -/
theorem calls_of_rest {colB : ℕ → Bool} {arr num : ℕ → ℕ → ℕ} {msR : List Mem} {N : Numbers}
    {Wp : Verify.Public} {lay : ReqLayout} {D : Sent} {f : ℕ → ℕ × ℕ}
    {Y : List (OracleShape × (ℕ × ℕ))}
    (hY : ∀ y, y ∈ msR.map (fun x => ((x.1.l.get x.2).1, seatOf x)) ↔ y ∈ Y)
    (h1 : ∀ μ, μ < (_root_.Meaning.sizesOf Wp 24).NM →
      (D.arrayOf.getD 24 #[])[(_root_.Meaning.tlAt Wp 24).gtTree.getD μ 0]? =
        some (ownerK (labAt Wp 24 μ), nameOf (ownerA (labAt Wp 24 μ))))
    (h2 : ∀ μ, μ < (_root_.Meaning.sizesOf Wp 24).NM →
      restCB (N.group 24) arr num Y lay D f (ownerK (labAt Wp 24 μ))
        (nameOf (ownerA (labAt Wp 24 μ))) = true) :
    callsB colB arr msR N Wp lay num D (fun _ => 0) 24 (fun j => f j.val) = true := by
  unfold callsB
  refine List.all_eq_true.2 fun μ _ => ?_
  rw [Bool.or_eq_true]
  right
  have a1 := h1 μ.val μ.isLt
  have a2 := h2 μ.val μ.isLt
  unfold restCB at a2
  cases hX : Desc.arrayOf lay (ownerK (labAt Wp 24 μ.val))
      (nameOf (ownerA (labAt Wp 24 μ.val))) with
  | none => rfl
  | some A =>
    rw [hX] at a2
    simp only [Option.all_some] at a2 ⊢
    cases hM : memberNo D 24 (ownerK (labAt Wp 24 μ.val)) A.message with
    | none =>
      rw [hM] at a2
      cases a2
    | some k =>
      rw [hM] at a2
      simp only [Option.any_some] at a2 ⊢
      by_cases hk : k < (sigListCalls D (fun _ => 0) 24).length
      · rw [dif_pos hk] at a2 ⊢
        simp only [Bool.and_eq_true, decide_eq_true_eq] at a2 ⊢
        exact ⟨⟨⟨⟨a1, a2.1.1.1⟩, a2.1.1.2⟩, a2.1.2⟩, c6_of_pairs hY a2.2⟩
      · rw [dif_neg hk] at a2
        cases a2

/-- The written letters. -/
def sentCB (arrs : Array (Array (ℕ × String))) : Sent :=
  ⟨codesFull2, shapeFull, layoutFull, arrs⟩

def pairsCB : List (OracleShape × (ℕ × ℕ)) :=
  (psFull.filter (·.smpd)).map fun p => (p.shape, p.seat)

def headPair (μ : ℕ) : ℕ × String := if μ == 7 then (22, nameOf 7) else (24, nameOf μ)

/-- **The kernel's fact.** -/
theorem calls_written : ((List.range 8).all fun μ =>
    restCB (N0Full.group 24) (arrOf seatsAllFull) (numOfPlan seatsAllFull) pairsCB layoutFull
      (sentCB #[]) (P6T.seatCallsT psFull (sentCB #[]) 24) (headPair μ).1 (headPair μ).2) =
    true := by
  decide +kernel

/-- It can fail. -/
theorem calls_bite :
    restCB (N0Full.group 24) (arrOf seatsAllFull) (numOfPlan seatsAllFull) pairsCB layoutFull
      (sentCB #[]) (fun k => P6T.seatCallsT psFull (sentCB #[]) 24 (k + 1)) 24 (nameOf 0) =
      false ∧
    restCB (N0Full.group 24) (arrOf seatsAllFull) (fun a b => numOfPlan seatsAllFull a b + 1)
      pairsCB layoutFull (sentCB #[]) (P6T.seatCallsT psFull (sentCB #[]) 24) 24 (nameOf 0) =
      false ∧
    restCB (N0Full.group 24) (arrOf seatsAllFull) (numOfPlan seatsAllFull) pairsCB layoutFull
      (sentCB #[]) (P6T.seatCallsT psFull (sentCB #[]) 24) 20 (nameOf 0) = false := by
  decide +kernel

/-- The rest reads no list of arrays: at all codes, shapes, layouts and seats. -/
theorem rest_arrs_any (grp : List (ℕ × ℕ)) (arr num : ℕ → ℕ → ℕ)
    (Y : List (OracleShape × (ℕ × ℕ))) (lay : ReqLayout) (c : Codes) (sh : ReqShape)
    (ly : ReqLayout) (ps : List P5T.PSeat) (arrs arrs' : Array (Array (ℕ × String))) (K : ℕ)
    (nm : String) :
    restCB grp arr num Y lay ⟨c, sh, ly, arrs⟩ (P6T.seatCallsT ps ⟨c, sh, ly, arrs⟩ 24) K nm =
      restCB grp arr num Y lay ⟨c, sh, ly, arrs'⟩ (P6T.seatCallsT ps ⟨c, sh, ly, arrs'⟩ 24) K
        nm :=
  rfl

theorem rest_arrs (grp : List (ℕ × ℕ)) (arr num : ℕ → ℕ → ℕ) (Y : List (OracleShape × (ℕ × ℕ)))
    (lay : ReqLayout) (arrs : Array (Array (ℕ × String))) (K : ℕ) (nm : String) :
    restCB grp arr num Y lay (sentCB arrs) (P6T.seatCallsT psFull (sentCB arrs) 24) K nm =
      restCB grp arr num Y lay (sentCB #[]) (P6T.seatCallsT psFull (sentCB #[]) 24) K nm :=
  rest_arrs_any grp arr num Y lay codesFull2 shapeFull layoutFull psFull arrs #[] K nm

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}

/-- **The field hCallsB.** -/
theorem hCallsB_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    callsB (colFourB (P5J.At.X Zp).hS (P5J.At.X Zp).HLy (borderOf (P5J.At.X Zp).y))
      hA.𝔇.arr hA.𝔇.ms hA.𝔇.N (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp) hA.𝔇.sent
      (fun _ => 0) 24 (fun j => P5J.At.seat3At Zp 24 false j.val) = true := by
  have hX : Verify.publicOf Zl.pol Zl.KL (some Zl.lay) = .ok (P5J.At.X Zp) := hA.pubOne
  have C := OnBytes.Road.Hd.core_of_scope hA.scope hA.reads hX
  have Bc := (OnBytes.Road.Hd.eleven_of_core hX C (OnBytes.Road.Hd.npOf (P5J.At.X Zp).hS)).1
  have hN : (P5J.At.X Zp).hS.NHf = 4 := (OnBytes.Road.Hd.numH_of_layout Bc.full Bc.head).NHf
  obtain ⟨_, i7, _⟩ := _root_.Meaning.ix_of_core hX C
  obtain ⟨eP, ePA, _⟩ := P5T.seats_in_scope hA.scope hA.laid.pub hP1 (laidP_atAll hA)
  have eS := PlanWritten.Joined.sends_in_scope hA.scope hA.laid.pub hP1
  obtain ⟨R, _, eR⟩ := rows_atAll hA O hP1
  have eM : hA.𝔇.ms =
      msOf (memberListsR proofSendsFull.1.sends.length (P5T.radOf R) psFull) := by
    show P5T.msAtR Zp (P5J.At.rad Zp Zl.lay) = _
    unfold P5T.msAtR
    rw [eS, eP, eR]
  have hn : ∀ p ∈ psFull, p.smpd = true → p.send < proofSendsFull.1.sends.length := by
    intro p hp _
    have h := P5T.planSeats_send_lt Zp Zp.D.1 p (by rw [eP]; exact hp)
    rw [eS] at h
    exact h
  have e8 : (_root_.Meaning.sizesOf (P5J.At.X Zp) 24).NM = 8 := by
    rw [(_root_.Meaning.follows_of_core hX C).NM _ (by omega)]
    exact _root_.Meaning.size_head hX C
  have el : P5J.At.layout Zp = layoutFull :=
    PlanWritten.Joined.layout_in_scope hA.scope hA.laid.pub hP1
  have ec : P5J.At.cs Zp = codesFull2 :=
    (K13.Law.likeFull_in_scope hA.scope hA.laid.pub hP1).codes
  have es : P5J.At.shape Zp = shapeFull := hDsh_atAll hA O hP1
  have eD : hA.𝔇.sent = sentCB (Zp.made.p.built.links.map (·.arrayOf)) := by
    show (⟨P5J.At.cs Zp, P5J.At.shape Zp, P5J.At.layout Zp, _⟩ : Sent) = _
    rw [ec, es, el]
    rfl
  refine calls_of_rest (f := P5J.At.seat3At Zp 24 false) (Y := pairsCB)
    (by rw [eM]; exact P5T.mems_sameR _ (P5T.radOf R) psFull hn) (fun μ hμ => ?_)
    (fun μ hμ => ?_)
  · rw [e8] at hμ
    have et : _root_.Meaning.tlAt (P5J.At.X Zp) 24 = (P5J.At.X Zp).H.tl := by
      unfold _root_.Meaning.tlAt
      rw [if_neg (by omega), if_pos rfl]
    rw [et]
    exact HeadNames.names_tie_head_all hA.scope hA.reads hA.laid.pub hμ
  · rw [e8] at hμ
    have hμm : μ < (_root_.Meaning.matsAt (P5J.At.X Zp) 24).size := by
      rw [_root_.Meaning.size_head hX C]
      exact hμ
    have ol := _root_.Meaning.owner_label hX C (by omega : 24 < 25) hμm
    have hpair : ownerK (labAt (P5J.At.X Zp) 24 μ) = (headPair μ).1 ∧
        nameOf (ownerA (labAt (P5J.At.X Zp) 24 μ)) = (headPair μ).2 := by
      by_cases e : μ = 7
      · subst e
        have oo : _root_.Meaning.ownerOf (P5J.At.X Zp) 24 7 = (22, 7) := by
          unfold _root_.Meaning.ownerOf
          rw [if_pos rfl, hN, if_pos rfl, i7]
        rw [oo] at ol
        have eK : ownerK (labAt (P5J.At.X Zp) 24 7) = 22 := congrArg Prod.fst ol
        have eA : ownerA (labAt (P5J.At.X Zp) 24 7) = 7 := congrArg Prod.snd ol
        rw [eK, eA]
        exact ⟨rfl, rfl⟩
      · have oo : _root_.Meaning.ownerOf (P5J.At.X Zp) 24 μ = (24, μ) := by
          unfold _root_.Meaning.ownerOf
          rw [if_pos rfl, hN, if_neg (by omega)]
        rw [oo] at ol
        have eK : ownerK (labAt (P5J.At.X Zp) 24 μ) = 24 := congrArg Prod.fst ol
        have eA : ownerA (labAt (P5J.At.X Zp) 24 μ) = μ := congrArg Prod.snd ol
        rw [eK, eA]
        unfold headPair
        rw [if_neg (by simpa using e)]
        exact ⟨rfl, rfl⟩
    have eg : hA.𝔇.N.group 24 = N0Full.group 24 := by
      rw [(atAll_letters hA O hP1).1]
      rfl
    have ea : hA.𝔇.arr = arrOf seatsAllFull := by
      show P5T.arrOf (P5T.planSeatsAll Zp Zp.D) = _
      rw [ePA]
    have en : P5J.At.num Zp = numOfPlan seatsAllFull := by
      show P5T.numOfPlan (P5T.planSeatsAll Zp Zp.D) = _
      rw [ePA]
    have ef : P5J.At.seat3At Zp 24 false =
        P6T.seatCallsT psFull (sentCB (Zp.made.p.built.links.map (·.arrayOf))) 24 := by
      funext k
      show P6T.seatCallsT (P5T.planSeats Zp Zp.D.1) hA.𝔇.sent 24 k = _
      rw [eP, eD]
    rw [hpair.1, hpair.2, eg, ea, en, el, eD, ef, rest_arrs]
    exact List.all_eq_true.1 calls_written μ (List.mem_range.2 hμ)

end

end VerifiableInference.Desc.K1
