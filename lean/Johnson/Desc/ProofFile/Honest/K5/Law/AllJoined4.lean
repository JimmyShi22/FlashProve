-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AllJoined4.lean: CONDITIONAL: ALL THE DEBTS OF THE MEMBER AT AN
ATTENTION SEGMENT's OWN ROUNDS (kind K5) IN ONE STATEMENT, AT THE FIRST CHAIN's LETTERS AS THEY ARE
LAID (`lettersHead`, Honest/Thread/FirstHead.lean): `k5_owes_all_joined_head₃`
(Honest/K5/Law/AllJoined3.lean) WITH TWO LETTERS FIXED AND SO TWO PREMISES STRUCK. It proves nothing
new: it joins.

WHAT IS STRUCK, AND BY WHAT.
  hb (the member's number is below n): n is fixed at the length of the description's first chain's
    flat list; the member stands in that list (`k5_member`, Honest/K5/Law/Member.lean). hfit is now
    the test T.fits at that length: the form in which Honest/Thread/FitsHead.lean's `fits_head`
    ends (that file is not imported)
  hN (N is at most the rounds in front of the member): N is fixed at that number of rounds. N stood
    in hN and in HQ alone. HQ's two clauses begin "N ≤ hd.length →": a larger N makes HQ weaker: so
    HQ is now asked in the weakest of the forms that served, SO FAR AS T.front IS 0 (hN's bound was
    T.front + that number; nothing in this file shows that T.front is 0 here: it is spent, by
    unfolding, in Honest/K5/Law/AllJoined3.lean)

  `k5ScriptQ_mono`             CONDITIONAL: from `K5ScriptQ` at N to `K5ScriptQ` at every larger N'
  `k5_owes_all_joined_head₄`   CONDITIONAL: **`Plays`, `Behind`, `Exchange`, `RidesPast` and, for
                               every fall, `Accepted`**, Kp and b₀ letters
  `k5_owes_all_joined_kind₄`   CONDITIONAL: the same at Kp := `kpBy` f
                               (Honest/Thread/KeepsBy.lean) with `K5KeepsAt` at K5

THE PREMISES OF `k5_owes_all_joined_head₄`, ALL OF THEM. h · hg · hG · hL · hfit · hKpM · hb₀ · hRdM
· hr · HQ · H3 · hH: each as in Honest/K5/Law/AllJoined3.lean's head, but hfit and HQ as said above.

THE FORMS WITH hLent. Of hr (one return of the frame's `ready`, a routine over the whole prover, the
whole book and all three chains) the laws here spend one thing alone: hLent: the book's lending to
the kind's own row returns, at all coins: `Lends5` (Honest/K5/Law/CoinsFewOf.lean) at what the maker
of the place's public data yields. It names no input, no trace, no other kind's half and no other
chain; of the book it reads the first chain's rows and the entries. `k5_owes_all_joined_head₄_lent`
and `k5_owes_all_joined_kind₄_lent` take hLent in hr's stead. hr gives hLent by
`k5_lent_of_ready_K3` (Honest/K5/Law/AllJoined2.lean). The forms with hr keep their names and
statements and follow from these. hLent is shown nowhere either.

Limits. Conditional. The limits of Honest/K5/Law/AllJoined.lean stand here too. A caller that holds
HQ at a smaller N passes to this N by `k5ScriptQ_mono`. h is a hypothesis of every statement that
names it. No file in the kind K5's folders shows HQ, H3, hH or hr; Honest/K5/Law/AllJoined5.lean has
H3 from `att_back_head`, a law of another folder. Kp and b₀ are letters of `lettersHead`. One kind's
twelve members of the chain. At the library's full size and the format's second hash function alone. The
other forms stand beside these.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AllJoined3

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.Sound (seatTab Mem MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt k5KeepsAt_iff)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open P5J (AtMgA TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop)
  (RdL : Nat → (Local W₀ Rc ProofFile.Inst Tr) → TS → Prop) (KpL : Place → TS → TS → Prop)
  (w : (Local W₀ Rc ProofFile.Inst Tr))

/-- **A larger N makes `K5ScriptQ` weaker.** CONDITIONAL: N is at most N'; `K5ScriptQ` at N. -/
theorem k5ScriptQ_mono {N N' : Nat} (hN : N ≤ N') {x₁ : VerifiableInference.Desc.First.Look.Place}
    {a : Attention.Plan} {cells : Tr → Cells} {Z5 : Seat5} {ν₅ : Nat}
    (HQ : K5ScriptQ h Q Vd N x₁ a cells Z5 ν₅) : K5ScriptQ h Q Vd N' x₁ a cells Z5 ν₅ :=
  ⟨fun k v hd hv hl => HQ.eMask k v hd hv (Nat.le_trans hN hl),
    fun k v hd hv hl => HQ.eCells k v hd hv (Nat.le_trans hN hl)⟩

/-- **ALL OF THE MEMBER's DEBTS AT THE LETTERS AS THEY ARE LAID, n AND N FIXED.** CONDITIONAL: every
premise stands, by name, in the file's head.
HERE WITH hLent (the book's lending to the kind's own row returns, at all coins) IN THE STEAD OF hr
(one return of `ready`), which gives it. -/
theorem k5_owes_all_joined_head₄_lent {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOfK3 Zp G) cells G)
    (hfit : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread.fits
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = true)
    (hKpM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ s s',
      KpL ⟨1, some (2 * g + 1), 3, .K5⟩ s s' ↔ K5KeepsM a.own s s')
    (hb₀ : b₀ ≠ borderOf g + 1)
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ Rc ProofFile.Inst X Bk cells (seatOf keyOfK3 Zp G cF g a))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a cells (seatOf keyOfK3 Zp G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (H3 : ∀ a blk₃, (P5J.At.X Zp).A[g]? = some a →
      cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk₃ →
      ∃ p : VerifiableInference.Desc.First.Look.P, p.shape = some a.fs ∧
        K3Back (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread.ft
          blk₃ p)
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g) ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g) ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        fall (borderOf g) := by
  obtain ⟨blk, -, hmem, -⟩ := k5_member h hg
  exact k5_owes_all_joined_head₃_lent h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg hG hL hfit
    (List.getElem?_eq_some_iff.1 hmem).1 hKpM hb₀ hRdM hLent (Nat.le_add_left _ _) HQ H3 hH

/-- **ALL OF THE MEMBER's DEBTS AT THE LETTERS AS THEY ARE LAID, n AND N FIXED.** CONDITIONAL: every
premise stands, by name, in the file's head.
By `k5_owes_all_joined_head₄_lent`: one return of `ready` gives hLent. -/
theorem k5_owes_all_joined_head₄ {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOfK3 Zp G) cells G)
    (hfit : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread.fits
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = true)
    (hKpM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ s s',
      KpL ⟨1, some (2 * g + 1), 3, .K5⟩ s s' ↔ K5KeepsM a.own s s')
    (hb₀ : b₀ ≠ borderOf g + 1)
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {c : Coins Bk} {R₀ : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (hr : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ c = .ok R₀)
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a cells (seatOf keyOfK3 Zp G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (H3 : ∀ a blk₃, (P5J.At.X Zp).A[g]? = some a →
      cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk₃ →
      ∃ p : VerifiableInference.Desc.First.Look.P, p.shape = some a.fs ∧
        K3Back (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread.ft
          blk₃ p)
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g) ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g) ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_head₄_lent h H Q test carryX item n₁ n₂ b₀ Vd RdL KpL w hg hG hL hfit hKpM hb₀
    hRdM (k5_lent_of_ready_K3 h H Q test carryX item n₁ n₂ Vd RdL KpL w hg hG hL hr) HQ H3 hH

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : (Local W₀ Rc ProofFile.Inst Tr) → Prop)
  (RdL : Nat → (Local W₀ Rc ProofFile.Inst Tr) → TS → Prop) (f : KindName → Place → TS → TS → Prop)
  (w : (Local W₀ Rc ProofFile.Inst Tr))

/-- **THE SAME WITH THE LETTER Kp LAID BY THE PLACE's KIND** (`kpBy` f), f AT THE KIND K5 THE CLAUSE
BY THE PLACE (`K5KeepsAt` at the public input). CONDITIONAL: the premises of
`k5_owes_all_joined_head₄`, with hf in hKpM's stead.
HERE WITH hLent (the book's lending to the kind's own row returns, at all coins) IN THE STEAD OF hr
(one return of `ready`), which gives it. -/
theorem k5_owes_all_joined_kind₄_lent {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOfK3 Zp G) cells G)
    (hfit : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread.fits
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = true)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hb₀ : b₀ ≠ borderOf g + 1)
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ Rc ProofFile.Inst X Bk cells (seatOf keyOfK3 Zp G cF g a))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a cells (seatOf keyOfK3 Zp G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (H3 : ∀ a blk₃, (P5J.At.X Zp).A[g]? = some a →
      cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk₃ →
      ∃ p : VerifiableInference.Desc.First.Look.P, p.shape = some a.fs ∧
        K3Back (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread.ft
          blk₃ p)
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_head₄_lent h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w hg hG hL hfit
    (fun a ha s s' => (kpBy_at f rfl s s').trans (by
      rw [hf]
      exact k5KeepsAt_iff ha s s'))
    hb₀ hRdM hLent HQ H3 hH

/-- **THE SAME WITH THE LETTER Kp LAID BY THE PLACE's KIND** (`kpBy` f), f AT THE KIND K5 THE CLAUSE
BY THE PLACE (`K5KeepsAt` at the public input). CONDITIONAL: the premises of
`k5_owes_all_joined_head₄`, with hf in hKpM's stead.
By `k5_owes_all_joined_kind₄_lent`: one return of `ready` gives hLent. -/
theorem k5_owes_all_joined_kind₄ {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {cells : Tr → Cells} (hL : LotLaid H.first (seatAtK keyOfK3 Zp G) cells G)
    (hfit : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread.fits
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = true)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hb₀ : b₀ ≠ borderOf g + 1)
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {c : Coins Bk} {R₀ : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (hr : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ c = .ok R₀)
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a cells (seatOf keyOfK3 Zp G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (H3 : ∀ a blk₃, (P5J.At.X Zp).A[g]? = some a →
      cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk₃ →
      ∃ p : VerifiableInference.Desc.First.Look.P, p.shape = some a.fs ∧
        K3Back (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread.ft
          blk₃ p)
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_kind₄_lent h H Q test carryX item n₁ n₂ b₀ Vd RdL f w hg hG hL hfit hf hb₀ hRdM
    (k5_lent_of_ready_K3 h H Q test carryX item n₁ n₂ Vd RdL (kpBy f) w hg hG hL hr) HQ H3 hH

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5ScriptQ_mono
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_head₄_lent
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_head₄
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_kind₄_lent
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_kind₄
