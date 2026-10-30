-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotLaidWider.lean: CONDITIONAL: IN THE PROVER THAT onlineProverFromPublicFiles
RETURNS AT THE FILLING widerFillAt (Honest/AtPureWiderAt.lean) THE LOT OF AN ATTENTION
SEGMENT's OWN ROUNDS (kind K5) IS LAID: so the premise hL of the kind's joined law
(k5_owes_all_joined_kind₅, Honest/K5/Law/AllJoined5.lean) IS EXCHANGED FOR TWO: "onlineProverFromPublicFiles returns" and
an equation on one letter of the filling. Statements with their proofs: calls.

  lotLaid_wider             CONDITIONAL: **LotLaid A.H.first (seatAtK O.keyOf A.Z A.G) id A.G**:
                            general in the three public files; no head
  lotLaid_wider_head        CONDITIONAL: **LotLaid A.H.first (seatAtK keyOfK3 Zp G) id G**: hL in
                            the joined law's own letters, at H := A.H and cells := id
  k5_owes_all_joined_wider  CONDITIONAL: the joined law at the prover that onlineProverFromPublicFiles returns, with hA
                            and hO in hL's stead: the same end
  k5_owes_all_joined_wider_lent   CONDITIONAL: the same with hLent (the book's lending to the kind's
                            own row returns, at all coins) in the stead of hr (one return of the
                            frame's ready), which gives it; the form with hr follows from it

What LotLaid says (Honest/K5/Law/LotLaid.lean): at each place of the kind K5 the first side of the
list is the first of the lot's own list there. How it is had: at a place of a list's kind the search
among A.H.first returns what the search in that list returns, whether a side or nothing:
first_find_all and first_none_in_all (Honest/Thread/FirstFillAll.lean), at the eighth of the
filling's ten lists. That A's public part and ground are the head's: atPure_at_laid_ground
(Honest/AtHeadGround.lean).

The premises. hA: onlineProverFromPublicFiles returns A at the filling (in the last two statements: at the format's
second hash function and the head's three files) · h: the library's head (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean) · hG: G is the ground that the maker makes of the head's public part · hO:
the filling's reader of the key points is keyOfK3 (Honest/K5/Law/KeyOfK3.lean): O is a free letter
of the filling, and the joined law is typed at keyOfK3: it is an ask to whoever lays O · in the
third: all premises of k5_owes_all_joined_kind₅ but hL, at H := A.H, cells := id and the filling's
own types.

Limits. Conditional. NO PREMISE IS PAID FOR NOTHING: hL, a premise on the free letter H, goes; H is
now A.H, and "onlineProverFromPublicFiles returns", WHICH IS SHOWN AT NO FILES, and hO come. The third statement keeps
hg, hG, hfit, hf, hb₀, hRdM, hr, HQ and hH: HQ is the Script's and is unpaid. LotLaid says which
side the search finds, or that it finds none: not that the maker of a place's public data yields.
Through its imports the file stands above the library's folder ThirdParty/. The last two statements:
at the library's full size and the format's second hash function alone. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AllJoined5
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll
import Johnson.Desc.ProofFile.Honest.AtHeadGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.FirstFill (first_find_all first_none_in_all)
open P5J (AtMgA TS CellsM)

section
variable {W₀ : Type} {I : WiderIn W₀} {o o' : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **THE LOT OF THE KIND K5 IS LAID IN THE PROVER THAT onlineProverFromPublicFiles RETURNS AT widerFillAt.**
CONDITIONAL: onlineProverFromPublicFiles returns A at the filling. -/
theorem lotLaid_wider (hA : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A) :
    LotLaid A.H.first (seatAtK O.keyOf A.Z A.G) id A.G := by
  intro pl hk
  have hq : ((k5LotK id O.keyOf, KindName.K5) :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit × KindName) ∈
      widerPairs I o S O := by
    unfold widerPairs
    exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  rw [← halves_k5LotK]
  cases hg : ((k5LotK (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) id O.keyOf).halves A.Z
      A.G).find? (fun q => q.place == pl) with
  | none => exact first_none_in_all hA hq hk hg
  | some g => exact first_find_all hA hq hk hg

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

include h in
/-- **THE PREMISE hL OF THE KIND's JOINED LAW, IN ITS OWN LETTERS.** CONDITIONAL: under the
hypothesis h; G is the ground that is made of the head's public part; onlineProverFromPublicFiles returns A at the head's
three files and the filling; the filling's reader of the key points is keyOfK3. -/
theorem lotLaid_wider_head {G : Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3) : LotLaid A.H.first (seatAtK keyOfK3 Zp G) id G := by
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid hG hA
  have e := lotLaid_wider hA
  rw [eZ, eG, hO] at e
  exact e

variable {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (RdL : Nat → (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- **ALL OF THE MEMBER's DEBTS AT THE PROVER THAT onlineProverFromPublicFiles RETURNS AT widerFillAt.** CONDITIONAL: the
premises of k5_owes_all_joined_kind₅ at H := A.H and cells := id, with hA and hO in hL's stead.
HERE WITH hLent (the book's lending to the kind's own row returns, at all coins) IN THE STEAD OF hr
(one return of `ready`), which gives it. -/
theorem k5_owes_all_joined_wider_lent {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hfit : (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread.fits
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = true)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hb₀ : b₀ ≠ borderOf g + 1)
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ IndexCommitterCoins ProofFile.Inst Unit Bk (id : Cells → Cells) (seatOf keyOfK3 Zp G cF g a))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (seatOf keyOfK3 Zp G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_kind₅_lent h A.H Q test carryX item n₁ n₂ b₀ Vd RdL f w hg hG
    (lotLaid_wider_head h hG hA hO) hfit hf hb₀ hRdM hLent HQ hH

/-- **ALL OF THE MEMBER's DEBTS AT THE PROVER THAT onlineProverFromPublicFiles RETURNS AT widerFillAt.** CONDITIONAL: the
premises of k5_owes_all_joined_kind₅ at H := A.H and cells := id, with hA and hO in hL's stead.
By `k5_owes_all_joined_wider_lent`: one return of `ready` gives hLent. -/
theorem k5_owes_all_joined_wider {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hfit : (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread.fits
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = true)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hb₀ : b₀ ≠ borderOf g + 1)
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    {w₀ : W₀} {rc : IndexCommitterCoins} {ξ : ProofFile.Inst} {c : Coins Bk}
    {R₀ : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    (hr : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk A.H w₀ rc ξ c = .ok R₀)
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (seatOf keyOfK3 Zp G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_wider_lent h Q test carryX item n₁ n₂ b₀ Vd RdL f w hg hG hA hO hfit hf hb₀
    hRdM (k5_lent_of_ready_K3 h A.H Q test carryX item n₁ n₂ Vd RdL (kpBy f) w hg hG
      (lotLaid_wider_head h hG hA hO) hr) HQ hH

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.lotLaid_wider
#print axioms ProofFile.Honest.K5.lotLaid_wider_head
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_wider_lent
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_wider
