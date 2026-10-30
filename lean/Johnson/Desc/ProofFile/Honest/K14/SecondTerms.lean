-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SecondTerms.lean: kind K14: "K14, second part" (the place
⟨3, none, 0, .K14⟩): THE LAST TEST OF secondRest3 (Honest/K14/SecondBlocks.lean), "addRow: the terms
fit their places", MET UNDER FOUR THINGS: THE LIBRARY's HEAD (P5J.AtMgA, Johnson/P5J/MgAtAll.lean) ·
Thr AT THE SHARED CHAIN's LAST BORDER · THE START's RETURN · THE RETURN OF A FOLD OVER THE FIRST
CHAIN's FLAT LIST; so secondDoor follows from two tests and sW there. Statements with their proofs;
one definition with code.

  secondRest2     secondRest3 WITHOUT ITS LAST TEST: its first two entries. THE LAW THAT TIES THE
                  TWO: rest3_of_two
  rest3_of_two    **secondRest3 from secondRest2**, where the terms of the row (Dot) fit their
                  places wherever the taking-over and linDotRow return
  omegaEnd_gives  what the list on Omega at the shared chain's end (omegaEndL,
                  Honest/K14/OmegaEnd.lean) says of the shared point's length and of Omega's shape
  start_w_member  a state that the start of the last chain returns has W, of the plan's shape, among
                  the own group's members: by start_at_last (Honest/K14/SecondDoor.lean) and the
                  library's start₃E_inv, firstOutFrom_inv, start₃_inv, numbersOk_inv
                  (Johnson/Desc/Third/Law/AtDoor.lean)
  weights_ok_at_fold   **every weight of every row on the table passes Tensor.ok at the fold's
                  return**: the library's weights_at_open (Johnson/LTPileR/AtGate.lean) through its
                  reach_of_fold (Johnson/Top/H0/Walk/Reach.lean)
  joined_at_head  three of the six parts of joined_facts (Honest/K14/OmegaJoin.lean) under the head,
                  at the shared chain's letters (lettersShared): the steps of second_door_shared,
                  second_door_plan, second_door_scope and second_door_laid
                  (Honest/K14/OmegaAtShared.lean, OmegaAtPlan.lean) in one proof
  fifth_at_fold   **THE TEST ITSELF**: under these four, wherever the taking-over and linDotRow
                  return, the terms of the row (Dot) fit their places: by dot_terms_fit
                  (Honest/K14/DotTermsFit.lean). Of its premises linOk, the shared point's length
                  and Omega's shape come from Thr at the shared chain's last border with the start's
                  return (joined_at_head); W's place and the border's rows from the start's return;
                  the weights' form and their passing Tensor.ok from the fold's return
  second_door_two_fold   **secondDoor from secondRest2 and sW**: second_door_three_fold's statement
                  (Honest/K14/SecondBlocksAtFold.lean) with two tests in the place of three: by
                  fifth_at_fold and rest3_of_two

"FOLD" MEANS foldBlocks 0 cF.blocksInOrder FROM THE FIRST CHAIN's OWN START, AT ANY ROUNDS AND COLUMNS AT
WHICH IT RETURNS. NO RUN, NO PROVER AND NO INSTANCE's WITNESS IS NAMED.

What stays a premise in second_door_two_fold: the head; ThrS at the shared chain's last border at
s₂; the start's return at s₁ and s₂; hF: s₁ is that fold's return; sW (where W's pad lies); the two
tests of secondRest2: "adopt: statement and book are in step" and "join: no member twice".

What is not claimed. That one of these premises holds at any run, or that they can hold together:
THE FOLD's RETURN IS SHOWN OF NO ROUNDS. That the head holds at other files than those at which the
library shows it. That the sub-protocol accepts: secondDoor is a list of this kind's own (door_owed,
Honest/K14/SecondDoor.lean). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondBlocksAtFold
import Johnson.Desc.ProofFile.Honest.K14.DotTermsFit
import Johnson.LTPileR.AtGate
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (linDotRow linLayOmega linLayW linOk)
open VerifiableInference.Desc (Chain Place foldBlocks OpenedColumn Own.tensorInOrder Own.placeFits)
open VerifiableInference.Desc.Ground (Clauses ok has)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut takeOver)
open VerifiableInference.Desc.Third.Law (oOf numbersOk_inv start₃E_inv firstOutFrom_inv start₃_inv)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St beforePointOf)

/-! ## Two tests in the place of three -/

/-- secondRest3 (Honest/K14/SecondBlocks.lean) without its last test. -/
def secondRest2 (s : S₃) : Clauses :=
  match s.loc.border with
  | none => []
  | some _ =>
    [("adopt: statement and book are in step", s.st.oracles.size == s.book.place.size),
     ("join: no member twice",
      has s.st.groups[s.loc.own]? (!·.members.contains s.st.oracles.size))]

/-- **secondRest3 from secondRest2**, where the terms of the row (Dot) fit their places wherever the
taking-over and linDotRow return. -/
theorem rest3_of_two (p : P₁₄) (s : S₃)
    (hT : ∀ x, s.loc.border = some x → ∀ a,
      takeOver p.S s.loc.own x.shared (s.withCols []) = .ok a → ∀ dot,
        linDotRow p.S x.g x.shared.psi a.1 (linLayOmega a.2.st.codes p.S) s.loc.w
          (linLayW a.2.st.codes p.S) = some dot →
          has a.2.st.groups[s.loc.own]? (fun G => dot.terms.all fun t =>
            Own.tensorInOrder t.v && Own.placeFits a.2.st G t.oracle t.part t.v.vars 0) = true)
    (h2 : ok (secondRest2 s) = true) : ok (secondRest3 p s) = true := by
  unfold secondRest2 at h2
  unfold secondRest3
  cases hb : s.loc.border with
  | none => rfl
  | some x =>
    rw [hb] at h2
    dsimp only at h2 ⊢
    rw [ok_cons, ok_cons] at h2 ⊢
    simp only [Bool.and_eq_true] at h2 ⊢
    refine ⟨h2.1, h2.2.1, ?_⟩
    cases ha : takeOver p.S s.loc.own x.shared (s.withCols []) with
    | error e => rfl
    | ok a =>
      dsimp only
      cases hd : linDotRow p.S x.g x.shared.psi a.1 (linLayOmega a.2.st.codes p.S) s.loc.w
          (linLayW a.2.st.codes p.S) with
      | none => rfl
      | some dot =>
        dsimp only
        rw [ok_cons, Bool.and_eq_true]
        exact ⟨hT x hb a ha dot hd, rfl⟩

/-! ## The facts that dot_terms_fit asks -/

/-- What the list on Omega at the shared chain's end says of the shared point and of Omega's
shape. -/
theorem omegaEnd_gives {S : OnBytes.Params.LinShape} {o : SharedOut}
    (h : ok (omegaEndL S o) = true) :
    o.psi.length = S.kCol ∧ ∀ y, o.st.oracles[o.omega]? = some y → y.shape = S.omega := by
  unfold omegaEndL at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i y hy
        rw [ok_cons, ok_cons, ok_cons, ok_cons] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        refine ⟨h.2.2.2.1, fun y' hy' => ?_⟩
        obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
        exact h.2.1

section start
variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl)

/-- A state that the start of the last chain returns has W, of the plan's shape, among the own
group's members. -/
theorem start_w_member (x : ProofFile.InstPub) (s₁ : P5J.TS) (s₂ : St) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s) :
    ∃ xw G, s.st.oracles[s.loc.w]? = some xw ∧ xw.shape = (ToldDesc.p14At Zp).S.w ∧
      s.st.groups[s.loc.own]? = some G ∧ G.members.contains s.loc.w = true := by
  obtain ⟨f, e, -, -, -, hst⟩ := start_at_last Zp Np cF x s₁ s₂ s hs
  obtain ⟨f', hf', hs'⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hst
  obtain ⟨hn, -⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf'
  obtain ⟨-, -, rfl⟩ := start₃_inv _ _ _ _ hs'
  obtain ⟨xw, G, a, b, c, d, -⟩ := numbersOk_inv _ _ hn
  exact ⟨xw, G, a, c, b, d⟩

end start

/-- **Every weight of every row on the table passes the program's test on a vector**, under the
library's head, at the state that foldBlocks 0 cF.blocksInOrder returns of the first chain's own start: the
library's weights_at_open at that fold. -/
theorem weights_ok_at_fold {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (p : ProofFile.InstPub)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s₁ : P5J.TS) (r' : List Fmt.RoundView) (cl : List OpenedColumn)
    (hF : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp p) rs cols = .ok (s₁, r', cl)) :
    ∀ row ∈ s₁.rows, ∀ v ∈ row.g, v.ok = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hw := Meaning.K2.weights_at_open O (P5J.flat_ok h.toAtMg) 0 cF.blocksInOrder.length (p, s₁)
    (Johnson.Desc.First.Walk.Tied.reach_of_fold cF.blocksInOrder.length (Nat.le_refl _) s₁ rs r' cols cl
      (by rw [List.take_length]; exact hF))
  unfold VerifiableInference.Desc.First.weightsB at hw
  intro row hrow v hv
  exact List.all_eq_true.1 (List.all_eq_true.1 hw row hrow) v hv

section top
variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS St P₁ Wt)
  (shape : Nat → St → Bool) (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd : Nat → Common W₀ Rc OnBytes.TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc OnBytes.TableKey)

/-- Three of the six things that Thr at the shared chain's last border and the start's return give
together (joined_facts, Honest/K14/OmegaJoin.lean): the border holds o_omega's message; omegaEndL;
linOk: under the library's head at the shared chain's letters. -/
theorem joined_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E' : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E')
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s) :
    ∃ g, s.loc.border = some { g := g, shared := oOf s₂ } ∧
      ok (omegaEndL (ToldDesc.p14At Zp).S (oOf s₂)) = true ∧
      linOk s.st.codes (ToldDesc.p14At Zp).S = true := by
  obtain ⟨sentU, layO, hQ⟩ := plan2_of_laid h.scope h.laid
  obtain ⟨nO, hO⟩ := H2K.JointK.omega_some_in_scope h.scope Zp ProofFile.pureRoad.links Np cF
    h.laid.planOk (LPFD.asks_written h.laid.asks)
  obtain ⟨h9, h10⟩ := plans_at_shared Zp Np cF nO hO h.laid.planOk
  obtain ⟨B⟩ := hQ.eight
  rw [shared_twelve Zp Np cF B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 nO hO B.made] at hA
  obtain ⟨g, a, b, -, c, -, -⟩ := joined_facts Zp Np cF (beforePointOf Np) hQ
    (chainAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w)
    (tailAt_shared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w B.b1
      B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 nO hO B.made h9 h10) hA x s₁ s hs
  exact ⟨g, a, b, c⟩

/-- **"addRow: the terms fit their places" is true**: under the library's head, Thr at the shared
chain's last border at s₂, the start's return s at s₁ and s₂, and where foldBlocks 0 cF.blocksInOrder returns
s₁ of the first chain's own start: wherever the taking-over and linDotRow return. -/
theorem fifth_at_fold {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E' : Env}
    (hA : Thr (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E')
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (p : ProofFile.InstPub) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r' : List Fmt.RoundView) (cl : List OpenedColumn)
    (hF : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp p) rs cols = .ok (s₁, r', cl)) :
    ∀ b, s.loc.border = some b → ∀ a,
      takeOver (ToldDesc.p14At Zp).S s.loc.own b.shared (s.withCols []) = .ok a → ∀ dot,
        linDotRow (ToldDesc.p14At Zp).S b.g b.shared.psi a.1
          (linLayOmega a.2.st.codes (ToldDesc.p14At Zp).S) s.loc.w
          (linLayW a.2.st.codes (ToldDesc.p14At Zp).S) = some dot →
          has a.2.st.groups[s.loc.own]? (fun G => dot.terms.all fun t =>
            Own.tensorInOrder t.v && Own.placeFits a.2.st G t.oracle t.part t.v.vars 0) = true := by
  obtain ⟨g, hb, hE, hlin⟩ := joined_at_head Zp Np cF H N Mg shape nothingLeft order wit table
    fixed n₁ n₂ Vd Rd Kp w h hA x s₁ s hs
  obtain ⟨hp, hO⟩ := omegaEnd_gives hE
  obtain ⟨row, o, hr, hb'⟩ := border_rows Zp Np cF x s₁ s₂ s hs
  have hB := blocks_at_border Zp Np cF x s₁ s₂ s hs
    (rows_at_head h _ (LPFK9.start_rows h.laid.pub p) rs cols s₁ r' cl hF)
  have hok := weights_ok_at_fold h p rs cols s₁ r' cl hF row
    (by rw [hr]; exact List.mem_singleton.2 rfl)
  intro b hbb a ha dot hd
  have e1 : b = { g := g, shared := oOf s₂ } := Option.some.inj (hbb.symm.trans hb)
  have e2 : b = { g := row.g, shared := o } := Option.some.inj (hbb.symm.trans hb')
  refine dot_terms_fit _ s b a dot ha hd (hB b hbb) ?_ hlin ?_ ?_
    (start_w_member Zp Np cF x s₁ s₂ s hs)
  · rw [e2]
    exact hok
  · rw [e1]
    exact hp
  · rw [e1]
    exact hO

/-- **secondDoor, with two tests of the list left as premises**: from the library's head; ThrS at
the shared chain's last border at s₂; the start's return s at s₁ and s₂; hF: foldBlocks 0 cF.blocksInOrder
returns s₁ of the first chain's own start; sW: where W's pad lies; and the two tests of
secondRest2. -/
theorem second_door_two_fold {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E' : Env}
    (hA : ThrS (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread Said (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E')
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (p : ProofFile.InstPub) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r' : List Fmt.RoundView) (cl : List OpenedColumn)
    (hF : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp p) rs cols = .ok (s₁, r', cl))
    (sW : PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol))
    (h2 : ok (secondRest2 s) = true) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true := by
  exact second_door_three_fold Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd
    Kp w h Said hA x s₁ s hs p rs cols r' cl hF sW
    (rest3_of_two _ s (fifth_at_fold Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂
      Vd Rd Kp w h hA.1 x s₁ s hs p rs cols r' cl hF) h2)

end top

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.rest3_of_two
#print axioms ProofFile.Honest.K14.omegaEnd_gives
#print axioms ProofFile.Honest.K14.start_w_member
#print axioms ProofFile.Honest.K14.weights_ok_at_fold
#print axioms ProofFile.Honest.K14.joined_at_head
#print axioms ProofFile.Honest.K14.fifth_at_fold
#print axioms ProofFile.Honest.K14.second_door_two_fold
