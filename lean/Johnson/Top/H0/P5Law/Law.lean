-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/P5Law/Law.lean: the base case of a proximity test as a block
(Johnson/Desc/Prox/BaseCase.lean): its law.

The part decides, so its law is of the sort "yes gives yes": THE PART's YES GIVES THE YES OF THE
LIBRARY's BASE CASE, AT THE SAME VIEW. The chain:
  (L1) decide_yes   where baseDecide says yes, the record is handed on unturned, the claim's two
                    vectors have the codes' message lengths, the stretch has the one form (heard),
                    and the format's own test Fmt.M1.baseOK says yes at what was heard.
       decide_iff   the same, both ways.
  (L2) accepts      then, at inputs as Block.step deals them (Dealt), the library's decision
                    Cb.LdwAccept holds, of the claim, of the two words that the opened columns show,
                    and of what the two rounds sent and drew, all read in the field: by the
                    library's OnBytes.Slice.baseOK_iff_accept_cols.
  (D)  stepDeals    Block.step shows decide just shownTo (its own two lines), and that is Dealt (as
                    many drawn positions as the entry says; every column's position below 2^a) and
                    FromView (every column heard is a column of the view under the key of the part's
                    one tree). By the library's Fmt.listOf_mem.
  base_sound        (L1), (L2), (D) in one: of Block.step itself, without a premise.
                    WHAT IT IS: the part's yes gives that the library's base-case decision says yes
                    AT WORDS MADE FROM THE VIEW.
  step_ok           what Block.step's yes says, of any block, one way.
"At the same view": heard reads off the part's stretch: τ* (round 1's one item), λ (round 1's one
drawn element), the shown elements (round 2's items), the drawn positions, the one group of columns.

WHAT IT IS NOT. The library's theorem on the proved block, OnBytes.Slice.base_block
(OnBytes/Slice/Base.lean), says: if the claim has no witness at the radius e the prover has lost at
the start of the two rounds, towards any goal that holds wherever "the format's base test says no".
THIS FILE RUNS BESIDE THAT THEOREM, NOT INTO IT: its premise H is over a typed transcript τ, at
nextN's readings and "last τ", AT THE COMMITTED WORDS; refuses_where_baseOK_does is the like
sentence
AT THE VIEW's READINGS. Not stated in this file:
  - a law for the part as it is lifted into a kind (Lifted.lean has it);
  - the map τ ↦ (rounds, columns, claim), and Accepts at the committed words (Rows.lean,
  AtChain.lean);
  - who pays a failed proof of work;
  - FromView is membership under a cut-off key anywhere among the columns: it loses the slot;
  - that the twelve words of a column are the two messages' symbols in the order that "four" takes.
No premise on the view's words is needed: a word from p on is read reduced, so the reading of a view
into the field is not one to one. At t = 0 the law is true and worthless: planOk, which asks 0 < t,
is
no premise here. No soundness of the protocol is claimed.



-/
import Johnson.Desc.Prox.BaseCase
import OnBytes.Slice.SimBase
import Fmt.Rules6Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Prox
open Fmt.M1 Cb OnBytes.Slice

/-- What the part hears. -/
structure BaseHeard where
  tauS : E
  lam : E
  sent : List E
  poss : List ℕ
  g : List (ℕ × List UInt64)

/-- The reading of the part's stretch. -/
def heard : List Fmt.RoundView → List (List (ℕ × List UInt64)) → Option BaseHeard
  | [rL, rB], [g] =>
    match rL.vals, rL.drawn.elems, elems rB.vals with
    | [.e tauS], [lam], some sent => some ⟨tauS, lam, sent, rB.drawn.poss, g⟩
    | _, _, _ => none
  | _, _ => none

/-- The four symbols at a position, as the group of columns shows them. -/
def colOf (g : List (ℕ × List UInt64)) : ℕ → Option (E × E × E × E) :=
  fun x => (g.find? (·.1 == x)).bind fun y => four y.2

def M0 (P : BasePar) (v : BaseHeard) : List E := v.sent.take P.C.l
def M1 (P : BasePar) (v : BaseHeard) : List E := (v.sent.drop P.C.l).take P.Z.l
def R0 (P : BasePar) (v : BaseHeard) : List E := (v.sent.drop (P.C.l + P.Z.l)).take P.C.r
def R1 (P : BasePar) (v : BaseHeard) : List E := v.sent.drop (P.C.l + P.Z.l + P.C.r)

/-- The format's own test at what was heard. -/
def okAt (P : BasePar) (s : BaseClaim) (v : BaseHeard) : Bool :=
  baseOK .two P.C P.Z s.c s.d s.tau v.tauS v.lam (M0 P v) (M1 P v) (R0 P v) (R1 P v) v.poss (colOf
      v.g)

/-- **(L1)** -/
theorem decide_yes (P : BasePar) (s s' : BaseClaim) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List
           UInt64)))
    (h : baseDecide P s rs gs = .ok s') :
    s' = s ∧ s.c.size = P.C.l ∧ s.d.size = P.Z.l ∧ ∃ v, heard rs gs = some v ∧ okAt P s v = true :=
        by
  unfold baseDecide at h
  split at h
  · rename_i rL rB g
    split at h
    · rename_i tauS lam sent h1 h2 h3
      split at h
      · rename_i hc
        split at h
        · rename_i hb
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          refine ⟨(Except.ok.inj h).symm, hc.1, hc.2, ⟨tauS, lam, sent, rB.drawn.poss, g⟩, ?_, hb⟩
          simp only [heard, h1, h2, h3]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- (L1)'s contrapositive, in the form that the library's base_block's premise H asks: where the
format's base test says no at what was heard, the part refuses. -/
theorem refuses_where_baseOK_does (P : BasePar) (s : BaseClaim) (rs : List Fmt.RoundView) (gs : List (List
           (ℕ × List UInt64))) (v : BaseHeard)
    (hv : heard rs gs = some v) (hno : okAt P s v = false) : ∃ e, baseDecide P s rs gs = .error e :=
        by
  cases hd : baseDecide P s rs gs with
  | error e => exact ⟨e, rfl⟩
  | ok s' =>
    obtain ⟨_, _, _, w, hw, hok⟩ := decide_yes P s s' rs gs hd
    rw [hv] at hw
    cases hw
    rw [hno] at hok
    exact absurd hok (by simp)

/-- (L1), both ways: the part says yes JUST where the stretch has the one form, the claim's vectors
have the codes' lengths and the format's own test says yes. -/
theorem decide_iff (P : BasePar) (s s' : BaseClaim) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List
           UInt64))) :
    baseDecide P s rs gs = .ok s' ↔
      (s' = s ∧ s.c.size = P.C.l ∧ s.d.size = P.Z.l ∧ ∃ v, heard rs gs = some v ∧ okAt P s v = true)
          := by
  constructor
  · exact decide_yes P s s' rs gs
  · rintro ⟨rfl, hc, hd, v, hv, hok⟩
    unfold heard at hv
    split at hv
    · split at hv
      · rename_i h1 h2 h3
        cases hv
        simp only [okAt, M0, M1, R0, R1] at hok
        simp [baseDecide, h1, h2, h3, hc, hd]
        exact hok
      · exact absurd hv (by simp)
    · exact absurd hv (by simp)

/-! ## The same decision with values in Option

baseDecide1 is baseDecide with "none" for every refusal and one "if" for its two. A LIMIT ON THE
EVIDENCE: the first runs, at the first chain's last proximity test of the two stored example proofs,
in
which the part said yes and was asked beside the hand-written program's own two calls at 35 altered
inputs, with a counter-run for each test, were of this form. same_yes ties the two decisions; it
says
nothing of Block.step. -/

def baseDecide1 (P : BasePar) (s : BaseClaim) : List Fmt.RoundView → List (List (Nat × List UInt64)) →
    Option BaseClaim
  | [rL, rB], [g] =>
    match rL.vals, rL.drawn.elems, elems rB.vals with
    | [.e tauS], [lam], some sent =>
      if s.c.size == P.C.l && s.d.size == P.Z.l &&
          Fmt.M1.baseOK .two P.C P.Z s.c s.d s.tau tauS lam (sent.take P.C.l) ((sent.drop
              P.C.l).take P.Z.l)
            ((sent.drop (P.C.l + P.Z.l)).take P.C.r) (sent.drop (P.C.l + P.Z.l + P.C.r))
                rB.drawn.poss
            (fun x => (g.find? (·.1 == x)).bind fun y => four y.2)
      then some s else none
    | _, _, _ => none
  | _, _ => none

theorem decide1_iff (P : BasePar) (s s' : BaseClaim) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List
           UInt64))) :
    baseDecide1 P s rs gs = some s' ↔
      (s' = s ∧ s.c.size = P.C.l ∧ s.d.size = P.Z.l ∧ ∃ v, heard rs gs = some v ∧ okAt P s v = true)
          := by
  constructor
  · intro h
    unfold baseDecide1 at h
    split at h
    · rename_i rL rB g
      split at h
      · rename_i tauS lam sent h1 h2 h3
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          refine ⟨(Option.some.inj h).symm, hc.1.1, hc.1.2, ⟨tauS, lam, sent, rB.drawn.poss, g⟩, ?_,
              hc.2⟩
          simp only [heard, h1, h2, h3]
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · rintro ⟨rfl, hc, hd, v, hv, hok⟩
    unfold heard at hv
    split at hv
    · split at hv
      · rename_i h1 h2 h3
        cases hv
        simp only [okAt, M0, M1, R0, R1] at hok
        simp [baseDecide1, h1, h2, h3, hc, hd]
        exact hok
      · exact absurd hv (by simp)
    · exact absurd hv (by simp)

/-- The two forms say yes at the same inputs, with the same record behind. -/
theorem same_yes (P : BasePar) (s s' : BaseClaim) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List
           UInt64))) :
    baseDecide P s rs gs = .ok s' ↔ baseDecide1 P s rs gs = some s' :=
  (decide_iff P s s' rs gs).trans (decide1_iff P s s' rs gs).symm

/-- Inputs as Block.step deals them. -/
structure Dealt (P : BasePar) (v : BaseHeard) : Prop where
  count : v.poss.length = P.t
  range : ∀ y ∈ v.g, y.1 < 2 ^ P.C.a

/-- The drawn positions as the library's typed positions. -/
def posQ (P : BasePar) (v : BaseHeard) : Fin P.t → Fin (2 ^ P.C.a) :=
  fun i => ⟨v.poss.getD i.val 0 % 2 ^ P.C.a, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The library's decision at what was heard, read in the field. -/
def Accepts (P : BasePar) (s : BaseClaim) (v : BaseHeard) : Prop :=
  LdwAccept (ldCw (baseCode P.C P.Z)) (baseForm P.C P.Z s.c s.d) (toE s.tau) (lastWord P.C.a (colOf
      v.g)) (maskWord P.C.a (colOf v.g))
    (toE v.tauS) (toE v.lam) (baseMs P.C P.Z (M0 P v) (M1 P v) (R0 P v) (R1 P v)) (posQ P v)

theorem lt_of_col {a : ℕ} {g : List (ℕ × List UInt64)} (hg : ∀ y ∈ g, y.1 < 2 ^ a) {x : ℕ} {o : E ×
    E × E × E}
    (h : colOf g x = some o) : x < 2 ^ a := by
  unfold colOf at h
  cases hf : g.find? (·.1 == x) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some y =>
    have hy := hg y (List.mem_of_find?_eq_some hf)
    have hx := List.find?_some hf
    simp only [beq_iff_eq] at hx
    exact hx ▸ hy

theorem poss_eq (P : BasePar) (v : BaseHeard) (hc : v.poss.length = P.t) (hl : ∀ x ∈ v.poss, x < 2 ^
    P.C.a) :
    (List.finRange P.t).map (fun i => (posQ P v i).val) = v.poss := by
  apply List.ext_getElem
  · simp [hc]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_finRange, posQ]
    have : v.poss.getD i 0 = v.poss[i] := by simp [List.getD_eq_getElem?_getD, h2]
    simp only [Fin.val_cast] at *
    rw [this, Nat.mod_eq_of_lt (hl _ (List.getElem_mem h2))]

/-- **(L2)** -/
theorem accepts (P : BasePar) (s : BaseClaim) (v : BaseHeard) (hd : Dealt P v) (hok : okAt P s v =
    true) : Accepts P s v := by
  have hl : ∀ x ∈ v.poss, x < 2 ^ P.C.a := by
    intro x hx
    obtain ⟨o, ho, _⟩ := ((baseOK_iff_parts _ _ _ _ _ _ _ _ _ _ _ _ _).1 hok).2.2 x hx
    exact lt_of_col hd.range ho
  unfold okAt at hok
  rw [← poss_eq P v hd.count hl] at hok
  exact ((baseOK_iff_accept_cols _ _ _ _ _ _ _ _ _ _ _ (posQ P v) _).1 hok).2.2

/-- The groups of columns that Block.step shows the part's decide, of the view's columns that are
not yet taken: Block.step's own two lines. -/
def shownTo (P : BasePar) (firstTree : ℕ) (rs : List Fmt.RoundView) (cols : List
           VerifiableInference.Desc.OpenedColumn) : List (List (ℕ × List UInt64)) :=
  regroup ((groupsOf firstTree (baseRounds P) (rs.map (·.drawn))).map (·.length))
    (cols.take ((groupsOf firstTree (baseRounds P) (rs.map (·.drawn))).flatMap id).length)

/-- Every column that was heard is a column of the view, under the key of the part's one tree. -/
def FromView (P : BasePar) (firstTree : ℕ) (cols : List VerifiableInference.Desc.OpenedColumn) (v :
             BaseHeard) : Prop :=
  ∀ y ∈ v.g, (P.label - firstTree, y.1, y.2) ∈ cols

/-- **(D)**: of Block.step. -/
def StepDeals : Prop :=
  ∀ (P : BasePar) (firstTree : ℕ) (s s' : BaseClaim) (rs : List Fmt.RoundView) (cols : List
             VerifiableInference.Desc.OpenedColumn) (k : ℕ),
    (baseCase (Cl := Unit) P).step firstTree s rs cols = .ok (s', k) →
      baseDecide P s (rs.map noDigest) (shownTo P firstTree rs cols) = .ok s' ∧
        ∃ v, heard (rs.map noDigest) (shownTo P firstTree rs cols) = some v ∧ Dealt P v ∧ FromView P
            firstTree cols v

/-- **P5.base_sound**: of Block.step itself: its yes gives the library's decision at what the
stretch shows. -/
def BaseSound : Prop :=
  ∀ (P : BasePar) (firstTree : ℕ) (s s' : BaseClaim) (rs : List Fmt.RoundView) (cols : List
             VerifiableInference.Desc.OpenedColumn) (k : ℕ),
    (baseCase (Cl := Unit) P).step firstTree s rs cols = .ok (s', k) →
      s' = s ∧ ∃ v, heard (rs.map noDigest) (shownTo P firstTree rs cols) = some v ∧ Dealt P v ∧
          FromView P firstTree cols v ∧ Accepts P s v

/-- P5.base_sound follows from (D). -/
theorem baseSound_of_stepDeals (h : StepDeals) : BaseSound := by
  intro P firstTree s s' rs cols k hs
  obtain ⟨hdec, v, hv, hd, hf⟩ := h P firstTree s s' rs cols k hs
  obtain ⟨he, _, _, w, hw, hok⟩ := decide_yes P s s' _ _ hdec
  rw [hv] at hw
  cases hw
  exact ⟨he, v, hv, hd, hf, accepts P s v hd hok⟩

/-! ## (D), proved -/

theorem groups_eq (P : BasePar) (firstTree : ℕ) (dL dB : Fmt.Drawn) :
    groupsOf firstTree (baseRounds P) [dL, dB] =
      [(Fmt.listOf (dB.poss.map (· % 2 ^ P.C.a))).map fun x => (P.label - firstTree, x, 12)] := by
  simp [groupsOf, baseRounds]

theorem heard_shape {rL rB : Fmt.RoundView} {g : List (ℕ × List UInt64)} {v : BaseHeard} (h : heard [rL,
           rB] [g] = some v) :
    v.poss = rB.drawn.poss ∧ v.g = g := by
  simp only [heard] at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

/-- What the part's second round reads: key, position, width. -/
def wantOf (P : BasePar) (firstTree : ℕ) (rB : Fmt.RoundView) : List (ℕ × ℕ × ℕ) :=
  (Fmt.listOf (rB.drawn.poss.map (· % 2 ^ P.C.a))).map fun x => (P.label - firstTree, x, 12)

theorem shownTo_eq (P : BasePar) (firstTree : ℕ) (rL rB : Fmt.RoundView) (cols : List
           VerifiableInference.Desc.OpenedColumn) :
    shownTo P firstTree [rL, rB] cols = [(cols.take (wantOf P firstTree rB).length).map fun c =>
        (c.2.1, c.2.2)] := by
  simp [shownTo, groups_eq, regroup, wantOf]

/-- What Block.step's yes says, of any block: its three lines. -/
theorem step_ok {S Cl : Type} (firstTree : ℕ) (b : Block S Cl) (s s' : S) (rs : List Fmt.RoundView) (cols :
           List VerifiableInference.Desc.OpenedColumn) (k : ℕ)
    (h : b.step firstTree s rs cols = .ok (s', k)) :
    roundsFit b.rounds rs = true ∧
      ((cols.take ((groupsOf firstTree b.rounds (rs.map (·.drawn))).flatMap id).length).map (fun c
          => (c.1, c.2.1, c.2.2.length)) ==
        (groupsOf firstTree b.rounds (rs.map (·.drawn))).flatMap id) = true ∧
      b.decide s (rs.map noDigest) (regroup ((groupsOf firstTree b.rounds (rs.map (·.drawn))).map
          (·.length))
        (cols.take ((groupsOf firstTree b.rounds (rs.map (·.drawn))).flatMap id).length)) = .ok s'
            := by
  unfold Block.step at h
  dsimp only [bind, Except.bind, need, pure, Except.pure] at h
  split at h
  · exact absurd h (by simp)
  rename_i u1 hu1
  split at h
  · exact absurd h (by simp)
  rename_i u2 hu2
  split at h
  · exact absurd h (by simp)
  rename_i v hv
  have hvs : v = s' := (Prod.mk.inj (Except.ok.inj h)).1
  subst hvs
  refine ⟨?_, ?_, hv⟩
  · split at hu1
    · assumption
    · exact absurd hu1 (by simp)
  · split at hu2
    · assumption
    · exact absurd hu2 (by simp)

theorem stepDeals : StepDeals := by
  intro P firstTree s s' rs cols k hs
  obtain ⟨hfit, hgot, hdec⟩ := step_ok firstTree _ s s' rs cols k hs
  rcases rs with _ | ⟨rL, _ | ⟨rB, _ | ⟨r3, l⟩⟩⟩
  · simp [baseCase, baseRounds, roundsFit] at hfit
  · simp [baseCase, baseRounds, roundsFit] at hfit
  · have hdec0 : baseDecide P s (List.map noDigest [rL, rB]) (shownTo P firstTree [rL, rB] cols) =
      .ok s' := hdec
    have hG : groupsOf firstTree (baseCase (Cl := Unit) P).rounds (List.map (·.drawn) [rL, rB]) =
        [wantOf P firstTree rB] :=
      groups_eq P firstTree rL.drawn rB.drawn
    rw [hG] at hgot
    have hgot' : (cols.take (wantOf P firstTree rB).length).map (fun c => (c.1, c.2.1,
        c.2.2.length)) = wantOf P firstTree rB := by
      simpa using hgot
    obtain ⟨_, _, _, v, hv, _⟩ := decide_yes P s s' _ _ hdec0
    refine ⟨hdec0, v, hv, ?_⟩
    have hv' := hv
    rw [shownTo_eq] at hv'
    simp only [List.map_cons, List.map_nil] at hv'
    obtain ⟨hp, hg⟩ := heard_shape hv'
    have key : ∀ y ∈ v.g, ∃ c ∈ cols, y = (c.2.1, c.2.2) ∧ c.1 = P.label - firstTree ∧ c.2.1 < 2 ^
        P.C.a := by
      intro y hy
      rw [hg] at hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
      have hm : (c.1, c.2.1, c.2.2.length) ∈ wantOf P firstTree rB := by
        rw [← hgot']
        exact List.mem_map.2 ⟨c, hc, rfl⟩
      obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hm
      have hx1 : c.1 = P.label - firstTree := (congrArg (fun t => t.1) hxe).symm
      have hx2 : c.2.1 = x := (congrArg (fun t => t.2.1) hxe).symm
      obtain ⟨p, _, hpx⟩ := List.mem_map.1 ((Fmt.listOf_mem _ x).1 hx)
      refine ⟨c, List.mem_of_mem_take hc, rfl, hx1, ?_⟩
      rw [hx2, ← hpx]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hp]
      have h := hfit
      simp [baseCase, baseRounds, roundsFit] at h
      tauto
    · intro y hy
      obtain ⟨c, _, rfl, _, hlt⟩ := key y hy
      exact hlt
    · intro y hy
      obtain ⟨c, hc, rfl, h1, _⟩ := key y hy
      rw [← h1]
      exact hc
  · simp [baseCase, baseRounds, roundsFit] at hfit

/-- **P5.base_sound.** -/
theorem base_sound : BaseSound := baseSound_of_stepDeals stepDeals

end VerifiableInference.Desc.Prox

#print axioms VerifiableInference.Desc.Prox.base_sound
#print axioms VerifiableInference.Desc.Prox.step_ok
#print axioms VerifiableInference.Desc.Prox.decide_iff
#print axioms VerifiableInference.Desc.Prox.same_yes
#print axioms VerifiableInference.Desc.Prox.decide_yes
#print axioms VerifiableInference.Desc.Prox.refuses_where_baseOK_does
#print axioms VerifiableInference.Desc.Prox.accepts
#print axioms VerifiableInference.Desc.Prox.baseSound_of_stepDeals
