-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AttentionFacts.lean: what a part and a simulator of the attention
segments' own rounds (kind K5: the label of that sub-protocol in the description) read, and the forms
of Good that the statement at the online prover asks. Statements with their proofs; no definition.

  k5_members_read       at a side with K5's row: each part takes no coin, carries none, has no stop and
                        reads of the input the trace alone; each simulator reads its own coins alone
  k5_rows_read          the same at every row of the lot, at the side that Side.seated makes
  exactAtOneTable_of_good   ExactAtOneTable from the field exact of Good
  good_of_never         Good at A := B := the empty sentence gives Good at every A that holds nowhere,
                        and every B: fits, exact and fresh read neither
  k5_lent_at_rows       CONDITIONAL: h; hA: at every run's coins the book that the maker returns lends
                        each row of the lot at the reader keyOfK3 what it spends

Limits. What a part reads says nothing of the law of what it sends. That the lot has rows is not said
here. h and hA are premises. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ExactAtOneTable
import Johnson.Desc.ProofFile.Honest.K5.Law.NoneSeen5
import Johnson.Desc.ProofFile.Honest.K5.Law.SLotRows
import Johnson.Desc.ProofFile.Honest.K5.Law.FillFoot
import Johnson.Desc.ProofFile.Honest.K5.Law.LendsHalf
import Johnson.Desc.ProofFile.Honest.K5.Law.KeysFitK3
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Place)
open P5J (AtMgA TS)

section Reads
variable {W₀ Rc Xi Tr X Pb S Cl : Type}

/-- A part lifted at a reader of the trace reads of the input the trace alone. -/
theorem lift_reads_trace {V V' W' X' Y : Type} (see : V → V') (f : Tr → W') (get : X' → Y)
    (set : X' → Y → X') (q : Part V' W' Y) :
    ReadsTheTraceAlone (q.lift see (fun t : Local W₀ Rc Xi Tr => f t.trace) get set) := by
  intro mv hmv c s t t' ht hh ho
  obtain ⟨mv₀, -, rfl⟩ := List.mem_map.1 hmv
  show mv₀.say c s (t.narrow _ get) = mv₀.say c s (t'.narrow _ get)
  have e : t.narrow (fun t : Local W₀ Rc Xi Tr => f t.trace) get =
      t'.narrow (fun t : Local W₀ Rc Xi Tr => f t.trace) get := by
    simp only [State.narrow, ht, hh, ho]
  rw [e]

/-- Each part of the row takes no coin, carries none and has no stop. -/
theorem partOf5_plain (cells : Tr → Cells) (Z : Seat5) (j : Nat) (s : H2K5.Honest.PartShape) :
    (partOf5 (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z j s).takes = ⟨0, 0⟩ ∧
      (partOf5 (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z j s).carries = [] ∧
      HasNoStop (partOf5 (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z j s) := by
  cases s with
  | sum k => exact ⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | one n =>
    cases n with
    | zero => exact ⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
    | succ n => exact ⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- Each simulator of the row reads its own coins alone. -/
theorem simOf5_reads (Z : Seat5) (j : Nat) (s : H2K5.Honest.PartShape) :
    ReadsItsCoinsAlone (simOf5 (Pb := Pb) Z j s) := by
  cases s with
  | sum k => exact fun _ _ _ _ _ _ _ _ _ => rfl
  | one n =>
    cases n with
    | zero => exact fun _ _ _ _ _ _ _ _ _ => rfl
    | succ n => exact fun _ _ _ _ _ _ _ _ _ => rfl

/-- **At a side with K5's row: what each member reads.** -/
theorem k5_members_read {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {cells : Tr → Cells} {Z : Seat5} (hr : σ.row = k5Pairs cells Z) :
    ∀ u ∈ σ.members, u.part.takes = ⟨0, 0⟩ ∧ u.part.carries = [] ∧ HasNoStop u.part ∧
      ReadsTheTraceAlone u.part ∧ ReadsItsCoinsAlone u.sim := by
  intro u hu
  obtain ⟨j, s, -, rfl⟩ := member_at hr hu
  obtain ⟨h1, h2, h3⟩ := partOf5_plain (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z j s
  exact ⟨h1, h2, h3,
    lift_reads_trace _ (fun tr => inOf Z.P.S Z.link (cells tr)) _ _ _, simOf5_reads Z j s⟩

/-- **The same at every row of the lot.** -/
theorem k5_rows_read {cells : Tr → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)} {Zp : Pub} {G : Ground}
    {r : Row5 W₀ Rc Xi Tr X Pb} (hr : r ∈ (k5SLot cells keyOf).rows Zp G)
    {bs : List (Block S Cl)} {fs₀ : List (Fall S)}
    {σ₀ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    (hσ : Side.seated bs r.place r.row fs₀ = some σ₀) :
    ∀ u ∈ σ₀.members, u.part.takes = ⟨0, 0⟩ ∧ u.part.carries = [] ∧ HasNoStop u.part ∧
      ReadsTheTraceAlone u.part ∧ ReadsItsCoinsAlone u.sim := by
  obtain ⟨_, _, Y, _, rfl⟩ := row_of_lot hr
  obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 hσ
  exact k5_members_read (cells := cells) (Z := Y) rfl

/-- **ExactAtOneTable from the field exact of Good.** -/
theorem exactAtOneTable_of_good {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} {Bk : ProverCoinCounts} {ord : List Place}
    {A B : Coins Bk → S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop}
    {On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) → CsAll u.part.carries →
      Mid (Local W₀ Rc Xi Tr) X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (g : Good pre .own σ Bk ord 0 0 A B On bud) : ExactAtOneTable σ On bud pre := by
  intro index table x trace u hu ca m front ds asks hm hOn hs ho hd hb hh hstop
  have e := g.exact u hu ca m front ds asks hOn hs ho hd hb hh hstop
  have hx : (Face.own : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xi).pub m.st.input = x := by
    rw [hm]
    rfl
  have et : (fun c => u.sim.tell x front ds asks c) =
      fun c => u.tells .own c m.st.input front ds asks := by
    funext c
    unfold Member.tells
    rw [hx]
  rw [et]
  exact e

/-- **Good at the empty sentence gives Good at every A that holds nowhere, and every B.** -/
theorem good_of_never {V W Pb' S' Cl' X' : Type} {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    {φ : Face V W Pb'} {σ : Side S' Cl' V W X' Pb'} {Bk : ProverCoinCounts} {ord : List Place}
    {chain firstTree : Nat}
    {On : (u : Member V W X' Pb') → CsAll u.part.carries → Mid W X' → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (g : Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) On bud)
    {P Q : Coins Bk → S' → Mid W X' → Env → Prop} (hP : ∀ k s m E, ¬ P k s m E) :
    Good pre φ σ Bk ord chain firstTree P Q On bud :=
  { fits := g.fits
    plays := fun k s m E _ h => absurd h (hP k s m E)
    acc := fun k s m E _ h => absurd h (hP k s m E)
    exact := g.exact
    fresh := g.fresh }

end Reads

section Lent
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X W₀' Rc' Xi X' Pb : Type}

/-- **At every run's coins the book that the maker returns lends each row what it spends.**
CONDITIONAL: h; hA. -/
theorem k5_lent_at_rows (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (cells : Tr → Cells) (k : Coins A.B) :
    ∀ r ∈ (k5SLot (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X') (Pb := Pb) cells keyOfK3).rows Zp A.G,
      ∃ c, lendRow A.B (A.B.rowsOf 0) (k.look 0) r.place r.half.parts 0 = .ok c := by
  have m := (parts_of_atPure hA).1
  have eZ : A.Z = Zp := Except.ok.inj (m.pub.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := eZ ▸ m.ground
  intro r hr
  obtain ⟨y, hy, Y, hY, rfl⟩ := row_of_lot hr
  rw [H2K5.Row.k5Places_scope h.scope h.reads h.laid.pub hG] at hy
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
  have hgl := List.mem_range.1 hg
  obtain ⟨hl, a, hA', hP⟩ := seat_facts hY
  have ha : (P5J.At.X Zp).A[g]? = some a := by
    rw [← hA', H2K5.Row.ground_W hG]
    rfl
  have hs := (seatAt_returns_at_head h hgl hG ha (keysFit_K3 h hgl hG ha)).2
  obtain rfl : Y = seatOf keyOfK3 Zp A.G cF g a := Option.some.inj (hY.symm.trans hs)
  have hL := (lends5_iff (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X') A.B cells
    (seatOf keyOfK3 Zp A.G cF g a)).2 (k5_lends_paid_fill h hgl hA a ha) k
  rw [← r5_half (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X') (Pb := Pb)] at hL
  exact hL

end Lent

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_members_read
#print axioms ProofFile.Honest.K5.k5_rows_read
#print axioms ProofFile.Honest.K5.exactAtOneTable_of_good
#print axioms ProofFile.Honest.K5.good_of_never
#print axioms ProofFile.Honest.K5.k5_lent_at_rows
