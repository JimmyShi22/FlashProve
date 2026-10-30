-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Keeps.lean: CONDITIONAL: what the step of the member at an
attention segment's own rounds (kind K5) leaves of the verifier's state, and three light
consequences, for the debts `Behind` and `Exchange` (Honest/Thread/Pays.lean) at that member.

  `keeps_of_ready`   GENERAL in `Thread`, CONDITIONAL: from a ready state in front, a member's
                     step leaves `K5Keeps` (Johnson/Desc/K5/Honest/Law/Returns.lean)
  `form_behind`      GENERAL in `Thread`: behind a member's step the state bears no mark
  `k5_keeps_at`      CONDITIONAL: the first at the kind's member of group g of the first chain's
                     `Thread` at the library's own letters
  `k5_behind_light`  CONDITIONAL: of the four clauses of `Behind` at that member: no mark of failure
                     behind: shown. `keeps`: `K5Keeps` is shown; the letter follows through the
                     premise Kp. `rides`: from `rides` in front through the premise Rd. The
                     table's promise behind: not here
  `AnsReadsRest`     a premise's form on the letter `ans` (what a pin says on the honest side): at
                     the listed tenants what it says of a state it says of every state that
                     `K5Keeps` ties to it
  `ctx_rides`        CONDITIONAL: the three items that the kind's row reads and owes again (the pin
                     of the segment's first sending, the pin of the stored table, "every cell of
                     the segment is small") say behind the step, of any witness, what they say in
                     front

  `ctx_asked`, `ctx_open`   the kind's row, read forward, asks the three; CONDITIONAL, under the
                     test `Thread.fits` on the letters: so they are open at the border in front
  `k5_ctx_owed`      CONDITIONAL: **the three hold behind the member's step, at every continuation
                     of the challenges**: the kind's row owes six items; these are three of them

How far the letters allow it. The pin of the stored table and the smallness constraint read nothing
of the verifier's state at the honest letters: the first because the decoder is there the constant
"the input's cells", the second by the library's own lemma on its body. The pin of the first sending
is the letter `ans`, which has no text: of it nothing can be shown; `AnsReadsRest` names what is
wanted, and whoever lays `ans` is meant to pay it.

The letters `keeps` and `rides`. They have no text. `k5_behind_light` takes Kp, "whatever `K5Keeps`
holds of, `keeps` holds of at the border", and Rd, "what `rides` says in front of the border it says
behind, of every state that `K5Keeps` ties to the one in front": the direction in which `Behind`
owes them. Both are met at `keeps` at the border := `K5Keeps` and a `rides` that says nothing; Rd
may fail at a `rides` that reads what the step turns. `ctx_rides` takes `K5Keeps` itself: whoever
spends it with the letter `keeps` in hand wants the other direction, "`keeps` at the border gives
`K5Keeps`". At `keeps` at the border := `K5Keeps` both hold.

Limits. Every theorem is conditional. The strings and the witness are the same on both sides.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Accepted
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place OpenedColumn Strs Chain Claim First.S noDigest)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (mgBase mgAll)
open VerifiableInference.Desc.First.Att.P
open H2K5.Honest (K5Keeps k5_keeps)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

/-! ## 1 General in `Thread` -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
  {b : Nat} {cells : Tr → Cells} {Z5 : Seat5} {p : Par} {blk : Block First.S Claim}

/-- **What a member's step leaves.** CONDITIONAL: the state in front is ready. -/
theorem keeps_of_ready (Hs : K5Seated T b cells Z5 p blk) (Dc : DecidesAs p blk)
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hR : ReadyO p s) (hd : drawsFit blk.rounds ds = true)
    (hS : T.Stepped blk k s m E ds y cols s') : K5Keeps s s' := by
  obtain ⟨a, -, e, -, -, hz, -⟩ := hR.open_
  refine k5_keeps p ((step_is T Hs Dc s s' hd hS.1).1 hS.2).1 fun a' e' => ?_
  rw [e] at e'
  cases e'
  exact hz

/-- Behind a member's step the state bears no mark of failure. CONDITIONAL: `K5Seated`, "blk
decides as the kind's decision", and the step's yes. -/
theorem form_behind (Hs : K5Seated T b cells Z5 p blk) (Dc : DecidesAs p blk)
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hd : drawsFit blk.rounds ds = true) (hS : T.Stepped blk k s m E ds y cols s') :
    s'.failed = none :=
  ((step_is T Hs Dc s s' hd hS.1).1 hS.2).2.1

end

/-! ## 2 At the library's own letters -/

/-- **At the tenants of the list L, what the letter `ans` says of a state it says of every state
that `K5Keeps` ties to it.** It is a definition: a premise's form. Nothing is claimed of it. -/
def AnsReadsRest {P Wt : Type} (ans : Nat → Nat → P × TS → Strs → Wt → Prop)
    (L : List (Nat × Nat)) : Prop :=
  ∀ z ∈ L, ∀ π s s' y v, K5Keeps s s' → ans z.1 z.2 (π, s) y v → ans z.1 z.2 (π, s') y v

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **THE STEP LEAVES `K5Keeps`**, at the kind's member of group g. CONDITIONAL: under the
hypothesis h, `K5Seated`, and `Thr` in front. -/
theorem k5_keeps_at {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Stepped blk k s m E
      ds y cols s') : K5Keeps s s' := by
  obtain ⟨Pl, Dc⟩ := seated_decides h hg ha Hs.member
  exact keeps_of_ready _ Hs Dc
    (readyO_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg Pl hT) hd hS

/-- **OF THE FOUR CLAUSES OF `Behind`**, at the kind's member of group g: no mark of failure behind:
shown; `rides`: through the premise Rd; `keeps`: through the premise Kp; the table's promise behind
is not here. CONDITIONAL: under the hypothesis h, `K5Seated`, `Thr` in front and the step's yes; Kp:
`keeps` at the border holds wherever `K5Keeps` does; Rd: what `rides` says in front of the border it
says behind, of every state that `K5Keeps` ties to the one in front. Whoever lays the two letters is
meant to pay Kp and Rd. -/
theorem k5_behind_light {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    (Kp : ∀ s s', K5Keeps s s' → keeps (borderOf g) s s')
    (Rd : ∀ w s s', rides (borderOf g) w s → K5Keeps s s' → rides (borderOf g + 1) w s')
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Stepped blk k s m E
      ds y cols s') :
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).form (borderOf g + 1)
        ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).seat k y.2 s') = true ∧
      (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).rides (borderOf g + 1)
        y.2.st.input s' ∧
      (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).keeps (borderOf g) s
        s' := by
  obtain ⟨-, Dc⟩ := seated_decides h hg ha Hs.member
  have hK := k5_keeps_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hT hd
    hS
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨?_, ?_, Kp _ _ hK⟩
  · show s'.failed.isNone = true
    rw [form_behind _ Hs Dc hd hS]
    rfl
  · show rides (borderOf g + 1) y.2.st.input s'
    rw [ei]
    exact Rd _ _ _ hT.2.2.2.2.2.1 hK

/-- **THE THREE ITEMS THAT THE KIND's ROW READS AND OWES AGAIN** say behind the step what they say
in front, of any witness. CONDITIONAL: under the hypothesis h; for the pin of the first sending, on
the letter ans at that sending's tenants. -/
theorem ctx_rides {g : Nat} (hg : g < 12) {s s' : TS} (hK : K5Keeps s s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (w : Local W₀ Rc ProofFile.Inst Tr) (π : ProofFile.InstPub) (y : Strs) (v : WtF) (i : Item)
    (hi : i ∈ [Item.pin (2 * g + 1) 0, Item.pinW, Item.constr (2 * g + 1) .small])
    (hm : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).means w i (π, s) y
      v) :
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).means w i (π, s') y v := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact fun z hz => hans z hz _ _ _ _ _ hK (hm z hz)
  · exact hm
  · obtain ⟨-, a, -, Pl, -⟩ := k5_member h hg
    have hne : 2 * g + 1 ≠ VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp) := by
      unfold VerifiableInference.OnPublicFiles.headLink
      rw [Pl.p4]
      simp only [if_true]
      omega
    have hm' : (mgAll { h.𝔇 with decT := fun _ _ => some (Q.cells w), cr1 := carryX } mgBase).constr
        (2 * g + 1) .small (π, s) y v := hm
    show (mgAll { h.𝔇 with decT := fun _ _ => some (Q.cells w), cr1 := carryX } mgBase).constr
      (2 * g + 1) .small (π, s') y v
    have h1 := (H2K5.Door.constrIs_any _ mgBase _ _ _ _ _).1 hm'
    refine (H2K5.Door.constrIs_any _ mgBase _ _ _ _ _).2 ?_
    rw [if_neg (by decide)] at h1 ⊢
    exact ⟨h1.1, fun M i hM hH => H2K5.Door.bodySmall_any _ hne i _ _ _ _ _ (h1.2 M i hM hH)⟩

/-- The kind's row, read forward, asks the three items. CONDITIONAL: g is below 12. -/
theorem ctx_asked {g : Nat} (hg : g < 12) (i : Item)
    (hi : i ∈ [Item.pin (2 * g + 1) 0, Item.pinW, Item.constr (2 * g + 1) .small]) :
    i ∈ ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).row
      (borderOf g)).asks := by
  have hpl : P5J.At.ps[borderOf g]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ :=
    H2K5.Door.place_full hg
  have e : FirstRows.rowAt P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩ = FwdRow.of
      (VerifiableInference.Desc.First.rowOf P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩).ins
      (VerifiableInference.Desc.First.rowOf P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩).outs
      (VerifiableInference.Desc.First.rowOf P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩).ctx := rfl
  show i ∈ (FirstRows.rows P5J.At.links P5J.At.ps (borderOf g)).asks
  unfold FirstRows.rows
  rw [hpl, Option.map_some, Option.getD_some, e, k5_row (place_k5 hg)]
  exact List.mem_append_right _ hi

/-- What a row asks is open in front of it. CONDITIONAL: the test on the rows says yes up to a
number beyond the row's. General in the table. -/
theorem mem_of_fwdFit {ι : Type} [DecidableEq ι] {start : List ι} {row : Nat → FwdRow ι} {n b : Nat}
    {i : ι} (hf : fwdFit start row n = true) (hb : b < n) (hi : i ∈ (row b).asks) :
    i ∈ fwdOpen start row b := by
  unfold fwdFit at hf
  have h1 := List.all_eq_true.1 hf b (List.mem_range.2 hb)
  exact List.contains_iff_mem.1 (List.all_eq_true.1 h1 i (List.mem_append_left _ hi))

/-- The three items are open at the border in front of the kind's member. CONDITIONAL: the test on
the letters says yes up to a number n beyond the border. -/
theorem ctx_open {g n : Nat} (hg : g < 12)
    (hfit : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).fits n = true)
    (hb : borderOf g < n) (i : Item)
    (hi : i ∈ [Item.pin (2 * g + 1) 0, Item.pinW, Item.constr (2 * g + 1) .small]) :
    i ∈ (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).opened
      (borderOf g) := by
  unfold Thread.fits at hfit
  simp only [Bool.and_eq_true] at hfit
  exact mem_of_fwdFit hfit.1.1.1.1 hb
    (ctx_asked h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg i hi)

/-- **THE THREE ITEMS HOLD BEHIND THE MEMBER's STEP**, at every continuation of the challenges
heard: three of the six items that the kind's row owes. CONDITIONAL: under the hypothesis h, the
test on the letters, `K5Seated`, the letter ans at the first sending's tenants, `Thr` in
front and the step's yes. -/
theorem k5_ctx_owed {g n : Nat} (hg : g < 12)
    (hfit : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).fits n = true)
    (hb : borderOf g < n) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Stepped blk k s m E
      ds y cols s') :
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Items
      [Item.pin (2 * g + 1) 0, Item.pinW, Item.constr (2 * g + 1) .small] k s' y.2
      (E.add y.1) := by
  intro ds' i hi
  have hK := k5_keeps_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hT hd
    hS
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hE := (k5_env _ Hs hd hT.2.2.2.2.1.2.2.2.1 hS.1).1
  have h0 := hT.2.2.2.1 (ds ++ ds') i
    (ctx_open h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hfit hb i hi)
  have h1 := ctx_rides h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hK hans
    m.st.input m.st.input.x.pub _ _ i hi h0
  show (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).means y.2.st.input i
    (y.2.st.input.x.pub, s')
    ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).strs (E.add y.1))
    ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).wit k y.2.st.input
      (y.2.st.heard ++ ds'))
  rw [hE, ei, eh, List.append_assoc]
  exact h1

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.keeps_of_ready
#print axioms ProofFile.Honest.K5.form_behind
#print axioms ProofFile.Honest.K5.k5_keeps_at
#print axioms ProofFile.Honest.K5.k5_behind_light
#print axioms ProofFile.Honest.K5.ctx_rides
#print axioms ProofFile.Honest.K5.ctx_asked
#print axioms ProofFile.Honest.K5.mem_of_fwdFit
#print axioms ProofFile.Honest.K5.ctx_open
#print axioms ProofFile.Honest.K5.k5_ctx_owed
