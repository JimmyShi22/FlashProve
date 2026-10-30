-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/RidesAtFifty.lean: WHAT RIDES PAST ONE OF THE KIND K1's FIFTY
LATER MEMBERS RIDES: `RidesPastS` at number `K1.noL l d`, at ProofFile's `lettersHead`, general in the
letters, under what the letter `Kp` gives at the member's place. The arms are L25's (PinOlder,
RowOlder, PileOlder, WoOlder, FormsOlderK1, their reading packs); its cells
`cell_pile_k1`, `cell_wo_k1`, `cellW_forms_k1` hang on files of other kinds, so here they are
called at K1's numbers alone.

  `k1RiderOk`, `k1_riders_fifty`   which items ride, by Lean's kernel, and a control
  `place_fifty`                     the member's place at the written list, by Lean's kernel
  `k1_keeps_cases`, `k1_keeps_mark`, `k1_keeps_left`   what the kind's clause says
  `k1_ridesPastS_fifty`             the law

Whose. `formsBehind_tests`, `border_at`, `weightAt_stands`, `weightAt_fwd`, `keptW_commit`, `wt_fwd` are L25's
text (Thread/FormsCells, FHeadGKeeps, FormsCellsWhole), copied here under this namespace because
their files hang on other kinds: they give way when L25 lands its own. The arms that this file calls
lie in L25's own files.

Limits. Nothing shows that an item holds at a run. Nothing on any property. Full size, the format's
second hash function.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.KeepsAtFifty
import Johnson.Desc.ProofFile.Honest.Thread.OpenNext
import Johnson.Desc.ProofFile.Honest.Thread.FormsKinds
import Johnson.Desc.ProofFile.Honest.Thread.WoKinds
import Johnson.Desc.ProofFile.Honest.Thread.ConstrDigitsRides
import Johnson.Desc.ProofFile.Honest.Thread.FHeadG
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW
import Johnson.Desc.ProofFile.Honest.Thread.PinRides
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes
import Johnson.Desc.Kinds.Law.KeptWLegs
import Johnson.Desc.Kinds.Law.WtK6Mono

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S Item HeadOwn Pub PubData borderOf)
open VerifiableInference.Desc.K9 (segAt? formsIn formsInA)
open VerifiableInference.Desc.Kinds.Head.Law (WeightAt KeptW weightAt_kept keptW_putTl)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (StepYes)
open ProofFile.Honest.FirstThread
open OnBytes.PscRun (Later)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- **Of the items that a member of the fifty neither shuts nor owes, which may ride.** d: the digits. -/
def k1RiderOk (d : Bool) : Item → Bool
  | .unmarked | .pinW | .pinI | .pile => true
  | .pin _ _ | .row _ _ | .wo _ => true
  | .constr _ q => P5J.parts4.contains q || q == .lookDigits
  | .forms _ _ _ => d
  | _ => false

set_option maxRecDepth 1000000 in
/-- **THE RIDERS AT THE FIFTY**, by Lean's kernel. -/
theorem k1_riders_fifty : ((List.range 25).all fun l => [false, true].all fun d =>
    (fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (K1.noL l d)).all fun i =>
      (FirstRows.rows P5J.At.links P5J.At.ps (K1.noL l d)).shuts.contains i ||
      (FirstRows.rows P5J.At.links P5J.At.ps (K1.noL l d)).owes.contains i || k1RiderOk d i) =
    true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The control: the test of the reads, asked at the digits' member of segment 0, says no, because an
item `forms` rides there. So the test can fail. -/
theorem k1_riders_control : ((fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (K1.noL 0 true)).all fun i =>
      (FirstRows.rows P5J.At.links P5J.At.ps (K1.noL 0 true)).shuts.contains i ||
      (FirstRows.rows P5J.At.links P5J.At.ps (K1.noL 0 true)).owes.contains i ||
      k1RiderOk false i) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **THE MEMBER's PLACE AT THE WRITTEN LIST**, by Lean's kernel. -/
theorem place_fifty_B : ((List.range 25).all fun l => [false, true].all fun d =>
    P5J.At.ps[K1.noL l d]? == some (IM.k1PlaceL l d)) = true := by
  decide +kernel

theorem place_fifty {l : ℕ} (hl : l < 25) (d : Bool) :
    P5J.At.ps[K1.noL l d]? = some (IM.k1PlaceL l d) :=
  eq_of_beq (List.all_eq_true.1 (List.all_eq_true.1 place_fifty_B l (List.mem_range.2 hl)) d
    (by cases d <;> simp))

/-- **WHICH CLAUSE THE KIND's CLAUSE IS AT A MEMBER OF THE FIFTY.** -/
theorem k1_keeps_cases {l : ℕ} {d : Bool} {s s' : TS} (k : K1KeepsAt (IM.k1PlaceL l d) s s') :
    (d = false ∧ K1ReadsKeepsM s s') ∨ (d = true ∧ K1CommitKeepsM s s') := by
  cases d with
  | true =>
    refine Or.inr ⟨rfl, ?_⟩
    by_cases e : l = 24
    · subst e
      exact k
    · have ep : IM.k1PlaceL l true = { chain := 1, link := some l, piece := 6, kind := .K1 } := by
        show (⟨1, some l, (5 + if l = 24 then 1 else 0) + 1, KindName.K1⟩ : Place) = _
        rw [if_neg e]
      rw [ep] at k
      exact k
  | false =>
    refine Or.inl ⟨rfl, ?_⟩
    by_cases e : l = 24
    · subst e
      exact k
    · have ep : IM.k1PlaceL l false = { chain := 1, link := some l, piece := 4, kind := .K1 } := by
        show (⟨1, some l, (3 + if l = 24 then 1 else 0) + 1, KindName.K1⟩ : Place) = _
        rw [if_neg e]
      rw [ep] at k
      exact k

theorem k1_keeps_mark {l : ℕ} {d : Bool} {s s' : TS} (k : K1KeepsAt (IM.k1PlaceL l d) s s') :
    s'.failed = none := by
  rcases k1_keeps_cases k with ⟨-, c⟩ | ⟨-, c⟩ <;> exact c.2

theorem k1_keeps_left {l : ℕ} {d : Bool} {s s' : TS} (k : K1KeepsAt (IM.k1PlaceL l d) s s') :
    Johnson.Desc.First.Walk.Law.leftOf s' =
      Johnson.Desc.First.Walk.Law.leftOf s := by
  rcases k1_keeps_cases k with ⟨-, c⟩ | ⟨-, c⟩
  · exact k1Reads_left c.1
  · exact k1Commit_left c.1

theorem k1_keeps_rest {l : ℕ} {d : Bool} {s s' : TS} (k : K1KeepsAt (IM.k1PlaceL l d) s s') :
    K1Rest s s' := by
  rcases k1_keeps_cases k with ⟨-, c⟩ | ⟨-, c⟩
  · exact rest_reads c.1
  · exact c.1.1

theorem formsBehind_tests {D : PubData} {p : Place} {s' : TS} (hB : formsBehind D p s')
    {m k : Nat} {ρ : String}
    (ho' : Item.forms m k ρ ∈
      IM.openAt P5J.At.links P5J.At.ps (borderOf P5J.At.ps (some p) + 1)) :
    (∀ q ∈ D.runs m k ρ, D.ah q.1 q.2 = true →
      formsInA (D.Rd m) (D.N.sent m) (D.N.group m) q.1 q.2 s' = true) ∧
    (∀ q ∈ D.runs m k ρ, ¬ D.ah q.1 q.2 = true →
      formsIn (D.Rd m) (D.N.group m) q.1 q.2 s' = true) := by
  have t : ((D.runs m k ρ).all fun q =>
      if D.ah q.1 q.2 then formsInA (D.Rd m) (D.N.sent m) (D.N.group m) q.1 q.2 s'
      else formsIn (D.Rd m) (D.N.group m) q.1 q.2 s') = true :=
    hB (Pub.formsIn m k ρ)
      (List.mem_flatMap.2 ⟨Item.forms m k ρ, ho', List.mem_singleton.2 rfl⟩)
  refine ⟨fun q hq ha => ?_, fun q hq ha => ?_⟩
  · have u : (if D.ah q.1 q.2 = true then
        formsInA (D.Rd m) (D.N.sent m) (D.N.group m) q.1 q.2 s'
        else formsIn (D.Rd m) (D.N.group m) q.1 q.2 s') = true := List.all_eq_true.1 t q hq
    rw [if_pos ha] at u
    exact u
  · have u : (if D.ah q.1 q.2 = true then
        formsInA (D.Rd m) (D.N.sent m) (D.N.group m) q.1 q.2 s'
        else formsIn (D.Rd m) (D.N.group m) q.1 q.2 s') = true := List.all_eq_true.1 t q hq
    rw [if_neg ha] at u
    exact u

theorem border_at {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p) :
    borderOf P5J.At.ps (some p) = b := by
  have e' : IM.placesW = P5J.At.ps := HashBuild.placesW_full
  have hb : b < 358 := by
    have hlt := (List.getElem?_eq_some_iff.1 hp).1
    rw [← e', IM.places_len] at hlt
    exact hlt
  have e := IM.border_W b (by omega)
  rw [e', hp] at e
  exact e

/-! ## «weights» forward -/

theorem weightAt_stands (W : OnBytes.Model.Verify.Public) {s : S} {c : _} {m : _}
    (H : WeightAt W s c m) : ∃ a, s.here = .head a := by
  obtain ⟨_, Hh, _, e, _⟩ := H
  revert e
  obtain ⟨st, book, roots, ro, fl, ck, out, here, req⟩ := s
  cases here with
  | head a => exact fun _ => ⟨a, rfl⟩
  | between => exact fun e => nomatch e
  | lay a => exact fun e => nomatch e
  | att a => exact fun e => nomatch e
  | fin a => exact fun e => nomatch e
  | mem a => exact fun e => nomatch e

/-- `WeightAt` passes forward. -/
theorem weightAt_fwd (W : OnBytes.Model.Verify.Public) {s s' : S}
    (hK : ∀ a, s.here = .head a → KeptW s s') {c : _} {m : _} (H : WeightAt W s c m) :
    WeightAt W s' c m := by
  obtain ⟨a, ha⟩ := weightAt_stands W H
  have H0 := H
  obtain ⟨_, Hh, _, e, _⟩ := H
  exact (weightAt_kept W (hK a ha) ⟨Hh, e⟩ c m).2 H0

theorem keptW_commit {s s' : S} (k : ProofFile.Honest.K1.K1CommitKeeps s s') {a : HeadOwn}
    (ha : s.here = .head a) : KeptW s s' := by
  obtain ⟨⟨-, hout, hreq, -⟩, -, -, L, F, tl, L', F', -, hF, -, hh, hS, -⟩ := k
  have hop : a.opened = true := by
    by_contra c
    simp [S.fork?, ha, c] at hF
  have eF : F = a.F := by
    simp [S.fork?, ha, hop] at hF
    exact hF.symm
  have e : ((s.putLink L').putFork F').here = .head { a with L := L', F := F' } := by
    obtain ⟨st, book, roots, ro, fl, ck, out, here, req⟩ := s
    obtain rfl : here = .head a := ha
    simp [S.putLink, S.putFork, hop]
  refine ⟨a, { a with L := L', F := F' }, ha, hh.trans e, rfl, rfl, rfl, rfl,
    congrArg (fun o => o.reply) hout, hreq, ?_⟩
  show Later a.F F'
  rw [← eF]
  exact hS.later


variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

include h in
theorem wt_fwd {s s' : TS} (hK : ∀ a, s.here = .head a → KeptW s s') (m : Nat)
    (z : ProofFile.InstPub) (y y' : Strs) (v : WtF) (H₀ : h.𝔇.wt m (z, s) y v) :
    h.𝔇.wt m (z, s') y' v := by
  by_cases e : m = 24
  · subst e
    exact VerifiableInference.Desc.Kinds.Head.Law.AtTable.hmono_atAll h (z, s') (z, s) y' y v
      (fun _ _ W => weightAt_fwd _ hK W) H₀
  · exact VerifiableInference.Desc.Kinds.Head.Law.AtTable.hidle_atAll h m e _ _ _


/-- **WHAT RIDES PAST A MEMBER OF THE FIFTY RIDES.** hK: what the letter Kp gives at the member's
place; hD: at the digits, the two relations that an item `forms` needs. -/
theorem k1_ridesPastS_fifty (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {l : ℕ} (hl : l < 25) (d : Bool)
    (hK : ∀ s s', Kp (IM.k1PlaceL l d) s s' → K1KeepsAt (IM.k1PlaceL l d) s s' ∧ K1LaterRels s s')
    (hD : d = true → ∀ s s', Kp (IM.k1PlaceL l d) s s' →
      k1RelsAt h.𝔇.pubD l (IM.k1PlaceL l d) s s' ∧ formsBehind h.𝔇.pubD (IM.k1PlaceL l d) s') :
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (K1.noL l d) := by
  have hp := place_fifty hl d
  have hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps
      (K1.noL l d) s s' → K1KeepsAt (IM.k1PlaceL l d) s s' ∧ K1LaterRels s s' :=
    fun s s' a => hK s s' ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp s s').1 a)
  have hlt : K1.noL l d < 345 := by
    by_cases e24 : l = 24
    · subst e24
      cases d <;> decide
    · cases d <;> simp only [K1.noL, IM.k1Ix, if_neg e24, Bool.false_eq_true, if_false, if_true] <;>
        omega
  have h3 : 3 ≤ K1.noL l d := by
    cases d <;> simp only [K1.noL, IM.k1Ix] <;> split <;> simp <;> omega
  have hb : K1.noL l d ≤ cF.blocksInOrder.length := by
    rw [head_len h]
    omega
  have hrest : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps
      (K1.noL l d) s s' → K1Rest s s' := fun s s' a => k1_keeps_rest (hk s s' a).1
  refine ridesPastS_shares _ _ fun i hi h1 h2 => ?_
  have ht : k1RiderOk d i = true := by
    have t := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 k1_riders_fifty l
      (List.mem_range.2 hl)) d (by cases d <;> simp)) i hi
    simp only [Bool.or_eq_true, List.contains_iff_mem] at t
    rcases t with (t | t) | t
    · exact absurd t h1
    · exact absurd t h2
    · exact t
  refine ridesPastAtS_of _ _ ?_
  cases i with
  | unmarked =>
    exact ridesPastAt_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' a => k1_keeps_mark (hk s s' a).1
  | pinW => exact ridesPastAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _
  | pinI =>
    exact ridesPastAt_pinI_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      (head_older_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hrest)
  | pin m t =>
    exact ridesPastAt_pin_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m t
      (head_older_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hrest)
  | pile =>
    exact ridesPastAt_pile_k1_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb h3 (by omega)
      fun s s' a => ⟨hrest s s' a, (hk s s' a).2⟩
  | row m c =>
    exact ridesPastAt_row_k1_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb
      (by rw [show P5J.At.ps.length = 358 by decide +kernel]; omega) m c
      (head_opened_openSets h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega) hi (by simp))
      fun s s' a => ⟨hrest s s' a, (hk s s' a).2⟩
  | wo m =>
    exact ridesPastAt_wo_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb m
      (fun s s' a => ⟨hrest s s' a, k1_keeps_left (hk s s' a).1, (hk s s' a).2.2.2.2.1⟩)
      fun _ _ _ _ hA => head_index h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA
        (open_pinI h3 (by omega))
  | constr m q =>
    simp only [k1RiderOk, Bool.or_eq_true, List.contains_iff_mem, beq_iff_eq, P5J.parts4,
      List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with (rfl | rfl | rfl | rfl) | rfl
    · exact fun _ _ _ _ _ _ _ _ _ h0 => h0
    · exact fun _ _ _ _ _ _ _ _ _ h0 => h0
    · exact fun _ _ _ _ _ _ _ _ _ h0 => h0
    · exact fun _ _ _ _ _ _ _ _ _ h0 => h0
    · exact ridesPastAt_constr_lookDigits h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _ _
  | forms m kk ρ =>
    have hd : d = true := ht
    subst hd
    obtain ⟨ho, ho'⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega) hi h1
      (by simp)
    have hbo : borderOf P5J.At.ps (some (IM.k1PlaceL l true)) = K1.noL l true := border_at hp
    refine ridesPastAt_forms_rec_test h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m kk ρ
      fun s s' a => ?_
    have a' := (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp s s').1 a
    obtain ⟨⟨new, r1, r2, r3⟩, k3⟩ := hD rfl s s' a'
    obtain ⟨e, r4⟩ := r3 m kk ρ (by rw [hbo]; exact ho)
    have tt := formsBehind_tests k3 (m := m) (k := kk) (ρ := ρ) (by rw [hbo]; exact ho')
    rw [← e] at r2
    have c : K1CommitKeeps s s' := by
      rcases k1_keeps_cases (hk s s' a).1 with ⟨hf, -⟩ | ⟨-, c⟩
      · cases hf
      · exact c.1
    exact ⟨c.1, new, r1, r4, fun q hq ha => ⟨tt.1 q hq ha, r2⟩,
      fun _ z y y' v => wt_fwd h (fun _ ha => keptW_commit c ha) m z y y' v⟩
  | _ => cases ht

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_riders_fifty
#print axioms ProofFile.Honest.K1.k1_riders_control
#print axioms ProofFile.Honest.K1.place_fifty
#print axioms ProofFile.Honest.K1.k1_ridesPastS_fifty
#print axioms ProofFile.Honest.K1.formsBehind_tests
#print axioms ProofFile.Honest.K1.border_at
#print axioms ProofFile.Honest.K1.weightAt_stands
#print axioms ProofFile.Honest.K1.weightAt_fwd
#print axioms ProofFile.Honest.K1.keptW_commit
#print axioms ProofFile.Honest.K1.wt_fwd
