-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Plan.PlaceOfPlan
import Johnson.G.PlansPriced
import OnBytes.Model.Fit.ReadNormMade
/-
Johnson/Desc/K12/Law/FreeOfMade.lean: THE NUMBER «free» OF A PROXIMITY TEST's PLACE, AS THE MAKER LAYS IT (placesOfMade, Johnson/Desc/K12/Plan/PlaceOfPlan.lean), IS THE COUNT OF ROOTS OF THE CHAIN's DECLARED ROUNDS IN FRONT OF THE PLACE's start (declPOf, Johnson/G/RoundsOfPlan.lean). It reads the plan and the makers alone: no block, no record, no view. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  sum_foldl · rootsOf_take   the maker's sum (a fold) is rootsOf of the declared rounds' front, where the declared rounds' entries are the list that was cut
  cutOn_free · testCutAt_free   what a cut lays as roots and start
  later_free · places_free   placesLater | placesOfMade: each place's free is the sum of the roots of «es.take start», es the MADE plan's entries of its chain
  PlanTie m       THE BRIDGE: the three plans' rounds AS READ BACK from the planner's bytes (over which the declared rounds are filled) are the MADE plans' entries (out of which the places are cut)
  planTie_of_read   configure = .ok made · ProofChains.read = some ‹the chains' proof› · every made plan fits the format's words (Fmt.Plan.fit: every number below 2^64: A TEST WITH CODE THAT configure DOES NOT ASK) ⇒ PlanTie m (that none of the three plans has an entry RECORD, which the rounds pass over, the readers ask themselves: first_noRecord · ProofChains.read_three): by proof_read_made (OnBytes/Model/ReadBackMade.lean)
  planTie_of_madeOf   madeOf pol lay KL = .ok m · proofFit m.p.chains.made = true (the test by name, Johnson/Desc/FitOk.lean: each plan of the proof file's chains fits the format's words; no description asks it) ⇒ PlanTie m: through madeOf_chains | chainsOf_made (Johnson/G/PlansPriced.lean).
  Like a b · PlanLike m   the same names and the same roots, in order · THE BRIDGE AS FAR AS IT IS SPENT: the plans' rounds as read back are like the made plans' entries · PlanTie.like
  SpeltRoots P · planLike_of_madeOf   WITHOUT «fit»: madeOf pol lay KL = .ok m · of every made plan of the proof: the names fit, none is the configuration's item's (Spelt), every entry's roots < 2^64 ⇒ PlanLike m: by proof_read_norm (OnBytes/Model/Fit/ReadNormMade.lean: the plans as read back are the plans as made with every number modulo 2^64)
  free_of_made    PlanLike m · placesOfMade m = .ok X · declPOf m = .ok D ⇒ X.L.nums.free = rootsOf (D.1.take X.L.start) ∧ X.U.nums.free = rootsOf (D.2.1.take X.U.start) ∧ (∀ o, X.O = some o → o.nums.free = rootsOf (D.2.1.take o.start)) ∧ X.W.nums.free = rootsOf (D.2.2.take X.W.start)
  free_at         the corollary: chain = preR ++ rest · preR.length = start · free = rootsOf (chain.take start) ⇒ free = rootsOf preR
WHAT IT DOES NOT SAY: THAT THE BLOCK's SEAT IN ITS CHAIN IS THE PLACE's start: «preR.length = x.start»: start never enters the kind's parameter: a number against a number, public: A PREMISE (Johnson/Desc/K12/Law/StartOfMade.lean turns it into a count) · THAT ANY RUNNING TEXT ASKS WHAT PAYS PlanLike (proofFit; or SpeltRoots): none does · that a description's plans are declPOf m's D: the description's maker's · that the rounds made off the place's numbers are the plan's own stretch: that is what the description tests.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Made
open OnBytes OnBytes.Params Johnson.G.OfPlan
open H2U (placesOfMade placesLater laterOfProof mkPlace Places4 PlaceNums Later3 LaterArgs cutOn
  testCutAt cutTestL TestCut entriesOf batPlaces)

theorem sum_foldl : ∀ (l : List Nat) (a : Nat), l.foldl (· + ·) a = a + l.sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, sum_foldl l (a + x), List.sum_cons, Nat.add_assoc]

/-- The maker's sum is rootsOf of the declared rounds' front. -/
theorem rootsOf_take (R : List Fmt.DeclaredRound) (es : List Fmt.Entry)
    (h : (R.map (·.entry)).map (·.roots) = es.map (·.roots))
    (i : Nat) : ((es.take i).map (·.roots)).foldl (· + ·) 0 = rootsOf (R.take i) := by
  rw [sum_foldl, Nat.zero_add, List.map_take, ← h, ← List.map_take, ← List.map_take]
  unfold rootsOf
  rw [List.map_map]
  rfl

theorem cutOn_free (es : List Fmt.Entry) (ch i : Nat) (st : List IoppStage) (t : TestCut)
    (h : cutOn es ch i st = some t) :
    t.start = i ∧ t.roots = ((es.take i).map (·.roots)).foldl (· + ·) 0 := by
  unfold cutOn at h
  dsimp only at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, rfl⟩

/-- A place's free is the sum of the roots in front of its start, on the list es. -/
def FreeOn (es : List Fmt.Entry) (x : PlaceNums) : Prop :=
  x.nums.free = ((es.take x.start).map (·.roots)).foldl (· + ·) 0

theorem bindCut_free (es : List Fmt.Entry) (ch : Nat) (st : List IoppStage) (o : Option Nat)
    (t : TestCut) (h : (o.bind fun i => cutOn es ch i st) = some t) :
    t.roots = ((es.take t.start).map (·.roots)).foldl (· + ·) 0 := by
  cases o with
  | none => cases h
  | some i =>
    obtain ⟨a, b⟩ := cutOn_free es ch i st t h
    rw [a]
    exact b

theorem get_some {α : Type} {x : Option α} {e : String} {t : α}
    (h : (match x with
      | some v => (pure v : Except String α)
      | none => throw e) = .ok t) : x = some t := by
  cases x with
  | none => exact absurd h (throw_ne _ _)
  | some v => rw [Except.ok.inj h]

theorem later_free (A : LaterArgs) (X : Later3) (h : placesLater A = .ok X) :
    FreeOn A.es1 X.U ∧ (∀ o, X.O = some o → FreeOn A.es1 o) ∧ FreeOn A.es2 X.W := by
  unfold placesLater at h
  dsimp only at h
  obtain ⟨t0, _, h⟩ := bind_ok h
  obtain ⟨t1, _, h⟩ := bind_ok h
  obtain ⟨t2, _, h⟩ := bind_ok h
  obtain ⟨fU, _, h⟩ := bind_ok h
  obtain ⟨fW, _, h⟩ := bind_ok h
  obtain ⟨tU, hU, h⟩ := bind_ok h
  obtain ⟨tW, hW, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  refine ⟨bindCut_free _ _ _ _ _ (get_some hU), ?_, bindCut_free _ _ _ _ _ (get_some hW)⟩
  intro o ho
  dsimp only at ho
  split at ho
  · rename_i tO fO h1 h2
    cases ho
    exact bindCut_free _ _ _ _ _ h1
  · cases ho

theorem testCutAt_free (C : Configured) (ch i : Nat) (st : List IoppStage) (t : TestCut)
    (h : testCutAt C ch i st = some t) :
    t.roots = (((entriesOf C.proof ch).take t.start).map (·.roots)).foldl (· + ·) 0 := by
  unfold testCutAt at h
  cases hP : C.proof[ch]? with
  | none => simp [hP] at h
  | some P =>
    simp only [hP, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · cases h
    · cases h
      unfold entriesOf
      rw [hP]
      rfl

theorem cutTestL_free (C : Configured) (t : TestCut) (h : cutTestL C = some t) :
    t.roots = (((entriesOf C.proof 0).take t.start).map (·.roots)).foldl (· + ·) 0 := by
  unfold cutTestL at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, i, _, h⟩ := h
  exact testCutAt_free C 0 i _ t h

/-- Each place's free is the sum of the roots in front of its start, on the MADE plan's entries of
its chain. -/
theorem places_free (m : Made) (X : Places4) (h : placesOfMade m = .ok X) :
    FreeOn (entriesOf m.p.chains.made.proof 0) X.L ∧
      FreeOn (entriesOf m.p.chains.made.proof 1) X.U ∧
      (∀ o, X.O = some o → FreeOn (entriesOf m.p.chains.made.proof 1) o) ∧
      FreeOn (entriesOf m.p.chains.made.proof 2) X.W := by
  unfold placesOfMade at h
  dsimp only at h
  obtain ⟨Fs, _, h⟩ := bind_ok h
  obtain ⟨tL, hL, h⟩ := bind_ok h
  obtain ⟨X3, hX3, h⟩ := bind_ok h
  obtain ⟨rows, _, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  obtain ⟨a, b, c⟩ := later_free _ X3 hX3
  exact ⟨cutTestL_free _ tL (get_some hL), a, b, c⟩

/-- The reader of a proof's first chain refuses a plan with an entry RECORD. -/
theorem first_noRecord {b : ByteArray} {q : First} (h : First.read b = some q) :
    q.given.record = none := by
  unfold First.read at h
  obtain ⟨g, hg, h⟩ := opt_bind h
  split at h
  · obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    dsimp only at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
      exact hc.2
    · cases h
  · cases h

/-- Two lists of entries have the same names and the same roots, in order. -/
def Like (a b : List Fmt.Entry) : Prop :=
  a.map (·.name) = b.map (·.name) ∧ a.map (·.roots) = b.map (·.roots)

/-- THE BRIDGE AS FAR AS IT IS SPENT: the three plans' rounds as read back are like the made plans'
entries: names and roots. -/
def PlanLike (m : Made) : Prop :=
  Like m.p.chains.proof.first.given.plan.rounds (entriesOf m.p.chains.made.proof 0) ∧
    Like m.p.chains.proof.shared.given.plan.rounds (entriesOf m.p.chains.made.proof 1) ∧
    Like m.p.chains.proof.second.given.plan.rounds (entriesOf m.p.chains.made.proof 2)

/-- THE BRIDGE: the three plans' rounds as read back are the made plans' entries. -/
def PlanTie (m : Made) : Prop :=
  m.p.chains.proof.first.given.plan.rounds = entriesOf m.p.chains.made.proof 0 ∧
    m.p.chains.proof.shared.given.plan.rounds = entriesOf m.p.chains.made.proof 1 ∧
    m.p.chains.proof.second.given.plan.rounds = entriesOf m.p.chains.made.proof 2

theorem PlanTie.like {m : Made} (h : PlanTie m) : PlanLike m := by
  unfold PlanLike Like
  rw [h.1, h.2.1, h.2.2]
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem planTie_of_read (m : Made) {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    (hc : configure l x cfg bits = .ok m.p.chains.made)
    (hk : ProofChains.read m.p.chains.made.first m.p.chains.made.shared m.p.chains.made.second =
      some m.p.chains.proof)
    (hf : ∀ P ∈ m.p.chains.made.proof, P.plan.fit = true) : PlanTie m := by
  obtain ⟨_, _, _, F, S2, S3, _, hm, _⟩ := configure_bytes hc
  obtain ⟨e1, e2, e3⟩ := proof_read_made hc hk hf hm
  obtain ⟨r1, _, _, n2, n3⟩ := ProofChains.read_three hk
  have h0 := first_noRecord r1
  unfold PlanTie entriesOf
  rw [hm]
  refine ⟨?_, ?_, ?_⟩
  · rw [rounds_of_noRecord h0, e1]
    rfl
  · rw [rounds_of_noRecord n2, e2]
    rfl
  · rw [rounds_of_noRecord n3, e3]
    rfl

/-- The bridge, off the three public files, under the test proofFit
(Johnson/Desc/FitOk.lean). The way from madeOf to configure and the proof's reader is
madeOf_chains | chainsOf_made (Johnson/G/PlansPriced.lean). -/
theorem planTie_of_madeOf {pol lay KL : ByteArray} {m : Made} (h : madeOf pol lay KL = .ok m)
    (hf : VerifiableInference.Desc.proofFit m.p.chains.made = true) : PlanTie m := by
  obtain ⟨X, layout, cfg, hc⟩ := madeOf_chains h
  obtain ⟨l, x, h1, _, _, h3⟩ := chainsOf_made hc
  exact planTie_of_read m h1 h3 fun P hP => List.all_eq_true.1 hf P hP

/-- WITHOUT «fit»: a made plan's names fit and none is the configuration's item's (Spelt,
OnBytes/Model/Fit/ReadNormMade.lean), and every entry's roots are below 2^64. -/
def SpeltRoots (P : Planned) : Prop := Spelt P ∧ ∀ e ∈ P.plan.entries, e.roots < 2 ^ 64

theorem like_norm (P : Planned) (h : ∀ e ∈ P.plan.entries, e.roots < 2 ^ 64) :
    Like ((P.plan.entries).map normE) (P.rounds.map (·.entry)) := by
  have e : P.plan.entries = P.rounds.map (·.entry) := rfl
  rw [← e]
  refine ⟨?_, ?_⟩
  · rw [List.map_map]
    rfl
  · rw [List.map_map]
    refine List.map_congr_left fun x hx => ?_
    exact Nat.mod_eq_of_lt (h x hx)

theorem planLike_of_norm (m : Made) {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    (hc : configure l x cfg bits = .ok m.p.chains.made)
    (hk : ProofChains.read m.p.chains.made.first m.p.chains.made.shared m.p.chains.made.second =
      some m.p.chains.proof)
    (hf : ∀ P ∈ m.p.chains.made.proof, SpeltRoots P) : PlanLike m := by
  obtain ⟨_, _, _, F, S2, S3, _, hm, _⟩ := configure_bytes hc
  obtain ⟨e1, e2, e3⟩ := proof_read_norm hc hk (fun P hP => (hf P hP).1) hm
  obtain ⟨r1, _, _, n2, n3⟩ := ProofChains.read_three hk
  have h0 := first_noRecord r1
  rw [hm] at hf
  unfold PlanLike entriesOf
  rw [hm]
  refine ⟨?_, ?_, ?_⟩
  · rw [rounds_of_noRecord h0, e1]
    exact like_norm F (hf F (by simp)).2
  · rw [rounds_of_noRecord n2, e2]
    exact like_norm S2 (hf S2 (by simp)).2
  · rw [rounds_of_noRecord n3, e3]
    exact like_norm S3 (hf S3 (by simp)).2

/-- The bridge as far as it is spent, off the three public files, WITHOUT «fit». -/
theorem planLike_of_madeOf {pol lay KL : ByteArray} {m : Made} (h : madeOf pol lay KL = .ok m)
    (hf : ∀ P ∈ m.p.chains.made.proof, SpeltRoots P) : PlanLike m := by
  obtain ⟨X, layout, cfg, hc⟩ := madeOf_chains h
  obtain ⟨l, x, h1, _, _, h3⟩ := chainsOf_made hc
  exact planLike_of_norm m h1 h3 hf


theorem free_of_made (m : Made) (X : Places4) (D : Decl3) (hT : PlanLike m)
    (hX : placesOfMade m = .ok X) (hD : declPOf m = .ok D) :
    X.L.nums.free = rootsOf (D.1.take X.L.start) ∧
      X.U.nums.free = rootsOf (D.2.1.take X.U.start) ∧
      (∀ o, X.O = some o → o.nums.free = rootsOf (D.2.1.take o.start)) ∧
      X.W.nums.free = rootsOf (D.2.2.take X.W.start) := by
  unfold declPOf at hD
  obtain ⟨d0, d1, d2⟩ := fileOf_entries hD
  obtain ⟨a, b, c, d⟩ := places_free m X hX
  refine ⟨a.trans (rootsOf_take _ _ (by rw [d0]; exact hT.1.2) _),
    b.trans (rootsOf_take _ _ (by rw [d1]; exact hT.2.1.2) _),
    fun o ho => (c o ho).trans (rootsOf_take _ _ (by rw [d1]; exact hT.2.1.2) _),
    d.trans (rootsOf_take _ _ (by rw [d2]; exact hT.2.2.2) _)⟩

/-- The corollary, in the letters of a seat in a chain. -/
theorem free_at (chain preR rest : List Fmt.DeclaredRound) (free start : Nat)
    (hDs : chain = preR ++ rest) (hstart : preR.length = start)
    (h : free = rootsOf (chain.take start)) : free = rootsOf preR := by
  rw [h, hDs, ← hstart, List.take_left]

end H2K.Made

#print axioms H2K.Made.places_free
#print axioms H2K.Made.planTie_of_read
#print axioms H2K.Made.planTie_of_madeOf
#print axioms H2K.Made.planLike_of_madeOf
#print axioms H2K.Made.free_of_made
#print axioms H2K.Made.free_at
