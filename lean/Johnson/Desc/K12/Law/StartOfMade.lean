-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.FreeOfMade
/-
Johnson/Desc/K12/Law/StartOfMade.lean: THE NUMBER «start» OF A PROXIMITY TEST's PLACE, AS THE MAKER LAYS IT, IS THE PLACE OF THE k-TH ROUND NAMED "BAT" ON ITS CHAIN: SO A SEAT IN THE CHAIN WHOSE FIRST ROUND IS NAMED "BAT" STANDS AT start JUST WHERE k ROUNDS NAMED "BAT" STAND IN FRONT OF IT. It reads the plan and the makers alone. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  bats l            how many entries of l are named "BAT"
  batPlaces_at      (batPlaces (pre ++ e :: rest))[bats pre]? = some pre.length, where e is named "BAT"
  batPlaces_last    … .getLast? = some pre.length, where moreover no entry of rest is named "BAT"
  StartOn es k x    x.start is number k of batPlaces es · later_start | places_start: U: k = 0 and O: k = 1 on the shared chain's made entries · W: k = 0 on the last chain's · L: the last one on the first chain's
  start_at          StartOn es k x · es = pre ++ e :: rest · e is named "BAT" · bats pre = k ⇒ x.start = pre.length
  free_seat         PlanLike m · placesOfMade m = .ok X · declPOf m = .ok D · the shared chain's declared rounds = preR ++ (r :: rest) · r's entry is named "BAT" · no round of preR is named "BAT" ⇒ X.U.nums.free = rootsOf preR; the like for O (one such round in preR), W (none), L (none behind)
WHAT IT DOES NOT SAY: how many rounds named "BAT" the blocks in front of a seat declare: A PREMISE: a count on public data. BESIDE IT STAND: what pays PlanLike (asked by no running text) · that a description's plans are declPOf m's D.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Made
open OnBytes OnBytes.Params Johnson.G.OfPlan
open H2U (placesOfMade placesLater laterOfProof mkPlace Places4 PlaceNums Later3 LaterArgs cutOn
  testCutAt cutTestL TestCut entriesOf batPlaces batsOn)

/-- How many entries are named "BAT". -/
def bats (l : List Fmt.Entry) : Nat := (l.filter fun e => e.name == "BAT").length

theorem batFrom_at (e : Fmt.Entry) (rest : List Fmt.Entry) (he : (e.name == "BAT") = true) :
    ∀ (pre : List Fmt.Entry) (n : Nat),
      ((((pre ++ e :: rest).zipIdx n).filter fun p => p.1.name == "BAT").map (·.2))[bats pre]? =
        some (n + pre.length)
  | [], n => by
    simp [bats, List.zipIdx_cons, he]
  | a :: pre, n => by
    have ih := batFrom_at e rest he pre (n + 1)
    rw [List.cons_append, List.zipIdx_cons]
    by_cases ha : (a.name == "BAT") = true
    · rw [List.filter_cons_of_pos (by simpa using ha), List.map_cons]
      have hb : bats (a :: pre) = bats pre + 1 := by
        unfold bats
        rw [List.filter_cons_of_pos (p := fun e : Fmt.Entry => e.name == "BAT") ha, List.length_cons]
      rw [hb, List.getElem?_cons_succ, ih, List.length_cons]
      congr 1
      omega
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      have hb : bats (a :: pre) = bats pre := by
        unfold bats
        rw [List.filter_cons_of_neg (p := fun e : Fmt.Entry => e.name == "BAT") ha]
      rw [hb, ih, List.length_cons]
      congr 1
      omega

theorem batPlaces_at (pre : List Fmt.Entry) (e : Fmt.Entry) (rest : List Fmt.Entry)
    (he : (e.name == "BAT") = true) :
    (batPlaces (pre ++ e :: rest))[bats pre]? = some pre.length := by
  have h := batFrom_at e rest he pre 0
  rw [Nat.zero_add] at h
  exact h

theorem batPlaces_len (l : List Fmt.Entry) : (batPlaces l).length = bats l := by
  unfold batPlaces bats
  rw [List.length_map]
  have : ∀ (l : List Fmt.Entry) (n : Nat),
      ((l.zipIdx n).filter fun p => p.1.name == "BAT").length =
        (l.filter fun e => e.name == "BAT").length := by
    intro l
    induction l with
    | nil => intro n; rfl
    | cons a l ih =>
      intro n
      rw [List.zipIdx_cons]
      by_cases ha : (a.name == "BAT") = true
      · rw [List.filter_cons_of_pos (by simpa using ha),
          List.filter_cons_of_pos (p := fun e : Fmt.Entry => e.name == "BAT") ha,
          List.length_cons, List.length_cons, ih]
      · rw [List.filter_cons_of_neg (by simpa using ha),
          List.filter_cons_of_neg (p := fun e : Fmt.Entry => e.name == "BAT") ha, ih]
  exact this l 0

theorem batPlaces_last (pre : List Fmt.Entry) (e : Fmt.Entry) (rest : List Fmt.Entry)
    (he : (e.name == "BAT") = true) (hr : bats rest = 0) :
    (batPlaces (pre ++ e :: rest)).getLast? = some pre.length := by
  have h := batPlaces_at pre e rest he
  have hl : (batPlaces (pre ++ e :: rest)).length = bats pre + 1 := by
    rw [batPlaces_len]
    unfold bats at hr ⊢
    rw [List.filter_append, List.filter_cons_of_pos (p := fun e : Fmt.Entry => e.name == "BAT") he,
      List.length_append, List.length_cons, hr]
  rw [List.getLast?_eq_getElem?, hl, Nat.add_sub_cancel]
  exact h

/-- The places of "BAT" hang on the names alone. -/
theorem batFrom_names : ∀ (a b : List Fmt.Entry) (n : Nat), a.map (·.name) = b.map (·.name) →
    ((a.zipIdx n).filter fun p => p.1.name == "BAT").map (·.2) =
      ((b.zipIdx n).filter fun p => p.1.name == "BAT").map (·.2)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: a, y :: b, n, h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    have ih := batFrom_names a b (n + 1) h.2
    rw [List.zipIdx_cons, List.zipIdx_cons]
    by_cases hx : (x.name == "BAT") = true
    · have hy : (y.name == "BAT") = true := by rw [← h.1]; exact hx
      rw [List.filter_cons_of_pos (by simpa using hx), List.filter_cons_of_pos (by simpa using hy),
        List.map_cons, List.map_cons, ih]
    · have hy : ¬ (y.name == "BAT") = true := by rw [← h.1]; exact hx
      rw [List.filter_cons_of_neg (by simpa using hx), List.filter_cons_of_neg (by simpa using hy),
        ih]

theorem batPlaces_names (a b : List Fmt.Entry) (h : a.map (·.name) = b.map (·.name)) :
    batPlaces a = batPlaces b := batFrom_names a b 0 h

/-- x.start is number k of the places of "BAT" on es. -/
def StartOn (es : List Fmt.Entry) (k : Nat) (x : PlaceNums) : Prop :=
  (batPlaces es)[k]? = some x.start

theorem bindCut_start (es : List Fmt.Entry) (ch : Nat) (st : List IoppStage) (o : Option Nat)
    (t : TestCut) (h : (o.bind fun i => cutOn es ch i st) = some t) : o = some t.start := by
  cases o with
  | none => cases h
  | some i => rw [(cutOn_free es ch i st t h).1]

theorem later_start (A : LaterArgs) (X : Later3) (h : placesLater A = .ok X) :
    StartOn A.es1 0 X.U ∧ (∀ o, X.O = some o → StartOn A.es1 1 o) ∧ StartOn A.es2 0 X.W := by
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
  refine ⟨bindCut_start _ _ _ _ _ (get_some hU), ?_, bindCut_start _ _ _ _ _ (get_some hW)⟩
  intro o ho
  dsimp only at ho
  split at ho
  · rename_i tO fO h1 h2
    cases ho
    exact bindCut_start _ _ _ _ _ h1
  · cases ho

theorem testCutAt_start (C : Configured) (ch i : Nat) (st : List IoppStage) (t : TestCut)
    (h : testCutAt C ch i st = some t) : t.start = i := by
  unfold testCutAt at h
  cases hP : C.proof[ch]? with
  | none => simp [hP] at h
  | some P =>
    simp only [hP, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · cases h
    · cases h
      rfl

theorem cutTestL_start (C : Configured) (t : TestCut) (h : cutTestL C = some t) :
    (batPlaces (entriesOf C.proof 0)).getLast? = some t.start := by
  unfold cutTestL at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨l, hl, i, hi, h⟩ := h
  rw [testCutAt_start C 0 i _ t h]
  unfold batsOn at hl
  cases hP : C.proof[0]? with
  | none => simp [hP] at hl
  | some P =>
    rw [hP] at hl
    obtain rfl := Option.some.inj hl
    unfold entriesOf
    rw [hP]
    exact hi

theorem places_start (m : Made) (X : Places4) (h : placesOfMade m = .ok X) :
    (batPlaces (entriesOf m.p.chains.made.proof 0)).getLast? = some X.L.start ∧
      StartOn (entriesOf m.p.chains.made.proof 1) 0 X.U ∧
      (∀ o, X.O = some o → StartOn (entriesOf m.p.chains.made.proof 1) 1 o) ∧
      StartOn (entriesOf m.p.chains.made.proof 2) 0 X.W := by
  unfold placesOfMade at h
  dsimp only at h
  obtain ⟨Fs, _, h⟩ := bind_ok h
  obtain ⟨tL, hL, h⟩ := bind_ok h
  obtain ⟨X3, hX3, h⟩ := bind_ok h
  obtain ⟨rows, _, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  obtain ⟨a, b, c⟩ := later_start _ X3 hX3
  exact ⟨cutTestL_start _ tL (get_some hL), a, b, c⟩

theorem start_at (es pre : List Fmt.Entry) (e : Fmt.Entry) (rest : List Fmt.Entry) (k : Nat)
    (x : PlaceNums) (h : StartOn es k x) (hes : es = pre ++ e :: rest)
    (he : (e.name == "BAT") = true) (hk : bats pre = k) : x.start = pre.length := by
  unfold StartOn at h
  rw [hes, ← hk, batPlaces_at pre e rest he] at h
  exact (Option.some.inj h).symm

/-- How many declared rounds are named "BAT". -/
def batsR (l : List Fmt.DeclaredRound) : Nat := bats (l.map (·.entry))

/-- A seat in a chain's declared rounds, at number k of the rounds named "BAT". -/
theorem free_seat_k (chain preR : List Fmt.DeclaredRound) (r : Fmt.DeclaredRound)
    (rest : List Fmt.DeclaredRound) (es : List Fmt.Entry) (k : Nat) (x : PlaceNums)
    (hE : Like (chain.map (·.entry)) es) (hS : StartOn es k x)
    (hF : x.nums.free = rootsOf (chain.take x.start)) (hDs : chain = preR ++ r :: rest)
    (hr : (r.entry.name == "BAT") = true) (hk : batsR preR = k) :
    preR.length = x.start ∧ x.nums.free = rootsOf preR := by
  have hs : x.start = preR.length := by
    have hS' : StartOn (chain.map (·.entry)) k x := by
      unfold StartOn at hS ⊢
      rw [batPlaces_names _ _ hE.1]
      exact hS
    have := start_at (chain.map (·.entry)) (preR.map fun d : Fmt.DeclaredRound => d.entry) r.entry
      (rest.map fun d : Fmt.DeclaredRound => d.entry) k x hS'
      (by rw [hDs, List.map_append, List.map_cons]) hr hk
    rw [this, List.length_map]
  exact ⟨hs.symm, free_at chain preR (r :: rest) _ _ hDs hs.symm hF⟩

/-- The three places on the two later chains. -/
theorem free_seat (m : Made) (X : Places4) (D : Decl3) (hT : PlanLike m)
    (hX : placesOfMade m = .ok X) (hD : declPOf m = .ok D) :
    (∀ preR r rest, D.2.1 = preR ++ r :: rest → (r.entry.name == "BAT") = true → batsR preR = 0 →
      preR.length = X.U.start ∧ X.U.nums.free = rootsOf preR) ∧
    (∀ o, X.O = some o → ∀ preR r rest, D.2.1 = preR ++ r :: rest →
      (r.entry.name == "BAT") = true → batsR preR = 1 →
      preR.length = o.start ∧ o.nums.free = rootsOf preR) ∧
    (∀ preR r rest, D.2.2 = preR ++ r :: rest → (r.entry.name == "BAT") = true → batsR preR = 0 →
      preR.length = X.W.start ∧ X.W.nums.free = rootsOf preR) := by
  obtain ⟨_, fU, fO, fW⟩ := free_of_made m X D hT hX hD
  obtain ⟨_, sU, sO, sW⟩ := places_start m X hX
  unfold declPOf at hD
  obtain ⟨_, d1, d2⟩ := fileOf_entries hD
  refine ⟨fun preR r rest h1 h2 h3 =>
      free_seat_k D.2.1 preR r rest _ 0 X.U (d1 ▸ hT.2.1) sU fU h1 h2 h3,
    fun o ho preR r rest h1 h2 h3 =>
      free_seat_k D.2.1 preR r rest _ 1 o (d1 ▸ hT.2.1) (sO o ho) (fO o ho) h1 h2 h3,
    fun preR r rest h1 h2 h3 =>
      free_seat_k D.2.2 preR r rest _ 0 X.W (d2 ▸ hT.2.2) sW fW h1 h2 h3⟩

/-- The first chain's last test: no round named "BAT" stands behind its own. -/
theorem free_seat_L (m : Made) (X : Places4) (D : Decl3) (hT : PlanLike m)
    (hX : placesOfMade m = .ok X) (hD : declPOf m = .ok D) (preR : List Fmt.DeclaredRound)
    (r : Fmt.DeclaredRound) (rest : List Fmt.DeclaredRound) (hDs : D.1 = preR ++ r :: rest)
    (hr : (r.entry.name == "BAT") = true) (hk : batsR rest = 0) :
    preR.length = X.L.start ∧ X.L.nums.free = rootsOf preR := by
  obtain ⟨fL, _⟩ := free_of_made m X D hT hX hD
  obtain ⟨sL, _⟩ := places_start m X hX
  unfold declPOf at hD
  obtain ⟨d0, _⟩ := fileOf_entries hD
  have hs : X.L.start = preR.length := by
    rw [← batPlaces_names _ _ (d0 ▸ hT.1).1, hDs, List.map_append, List.map_cons,
      batPlaces_last (preR.map fun d : Fmt.DeclaredRound => d.entry) r.entry
        (rest.map fun d : Fmt.DeclaredRound => d.entry) hr hk] at sL
    rw [← Option.some.inj sL, List.length_map]
  exact ⟨hs.symm, free_at D.1 preR (r :: rest) _ _ hDs hs.symm fL⟩

end H2K.Made

#print axioms H2K.Made.batPlaces_at
#print axioms H2K.Made.places_start
#print axioms H2K.Made.free_seat
#print axioms H2K.Made.free_seat_L
