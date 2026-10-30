-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SendP4.lean: a yes of the kind's decision of a sending whose answers are the
first items of a round in which the caller goes on (decideOpen, Johnson/Desc/K1/Open.lean) is a yes
of the sending that is written over the verifier program's own functions with the round of the
answers not its own (sendP at own := false), with the same numbers, the same count of items taken
and the same record.

Main names: cutTo; sum_answers, fitB_len (the counts fit only where the answers are as many as the
place's); mapM_of_len; sendP_of_cut; sendP_of_open.
The proof of sendP_of_cut follows that of sendP_of_decide (SendP3.lean) step by step.

What is not claimed. One direction alone. The premises: the tests on the plan; every code's message
length a power of two; the first round shows no item and draws as many elements as the place's seeds
take, no position and no matrix entry. Nothing is asked or said of what the second round draws or of
its other items. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.SendP3
import Johnson.Desc.K1.Open

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

variable {L : Type}

/-- The second round, cut to the place's answers. -/
def cutTo (P : Par) (r₂ : Fmt.RoundView) : Fmt.RoundView := { r₂ with vals := r₂.vals.take P.answers }

theorem foldl_answers : ∀ (l : List OracleShape) (a : Nat),
    l.foldl (fun a s => a + s.answers) a = a + (l.map fun s => s.answers).sum
  | [], a => by simp
  | s :: l, a => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, foldl_answers l]
    omega

theorem sum_filter : ∀ l : List OracleShape,
    ((l.filter fun s => s.answers != 0).map fun s => s.answers).sum =
      (l.map fun s => s.answers).sum
  | [] => rfl
  | s :: l => by
    by_cases h : s.answers = 0
    · simp [h, sum_filter l]
    · simp [h, sum_filter l]

/-- The place's answers are the sum of its messages'. -/
theorem sum_answers (P : Par) : P.answers = ((shapesOf P).map fun s => s.answers).sum := by
  unfold Par.answers Par.tuple
  rw [foldl_answers, Nat.zero_add]
  exact sum_filter _

theorem fitB_sum (codes : Codes) (n : Nat) : ∀ (l : List OracleShape) (ys : List E),
    fitB codes n l ys = true → ys.length = (l.map fun s => s.answers).sum
  | [], ys, h => by
    simp only [fitB, List.isEmpty_iff] at h
    subst h
    rfl
  | s :: l, ys, h => by
    unfold fitB at h
    by_cases h0 : s.answers = 0
    · rw [if_pos h0] at h
      simp [h0, fitB_sum codes n l ys h]
    · rw [if_neg h0] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have ih := fitB_sum codes n l _ h.2
      rw [List.length_drop] at ih
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **The counts fit only where the answers are as many as the place's.** -/
theorem fitB_len (P : Par) (ys : List E) (h : fitB P.codes P.seeds (shapesOf P) ys = true) :
    ys.length = P.answers := by
  rw [sum_answers]
  exact fitB_sum _ _ _ _ h

/-- Items of which as many are answers as there may be items are all answers. -/
theorem mapM_of_len : ∀ (vals : List Fmt.ItemValue) (n : Nat), vals.length ≤ n →
    (vals.filterMap fun | .answer x => some (E.ofTriple x) | _ => none).length = n →
    (vals.mapM fun
      | .answer x => some (E.ofTriple x)
      | _ => none) = some (vals.filterMap fun | .answer x => some (E.ofTriple x) | _ => none)
  | [], _, _, _ => rfl
  | g :: l, n, h1, h2 => by
    have hle := List.length_filterMap_le
      (fun | Fmt.ItemValue.answer x => some (E.ofTriple x) | _ => none) l
    cases g with
    | answer x =>
      cases n with
      | zero => simp at h1
      | succ n =>
        have ih := mapM_of_len l n (by simpa using h1) (by simpa using h2)
        simp [List.mapM_cons, ih]
    | f _ => simp only [List.filterMap_cons, List.length_cons] at h1 h2; omega
    | e _ => simp only [List.filterMap_cons, List.length_cons] at h1 h2; omega
    | word _ => simp only [List.filterMap_cons, List.length_cons] at h1 h2; omega
    | root _ => simp only [List.filterMap_cons, List.length_cons] at h1 h2; omega

/-- **A yes of the kind's decision at the second round cut to the place's answers is a yes of the
sending over the program's own functions, with the round of the answers not its own.** -/
theorem sendP_of_cut (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (hB : planOkOwn P = true) (hl : P.codes.lengthsOk = true)
    (hdraw : (r₁.drawn.elems.map E.ofTriple).length = P.seeds * (P.coordinates + 1))
    (f1 : r₁.vals = []) (f2 : r₁.drawn.poss = []) (f3 : r₁.drawn.trits = [])
    (hyes : decideSend P owed d [r₁, cutTo P r₂] = .ok (ids, d')) :
    sendP groundG P.gp false d P.sent r₁ r₂ =
      some (ids, r₁.drawn.elems.map E.ofTriple, answersIn (cutTo P r₂), P.answers, d') := by
  obtain ⟨d₁, hrecv, hlay⟩ := decideSend_parts P owed d d' r₁ (cutTo P r₂) ids hyes
  obtain ⟨⟨_, hc, hnz, _, hfB⟩, _, _⟩ := (decideSend_iff P owed d d' r₁ (cutTo P r₂) ids).1 hyes
  obtain ⟨_, lay, _, hids, hd₁⟩ := (recvP_iff _ _ _ _ _).1 hrecv
  have hor : d₁.st.oracles.toList = d.st.oracles.toList ++ (shapesOf P).map fresh := by
    rw [hd₁]
    exact recvD_toList _ d P lay
  have hcodes : d₁.st.codes = P.codes := by
    rw [hd₁]
    exact hc
  have hzip : ids.toList.zip (shapesOf P) = tag d.st.oracles.size (shapesOf P) := by
    rw [hids]
    exact ids_zip P _
  have hidl : ids.toList = (tag d.st.oracles.size (shapesOf P)).map Prod.fst := by
    rw [← hzip, List.map_fst_zip]
    rw [hids]
    simp [shapesOf]
  have hget : ∀ x ∈ tag d.st.oracles.size (shapesOf P),
      d₁.st.oracles[x.1]? = some (fresh x.2) := by
    have := tag_get d₁.st.oracles (shapesOf P) d.st.oracles.toList hor
    simpa using this
  have htodo : (ids.toList.filter fun o =>
      ((d₁.st.oracles[o]?).map (·.shape.answers)).getD 0 != 0) =
      ((tag d.st.oracles.size (shapesOf P)).filter fun x => x.2.answers != 0).map Prod.fst := by
    rw [hidl, List.filter_map]
    congr 1
    refine List.filter_congr fun x hx => ?_
    simp [Function.comp, hget x hx, fresh]
  have hshapes : (((tag d.st.oracles.size (shapesOf P)).filter fun x =>
      x.2.answers != 0).map Prod.fst).mapM (fun o => (d₁.st.oracles[o]?).map (·.shape)) =
      some P.tuple := by
    rw [mapM_tagged _ _ (fun x hx => by rw [hget x (List.mem_of_mem_filter hx)]; rfl),
      tag_filter_snd]
    rfl
  have hbits : P.tuple.foldl (fun b s => max b (Send.cube d₁.st.codes s).bits) 0 =
      P.coordinates := by
    rw [hcodes]
    unfold Par.coordinates
    congr 1
    funext b s
    rw [cube_bits]
  have hbits' : P.tuple.foldl (fun b s => max b (Send.cube P.codes s).bits) 0 =
      P.coordinates := by
    rw [← hcodes]
    exact hbits
  have hsd : P.tuple.foldl (fun a s => max a s.answers) 0 = P.seeds := rfl
  have hneed : P.tuple.foldl (fun a s => a + s.answers) 0 = P.answers := rfl
  have hseeds : Send.seedsOf P.coordinates P.seeds (r₁.drawn.elems.map E.ofTriple) =
      some ((seedsOf P r₁).map seedOf) := seedsOf_cut _ _ _ hdraw
  have hcount : (answersIn (cutTo P r₂)).length = P.answers := fitB_len P _ hfB
  have hans : answersOf { r₂ with vals := r₂.vals.take P.answers } =
      some (answersIn (cutTo P r₂)) :=
    mapM_of_len (r₂.vals.take P.answers) P.answers (List.length_take_le _ _) hcount
  have hzip2 : (((tag d.st.oracles.size (shapesOf P)).filter fun x =>
      x.2.answers != 0).map Prod.fst).zip P.tuple =
      (tag d.st.oracles.size (shapesOf P)).filter fun x => x.2.answers != 0 := by
    have e : P.tuple = ((tag d.st.oracles.size (shapesOf P)).filter fun x =>
        x.2.answers != 0).map Prod.snd := (tag_filter_snd _ _).symm
    rw [e, zip_fst_snd]
  have hq : ∀ x ∈ tag d.st.oracles.size (shapesOf P), x.2.answers ≠ 0 →
      Blk.shapeOk P.codes x.2 = true ∧ (Msg.of P.codes x.2).padFits = true := by
    intro x hx h0
    have hm : x.2 ∈ shapesOf P := by
      rw [← tag_snd (shapesOf P) d.st.oracles.size]
      exact List.mem_map_of_mem hx
    simp only [planOkOwn, planOk, Bool.and_eq_true] at hB
    obtain ⟨nn, hn, hnn⟩ := List.mem_map.1 hm
    have h1 := Array.all_eq_true_iff_forall_mem.1 hB.1.1.1 nn (Array.mem_toList_iff.1 hn)
    rw [hnn] at h1
    exact ⟨h1, List.all_eq_true.1 hB.2 x.2 (List.mem_filter.2 ⟨hm, by simpa using h0⟩)⟩
  have hloop := sampleLoop_of_lay P.gp P.codes (seedsOf P r₁) hl _ (answersIn (cutTo P r₂)) d₁ d' hq
    (by rw [← hzip]; exact hlay)
  have hr : groundG.recv P.gp d P.sent = some (ids, d₁) := hrecv
  have hne : (((tag d.st.oracles.size (shapesOf P)).filter fun x =>
      x.2.answers != 0).map Prod.fst).isEmpty = false := by
    have h3 : P.tuple.isEmpty = false := by
      simp only [planOkOwn, planOk, Bool.and_eq_true] at hB
      simpa using hB.1.2
    have e : P.tuple = ((tag d.st.oracles.size (shapesOf P)).filter fun x =>
        x.2.answers != 0).map Prod.snd := (tag_filter_snd _ _).symm
    rw [e] at h3
    cases hh : (tag d.st.oracles.size (shapesOf P)).filter fun x => x.2.answers != 0 with
    | nil => rw [hh] at h3; simp at h3
    | cons a b => rfl
  have hinc : Fmt.increasing (((tag d.st.oracles.size (shapesOf P)).filter fun x =>
      x.2.answers != 0).map Prod.fst) = true :=
    increasing_of_pairwise _ ((tag_pairwise (shapesOf P) d.st.oracles.size).sublist
      (List.filter_sublist.map Prod.fst))
  have hfresh : (((tag d.st.oracles.size (shapesOf P)).filter fun x =>
      x.2.answers != 0).map Prod.fst).all
      (fun o => ((d₁.st.oracles[o]?).map (!·.sampled)).getD false) = true := by
    rw [List.all_eq_true]
    intro o ho
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ho
    rw [hget x (List.mem_of_mem_filter hx)]
    rfl
  have hlen : ((r₁.drawn.elems.map E.ofTriple).length == (P.coordinates + 1) * P.seeds) = true := by
    rw [hdraw, Nat.mul_comm]
    exact beq_self_eq_true _
  have hnz' : ((seedsOf P r₁).map seedOf).all (fun s => !isZeroE s.beta) = true := by
    rw [List.all_eq_true]
    intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    show (!isZeroE x.2) = true
    rw [hnz x hx]
    rfl
  have hal : ((answersIn (cutTo P r₂)).length == P.answers) = true := by
    rw [hcount]
    exact beq_self_eq_true _
  unfold sendP
  simp only [hr, Option.bind_eq_bind, Option.bind_some, htodo, hshapes, hcodes, hbits', hsd, hneed,
    Own.seedsMade_eq, ← Own.allZero_agrees, ← Own.rising_agrees, hseeds, hans, hzip2]
  split
  · simp only [hloop, Option.bind_some, List.isEmpty_nil, if_true]
  · rename_i hcond
    refine absurd ?_ hcond
    have c4 : r₁.vals.isEmpty = true := by rw [f1]; rfl
    have c5 : r₁.drawn.poss.isEmpty = true := by rw [f2]; rfl
    have c6 : r₁.drawn.trits.isEmpty = true := by rw [f3]; rfl
    clear hloop hq hzip2 hans hseeds hshapes htodo hget hidl hzip hor hlay hrecv hyes hr
    simp only [hne, hinc, hfresh, c4, c5, c6, hlen, hnz', hal, Bool.not_false, Bool.and_self,
      Bool.true_or]

/-- **A yes of the decision where the caller goes on in the round of the answers.** -/
theorem sendP_of_open (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (n : Nat) (hB : planOkOwn P = true) (hl : P.codes.lengthsOk = true)
    (hdraw : (r₁.drawn.elems.map E.ofTriple).length = P.seeds * (P.coordinates + 1))
    (f1 : r₁.vals = []) (f2 : r₁.drawn.poss = []) (f3 : r₁.drawn.trits = [])
    (hopen : decideOpen P owed d [r₁, r₂] = .ok (ids, n, d')) :
    n = P.answers ∧ sendP groundG P.gp false d P.sent r₁ r₂ =
      some (ids, r₁.drawn.elems.map E.ofTriple, answersIn (cutTo P r₂), n, d') := by
  have hopen' : (decideSend P owed d [r₁, cutTo P r₂]).map (fun x => (x.1, P.answers, x.2)) =
      .ok (ids, n, d') := hopen
  cases hyes : decideSend P owed d [r₁, cutTo P r₂] with
  | error e =>
    rw [hyes] at hopen'
    cases hopen'
  | ok x =>
    rw [hyes] at hopen'
    obtain ⟨e1, e23⟩ := Prod.mk.inj (Except.ok.inj hopen')
    obtain ⟨e2, e3⟩ := Prod.mk.inj e23
    subst e1 e2 e3
    exact ⟨rfl, sendP_of_cut P owed d x.2 r₁ r₂ x.1 hB hl hdraw f1 f2 f3 hyes⟩

end VerifiableInference.Desc.K1
