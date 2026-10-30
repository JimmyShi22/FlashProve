-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SendP5.lean: THE OTHER DIRECTION: a yes of the sending that is written over the
verifier program's own functions (sendP, at either value of its flag) is a yes of the kind's
decision at the second round cut to the place's answers, with the same numbers and the same record.
So what is proved of the kind's decision holds of every block that calls sendP.

Main names: rowsFor_len; lay_of_sampleLoop; filterMap_of_mapM; decide_of_sendP.
The first part of the proof of decide_of_sendP is that of sendP_of_decide (SendP3.lean).

What is not claimed. The premises: the tests on the plan; every code's message length a power of
two; the record's codes are the plan's. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.SendP4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

variable {L : Type}

/-- The rows are made only where an answer is there for each. -/
theorem rowsFor_len (codes : Codes) (s : OracleShape) (o : Nat) (seeds : List SampleSeed) :
    ∀ (is : List Nat) (ys : List E) (acc : Array OnBytes.Row) (x : Array OnBytes.Row × List E),
      rowsFor codes s o seeds is ys acc = some x → is.length ≤ ys.length
  | [], _, _, _, _ => Nat.zero_le _
  | _ :: _, [], _, _, h => by simp [rowsFor] at h
  | i :: is, y :: ys, acc, x, h => by
    unfold rowsFor at h
    split at h
    · cases h
    · split at h
      · cases h
      · exact Nat.succ_le_succ (rowsFor_len codes s o seeds is ys _ x h)

/-- **The two loops, the other way.** -/
theorem lay_of_sampleLoop (p : GPar) (codes : Codes) (seeds : List (List E × E))
    (hl : codes.lengthsOk = true) :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : DState L),
    (∀ x ∈ l, x.2.answers ≠ 0 → Blk.shapeOk codes x.2 = true ∧
      (Msg.of codes x.2).padFits = true ∧ x.2.answers ≤ seeds.length) →
    sampleLoop groundG p codes (seeds.map seedOf) (l.filter fun x => x.2.answers != 0) ys d =
      some (d', []) →
    layRows codes seeds l ys d = .ok d'
  | [], ys, d, d', _, h => by
    have h' : some (d, ys) = some (d', ([] : List E)) := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    rfl
  | (o, s) :: l, ys, d, d', hq, h => by
    unfold layRows
    by_cases h0 : s.answers = 0
    · rw [if_pos (by simpa using h0)]
      rw [List.filter_cons_of_neg (by simpa using h0)] at h
      exact lay_of_sampleLoop p codes seeds hl l ys d d'
        (fun x hx => hq x (List.mem_cons_of_mem _ hx)) h
    · obtain ⟨q1, q2, q3⟩ := hq (o, s) List.mem_cons_self h0
      rw [List.filter_cons_of_pos (by simpa using h0)] at h
      unfold sampleLoop at h
      cases hr : rowsFor codes s o (seeds.map seedOf) (List.range s.answers) ys #[] with
      | none => rw [hr] at h; cases h
      | some x =>
        have hlen : s.answers ≤ ys.length := by
          have := rowsFor_len _ _ _ _ _ _ _ _ hr
          simpa using this
        have he := rowsFor_eq codes s o seeds ys hl q1 q2 q3 hlen
        rw [he] at h
        simp only at h
        cases ha : groundG.admit p d o (rowsOf codes seeds o s ys) with
        | none => rw [ha] at h; cases h
        | some d₁ =>
          rw [ha] at h
          have ih := lay_of_sampleLoop p codes seeds hl l (ys.drop s.answers) d₁ d'
            (fun x hx => hq x (List.mem_cons_of_mem _ hx)) h
          rw [if_neg (by simpa using h0), if_neg (by simpa using q3),
            if_neg (by simpa using hlen)]
          have ha' : Ground.admitP d o (rowsOf codes seeds o s ys) = some d₁ := ha
          exact (bind_ok _ _ _).2 ⟨d₁, (named_ok _ _ _).2 ha', ih⟩

/-- Items that are all read are read alike by the two ways. -/
theorem filterMap_of_mapM : ∀ (vals : List Fmt.ItemValue) (l : List E),
    (vals.mapM fun
      | .answer x => some (E.ofTriple x)
      | _ => none) = some l →
    (vals.filterMap fun | .answer x => some (E.ofTriple x) | _ => none) = l
  | [], l, h => by
    obtain rfl : [] = l := Option.some.inj h
    rfl
  | g :: vs, l, h => by
    rw [List.mapM_cons] at h
    cases g with
    | answer x =>
      cases hm : (vs.mapM fun
        | .answer x => some (E.ofTriple x)
        | _ => none) with
      | none => simp [hm] at h
      | some t =>
        simp [hm] at h
        subst h
        simp [filterMap_of_mapM vs t hm]
    | f _ => simp at h
    | e _ => simp at h
    | word _ => simp at h
    | root _ => simp at h

/-- **A yes of the sending over the program's own functions is a yes of the kind's decision**, at
the second round cut to the place's answers, with the same numbers and the same record. -/
theorem decide_of_sendP (P : Par) (own : Bool) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids' : Array Nat) (sd an : List E) (need : Nat) (hB : planOkOwn P = true)
    (hl : P.codes.lengthsOk = true) (hc : d.st.codes = P.codes)
    (h : sendP groundG P.gp own d P.sent r₁ r₂ = some (ids', sd, an, need, d')) :
    decideSend P none d [r₁, cutTo P r₂] = .ok (ids', d') ∧
      sd = r₁.drawn.elems.map E.ofTriple ∧ an = answersIn (cutTo P r₂) ∧ need = P.answers := by
  unfold sendP at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨⟨ids, d₁⟩, hr, h⟩ := Option.bind_eq_some_iff.1 h
  have hrecv : Ground.recvP P.gp.firstTree d P.sent = some (ids, d₁) := hr
  obtain ⟨_, lay2, hlay2, _, _⟩ := (recvP_iff _ _ _ _ _).1 hrecv
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
  simp only [htodo, hshapes, Option.bind_some, hcodes, hbits', hsd, hneed, Own.seedsMade_eq,
    ← Own.allZero_agrees, ← Own.rising_agrees, hzip2] at h
  obtain ⟨seeds', hs', h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨an', ha', h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · rename_i hcond
    obtain ⟨⟨d₂, left⟩, hloop, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · rename_i hleft
      obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨e2, e3⟩ := Prod.mk.inj e2
      obtain ⟨e3, e4⟩ := Prod.mk.inj e3
      obtain ⟨e4, e5⟩ := Prod.mk.inj e4
      subst e1 e2 e3 e4 e5
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, c2⟩, c3⟩, _⟩, _⟩, _⟩, c7⟩, c8⟩, _⟩, _⟩ := hcond
      have hdraw : (r₁.drawn.elems.map E.ofTriple).length = P.seeds * (P.coordinates + 1) := by
        rw [c7, Nat.mul_comm]
      have hseeds : seeds' = (seedsOf P r₁).map seedOf :=
        Option.some.inj (hs'.symm.trans (seedsOf_cut _ _ _ hdraw))
      have han : answersIn (cutTo P r₂) = an' := filterMap_of_mapM _ _ ha'
      have hleft' : left = [] := List.isEmpty_iff.1 hleft
      subst hseeds hleft'
      have hq' : ∀ x ∈ tag d.st.oracles.size (shapesOf P), x.2.answers ≠ 0 →
          Blk.shapeOk P.codes x.2 = true ∧ (Msg.of P.codes x.2).padFits = true ∧
            x.2.answers ≤ (seedsOf P r₁).length := by
        intro x hx h0
        obtain ⟨a, b⟩ := hq x hx h0
        refine ⟨a, b, ?_⟩
        have hm : x.2 ∈ shapesOf P := by
          rw [← tag_snd (shapesOf P) d.st.oracles.size]
          exact List.mem_map_of_mem hx
        obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hm
        rw [show (seedsOf P r₁).length = P.seeds from cutSeeds_length _ _ _, ← e]
        exact msgAt_answers_le P ⟨i, hi⟩
      have hlay := lay_of_sampleLoop P.gp P.codes (seedsOf P r₁) hl _ an' d₁ d₂ hq' hloop
      refine ⟨?_, rfl, han.symm, rfl⟩
      unfold decideSend
      refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2 rfl, ?_⟩
      refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2 (by simpa using hc), ?_⟩
      refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2
        (by rw [Own.treesCan_eq, ← hc, hlay2]; rfl), ?_⟩
      refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2 (List.all_eq_true.2 fun s hs => ?_), ?_⟩
      · rw [← Own.allZero_agrees]
        exact List.all_eq_true.1 c8 (seedOf s) (List.mem_map_of_mem hs)
      refine (bind_ok _ _ _).2 ⟨(ids, d₁), (named_ok _ _ _).2 hrecv, ?_⟩
      refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2 ?_, ?_⟩
      · show Own.rising (((ids.toList.zip (shapesOf P)).filter fun y =>
          y.2.answers != 0).map (·.1)) = true
        rw [hzip, ← Own.rising_agrees]
        exact c2
      refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2 ?_, ?_⟩
      · show (((ids.toList.zip (shapesOf P)).filter fun y => y.2.answers != 0).map (·.1)).all
          (fun o => ((d₁.st.oracles[o]?).map (!·.sampled)).getD false) = true
        rw [hzip]
        exact c3
      refine (bind_ok _ _ _).2 ⟨d₂, ?_, rfl⟩
      show layRows P.codes (seedsOf P r₁) (ids.toList.zip (shapesOf P))
        (answersIn (cutTo P r₂)) d₁ = .ok d₂
      rw [hzip, han]
      exact hlay
    · cases h
  · cases h

end VerifiableInference.Desc.K1
