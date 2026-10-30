-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SendP3.lean: a yes of the kind's decision of a sending is a yes of the sending
that is written over the verifier program's own functions (sendP, with the round of the answers its
own), with the same numbers and the same record.

Main names: decideSend_parts; tag_fst, tag_snd, tag_filter_snd, zip_fst_snd; sendP_of_decide.

What is not claimed. One direction alone. The premises: the tests on the plan, every code's message
length a power of two, rounds that fit. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.SendP2
import Johnson.Desc.K1.Law.RowsOn
import Johnson.Desc.Own.RowsAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

variable {L : Type}

/-- What a yes of the decision holds, with the loop as it is called. -/
theorem decideSend_parts (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) :
    ∃ d₁, Ground.recvP P.gp.firstTree d P.sent = some (ids, d₁) ∧
      layRows P.codes (seedsOf P r₁) (ids.toList.zip (shapesOf P)) (answersIn r₂) d₁ = .ok d' := by
  unfold decideSend at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨x, h5, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨d₂, h8, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Except.ok.inj h)
  subst e2
  refine ⟨x.2, ?_, ?_⟩
  · rw [(named_ok _ _ _).1 h5, ← e1]
  · rw [← e1]
    exact h8

theorem tag_fst_len : ∀ (l : List OracleShape) (o : Nat), (tag o l).length = l.length
  | [], _ => rfl
  | _ :: l, o => by simp [tag, tag_fst_len l (o + 1)]

theorem tag_snd : ∀ (l : List OracleShape) (o : Nat), (tag o l).map Prod.snd = l
  | [], _ => rfl
  | s :: l, o => by simp [tag, tag_snd l (o + 1)]

theorem tag_filter_snd (l : List OracleShape) (o : Nat) :
    ((tag o l).filter fun x => x.2.answers != 0).map Prod.snd =
      l.filter fun s => s.answers != 0 := by
  have := List.filter_map (f := Prod.snd) (p := fun s : OracleShape => s.answers != 0)
    (l := tag o l)
  rw [tag_snd] at this
  rw [this]
  rfl

theorem zip_fst_snd {α β : Type} : ∀ l : List (α × β), (l.map Prod.fst).zip (l.map Prod.snd) = l
  | [] => rfl
  | x :: l => by simp [zip_fst_snd l]

/-- **A yes of the kind's decision is a yes of the sending over the program's own functions, with
the same numbers and the same record.** It returns beside them the elements drawn, the answers and
their number. -/
theorem sendP_of_decide (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (hB : planOkOwn P = true) (hl : P.codes.lengthsOk = true)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d')) :
    sendP groundG P.gp true d P.sent r₁ r₂ =
      some (ids, r₁.drawn.elems.map E.ofTriple, answersIn r₂, P.answers, d') := by
  obtain ⟨d₁, hrecv, hlay⟩ := decideSend_parts P owed d d' r₁ r₂ ids hyes
  obtain ⟨⟨_, hc, hnz, _, _⟩, _, _⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
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
      some ((seedsOf P r₁).map seedOf) := seedsOf_cut _ _ _ (draw_len P r₁ r₂ hfit)
  have hit : r₂.vals.map itemOf = List.replicate P.answers .answer := by
    rw [(fit_facts P r₁ r₂ hfit).2]
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, answerEntry]
  obtain ⟨hvl, han⟩ := answers_all r₂.vals P.answers hit
  have hans : answersOf { r₂ with vals := r₂.vals.take P.answers } = some (answersIn r₂) := by
    unfold answersOf
    show (r₂.vals.take P.answers).mapM _ = _
    rw [← hvl, List.take_length]
    exact han
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
  have hloop := sampleLoop_of_lay P.gp P.codes (seedsOf P r₁) hl _ (answersIn r₂) d₁ d' hq
    (by rw [← hzip]; exact hlay)
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := fit_more P r₁ r₂ hfit
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
    rw [draw_len P r₁ r₂ hfit, Nat.mul_comm]
    exact beq_self_eq_true _
  have hnz' : ((seedsOf P r₁).map seedOf).all (fun s => !isZeroE s.beta) = true := by
    rw [List.all_eq_true]
    intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    show (!isZeroE x.2) = true
    rw [hnz x hx]
    rfl
  have hal : ((answersIn r₂).length == P.answers) = true := by
    rw [answers_len P r₁ r₂ hfit]
    exact beq_self_eq_true _
  have hsil : silent r₂ = true := by simp [silent, f4, f5, f6]
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
    have c10 : (r₂.vals.length == P.answers) = true := by rw [hvl]; exact beq_self_eq_true _
    clear hloop hq hzip2 hans han hit hseeds hshapes htodo hget hidl hzip hor hlay hrecv hyes hr
    simp only [hne, hinc, hfresh, c4, c5, c6, hlen, hnz', hal, c10, hsil, Bool.not_false,
      Bool.not_true, Bool.and_self, Bool.or_true, Bool.false_or]

end VerifiableInference.Desc.K1
