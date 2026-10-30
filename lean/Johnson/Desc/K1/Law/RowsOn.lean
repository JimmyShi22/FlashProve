-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RowsOn.lean: every sample row that the sending lays is on its own message's
tables.

Main names: rowsOf_mem_inv, rowsOf_on, plan_msg, behind_rows_on.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Joined2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

variable {L : Type}

theorem rowsOf_mem_inv (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape)
    (ys : List E) (r : OnBytes.Row) (h : r ∈ (rowsOf codes seeds o s ys).toList) :
    ∃ sd ∈ seeds, ∃ i y, r = sampleRow (Msg.of codes s) o sd.1 sd.2 i y := by
  unfold rowsOf at h
  simp only [List.mem_map] at h
  obtain ⟨⟨⟨sd, y⟩, i⟩, hm, rfl⟩ := h
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some] at hm
  exact ⟨sd, List.mem_of_mem_take (List.mem_of_getElem? hm.1), i, y, rfl⟩

/-- **The sample rows of a message are on the message's own tables**: each has what the laying of a
row asks at the group whose one member is the message: at every statement that holds the message
under these codes and this shape. -/
theorem rowsOf_on (S : Statement) (o : Nat) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x)
    (seeds : List (List E × E)) (ys : List E)
    (hne : ((Msg.of S.codes x.shape).K != 0 || (Msg.of S.codes x.shape).Kzk != 0) = true)
    (hf : (Msg.of S.codes x.shape).padFits = true)
    (hz : ∀ sd ∈ seeds, (Msg.of S.codes x.shape).v ≤ sd.1.length) :
    ∀ r ∈ (rowsOf S.codes seeds o x.shape ys).toList,
      Means.RowIn S { code := 0, members := #[o] } r := by
  intro r hr
  obtain ⟨sd, hsd, i, y, rfl⟩ := rowsOf_mem_inv _ _ _ _ _ _ hr
  exact rowIn_sample S _ o x hx (by simp) sd.1 sd.2 i y hne hf (hz sd hsd)

/-- What the tests on the plan give of a sampled message's numbers. -/
theorem plan_msg (P : Par) (hB : planOkOwn P = true) (k : Fin (shapesOf P).length)
    (hk : sampledAt P k) :
    ((msgAt P k).K != 0 || (msgAt P k).Kzk != 0) = true ∧ (msgAt P k).padFits = true := by
  have hk' : (shapesOf P)[k.val].answers ≠ 0 := hk
  simp only [planOkOwn, planOk, Bool.and_eq_true] at hB
  constructor
  · have hmem : (shapesOf P)[k.val] ∈ shapesOf P := List.getElem_mem k.isLt
    obtain ⟨nn, hn, hnn⟩ := List.mem_map.1 hmem
    have := Array.all_eq_true_iff_forall_mem.1 hB.1.1.1 nn (Array.mem_toList_iff.1 hn)
    rw [hnn] at this
    simp only [← Own.sentShapeFits_agrees, Blk.shapeOk, Bool.and_eq_true, decide_eq_true_eq] at this
    have h0 := this.1.1.1
    show ((shapesOf P)[k.val].mainRows != 0 || (shapesOf P)[k.val].maskRows != 0) = true
    by_cases hm : (shapesOf P)[k.val].mainRows = 0
    · have : (shapesOf P)[k.val].maskRows ≠ 0 := by omega
      simp [this]
    · simp [hm]
  · refine List.all_eq_true.1 hB.2 _ ?_
    simp only [Par.tuple, List.mem_filter]
    exact ⟨List.getElem_mem k.isLt, by simpa using hk'⟩

/-- **Behind a yes of the sending, at a place that passes the tests on the plan and rounds that fit:
every sample row of every new message is on that message's own tables, at the statement behind.** -/
theorem behind_rows_on (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (hB : planOkOwn P = true) (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (o : Nat) (x : OnBytes.Oracle)
    (hx : d'.st.oracles[o]? = some x) (ho : d.st.oracles.size ≤ o) :
    ∀ r ∈ x.sampleRows.toList, Means.RowIn d'.st { code := 0, members := #[o] } r := by
  obtain ⟨⟨_, hc, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ho
  have hx' : (outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P) (answersIn r₂))[k]? =
      some x := by
    have h : (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
      (answersIn r₂)).toArray[d.st.oracles.size + k]? = some x := hx
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)] at h
    simpa using h
  have hlen : ∀ (shapes : List OracleShape) (o : Nat) (ys : List E),
      (outs P.codes (seedsOf P r₁) o shapes ys).length = shapes.length := by
    intro shapes
    induction shapes with
    | nil => intro o ys; rfl
    | cons s l ih => intro o ys; simp [outs, ih]
  have hk : k < (shapesOf P).length := by
    rw [← hlen (shapesOf P) d.st.oracles.size (answersIn r₂)]
    exact (List.getElem?_eq_some_iff.1 hx').1
  obtain ⟨ys', _, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
    d.st.oracles.size (answersIn r₂) hf k hk
  obtain rfl : wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys' = x :=
    Option.some.inj (hget.symm.trans hx')
  intro r hr
  by_cases h0 : (shapesOf P)[k].answers = 0
  · simp [wr, h0, fresh] at hr
  · have hs : sampledAt P ⟨k, hk⟩ := h0
    obtain ⟨h1, h2⟩ := plan_msg P hB ⟨k, hk⟩ hs
    have hshape : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys').shape =
        (shapesOf P)[k] := by
      unfold wr
      split <;> rfl
    have hcodes : (behind P d (seedsOf P r₁) (answersIn r₂)).st.codes = P.codes := hc
    have hdraw : (r₁.drawn.elems.map E.ofTriple).length = P.seeds * (P.coordinates + 1) :=
      draw_len P r₁ r₂ hfit
    have key := rowsOf_on _ _ _ hx (seedsOf P r₁) ys'
    rw [hcodes, hshape] at key
    refine key h1 h2 (fun sd hsd => ?_) r (by simpa [wr, h0] using hr)
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hsd
    rw [cutSeeds_get _ _ _ i sd hdraw hi]
    exact msgAt_v_le P ⟨k, hk⟩ hs

end VerifiableInference.Desc.K1
