-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RowsKeptPlan.lean:
Johnson/Desc/K1/Law/RowsKept.lean's law on the new stored sample rows behind a sending of the kind
K1, UNDER A LIGHTER PREMISE: in the place of the kind's condition condPort P rad (which also asks
one answer a sampled message, and a radius inside the Johnson range): THE SUB-PROTOCOL's OWN TEST ON
ITS PARAMETERS (planOkOwn P: its field planOk) and "every code's message length is a power of two".
Both are at hand wherever the IOP as written in Lean has passed its own test on the list of rounds:
so the law holds of the sub-protocols AS SEATED, with no tie to written values. A law file; no
running text imports it.
  rowsOf_get: the i-th stored row of a new message, by number
  decideSend_newP: NewInv QGoodS behind an accept of the kind's decision, at any number of
      answers: the stored rows are as many as the answers; the i-th is { Send.form cs s o ⟨z_i, β_i⟩
      i with target := y_i } at the round's i-th seed; every seed of the round has (Send.cube cs
      s).bits ≤ z.length, isZeroE β = false, okE β = true
  planOwn_sendAtS, planOwn_commitAtS, planOwn_firstAtS: the sub-protocol's field planOk gives
      planOkOwn P
  keepsInv_sendAtS_plan, keepsInv_commitAtS_plan, keepsInv_firstAtS_plan, keepsInv_laterAt_plan,
      keepsInv_wAt_plan: KeepsInv QGoodS from b.planOk = true and the codes' lengths

What is not claimed. That the first chain of the IOP as written in Lean is made of these
sub-protocols. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.RowsKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2

/-- The i-th stored row of a new message. -/
theorem rowsOf_get (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape)
    (ys : List E) (i : Nat) (hi : i < s.answers) (sd : List E × E) (y : E)
    (h1 : seeds[i]? = some sd) (h2 : ys[i]? = some y) :
    (rowsOf codes seeds o s ys)[i]? = some (sampleRow (Msg.of codes s) o sd.1 sd.2 i y) := by
  have hz : ((seeds.take s.answers).zip (ys.take s.answers))[i]? = some (sd, y) :=
    List.getElem?_zip_eq_some.2 ⟨by rw [List.getElem?_take_of_lt hi]; exact h1,
      by rw [List.getElem?_take_of_lt hi]; exact h2⟩
  simp [rowsOf, List.getElem?_zipIdx, hz]

/-- **Behind an accept of the kind's decision**, under the sub-protocol's own test on its
parameters and the codes' lengths. -/
theorem decideSend_newP {L : Type} (P : Par) (hB : planOkOwn P = true)
    (hl : P.codes.lengthsOk = true) (owed : Option Nat) (d d' : DState L) (rs : List Fmt.RoundView)
    (ids : Array Nat) (hr : ∀ r ∈ rs, OkDrawn r) (h : decideSend P owed d rs = .ok (ids, d')) :
    NewInv QGoodS d.st.oracles.size d'.st := by
  match rs, hr, h with
  | [r₁, r₂], hr, h =>
    obtain ⟨⟨_, hc, hz, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
    intro o x ho hx hs
    have hcod : (behind P d (seedsOf P r₁) (answersIn r₂)).st.codes = P.codes :=
      (kept_behind P d _ _).1.trans hc
    obtain ⟨k, rfl⟩ : ∃ k, o = d.st.oracles.size + k := ⟨o - d.st.oracles.size, by omega⟩
    have hx' : (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
        (answersIn r₂)).toArray[d.st.oracles.size + k]? = some x := hx
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)] at hx'
    have hx2 : (outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P) (answersIn r₂))[k]? =
        some x := by simpa using hx'
    have hk : k < (shapesOf P).length := by
      have := (List.getElem?_eq_some_iff.1 hx2).1
      rwa [outs_length] at this
    obtain ⟨ys', hy, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
      d.st.oracles.size (answersIn r₂) hf k hk
    obtain rfl : wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys' = x :=
      Option.some.inj (hget.symm.trans hx2)
    have hk' : (shapesOf P)[k].answers ≠ 0 := by
      intro h0
      apply hs
      simp [wr, h0, fresh]
    have hkS : sampledAt P ⟨k, hk⟩ := hk'
    have hsh : Blk.shapeOk P.codes (shapesOf P)[k] = true := plan_shape P hB ⟨k, hk⟩
    have hpad : (Msg.of P.codes (shapesOf P)[k]).padFits = true := (plan_msg P hB ⟨k, hk⟩ hkS).2
    have hlenS : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
    have hle : (shapesOf P)[k].answers ≤ (seedsOf P r₁).length := by
      rw [hlenS]
      exact msgAt_answers_le P ⟨k, hk⟩
    have hshape : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys').shape =
        (shapesOf P)[k] := by
      unfold wr
      split <;> rfl
    have hrows : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k]
        ys').sampleRows = rowsOf P.codes (seedsOf P r₁) (d.st.oracles.size + k)
          (shapesOf P)[k] ys' := by simp [wr, hk']
    rw [hcod, hshape, hrows]
    refine ⟨(seedsOf P r₁).map fun sd => (⟨sd.1, sd.2⟩ : SampleSeed),
      ⟨rowsOf_size _ _ _ _ _ hle hy, fun i hi => ?_⟩, fun s' hs' => ?_⟩
    · obtain ⟨sd, hsd⟩ : ∃ sd, (seedsOf P r₁)[i]? = some sd :=
        ⟨(seedsOf P r₁)[i]'(Nat.lt_of_lt_of_le hi hle), List.getElem?_eq_getElem _⟩
      obtain ⟨y, hyi⟩ : ∃ y, ys'[i]? = some y :=
        ⟨ys'[i]'(Nat.lt_of_lt_of_le hi hy), List.getElem?_eq_getElem _⟩
      have hform := form_eq P.codes (shapesOf P)[k] (d.st.oracles.size + k) sd.1 sd.2 i y hl hsh
        hpad
      obtain ⟨row, hrow, erow⟩ := Option.map_eq_some_iff.1 hform
      refine ⟨⟨sd.1, sd.2⟩, row, y, by simp [hsd], hrow, ?_⟩
      rw [rowsOf_get _ _ _ _ _ i hi sd y hsd hyi, erow]
    · obtain ⟨sd, hmemS, rfl⟩ := List.mem_map.1 hs'
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmemS
      have hzs : isZeroE sd.2 = false := hz sd hmemS
      obtain ⟨hlen, hmem⟩ := cutSeeds_full _ _ _ _ sd hi hzs
      refine ⟨?_, hzs, hr r₁ List.mem_cons_self sd.2 hmem⟩
      show (Send.cube P.codes (shapesOf P)[k]).bits ≤ sd.1.length
      rw [cube_bits, v_bitsZ, hlen]
      exact bits_le_coordinates P ⟨k, hk⟩ hkS

variable {Cl : Type}

/-! ## The sub-protocol's own test on its parameters -/

theorem planOwn_sendAtS {P : Par} (h : (sendAtS P : Block S Cl).planOk = true) :
    planOkOwn P = true := h

theorem planOwn_commitAtS {P : Par} {link moment : Nat} {arrays : Option (List Nat)}
    (h : (commitAtS P link moment arrays : Block S Cl).planOk = true) : planOkOwn P = true := by
  have h' : (planOkOwn P && arrays.isSome) = true := h
  exact (Bool.and_eq_true _ _ ▸ h').1

theorem planOwn_firstAtS {q : Params.First} {gp : GPar}
    (h : (firstSegmentOpening q gp : Block S Cl).planOk = true) : planOkOwn (firstPar q gp) = true := by
  have h' : (planOkOwn (firstPar q gp) && firstPlanOk q gp.samples) = true := h
  exact (Bool.and_eq_true _ _ ▸ h').1

/-! ## The sub-protocols keep the invariant -/

theorem keepsInv_sendAtS_plan (P : Par) (hp : (sendAtS P : Block S Cl).planOk = true)
    (hl : P.codes.lengthsOk = true) : KeepsInv QGoodS (sendAtS P : Block S Cl) :=
  keepsInv_of_old (keepsOld_sendAtS P) fun s s' rs gs hr hy => by
    obtain ⟨ids, d', h1, e1, _⟩ := sendAtS_ok P s s' _ gs hy
    rw [e1]
    exact decideSend_newP P (planOwn_sendAtS hp) hl _ (stateOf s (#[] : Array Nat)) d' rs ids hr h1

theorem keepsInv_commitAtS_plan (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (hp : (commitAtS P link moment arrays : Block S Cl).planOk = true)
    (hl : P.codes.lengthsOk = true) :
    KeepsInv QGoodS (commitAtS P link moment arrays : Block S Cl) :=
  keepsInv_of_old (keepsOld_commitAtS P link moment arrays) fun s s' rs gs hr hy => by
    obtain ⟨t, y, e0, h1, e1, _⟩ := commitAtS_ok P link moment arrays s s' _ gs hy
    obtain ⟨ids, d₁, f', h2, h3⟩ := commitOwn_ok P link moment arrays t y _ gs h1
    have a := decideSend_newP P (planOwn_commitAtS hp) hl _ _ d₁ rs ids hr h2
    rw [e0] at a
    rw [e1]
    exact newInv_same a (sameRows_of_same (joinOwnP_msgs _ _ _ _ _ _ _ h3))

theorem keepsInv_firstAtS_plan (q : Params.First) (gp : GPar)
    (hp : (firstSegmentOpening q gp : Block S Cl).planOk = true) (hl : q.codes.lengthsOk = true) :
    KeepsInv QGoodS (firstSegmentOpening q gp : Block S Cl) :=
  keepsInv_of_old (keepsOld_firstAtS q gp) fun s s' rs gs hr hy => by
    obtain ⟨c, d', h1, e1, _⟩ := firstAtS_ok q gp s s' _ gs hy
    obtain ⟨g, d₁, ids, d₂, h0, h2, f₁, own, mine, f₂, h3⟩ := firstOwn_ok _ _ _ _ _ _ _ h1
    have a0 : d₁.st.oracles = (stateOf s ()).st.oracles := by
      unfold Ground.newGroupP at h0
      split at h0
      · obtain rfl : _ = d₁ := (Prod.mk.inj (Option.some.inj h0)).2
        rfl
      · cases h0
    have a := decideSend_newP (firstPar q gp) (planOwn_firstAtS hp) hl _ d₁ d₂ rs ids hr h2
    rw [a0] at a
    rw [e1]
    exact newInv_same a (sameRows_of_same (joinOwnP_msgs _ _ _ _ _ _ _ h3))

theorem keepsInv_laterAt_plan (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat))
    (hp : (laterAt q gp link piece moment arrays : Block S Cl).planOk = true)
    (hl : q.codes.lengthsOk = true) :
    KeepsInv QGoodS (laterAt q gp link piece moment arrays : Block S Cl) :=
  keepsInv_commitAtS_plan _ link moment arrays hp hl

theorem keepsInv_wAt_plan (q : Params.First) (gp : GPar) (piece : Nat) (msg : Array OracleNotice)
    (hp : (sendAtS (parW q gp piece msg) : Block S Cl).planOk = true)
    (hl : q.codes.lengthsOk = true) :
    KeepsInv QGoodS (sendAtS (parW q gp piece msg) : Block S Cl) :=
  keepsInv_sendAtS_plan _ hp hl

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.rowsOf_get
#print axioms VerifiableInference.Desc.K1.decideSend_newP
#print axioms VerifiableInference.Desc.K1.keepsInv_sendAtS_plan
#print axioms VerifiableInference.Desc.K1.keepsInv_commitAtS_plan
#print axioms VerifiableInference.Desc.K1.keepsInv_firstAtS_plan
#print axioms VerifiableInference.Desc.K1.keepsInv_laterAt_plan
#print axioms VerifiableInference.Desc.K1.keepsInv_wAt_plan
