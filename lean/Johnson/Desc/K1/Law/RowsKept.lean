-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RowsKept.lean: the messages' stored sample rows along the proof file's first
chain (the invariant of Johnson/Top/H0/K2Hands/SampleChain.lean: RowsInv QGoodS, KeepsInv
QGoodS): the share of K1's files: for the kind K1's three sub-protocols that send messages. A
sending lays new stored rows: here each such row is the program's own row at a seed, and the seed
is good. A law file; no running text imports it.
  cutSeeds_full: a seed that is cut off the round's sampled elements and whose factor is not zero
      has all its coordinates, and its factor is one of the sampled elements
  newInv_same: NewInv passes along SameRows
  decideSend_new: behind an accept of the kind's decision, on rounds whose sampled elements are in
      canonical form, under the kind's one condition on the list of rounds (condPort): each NEW
      message that has stored rows has one row, { Send.form cs s o ⟨z, β⟩ 0 with target := t }, with
      (Send.cube cs s).bits ≤ z.length, isZeroE β = false, okE β = true: NewInv QGoodS
  oldRows_sendAtS, oldRows_commitAtS, oldRows_firstAtS: an accept leaves the older messages' shapes
      and stored rows (OldRows): calls of keepsOld_*
  keepsInv_sendAtS, keepsInv_commitAtS, keepsInv_firstAtS, keepsInv_laterAt, keepsInv_wAt: so each
      keeps the invariant

Whence each clause. The row: form_eq (Johnson/Desc/K1/Law/FormEq.lean: the kind's sample row is the
program's row with the answer as its target). The factor is not zero: the kind's decision tests it
at every seed (asks, Writes3.lean). All coordinates: a factor that is not zero is not the filling
value, so the list was long enough. Canonical form: the factor is a sampled element, and OkDrawn
says it of these.

What is not claimed. condPort at a seated place: the kind's condition, a test on the list of rounds.
That the first chain of the IOP as written in Lean is made of these sub-protocols. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Top.H0.K2Hands.RowsGround
import Johnson.Desc.K1.Law.FormEq
import Johnson.Desc.K1.Law.GoodSend5
import Johnson.Desc.K1.Law.SeedIs
import Johnson.Desc.K1.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2

/-- A seed whose factor is not zero has all its coordinates, and its factor is in the list. -/
theorem cutSeeds_full (v : Nat) : ∀ (n : Nat) (l : List E) (i : Nat) (sd : List E × E),
    (cutSeeds v n l)[i]? = some sd → isZeroE sd.2 = false → sd.1.length = v ∧ sd.2 ∈ l
  | 0, _, i, sd, h, _ => by simp [cutSeeds] at h
  | n + 1, l, i, sd, h, hz => by
    cases i with
    | zero =>
      simp only [cutSeeds, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      cases hd : l.drop v with
      | nil =>
        simp only [hd, List.headD_nil] at hz
        exact absurd hz (by decide)
      | cons a t =>
        have hlen : v < l.length := by
          by_contra hn
          rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hn)] at hd
          cases hd
        refine ⟨by simp [List.length_take, Nat.le_of_lt hlen], ?_⟩
        show a ∈ l
        exact List.mem_of_mem_drop (i := v) (by rw [hd]; exact List.mem_cons_self)
    | succ j =>
      simp only [cutSeeds, List.getElem?_cons_succ] at h
      obtain ⟨a, b⟩ := cutSeeds_full v n (l.drop (v + 1)) j sd h hz
      exact ⟨a, List.mem_of_mem_drop b⟩

variable {Q : Codes → OracleShape → Nat → Array OnBytes.Row → Prop}

theorem newInv_same {n : Nat} {A B : Statement} (h : NewInv Q n A) (hs : SameRows A B) :
    NewInv Q n B := by
  intro o x ho hx hr
  have e := hs.2 o
  rw [hx] at e
  obtain ⟨x0, hx0, e0⟩ := Option.map_eq_some_iff.1 e.symm
  obtain ⟨e1, e3⟩ := Prod.mk.inj e0
  rw [hs.1, ← e1, ← e3]
  exact h o x0 ho hx0 (by rw [e3]; exact hr)

/-- **Behind an accept of the kind's decision each new stored row is the program's row at a good
seed.** -/
theorem decideSend_new {L : Type} (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true)
    (owed : Option Nat) (d d' : DState L) (rs : List Fmt.RoundView) (ids : Array Nat)
    (hr : ∀ r ∈ rs, OkDrawn r) (h : decideSend P owed d rs = .ok (ids, d')) :
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
    have hT : Tie P.codes (shapesOf P)[k] := cond_tie P rad hC ⟨k, hk⟩ hkS
    have h1 : 0 < P.seeds := one_le_seeds P ⟨k, hk⟩ hkS
    have hlenS : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
    obtain ⟨sd, hsd⟩ : ∃ sd, (seedsOf P r₁)[0]? = some sd :=
      ⟨(seedsOf P r₁)[0]'(by rw [hlenS]; exact h1), List.getElem?_eq_getElem _⟩
    obtain ⟨t, ht⟩ : ∃ t, ys'[0]? = some t :=
      ⟨ys'[0]'(Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hk') hy), List.getElem?_eq_getElem _⟩
    have hzs : isZeroE sd.2 = false := hz sd (List.mem_of_getElem? hsd)
    obtain ⟨hlen, hmem⟩ := cutSeeds_full _ _ _ _ sd hsd hzs
    have hshape : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys').shape =
        (shapesOf P)[k] := by
      unfold wr
      split <;> rfl
    have hrows : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k]
        ys').sampleRows = #[sampleRow (Msg.of P.codes (shapesOf P)[k]) (d.st.oracles.size + k)
          sd.1 sd.2 0 t] := by
      have e : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k]
          ys').sampleRows = rowsOf P.codes (seedsOf P r₁) (d.st.oracles.size + k)
            (shapesOf P)[k] ys' := by simp [wr, hk']
      rw [e]
      exact rowsOf_one _ _ _ _ _ hT.one sd t hsd ht
    rw [hcod, hshape, hrows]
    have hform := form_eq P.codes (shapesOf P)[k] (d.st.oracles.size + k) sd.1 sd.2 0 t
      hT.lengths hT.shape hT.fits
    obtain ⟨row, hrow, erow⟩ := Option.map_eq_some_iff.1 hform
    refine ⟨[⟨sd.1, sd.2⟩], ⟨by rw [hT.one]; rfl, fun i hi => ?_⟩, fun s' hs' => ?_⟩
    · obtain rfl : i = 0 := by
        have := hT.one
        have hi' : i < (shapesOf P)[k].answers := hi
        omega
      exact ⟨⟨sd.1, sd.2⟩, row, t, rfl, hrow, by rw [erow]; rfl⟩
    · obtain rfl : s' = ⟨sd.1, sd.2⟩ := by simpa using hs'
      refine ⟨?_, hzs, hr r₁ List.mem_cons_self sd.2 hmem⟩
      show (Send.cube P.codes (shapesOf P)[k]).bits ≤ sd.1.length
      rw [cube_bits, v_bitsZ, hlen]
      exact bits_le_coordinates P ⟨k, hk⟩ hkS

variable {Cl : Type}

/-! ## The older messages -/

theorem oldRows_sendAtS (P : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s rs gs = .ok s') : OldRows s.st s'.st :=
  oldRows_of_old (keepsOld_sendAtS P s s' rs gs h)

theorem oldRows_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    OldRows s.st s'.st := oldRows_of_old (keepsOld_commitAtS P link moment arrays s s' rs gs h)

theorem oldRows_firstAtS (q : Params.First) (gp : GPar) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s rs gs = .ok s') : OldRows s.st s'.st :=
  oldRows_of_old (keepsOld_firstAtS q gp s s' rs gs h)

/-! ## The three sub-protocols keep the invariant -/

theorem keepsInv_sendAtS (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true) :
    KeepsInv QGoodS (sendAtS P : Block S Cl) :=
  keepsInv_of_old (keepsOld_sendAtS P) fun s s' rs gs hr hy => by
    obtain ⟨ids, d', h1, e1, _⟩ := sendAtS_ok P s s' _ gs hy
    rw [e1]
    exact decideSend_new P rad hC _ (stateOf s (#[] : Array Nat)) d' rs ids hr h1

theorem keepsInv_commitAtS (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true)
    (link moment : Nat) (arrays : Option (List Nat)) :
    KeepsInv QGoodS (commitAtS P link moment arrays : Block S Cl) :=
  keepsInv_of_old (keepsOld_commitAtS P link moment arrays) fun s s' rs gs hr hy => by
    obtain ⟨t, y, e0, h1, e1, _⟩ := commitAtS_ok P link moment arrays s s' _ gs hy
    obtain ⟨ids, d₁, f', h2, h3⟩ := commitOwn_ok P link moment arrays t y _ gs h1
    have a := decideSend_new P rad hC _ _ d₁ rs ids hr h2
    rw [e0] at a
    rw [e1]
    exact newInv_same a (sameRows_of_same (joinOwnP_msgs _ _ _ _ _ _ _ h3))

theorem keepsInv_firstAtS (q : Params.First) (gp : GPar) (rad : Nat → Nat)
    (hC : condPort (firstPar q gp) rad = true) :
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
    have a := decideSend_new (firstPar q gp) rad hC _ d₁ d₂ rs ids hr h2
    rw [a0] at a
    rw [e1]
    exact newInv_same a (sameRows_of_same (joinOwnP_msgs _ _ _ _ _ _ _ h3))

/-- A segment's later sending. -/
theorem keepsInv_laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) (rad : Nat → Nat)
    (hC : condPort (parLater q gp link piece moment) rad = true) :
    KeepsInv QGoodS (laterAt q gp link piece moment arrays : Block S Cl) :=
  keepsInv_commitAtS _ rad hC link moment arrays

/-- W's sending. -/
theorem keepsInv_wAt (q : Params.First) (gp : GPar) (piece : Nat) (msg : Array OracleNotice)
    (rad : Nat → Nat) (hC : condPort (parW q gp piece msg) rad = true) :
    KeepsInv QGoodS (sendAtS (parW q gp piece msg) : Block S Cl) :=
  keepsInv_sendAtS _ rad hC

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.cutSeeds_full
#print axioms VerifiableInference.Desc.K1.decideSend_new
#print axioms VerifiableInference.Desc.K1.oldRows_sendAtS
#print axioms VerifiableInference.Desc.K1.oldRows_commitAtS
#print axioms VerifiableInference.Desc.K1.oldRows_firstAtS
#print axioms VerifiableInference.Desc.K1.keepsInv_sendAtS
#print axioms VerifiableInference.Desc.K1.keepsInv_commitAtS
#print axioms VerifiableInference.Desc.K1.keepsInv_firstAtS
#print axioms VerifiableInference.Desc.K1.keepsInv_laterAt
#print axioms VerifiableInference.Desc.K1.keepsInv_wAt
